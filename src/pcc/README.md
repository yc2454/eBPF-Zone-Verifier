# PCC — Proof-Carrying Code Module

This module implements certificate-aided verification for eBPF programs. It lets a **zone-mode producer** attach a lightweight proof to a program so that a **interval-mode checker** can accept packet accesses that would otherwise be rejected — without running the full zone analysis at check time.

## Background

The kernel's interval verifier rejects programs that use variable-offset pointer arithmetic (e.g. `r5 += r4`) before a packet load, because it cannot track the resulting pointer offset precisely enough to prove the access is in bounds. The zone domain *can* prove these accesses safe using relational constraints, but the zone domain is not available in the kernel verifier.

PCC bridges this gap: the zone analysis runs once (offline) and emits a certificate encoding the key relational facts it derived. The interval checker replays just those facts at the relevant program points, re-derives the safety bound, and admits the access.

## Architecture

```
  [Zone analysis] ──generates──> [Certificate (.cert.json)]
                                         │
                                         ▼
  [Interval analysis] ──checks──> [Checker (this module)]
                                         │
                                         ▼
                     accepted / skipped (fail-closed)
```

The **certificate is not trusted**. The checker independently verifies every step against the program's own instruction stream and the interval abstract state. A malformed or adversarial certificate can only cause entries to be silently skipped — it cannot cause an unsafe program to be accepted.

## Certificate Format

Certificates are JSON files (v2 schema) with the following structure:

```json
{
  "version": 2,
  "program_hash": "<fnv1a hex>",
  "pc_annotations": [
    {
      "pc": 10,
      "entries": [
        {
          "left_reg": 6,
          "right_reg": 14,
          "bound": -5,
          "proof": [
            { "kind": "Guard", "pc": 9, "left_reg": 6, "right_reg": 14, "c": -8 },
            { "kind": "Transfer", "pc": 9,
              "pre_left_reg": 6, "pre_right_reg": 14,
              "post_left_reg": 6, "post_right_reg": 14,
              "delta": 3 }
          ]
        }
      ]
    }
  ]
}
```

### Fields

- **`program_hash`** — FNV-1a hash of the program's instruction bytes. The checker rejects the certificate immediately if this does not match.
- **`pc`** — the program counter of the instruction being annotated (i.e. the load instruction whose safety is being proven).
- **`left_reg`, `right_reg`** — register indices for the constraint `left_reg - right_reg <= bound`. See the register index table below.
- **`bound`** — the claimed upper bound. Must equal `Guard.c + sum(Transfer.delta)`.
- **`proof`** — ordered chain of proof steps: one Guard followed by zero or more Transfers. See [Proof Steps](#proof-steps).

### Register Index Table

| Index | Register |
|-------|----------|
| 0 | Zero (constant 0) |
| 1–10 | R0–R9 |
| 11 | R10 (frame pointer) |
| 12 | `@data_meta` anchor |
| 13 | `@data` anchor |
| 14 | `@end` anchor |

Packet safety annotations almost always use `right_reg = 14` (`@end`), expressing that a register lies at least `|bound|` bytes before the end of the packet.

## Proof Steps

Each annotation entry contains a forward chain of steps that together prove `left_reg - right_reg <= bound`. Two step types are available.

### `Guard`

```json
{ "kind": "Guard", "pc": 9, "left_reg": 6, "right_reg": 14, "c": -8 }
```

The base case of the proof chain. Asserts that the interval pre-state at `pc` proves `left_reg - right_reg <= c`. Placed at the **divergence point** — the instruction where zone and interval first disagree on the tracked constraint.

The checker verifies this via two paths:
1. **State-derived** (most common): `distance_upper_bound(state, left, right) <= c`.
2. **Branch-derived**: the instruction at `pc` is a conditional branch and the branch condition implies the constraint.

| Branch | Edge | Constraint |
|--------|------|------------|
| `JGE dst, src` | fall-through | `dst - src <= -1` |
| `JGT dst, src` | fall-through | `dst - src <= 0`  |
| `JGE dst, src` | taken         | `src - dst <= 0`  |
| `JGT dst, src` | taken         | `src - dst <= -1` |

### `Transfer`

```json
{ "kind": "Transfer", "pc": 9,
  "pre_left_reg": 6, "pre_right_reg": 14,
  "post_left_reg": 6, "post_right_reg": 14,
  "delta": 3 }
```

The inductive step. Asserts that the instruction at `pc` transforms a constraint on `(pre_left_reg, pre_right_reg)` into a constraint on `(post_left_reg, post_right_reg)` with a bound shift of `delta`.

The checker verifies this by looking up the interval pre-state and the instruction at `pc`:

| Instruction | Effect | Delta |
|-------------|--------|-------|
| `mov dst, src` | If `pre_left_reg == src`, track value in `dst` | 0 |
| `add dst, imm` | If `pre_left_reg == dst`, bound shifts | `imm` |
| `add dst, src_reg` | If `pre_left_reg == dst`, bound shifts by `ub(src)` | `>= ub(src)` |
| Other (no tracked write) | Passthrough | 0 |
| Other (writes tracked reg) | **Rejected** | — |

### Chain Rules

A valid proof chain must satisfy:

1. **Structure** — `proof[0]` is a Guard; all subsequent steps are Transfers.
2. **Connectivity** — `Transfer[k].(pre_left_reg, pre_right_reg) == prev_step.(post_left_reg, post_right_reg)`.
3. **Endpoints** — last step's `(post_left_reg, post_right_reg) == entry.(left_reg, right_reg)`.
4. **Sum** — `Guard.c + Σ Transfer.delta == entry.bound`.
5. **PC ordering** — Guard PC <= first Transfer PC (may be equal); subsequent strictly increasing; all < target PC.

## Checker Behavior

At each annotated PC, the checker:

1. Verifies the certificate hash matches the program.
2. For each entry at that PC, replays the proof chain step by step, looking up the interval pre-state at each step's PC from `explored_states`.
3. If all steps pass, the sum matches, and endpoint registers match, refines the successor interval state with the proven `left_reg - right_reg <= bound` fact (sets the pointer's `range` field).
4. If any step fails, the entry is **silently skipped**. The interval verifier continues with its unrefined state.

## Validation vs. Checking

`validate` (run before the checker) is **structural only** — it checks schema version, register index bounds, chain connectivity, PC ordering, and that the sum does not overflow `i64`. It does **not** verify the semantic correctness of any step. That is the checker's job.

This means a certificate can pass validation and still be rejected at check time (e.g. if the Guard's `c` is tighter than what the interval state supports, or a Transfer's `delta` exceeds the interval's `ub(src)`).

## Practical Limits

| Limit | Value |
|-------|-------|
| Max steps per entry | 16 |
| Max entries per PC | 8 |

Entries exceeding these caps are rejected at validation and never reach the checker.

## CLI

```bash
# Generate a certificate for a test program (zone-mode analysis)
zovia pcc-gen  <prog.json> <test_name> [cert_out.json]

# Check a program against an existing certificate (interval-mode)
zovia pcc-check <prog.json> <test_name> <cert.json>

# Generate and immediately check (round-trip)
zovia pcc-cycle <prog.json> <test_name> [cert_out.json]

# Run all cases in a regression file
zovia pcc-regress [cert_cases.json]
```

## Trust Model

Only the following are in the TCB:

- The baseline interval verifier.
- `verify_proof_chain_replay` — step-by-step proof checker using `explored_states`.
- `apply_verified_refinements` — state refinement on verified entries.

The certificate file, the generator, and the zone analysis are **not** in the TCB. Compromise of the certificate or generator cannot cause the checker to accept an unsafe program.
