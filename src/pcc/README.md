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
                      accepted / skipped (fail-closed)
```

The **certificate is not trusted**. The checker independently verifies every step against the program's own instruction stream and the interval abstract state. A malformed or adversarial certificate can only cause entries to be silently skipped — it cannot cause an unsafe program to be accepted.

## Certificate Format

Certificates are JSON files with the following structure:

```json
{
  "version": 1,
  "program_hash": "<fnv1a hex>",
  "pc_annotations": [
    {
      "pc": 10,
      "entries": [
        {
          "i": 6,
          "j": 14,
          "bound": -5,
          "proof": [
            { "kind": "PredCarry", "i": 6, "j": 7, "c": 3  },
            { "kind": "PredCarry", "i": 7, "j": 14, "c": -8 }
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
- **`i`, `j`** — register indices for the constraint `i - j <= bound`. See the register index table below.
- **`bound`** — the claimed upper bound. Must equal the sum of the `c` fields across all proof steps.
- **`proof`** — ordered chain of proof steps. See [Proof Steps](#proof-steps).

### Register Index Table

| Index | Register |
|-------|----------|
| 0 | Zero (constant 0) |
| 1–10 | R0–R9 |
| 11 | R10 (frame pointer) |
| 12 | `@data_meta` anchor |
| 13 | `@data` anchor |
| 14 | `@end` anchor |

Packet safety annotations almost always use `j = 14` (`@end`), expressing that a register lies at least `|bound|` bytes before the end of the packet.

## Proof Steps

Each annotation entry contains a chain of steps that together prove `i - j <= bound`. Two step types are available.

### `Guard`

```json
{ "kind": "Guard", "i": 6, "j": 7, "c": -1 }
```

Extracts a constraint directly from the **branch condition** on the predecessor edge. If the predecessor instruction is a conditional jump (e.g. `JGE r5, r6`) and execution reaches the annotation PC via the fall-through edge, then the branch guarantees `r5 < r6`, i.e. `r5 - r6 <= -1`.

The checker verifies this by re-deriving the guard constraint from the branch opcode and edge direction. `Guard` must always be the **first step** in a chain.

| Branch | Edge | Constraint |
|--------|------|------------|
| `JGE dst, src` | fall-through | `dst - src <= -1` |
| `JGT dst, src` | fall-through | `dst - src <= 0`  |
| `JGE dst, src` | taken         | `src - dst <= 0`  |
| `JGT dst, src` | taken         | `src - dst <= -1` |

### `PredCarry`

```json
{ "kind": "PredCarry", "i": 7, "j": 14, "c": -8 }
```

Carries a pairwise bound from the **predecessor abstract state** forward through the predecessor instruction. The interval domain implicitly encodes pairwise bounds between `PtrToPacket` registers via their pointer offsets and the packet size lower bound established by earlier guards. A `PredCarry` step makes one such implicit bound explicit and propagates it to the post-state.

The checker computes the post-state upper bound on `i - j` by applying the predecessor instruction's effect:

| Predecessor instruction | Effect on `i - j` |
|-------------------------|-------------------|
| Does not write `i` or `j` | bound unchanged |
| `i += imm` | bound shifts by `imm` |
| `i += src` where `src ∈ [lo, hi]` | bound shifts by `hi` |

The step is accepted if this computed bound is `<= c`.

### Chain Rules

A valid proof chain must satisfy:

1. **Connectivity** — `step[k].j == step[k+1].i` for all consecutive steps.
2. **Endpoints** — `step[0].i == entry.i` and `step[-1].j == entry.j`.
3. **Sum** — `Σ step.c == entry.bound`.
4. **Guard position** — at most one `Guard` step, and it must be first.

## Checker Behavior

At each annotated PC, the checker:

1. Verifies the certificate hash matches the program.
2. For each entry at that PC, runs through the proof chain step by step.
3. If all steps pass and the sum is correct, refines the successor interval state with the proven `i - j <= bound` fact (currently: tightens the pointer's accessible packet range).
4. If any step fails, the entry is **silently skipped**. The interval verifier continues with its unrefined state.

Verbosity levels (controlled by `-v` / `-vv` flags):
- Default — logs accepted/rejected annotations at the entry level.
- `-v` — logs per-step pass/fail with computed bounds.
- `-vv` — full trace including transfer function internals.

## Validation vs. Checking

`validate` (run before the checker) is **structural only** — it checks schema version, register index bounds, chain connectivity, and that the sum does not overflow `i64`. It does **not** verify the semantic correctness of any step. That is the checker's job.

This means a certificate can pass validation and still be rejected at check time (e.g. if the `PredCarry` bound is tighter than what the predecessor state supports).

## Practical Limits

| Limit | Value |
|-------|-------|
| Max steps per entry | 3 |
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
- `verify_certificate_entries_for_edge` — step-by-step proof checker.
- `apply_verified_refinements` — state refinement on verified entries.

The certificate file, the generator, and the zone analysis are **not** in the TCB. Compromise of the certificate or generator cannot cause the checker to accept an unsafe program.
