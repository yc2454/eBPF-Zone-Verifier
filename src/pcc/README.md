# PCC — Proof-Carrying Code Module

This module implements certificate-aided verification for eBPF programs. It lets a **zone-mode producer** attach a lightweight proof to a program so that an **interval-mode checker** can verify safety properties that the interval domain alone cannot establish — without running the full zone analysis at check time.

## Background

The interval verifier tracks each register's value range independently. This works well for scalar arithmetic but loses precision whenever a safety property depends on the *relationship* between two registers — e.g. when the two have a fixed difference. The zone (DBM) domain captures exactly these relational constraints, but it is significantly more expensive and may not be available in all verification contexts.

PCC bridges this precision gap: the zone analysis runs once (offline) and emits a certificate that encodes the key relational facts it derived — expressed as difference-bound constraints of the form `left_reg - right_reg <= bound`. The interval checker *replays* just those facts at the relevant program points, verifying each step against the instruction stream and its own interval abstract state, and uses the proven constraints to tighten `var_off` on pointer registers that it would otherwise reject.

PCC currently supports three access types: **packet**, **stack**, and **map value** accesses. The certificate format and proof-step semantics are not inherently limited to these — any relational invariant that the zone domain can derive and that can be expressed as a chain of Guard and Transfer steps over the interval pre-states is a valid candidate.

## Architecture

```
  [Zone analysis] ──generates──> [Certificate (.cert.json)]
                                         │
                                         ▼
  [Interval analysis] ──checks──>    [Checker]
                                         │
                                         ▼
                                accepted / skipped
```

The **certificate is not trusted**. The checker independently verifies every step against the program's own instruction stream and the interval abstract state. A malformed or adversarial certificate can only cause the proof to be silently skipped and we fall back to the plain interval verifier.

## Certificate Format

Certificates are JSON files with the following structure:

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
            { "kind": "Guard", "pc": 8, "left_reg": 6, "right_reg": 14, "c": -8 },
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

Packet safety annotations use `right_reg = 14` (`@end`), expressing that a register lies at least `|bound|` bytes before the end of the packet. Stack annotations use `right_reg = 11` (R10, the frame pointer). Map value annotations use a real BPF register index — the same-map anchor register whose type-level offset is known.

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
| `JSGE dst, src` | fall-through | `dst - src <= -1` |
| `JSGT dst, src` | fall-through | `dst - src <= 0`  |
| `JGE dst, src` | taken | `src - dst <= 0`  |
| `JGT dst, src` | taken | `src - dst <= -1` |
| `JSGE dst, src` | taken | `src - dst <= 0`  |
| `JSGT dst, src` | taken | `src - dst <= -1` |

Signed (`JS*`) and unsigned (`J*`) comparisons of the same kind produce the same difference-bound constraint. The distinction matters for the branch refinement in the type domain but not for the relational bound recorded in the certificate.

### `Transfer`

```json
{ "kind": "Transfer", "pc": 9,
  "pre_left_reg": 6, "pre_right_reg": 14,
  "post_left_reg": 6, "post_right_reg": 14,
  "delta": 3 }
```

The inductive step. Formally: if `pre_left_reg - pre_right_reg <= b` holds in the
pre-state of the instruction at `pc`, then `post_left_reg - post_right_reg <= b + delta`
holds in the post-state.

Let `L = pre_left_reg` and `R = pre_right_reg`. The checker verifies the step by looking
up the **interval** pre-state and the instruction at `pc`, and checking that the claimed
`delta` (and register remapping) is a sound algebraic consequence (forward direction —
see [backward transfer](#generation-and-verification-two-directions-of-the-same-arithmetic)
for how the generator derives these values in the opposite direction):

| Instruction | Condition | Derivation | Required `delta` |
|---|---|---|---|
| `add dst, imm` | `dst == L` | `(L+imm) - R = (L-R) + imm <= b + imm` | exactly `imm` |
| `add dst, imm` | `dst == R` | `L - (R+imm) = (L-R) - imm <= b - imm` | exactly `-imm` |
| `add dst, src` | `dst == L` | `(L+src) - R = (L-R) + src <= b + ub(src)` since `src <= ub(src)` | `>= ub(src)` |
| `add dst, src` | `dst == R` | `L - (R+src) = (L-R) - src <= b - lb(src)` since `src >= lb(src)` | `>= -lb(src)` |
| `mov dst, src` | `src == L` | value moved into `dst`; `post_left_reg = dst.idx()`, bound unchanged | exactly `0` |
| passthrough | `dst` ∉ {`L`,`R`} | neither register touched; constraint unchanged | exactly `0` |
| other (writes `L` or `R`) | — | **Rejected** | — |

Here `ub(src)` and `lb(src)` are the interval upper and lower bounds of `src` read from
the interval pre-state at `pc`. For `add dst, src`, the generator uses the tightest value
(`delta == ub(src)`), but the checker accepts any `delta >= ub(src)` (sound overestimate).

### Chain Rules

A valid proof chain must satisfy:

1. **Structure** — `proof[0]` is a Guard; all subsequent steps are Transfers.
2. **Connectivity** — `Transfer[k].(pre_left_reg, pre_right_reg) == prev_step.(post_left_reg, post_right_reg)`.
3. **Endpoints** — last step's `(post_left_reg, post_right_reg) == entry.(left_reg, right_reg)`.
4. **Sum** — `Guard.c + Σ Transfer.delta == entry.bound`.
5. **PC ordering** — Guard PC <= first Transfer PC (may be equal); subsequent strictly increasing; all < target PC.

## Supported Access Types

### Packet Accesses

For a load from register `base` with load size `sz`, the required constraint is `base - @end <= -(off + sz)`. The certificate's `right_reg` is the synthetic `@end` anchor (index 14).

The injector tightens `base`'s `var_off` using: `new_var_off_ub = cert_bound - po.off`, where `po.off` is the constant component of `base`'s `PtrOffset`. This allows the interval access check to pass where it would have rejected due to an over-wide `var_off`.

### Stack Accesses

Stack accesses use the same `var_off` tightening as packets, but the right register is R10 (frame pointer, index 11) rather than `@end`. The access pointer's `PtrOffset.anchor` is R10, so the injector recognises the match and applies `new_var_off_ub = cert_bound - po.off`.

A typical pattern: after a variable add like `r1 += r0` where `r1` starts as a stack pointer, a branch `JSGE r1, r10` on the fall-through path establishes `r1 - r10 <= -1`. The cert encodes this Guard + passthrough Transfer, and the injector narrows `r1.var_off` from the AND-mask worst case to the branch-constrained tight bound.

### Map Value Accesses

Map value pointers require a different strategy because there is no single synthetic anchor: the zone domain does not initialise map pointer registers relative to `Zero` (doing so across multiple maps would produce unsound cross-map relationships via Floyd-Warshall closure).

Instead the generator scans for a **same-map anchor**: another register `k` with type `PtrToMapValue{ map_idx: same, offset: Some(k_off) }` for which `zone_upper_bound(base, k)` is finite. The cert encodes `base - k <= c`, and the injector composes: `new_var_off_ub = c + (k_off + k.var_off) - po.off`.

Concretely: `r7 = map_ptr + 8` (end-of-value sentinel), and a branch `JSGE r6, r7` on the fall-through derives `r6 - r7 <= -1`. The cert records `(r6, r7, -1)`. The injector sees both registers are `PtrToMapValue` from the same map, looks up r7's type-level offset (8), and computes `var_off_ub = -1 + 8 - 0 = 7`. This lets `r6 + 0` pass the 8-byte value-size check.

## Certificate Generation

The generator (`generator.rs`) produces the certificate automatically from the zone and interval analysis results. It runs offline and its output is not in the TCB.

### Overview

For any `target_pc` which requires access checking (such as a `Load` instruction), the generator:

1. **Queries the zone** — checks whether the zone DBM at `target_pc` proves the access is safe. For packet and stack accesses this means `base - anchor <= req` in zone's DBM. For map value accesses, zone's own per-register check may fail (because zone does not track `base - Zero` for map pointers), but zone's relational data is still useful: the generator instead searches for a same-map anchor register `k` such that `zone_upper_bound(base, k) + k.type_offset <= req`. If neither check finds a proof, nothing is certified.
2. **Queries the interval** — checks whether the interval verifier already proves the access safe on its own. If so, PCC is not needed.
3. **Backward-traces** from `target_pc - 1` toward the start of the program to find the **divergence point**: the instruction whose interval pre-state independently agrees with the zone on the tracked constraint.
4. **Emits the proof chain** — reverses the backward steps into a forward `[Guard, Transfer, …, Transfer]` chain and writes it into the certificate.

### Generation and Verification: Two Directions of the Same Arithmetic

The generator and checker both reason about the same arithmetic, but from **opposite directions**:

- The **generator** walks *backward* from the load. At each instruction it asks: "given that the constraint `L - R <= b` holds *after* this instruction, what must have held *before* it?" It uses the zone DBM (which has full relational precision) to bound variable-offset additions.
- The **checker** walks *forward* through the emitted proof chain. At each Transfer it asks: "given that the constraint `L - R <= b` holds *before* this instruction, does `L' - R' <= b + delta` follow *after* it?" It uses the interval pre-state (available at check time, without the zone) to verify the bound on variable-offset additions.

The `delta` field in each Transfer is the shared language between them: the generator computes it during inversion, and the checker verifies it during replay.

**Generator — backward transfer** (given post-constraint `L - R <= b`, derive pre-constraint):

| Instruction | Inversion | Recorded `delta` |
|---|---|---|
| `add dst, imm` (`dst == L`) | `b - imm` before → `b` after | `imm` |
| `add dst, imm` (`dst == R`) | `b + imm` before → `b` after | `-imm` |
| `add dst, src` (`dst == L`) | `b - ub(src)` before, using `ub(src)` from **zone DBM** | `ub(src)` |
| `add dst, src` (`dst == R`) | `b + lb(src)` before, using `lb(src)` from **zone DBM** | `-lb(src)` |
| `mov dst, src` (`dst == L`) | track `src` instead of `dst`; bound unchanged | `0` |
| passthrough | constraint unchanged | `0` |

After each inversion, the generator checks whether the interval pre-state at that PC can independently prove the derived pre-constraint. The first PC where it can is the **divergence point**: the interval and zone agree there without any relational help. A `Guard` is placed at that PC, and all subsequent instructions become Transfer steps.

See the [Transfer step verification table](#transfer) for the corresponding forward direction used by the checker.

### Proof Chain Length

A proof chain always contains exactly **one Guard** step. The number of Transfer steps equals the number of hops from the Guard's source PC to the annotation PC:

```
branch (or zone-proven point) @ pc G
  ... k intermediate instructions ...
load  @ pc L         ← annotation site

steps = 1 Guard + (k + 1) Transfers
```

The Guard and the first Transfer both reference `pc G` — the Guard because that is where the constraint is established, and the Transfer because it models the edge `G → G+1`. In practice the generator finds zone has already propagated the constraint to the immediate predecessor of the load, so almost all current certs have exactly **2 steps** (k = 0): one Guard and one Transfer, both at `pc L - 1`.

### Example

Consider a program fragment where `r4` is a packet data pointer that a prior bounds check has established is at least 12 bytes before end-of-packet, and `r3` is a variable offset known by the zone to be at most 3:

```
pc  instruction           purpose
──────────────────────────────────────────────────────────────────────
5   r5 = r4               copy packet pointer into r5
6   r5 += 4               skip a 4-byte fixed header
7   r5 += r3              advance by variable offset r3 (zone: 0 ≤ r3 ≤ 3)
8   r1 = *(u8 *)(r5 + 0)  load 1 byte — needs r5 - @end ≤ -1
```

The table below shows the **pre-state of each instruction** — what each domain knows just *before* that instruction executes:

```
pc  instruction           zone pre-state           interval pre-state
──────────────────────────────────────────────────────────────────────
5   r5 = r4               r4 - @end ≤ -12          r4 - @end = ∞
6   r5 += 4               r5 - @end ≤ -12          r5 - @end = ∞
7   r5 += r3              r5 - @end ≤ -8           r5 - @end = ∞
8   r1 = *(u8 *)(r5 + 0)  r5 - @end ≤ -5  ✓        r5 - @end = ∞  → REJECTED
```

At pc=8 the zone pre-state proves the load is safe (`-5 ≤ -1`), but the interval pre-state does not. PCC is needed.

**Backward trace** (starting from target constraint `r5 - @end ≤ -5` at pc=8):

- **Invert pc=7** (`add r5, r3`): `ub(r3) = 3` from zone pre-state at pc=7 → pre-bound = `-5 - 3 = -8`. Check interval pre-state at pc=7: `r5 - @end = ∞ > -8` — interval does not agree. Continue backward.
- **Invert pc=6** (`add r5, 4`): pre-bound = `-8 - 4 = -12`. Check interval pre-state at pc=6: `r5 - @end = ∞ > -12` — no agreement. Continue backward.
- **Invert pc=5** (`mov r5, r4`): register substitution — track `r4` instead of `r5`, pre-bound = `-12` (unchanged). Check interval pre-state at pc=5: `r4 - @end ≤ -12` ✓ — **divergence point found**.

**Emitted proof chain** (forward order, ready for the certificate):

```
Guard    pc=5,  r4 - @end ≤ -12                              [interval pre-state at pc=5 proves this]
Transfer pc=5,  (r4,@end) → (r5,@end),  delta=0             [mov r5,r4: value moves into r5]
Transfer pc=6,  (r5,@end) → (r5,@end),  delta=4             [add r5,4: bound shifts by +4]
Transfer pc=7,  (r5,@end) → (r5,@end),  delta=3             [add r5,r3: bound shifts by ub(r3)=3]
```

Accumulated bound: `-12 + 0 + 4 + 3 = -5`. At check time, the checker walks this chain forward, verifying each Transfer against the interval pre-state and instruction stream independently — no zone required.

## Checker Behavior

At each annotated PC, the checker:

1. Verifies the certificate hash matches the program.
2. For each entry at that PC, replays the proof chain step by step, looking up the interval pre-state at each step's PC from `explored_states`.
3. If all steps pass, the sum matches, and endpoint registers match, the injector (`injector.rs`) uses the proven `left_reg - right_reg <= bound` to tighten `var_off` on the access pointer:

   | Case | Condition | Tightening |
   |---|---|---|
   | **Packet / same-anchor** | `right_reg == po.anchor` (e.g. `@end` or R10) | `var_off = min(var_off, bound - po.off)` |
   | **Same-map transitive** | both regs are `PtrToMapValue` with same `map_idx` | `var_off = min(var_off, bound + j_max_off - po.off)` |

   where `po` is the `PtrOffset` of the access pointer and `j_max_off = j.off + j.var_off` is the maximum offset of the anchor register.

4. If any step fails, the entry is **silently skipped**. The interval verifier continues with its unrefined state.

## Validation vs. Checking

`validate` (run before the checker) is **structural only** — it checks schema version, register index bounds, chain connectivity, PC ordering, and that the sum does not overflow `i64`. It does **not** verify the semantic correctness of any step. That is the checker's job.

This means a certificate can pass validation and still be rejected at check time (e.g. if the Guard's `c` is tighter than what the interval state supports, or a Transfer's `delta` is less than the interval's `ub(src)`).

## Practical Limits

| Limit | Value | Nature |
|-------|-------|--------|
| Max steps per entry | 16 | Bounds proof chain length; generator traces at most a few instructions in practice |
| Max entries per PC | 8 | **Defensive cap only** — the current generator emits at most 1 entry per PC |

Both limits are enforced by the validator; entries that exceed them are rejected before they reach the checker.

Note for `max entries per PC`: the generator loops over instructions and produces at most one entry per load PC, so this limit is never approached in practice. It exists purely to bound the work an adversarial certificate could force the checker to perform — without it, a malicious certificate could embed an arbitrarily large number of entries at a single PC, each triggering a full proof replay.

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
