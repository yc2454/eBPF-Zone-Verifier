# PCC — Proof-Carrying Code Module

This module implements certificate-aided verification for eBPF programs. A **zone-mode producer** attaches a lightweight proof to a program so that an **interval-mode checker** can verify safety properties that the interval domain alone cannot establish — without running the full zone analysis at check time.

## Background

The interval verifier tracks each register's value range independently. This works well for scalar arithmetic but loses precision whenever a safety property depends on the *relationship* between two registers. The zone (DBM) domain captures exactly these relational constraints, but is significantly more expensive and may not be available in all verification contexts.

PCC bridges this precision gap: the zone analysis runs once (offline) and emits a certificate encoding the key relational facts it derived — expressed as difference-bound constraints of the form `left_reg - right_reg <= bound`. The interval checker *replays* those facts at the relevant program points, verifying each step against the instruction stream and its own interval abstract state, and uses the proven constraints to tighten `var_off` on pointer registers it would otherwise reject.

### Motivating example

Consider the following map-value access where `r2` is a variable offset:

```
pc  instruction           purpose
──────────────────────────────────────────────────────────────────────
10  r2 = r0               r2 = random & 0xf  (r2 ∈ [0,15])
11  r3 = r2               r3 = r2
12  r3 += 4               r3 = r2 + 4
13  if r3 > 8 goto end    branch: fall-through means r3 ≤ 8, so r2 ≤ 4
14  r6 += r2              r6 = map_ptr + r2
15  load *(u8 *)(r6 + 0)  needs r6 - Zero ≤ 4 (map size = 5)
```

The branch on `r3` at pc 13 implies `r2 ≤ 4`, which makes pc 15 safe. The zone domain tracks the relationship `r3 = r2 + 4` and closes the bound across the branch. The interval domain does not: it sees `r2 ∈ [0,15]` and rejects pc 15.

The certificate bridges this gap with three steps:

```
Fact     @ pc 13:  r3 - 0 ≤ 8            [branch condition on fall-through edge]
Derive   @ pc 11→12:  r3 = r2 + 4  =>  r2 ≤ 4
Transfer @ pc 14:  r6 += r2              [r6 - 0 ≤ 0 + 4 = 4]
```

At check time, the interval checker independently verifies each step and then tightens `r6.var_off` from 15 to 4, allowing pc 15 to pass.

## Architecture

```
  [Zone analysis] ──generates──> [Certificate (.cert.json)]
                                         │
                                   not in TCB
                                         │
                                         ▼
  [Interval analysis] ──verifies──>  [Checker]
                                         │
                                         ▼
                                accepted / skipped
```

The **certificate is not trusted**. The checker independently verifies every step against the program's own instruction stream and the interval abstract state. A malformed or adversarial certificate causes the proof to be silently skipped; the plain interval verifier continues.

## Certificate Format (v3)

Certificates are JSON with tagged proof steps. Schema highlights:

```json
{
  "version": 3,
  "program_hash": "<fnv1a hex>",
  "pc_annotations": [
    {
      "pc": 15,
      "entries": [
        {
          "left_reg": 7,
          "right_reg": 14,
          "bound": -5,
          "proof": [
            { "kind": "Compose",
              "via": 2,
              "left":  [ { "kind": "Fact", "pc": 8, "left_reg": 7, "right_reg": 2, "c": 3 } ],
              "right": [ { "kind": "Fact", "pc": 4, "left_reg": 2, "right_reg": 14, "c": -8 } ]
            }
          ]
        }
      ]
    }
  ]
}
```

Fields:
- `program_hash` — FNV-1a over instruction bytes; must match at check time.
- `pc` — load instruction being annotated.
- `left_reg`, `right_reg`, `bound` — final constraint `left_reg - right_reg <= bound`.
- `proof` — vector of proof steps (can be a linear chain or a single top-level `Compose`).

Register indices:

| Index | Register |
|-------|----------|
| 0 | Zero (constant 0) |
| 1–10 | R0–R9 |
| 11 | R10 (frame pointer) |
| 12 | `@data_meta` anchor |
| 13 | `@data` anchor |
| 14 | `@data_end` anchor |

## Proof Steps

A proof chain proves `left_reg - right_reg <= bound` at the load site. Four step types:

### `Fact`

```json
{ "kind": "Fact", "pc": 13, "left_reg": 4, "right_reg": 0, "c": 8 }
```

The base case of every proof chain. Always `proof[0]`. Claims that at the interval pre-state of `pc`, the constraint `left_reg - right_reg <= c` is independently provable by the interval verifier. It is the only step that *creates* a bound; all other steps transform it.

The checker verifies via one of two paths:

**State-derived:** `distance_upper_bound(interval_state, left, right) <= c`. This is the divergence-point case — the instruction whose interval pre-state already agrees with the zone on the tracked constraint.

**Branch-derived:** the instruction at `pc` is a conditional branch and the claimed constraint follows from the branch condition on the fall-through edge. The checker derives the constraint directly from the opcode — no abstract state lookup needed.

| Branch condition | Fall-through edge | Constraint |
|---|---|---|
| `JLE dst, src` / `JGT dst, src` | fall-through of JGT | `dst - src <= 0` |
| `JLT dst, src` / `JGE dst, src` | fall-through of JGE | `dst - src <= -1` |
| `JGE dst, src` / `JLE dst, src` | taken of JGE | `src - dst <= 0` |
| `JGT dst, src` / `JLT dst, src` | taken of JGT | `src - dst <= -1` |
| `JLE dst, imm` / `JGT dst, imm` | fall-through of JGT | `dst - Zero <= imm` |
| `JLT dst, imm` / `JGE dst, imm` | fall-through of JGE | `dst - Zero <= imm - 1` |

Signed (`JS*`) and unsigned (`J*`) comparisons of the same kind produce the same difference-bound constraint.

### `Derive`

```json
{ "kind": "Derive", "pc_start": 11, "pc_end": 12,
  "source_reg": 4, "target_reg": 3, "offset": 4 }
```

A register aliasing step. Claims that the instructions from `pc_start` to `pc_end` establish `source_reg = target_reg + offset`.

This allows the chain to switch which register it tracks: if the preceding Fact proved `source_reg - Zero <= c`, then after Derive we know `target_reg - Zero <= c - offset`.

- **Connectivity:** `source_reg` must match the current tracked left register.
- **Verification:** the checker replays `pc_start..=pc_end` syntactically to confirm the pattern `mov source, target_reg` followed by `add source, imm` (with no overwrites of either register in between), and that `imm == offset`.
- **Effect:** the tracked left register switches from `source_reg` to `target_reg`; the tracked right register becomes Zero (index 0); the accumulated bound decreases by `offset`.

Derive steps reference the instructions that establish the alias, which typically occur *before* the Fact's PC (the alias is set up before the branch that constrains it). The PC ordering rules accommodate this — see [Chain Rules](#chain-rules).

### `Transfer`

```json
{ "kind": "Transfer", "pc": 14,
  "pre_left_reg": 3, "pre_right_reg": 0,
  "post_left_reg": 7, "post_right_reg": 0,
  "delta": 0 }
```

The inductive step. Claims: if `pre_left - pre_right <= b` holds in the pre-state of the instruction at `pc`, then `post_left - post_right <= b + delta` holds in the post-state.

Let `L = pre_left_reg` and `R = pre_right_reg`. The checker verifies the step by looking up the interval pre-state and instruction at `pc`:

| Instruction | Condition | Derivation | Required `delta` |
|---|---|---|---|
| `add dst, imm` | `dst == L` | `(L+imm) - R = (L-R) + imm <= b + imm` | exactly `imm` |
| `add dst, imm` | `dst == R` | `L - (R+imm) = (L-R) - imm <= b - imm` | exactly `-imm` |
| `add dst, src` | `dst == L` | `(L+src) - R <= b + ub(src)` since `src <= ub(src)` | `>= ub(src)` |
| `add dst, src` | `dst == R` | `L - (R+src) <= b - lb(src)` since `src >= lb(src)` | `>= -lb(src)` |
| `add dst, src` | `src == L`, `dst` ∉ {`L`,`R`} | absorb: `dst_new - R <= ub(dst_old) + b` | `>= ub(dst_old - R)` |
| `mov dst, src` | `src == L` | value copied; track `dst`: `post_left = dst`, bound unchanged | exactly `0` |
| passthrough | `dst` ∉ {`L`,`R`} | constraint registers untouched | exactly `0` |
| other | writes `L` or `R` | **Rejected** | — |

Here `ub(x)` and `lb(x)` are the interval upper and lower bounds of register `x` from the interval pre-state at `pc`.

The **absorb** case handles `add dst, src_reg` where `src_reg` is the tracked left register `L`. The new register `dst` (which was bounded at `ub(dst - R)`) absorbs `L`, and the tracked pair switches to `(dst, R)`. This arises in the derived-register pattern when the map pointer accumulates the variable offset: `r6 += r2` where r2 is the tracked register.

The optional `hint` field is a human-readable description of the instruction and its effect. It carries no semantic weight and is ignored by the checker.

### `Compose`

Combines two sub-proofs through an intermediate register `via`.

```
Compose {
  left:  proves L - via <= a
  right: proves via - R <= b
  via: <register index>
}
⇒ proves L - R <= a + b
```

Both `left` and `right` are themselves valid proof chains (which can include nested Compose). Compose is needed when the zone DBM’s transitive closure combines multiple independent register pairs; linear replay cannot see this without reconstructing the provenance path.

## Chain Rules

A valid proof chain must satisfy:

1. **Structure** — `proof[0]` is a Fact; subsequent steps are Derives or Transfers; no Fact appears after position 0.
2. **Connectivity** — `Derive[k].source_reg == prev_step.output_left_reg`; `Transfer[k].(pre_left_reg, pre_right_reg) == prev_step.(output_left_reg, output_right_reg)`.
3. **Endpoints** — the last step's `(output_left_reg, output_right_reg) == entry.(left_reg, right_reg)`.
4. **Sum** — `Fact.c + Σ(Derive contributions) + Σ(Transfer.delta) == entry.bound`, where each Derive contributes `-offset`.
5. **PC ordering:**
   - All step PCs < target (annotation) PC.
   - Derive steps may reference PCs before the Fact's PC (the alias is established before the branch).
   - The Fact and the step immediately following it may share the same PC.
   - After the first Transfer, PCs must be strictly increasing.
   - Compose sub-proofs have their own internal PC ordering; top-level chain skips PC ordering for the Compose node.

## Supported Access Types

### Packet Accesses

For a load from register `base` at offset `off` with access size `sz`, the required constraint is `base - @data_end <= -(off + sz)`. The certificate's `right_reg` is the synthetic `@data_end` anchor (index 14).

The injector tightens `base.var_off` using `new_var_off_ub = cert_bound - po.off`, where `po.off` is the constant component of `base`'s `PtrOffset`. This allows the interval access check to pass.

### Stack Accesses

Stack accesses use the same tightening as packets, but `right_reg` is R10 (frame pointer, index 11). A typical pattern: after `r1 += r0` where `r1` starts as a stack pointer, a branch `JSGE r1, r10` on the fall-through path establishes `r1 - r10 <= -1`. The certificate encodes this Fact + Transfer chain and the injector narrows `r1.var_off`.

### Map Value Accesses

Map value pointers require a different strategy because there is no single synthetic anchor — the zone domain does not initialise map pointer registers relative to Zero (doing so across multiple maps would produce unsound cross-map relationships via Floyd-Warshall closure).

For **same-map anchor**: the generator finds another register `k` with type `PtrToMapValue{ map_idx: same, offset: Some(k_off) }` for which `zone_upper_bound(base, k)` is finite. The cert encodes `base - k <= c`, and the injector computes `new_var_off_ub = c + (k_off + k.var_off) - po.off`.

For **derived-register** accesses (the motivating example above): the generator uses the derive chain strategy — see [Certificate Generation](#certificate-generation).

## Certificate Generation

The generator (`generator.rs`) produces certificates automatically from the zone and interval analysis results. It runs offline and its output is not in the TCB.

### Overview

For each `target_pc` that zone proves safe but interval rejects, the generator tries three strategies in order:

1. **Backward trace** — linear `Fact + Transfer` chain.
2. **Derive chain** — alias pattern `k = src + offset` guarded by a branch.
3. **Provenance-based Compose** — decomposes a transitive constraint into primitive edges using the DBM’s provenance and folds them into nested `Compose` nodes.

### Strategy 1: Backward Trace

The generator walks *backward* from the load. At each instruction it asks: "given that the constraint `L - R <= b` holds *after* this instruction, what must have held *before* it?" The zone DBM provides tight bounds for variable-offset additions.

**Generator — backward transfer** (given post-constraint `L - R <= b`, derive pre-constraint):

| Instruction | Inversion | Recorded `delta` |
|---|---|---|
| `add dst, imm` (`dst == L`) | pre-bound: `b - imm` | `imm` |
| `add dst, imm` (`dst == R`) | pre-bound: `b + imm` | `-imm` |
| `add dst, src` (`dst == L`) | pre-bound: `b - ub(src)`, using `ub(src)` from **zone DBM** | `ub(src)` |
| `add dst, src` (`dst == R`) | pre-bound: `b + lb(src)`, using `lb(src)` from **zone DBM** | `-lb(src)` |
| `mov dst, src` (`dst == L`) | track `src` instead; bound unchanged | `0` |
| passthrough | constraint unchanged | `0` |

At each step, the generator checks whether the interval pre-state at that PC independently agrees with the derived pre-constraint. The first PC where it does is the **divergence point**: a Fact is placed there, and all subsequent instructions become Transfer steps.

**Example:** `r4` is a packet pointer and `r3` is a variable offset known by zone to be at most 3:

```
pc  instruction     zone pre-state      interval pre-state
──────────────────────────────────────────────────────────
5   r5 = r4         r4 - @end ≤ -12    r4 - @end ≤ -12  ← interval agrees here
6   r5 += 4         r5 - @end ≤ -12    r5 - @end = ∞
7   r5 += r3        r5 - @end ≤ -8     r5 - @end = ∞
8   load *(r5 + 0)  r5 - @end ≤ -5 ✓  r5 - @end = ∞ → REJECTED
```

Backward trace from `r5 - @end <= -5` at pc 8:
- Invert pc 7 (`add r5, r3`): `ub(r3)=3` from zone → pre-bound `-8`. Interval: `r5-@end=∞`. Continue.
- Invert pc 6 (`add r5, 4`): pre-bound `-12`. Interval: `r5-@end=∞`. Continue.
- Invert pc 5 (`mov r5, r4`): track r4, pre-bound `-12`. Interval: `r4-@end ≤ -12` ✓ — **divergence point**.

Emitted chain:
```
Fact     @ pc 5:  r4 - @end ≤ -12
Transfer @ pc 5:  (r4,@end)→(r5,@end),  delta=0    [mov r5,r4]
Transfer @ pc 6:  (r5,@end)→(r5,@end),  delta=4    [add r5,4]
Transfer @ pc 7:  (r5,@end)→(r5,@end),  delta=3    [add r5,r3; ub(r3)=3]
```

Accumulated bound: `-12 + 0 + 4 + 3 = -5`.

### Strategy 2: Derive Chain

Used when backward trace fails because the tracked register is itself *derived* from another — the branch constrains register `k` but the memory access uses `src_reg`, connected by `k = src_reg + offset`.

The generator:
1. Scans backward from the load to find the `add base, src_reg` instruction.
2. Scans backward from there for a branch that constrains some `k` with `k - anchor <= c`.
3. Calls `find_derive_sequence` to verify that instructions between the branch and the add establish `k = src_reg + offset` via `mov k, src_reg; add k, imm`.
4. Verifies the derived bound: `c - offset <= required_src_bound`.
5. Emits: `Fact(k ≤ c) + Derive(k = src_reg + offset) + Transfer(base += src_reg, absorb)`.

This is the pattern from the motivating example: `r3 = r2 + 4; if r3 ≤ 8 → r2 ≤ 4; r6 += r2`.

**Transfer delta soundness filter:** backward trace may succeed but produce an unsound proof — the zone-derived delta for a variable-offset add may be tighter than what the interval can verify (the zone has relational precision the interval lacks). The generator filters out such proofs and falls through to Strategy 2.

### Strategy 3: Provenance-based Compose

Problem: zone’s Floyd–Warshall closure can prove `L - R` via multiple intermediate registers; linear replay can’t see the path. Solution: use the DBM’s provenance tracker.

Algorithm (`try_provenance_compose`):
1. With provenance enabled during zone analysis, call `dbm.reconstruct_path(L, R)` at `target_pc` to get primitive edges `(to, from, weight, pc)` that form the shortest path.
2. For each edge, try `backward_trace` (with transfer-delta soundness check) to build a sub-proof of `to - from <= weight`.
3. Fold sub-proofs right-associatively into nested `Compose` nodes so adjacent edges meet at the `via` register.
4. Emit a single-step proof `[Compose { .. }]` if all segments succeed; otherwise skip Compose.

Fail-closed: any missing provenance, failed segment proof, or overflow aborts the Compose attempt and the generator moves on.

## Checker Behavior

At each annotated PC, the checker:

1. Verifies the certificate hash matches the program.
2. For each entry at that PC, replays the proof chain recursively:
   - **Fact:** interval pre-state or branch fall-through must prove the constraint.
   - **Derive:** syntactically verifies alias slice; switches tracked left to target; subtracts offset.
   - **Transfer:** uses interval pre-state + instruction semantics to check `delta` and post pair; adds `delta`.
   - **Compose:** recursively verifies left and right; requires matching `via`; adds sub-bounds.
3. If all steps pass, the sum matches, and endpoint registers match, the injector (`injector.rs`) tightens `var_off` on the access pointer:

   | Case | Condition | Tightening |
   |---|---|---|
   | **Packet / same-anchor** | `right_reg == po.anchor` (e.g. `@data_end` or R10) | `var_off = min(var_off, bound - po.off)` |
   | **Same-map transitive** | both regs are `PtrToMapValue` with same `map_idx` | `var_off = min(var_off, bound + j_max_off - po.off)` |

   where `po` is the `PtrOffset` of the access pointer.

4. If any step fails, the entry is **silently skipped**. The interval verifier continues with its unrefined state.

## Validation vs. Checking

`validate` (run before the checker) performs **structural checks only**: schema version, register index bounds, chain structure (Fact must be first), connectivity, PC ordering, and overflow-safe bound sum. It does **not** verify the semantic correctness of any step.

A certificate can pass validation and still be rejected at check time — for example, if the Fact's `c` is tighter than what the interval state supports, or a Transfer's `delta` is less than the interval's `ub(src)`. Validation failure is reported as an error; check-time failure is silent (fail-closed).

## Worked Examples (run with `cargo run -- pcc-cycle …`)

The suite `pcc-tests/pcc_examples.json` contains representative cases:

1. **Direct branch fact (linear):** `"pcc: var add + constant skip (add-imm, zone ok, interval reject)"`  
   Emits `Fact + Transfer`.
2. **Alias guard (derive chain):** `"pcc: derived-register guard (r3=r2+4, check r3, prove r2, zone ok, interval reject)"`  
   Emits `Fact + Derive + Transfer`.
3. **Transitive closure (Compose):** `"pcc: transitive compose (r5=r4+r2, zone closure via r2, interval reject)"`  
   Backward trace and derive chain fail on the full constraint; provenance reconstructs the path and emits a nested `Compose`.

Command template:
```
cargo run -- pcc-cycle pcc-tests/pcc_examples.json "<test name>"
```

Certificates are written to `pcc-tests/certs/generated/<suite>.<test>.<hash>.cert.json` by default; use `--certificate-output` to override.

## Practical Limits

| Limit | Value | Nature |
|-------|-------|--------|
| Max steps per entry | 16 | Bounds proof chain length; generator traces at most a few instructions in practice |
| Max entries per PC | 8 | Defensive cap only — the current generator emits at most 1 entry per PC |

Both limits are enforced by the validator. The `max entries per PC` cap exists to bound work an adversarial certificate could force the checker to perform without it a malicious certificate could embed arbitrarily many entries per PC each requiring a full proof replay.

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
