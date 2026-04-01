# Plan: Compose Proof Step & Provenance-Based Generation

## Context

The PCC (Proof-Carrying Code) system lets a zone-mode producer attach a
lightweight certificate to an eBPF program so an interval-mode checker can
verify safety properties that the interval domain alone cannot establish.

### Current proof step types
- **Fact** (was "Guard" — renamed in this session): base constraint independently
  verifiable by the interval domain, either from the abstract state or from a
  branch condition. Always `proof[0]`. The only step that *creates* a bound.
- **Derive**: register aliasing from instruction sequence (`source = target + offset`).
  Switches tracked register and adjusts bound. Verified by replaying ~2 instructions.
- **Transfer**: instruction-level bound propagation. Models how a single instruction
  transforms the tracked constraint pair.

### Current generation strategies
1. **Backward trace** (`backward_trace` in generator.rs): walks backward from load,
   inverting each instruction, checking if the interval agrees at each step. Works
   for straight-line code where the constraint is established by a single branch or
   state fact.
2. **Derive chain** (`try_derive_chain`): fallback for derived-register patterns
   where branch constrains register A but load uses register B, connected by
   `A = B + constant`. Emits `Fact + Derive + Transfer`.

### The gap
Both strategies fail when the zone constraint depends on **transitive closure
through multiple independent register pairs**. Example:

```
pc 4: if r0 > r2 goto end    // bounds check: r0 - @end ≤ 0
pc 7: r4 += r3               // r4 = packet_ptr + var_offset
pc 8: load *(r4 + 0)         // needs r4 - @end ≤ -1
```

Zone knows `r4 - @end ≤ -5` via Floyd-Warshall combining:
- `r4 - r1 ≤ 3` (from add at pc 7)
- `r1 - @end ≤ -8` (from bounds check at pc 4)

Backward trace can't handle this because the constraint involves two different
register pairs combined by closure, not a single pair transformed by instructions.

### The provenance tracker (already built, never used)
The DBM has a `ProvenanceTracker` shadow matrix tracking `EdgeOrigin` for each
cell:
- `Init`: default (diagonal or unconstrained)
- `Primitive { pc }`: set directly by `add_constraint` at a specific PC
- `Derived { via }`: derived by Floyd-Warshall closure through intermediate index

`reconstruct_path(i, j)` recursively decomposes a constraint into primitive edges.
This infrastructure was built in Phases 1-3 but never used by the generator.

## Design Decision

Add a 4th proof step type `Compose` that expresses transitive composition.
Keep `Derive` as a separate step (it's a special case of Compose where one leg
is a syntactic instruction-sequence fact, with simpler verification).

`Compose` makes proofs tree-shaped:
```
Compose { via: r1,
  left:  [Fact@pc4 ... Transfer ...]  -- proves r4 - r1 ≤ 3
  right: [Fact@pc2 ... Transfer ...]  -- proves r1 - @end ≤ -8
}
→ r4 - @end ≤ 3 + (-8) = -5
```

## Implementation Phases

### Phase 1: Model — Add `Compose` to `ProofStep`
**File: `src/pcc/model.rs`**

Add variant:
```rust
Compose {
    left: Vec<ProofStep>,   // proves L - K ≤ a
    right: Vec<ProofStep>,  // proves K - R ≤ b
    via: usize,             // intermediate register K (index)
}
```

- Sub-proofs are themselves `[Fact, Derive*, Transfer+]` or nested Compose
- Update `pc()`, `output_left_reg()`, `output_right_reg()`, `bound_contribution()`
- Update `Display` impl (indent sub-proofs)
- Update serde serialization (tagged enum, `"kind": "Compose"`)
- Bump `ProgramCertificate::VERSION` to 3
- Add round-trip unit tests

Design: An `AnnotationEntry.proof` is either:
- Linear chain: `[Fact, Derive*, Transfer+]` (unchanged)
- Single Compose: `[Compose { ... }]` (new, for transitive closure)
- Or a chain ending with Compose: `[Fact, Transfer*, Compose]` if needed

### Phase 2: Validator — Recursive structural checks
**File: `src/pcc/validate.rs`**

- Extract a `validate_sub_proof()` helper that validates a proof chain recursively
- For Compose: validate `via` register index, recursively validate `left` and `right`
- Check connectivity: `left`'s output right == `via`, `right`'s output left == `via`
- Total node count across all sub-proofs ≤ `MAX_STEPS_PER_ENTRY` (raise to 32)
- Sub-proofs' PC ranges may overlap (they trace independent constraints)

### Phase 3: Checker — Recursive verification
**File: `src/pcc/checker.rs`**

- Factor `verify_proof_chain_replay` into a helper that can be called recursively
- When encountering `Compose { left, right, via }`:
  - Recursively verify `left` → get `(left_left, via, left_bound)`
  - Recursively verify `right` → get `(via, right_right, right_bound)`
  - Composed bound = `left_bound + right_bound` (overflow-checked)
  - Update `ProofCheckState` with composed result

`get_unique_state` restriction stays: sub-proofs can only reference PCs with
a single explored state. This is fail-safe.

### Phase 4: Provenance fix in DBM
**Files: `src/domains/zone/dbm.rs`, `src/domains/zone/ops.rs`**

**Problem:** `apply_add_reg` in ops.rs uses `set_idx` to shift constraint values,
but `set_idx` does NOT update provenance. After the shift, provenance still
records stale `Primitive{pc}` or `Derived{via}` from before the shift.
The subsequent `close()` records new `Derived` edges, but the shifted base
edges have wrong provenance.

**Fix:** After `set_idx` shifts in `apply_add_reg`, mark all affected finite
edges as `Primitive{pc: current_pc}`. Add a helper method:
```rust
fn stamp_provenance_for_var(&mut self, reg_idx: usize) {
    if let Some(prov) = &mut self.provenance {
        let n = self.num_vars();
        for j in 0..n {
            if self.data[reg_idx][j] < INF && reg_idx != j {
                prov.edges[reg_idx][j] = EdgeOrigin::Primitive { pc: prov.current_pc };
            }
            if self.data[j][reg_idx] < INF && reg_idx != j {
                prov.edges[j][reg_idx] = EdgeOrigin::Primitive { pc: prov.current_pc };
            }
        }
    }
}
```

Call this after the `set_idx` loop in `apply_add_reg`.

**Must be done BEFORE Phase 5** — the generator relies on correct provenance.

### Phase 5: Generator — `try_provenance_compose`
**File: `src/pcc/generator.rs`**

New function:
```rust
fn try_provenance_compose(
    prog: &Program,
    zone_dbms: &[Dbm],
    interval_states: &[State],
    target_pc: usize,
    target_i: Reg,
    target_j: Reg,
    target_bound: i64,
) -> Option<Vec<ProofStep>>
```

Algorithm:
1. Get DBM at `target_pc`. Call `dbm.reconstruct_path(target_i, target_j)`.
2. If only 1 primitive edge, fall through (backward_trace should handle it).
3. For 2+ edges, each edge `(to, from, weight, pc)` is a primitive constraint.
4. For each segment, generate a sub-proof:
   - Try `backward_trace(target_pc, to, from, weight)` on that segment
   - If fails, try `try_derive_chain` for that segment
   - If both fail, the whole Compose fails
5. Fold segments into nested Compose nodes (right-associative).

Integration into `generate_certificate` (around line 853):
```
1. Try backward_trace (filtered by transfer_deltas_sound)
2. Try try_derive_chain
3. Try try_provenance_compose   ← NEW
4. Skip if all fail
```

### Phase 6: Test case
**File: `pcc-tests/pcc_examples.json`**

Create a test program where zone proves safety via transitive closure:
```
r1 = pkt_data
r2 = pkt_end
r0 = r1 + 8
if r0 > r2 goto end       // establishes r1 - @end ≤ -8
r3 = random & 3           // r3 ∈ [0, 3]
r4 = r1
r4 += r3                  // r4 = pkt_data + r3
load *(u32 *)(r4 + 0)     // needs r4 - @end ≤ -4
```

Zone: `r4 - @end = (r4 - r1) + (r1 - @end) ≤ 3 + (-8) = -5 ≤ -4` ✓
Interval: r4 - @end = ∞ → REJECT

Expected certificate:
```
Compose { via: r1,
  left:  [Fact@branch, Transfer (r1→r4 via mov+add)]  // r4 - r1 ≤ 3
  right: [Fact@branch]                                  // r1 - @end ≤ -8
}
```

### Phase 7: Regression
Run `cargo run -- pcc-regress` to ensure all 15 existing tests still pass.

## Key Risks

1. **Provenance accuracy after `apply_add_reg`**: `set_idx` doesn't stamp provenance.
   Phase 4 fix is critical. Test by inspecting `reconstruct_path` output on known
   programs before proceeding to Phase 5.

2. **Sub-proof generation can fail**: If `backward_trace` fails for any segment of
   the decomposed path, the entire Compose fails. Fail-safe but reduces coverage.
   A "FactOnly" leaf strategy for trivially-provable segments may help.

3. **Widening destroys provenance**: `widen()` sets `provenance = None`. When
   widening is enabled, `reconstruct_path` returns `None`, so `try_provenance_compose`
   gracefully falls back to existing strategies. Not a correctness issue.

4. **Multiple states per PC**: `get_unique_state` rejects PCs with multiple explored
   states. Sub-proofs inherit this restriction. Not new to Compose — backward_trace
   has the same limitation. Fail-safe.

5. **Certificate size**: Compose proofs are larger. Practical programs should have
   shallow trees (depth 2-3). `MAX_STEPS_PER_ENTRY` cap bounds worst case.

## File Map

| File | What it does |
|------|-------------|
| `src/pcc/model.rs` | ProofStep enum, certificate serialization, Display |
| `src/pcc/checker.rs` | `verify_proof_chain_replay`, `verify_fact`, `verify_transfer`, `verify_derive`, `derive_fact_from_branch`, `distance_upper_bound` |
| `src/pcc/validate.rs` | Structural validation (schema, connectivity, PC ordering, bound sum) |
| `src/pcc/generator.rs` | `generate_certificate`, `backward_trace`, `backward_transfer`, `try_derive_chain`, `find_derive_sequence`, `transfer_deltas_sound` |
| `src/pcc/injector.rs` | `apply_verified_refinements` — tightens interval state using verified entries |
| `src/domains/zone/dbm.rs` | DBM matrix, `ProvenanceTracker`, `reconstruct_path`, `close`, `add_constraint`, `forget_var` |
| `src/domains/zone/ops.rs` | Zone domain operations: `apply_add_reg`, `apply_add_imm`, `assume_*` |
| `src/analysis/transfer/alu/arithmetic.rs` | Zone transfer function for ADD (calls `forget`, `assign_interval`, `apply_add_reg`) |
| `src/analysis/mod.rs` | Main analysis loop, calls `set_current_pc` at line 265 |
| `pcc-tests/pcc_examples.json` | Test programs |
| `pcc-tests/cert_cases.json` | Regression test cases |
