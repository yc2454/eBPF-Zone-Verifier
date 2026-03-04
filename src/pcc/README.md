# PCC Module Notes

This prototype uses one proof model: **PC-local inductive annotations**.

## Certificate schema

- `ProgramCertificate { version, program_hash, pc_annotations }`
- `PcAnnotation { pc, entries }`
- `AnnotationEntry { i, j, bound, proof }`
- `ProofStep`:
  - `GuardStep { i, j, c }`
  - `PreStateStep { i, j, c }`

Constraint meaning is always:

- `i - j <= c`

## Checker model

For successor state at `pc = k`, checker reads `PcAnnotation { pc: k }` and verifies each entry from:

1. predecessor state,
2. predecessor instruction,
3. edge guard (if predecessor is a branch and this edge has a polarity).

Entry is accepted only if all hold:

1. proof chain is connected and endpoints match `(i, j)`,
2. each step is justified:
   - `GuardStep`: must match the guard implied by branch op + edge,
   - `PreStateStep`: must be justified by one-step transfer upper-bound from predecessor state,
3. sum of step bounds equals `entry.bound`.

On success, checker applies narrow packet-range refinement only.
On failure, entry is ignored (fail-closed).

## Validation model

`validate` is structural only:

- schema version check,
- PC and register index bounds,
- proof non-empty and capped length,
- chain connectivity and i64-safe sum.

No semantic proof happens in `validate`; that is checker-only.

## Practical caps

- `MAX_STEPS_PER_ENTRY = 3`
- `MAX_ENTRIES_PER_PC = 8`

If an entry exceeds caps, it is rejected at validation.
