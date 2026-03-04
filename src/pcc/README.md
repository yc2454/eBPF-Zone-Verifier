# PCC Module Notes

This folder implements certificate-aided verification for the userspace verifier.

## Why this module exists

Zone mode can derive relational facts that interval/kernel mode may not keep. PCC lets us carry selected facts from an offline proof artifact (certificate) and re-check them locally during interval analysis.

## Core terms

- `ProgramCertificate`: certificate file bound to a single lowered program (`program_hash`).
- `EdgeObligation`: one local claim for one CFG edge (`pred_pc -> succ_pc`).
- `ProofStep`: one inequality atom used in the proof chain.
  - `GuardStep { i, j, c }`: implied by branch semantics + edge polarity.
  - `PreStateStep { i, j, c }`: read from predecessor abstract state.
- `Constraint { i, j, c }`: means `reg(i) - reg(j) <= c`.

## What is `ObligationKind`

`ObligationKind` is the theorem template tag. It tells the checker:

1. what the claim means,
2. what step patterns are legal,
3. what transfer/equation checks are required,
4. what refinement is allowed on success.

This is intentionally separate from `ProofStep`:
- `ProofStep` says where each inequality came from.
- `ObligationKind` says how the whole proof should be interpreted.

Current kinds:

- `add_reg_packet_bound`:
  - Pattern: additive pointer update (`dst += src`) style bound reconstruction.
  - Uses `PreStateStep` chain in current implementation.
  - On success: narrows packet pointer range metadata only.

- `branch_guard_bound`:
  - Pattern: combine guard-implied inequality from a branch edge with prestate facts.
  - Requires `branch_taken` to pin edge polarity.
  - On success: same narrow packet-range refinement sink.

## Validate vs Checker (important)

The module uses two phases on purpose.

### `validate` phase (`validate.rs`)

Structural gate at certificate load time:
- version compatibility;
- in-bounds PCs/register indices;
- per-kind static shape checks (required fields, allowed branch ops, etc.).

This phase does **not** prove semantic correctness of obligations.

### `checker` phase (`checker.rs`)

Semantic gate during analysis, per edge:
- recompute predecessor fingerprint from live state + instruction;
- verify proof steps against live predecessor state and/or branch-implied guard;
- verify equation consistency;
- apply only narrow refinement on success.

If any check fails, refinement is skipped (fail-closed) and baseline verifier behavior continues.

## Soundness posture

- Unknown/malformed/inapplicable obligations do not broaden behavior.
- Refinement sink is intentionally narrow (packet range only).
- Certificate and program are hash-bound.

## Current limitations

- No global/loop proof obligations yet.
- Guard reasoning currently supports a restricted branch family.
- Obligation generation is still targeted at motivating shapes.
