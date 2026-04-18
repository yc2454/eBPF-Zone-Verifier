# legacy/verifier_backport/

Hand-authored old-style test files (pre-6.2 `struct bpf_test` / `BPF_RAW_INSN`
format, consumable by `convert.sh`) that translate post-6.2 upstream tests
from `../../progs/verifier_*.c`.

Each backport file should:

- Carry a header comment naming its upstream source file and the kernel tag
  it was translated from (matches `../../SOURCE_TAG`).
- Preserve the original test names so reviewers can cross-reference.
- Use `BPF_RAW_INSN(...)` for any opcode the old macro set (`BPF_MOV64_IMM`,
  `BPF_LDX_MEM`, etc.) doesn't cover — notably LDSX, MOVSX, gotol, may_goto,
  load_acq, store_rel.

This directory exists because Phase 1 ISA additions landed upstream *after*
the old `tools/testing/selftests/bpf/verifier/` dir was removed, so there
are no upstream old-style tests to import directly.
