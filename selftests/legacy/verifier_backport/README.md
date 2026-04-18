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

## Translation shortcuts (log here as we encounter them)

Hand-translation collapses some upstream niceties that don't map to the
old format. Record them here so reviewers (and future-us) know what was
dropped:

- **`__retval(...)` dropped.** Our runner checks ACCEPT/REJECT, not program
  return value.
- **`__log_level(N) __msg("R1_w=...")` dropped.** We can't assert internal
  verifier register state; we keep the ACCEPT/REJECT verdict only.
- **Big-endian `#if __BYTE_ORDER__` branches dropped.** convert_tests.c
  compiles LE-only.
- **Modern `SEC()` names collapsed to underlying prog types.** Upstream
  uses `tcx/ingress` / `tcx/egress` which are sched_cls under the hood;
  our backports set `.prog_type = BPF_PROG_TYPE_SCHED_CLS` directly.
  Tracked in the modernization plan as a Phase 6 item: recognize modern
  SEC naming natively.
- **Struct-field offsets hardcoded.** Upstream uses
  `offsetof(struct xdp_md, data)` via kernel headers; we use literal
  numbers (xdp_md: data=0, data_end=4, data_meta=8; __sk_buff: data=76,
  data_end=80, data_meta=84) to avoid pulling headers into
  convert_tests.c.
