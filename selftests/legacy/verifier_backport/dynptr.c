/*
 * Dynptr backport (Phase 4 W4.2c).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source files: tools/testing/selftests/bpf/progs/dynptr_success.c,
 *               tools/testing/selftests/bpf/progs/dynptr_fail.c (inspiration).
 * Feature:      bpf_dynptr stack-resident handles, lifecycle managed via
 *               kfunc calls (BPF_PSEUDO_KFUNC_CALL, src_reg=2, imm=btf_id).
 *               Dynptrs landed in v5.19 (Joanne Koong); ringbuf dynptr
 *               kfuncs in the same series.
 *
 * First W4.2 cluster covers ringbuf reserve/submit/discard only —
 * enough to exercise acquire/release tracking, the two-slot stack
 * invariant, and the exit-time leak check. `bpf_dynptr_from_mem`,
 * `bpf_dynptr_read/write/slice`, and the skb/xdp ctors land in later
 * W4.2 sub-steps once their helper-side mem-size-pair plumbing
 * generalizes for kfuncs.
 *
 * Test BTF wiring: selftest harness registers the dynptr kfunc names
 * at synthetic btf_ids 114..116 (see src/testing/selftest.rs):
 *   bpf_ringbuf_reserve_dynptr   = 114
 *   bpf_ringbuf_submit_dynptr    = 115
 *   bpf_ringbuf_discard_dynptr   = 116
 *
 * Stack layout: programs put `&dynptr` at R10 - 16 (16-byte STACK_DYNPTR
 * pair occupying offsets -16 and -8).
 *
 * REJECT cases intentionally omit .errstr — the harness accepts any
 * rejection reason when errstr is absent, keeping tests resilient to
 * future error-message polish.
 */
