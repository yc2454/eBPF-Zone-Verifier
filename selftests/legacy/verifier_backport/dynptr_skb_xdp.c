/*
 * skb / xdp dynptr backport (Phase 4 W4.2f).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source files: tools/testing/selftests/bpf/progs/dynptr_success.c,
 *               tools/testing/selftests/bpf/progs/dynptr_fail.c (inspiration).
 * Feature:      bpf_dynptr_from_skb / from_xdp construct dynptrs
 *               wrapping packet data. Forced rdonly in this cluster
 *               to match the conservative kernel default (writable
 *               skb/xdp dynptrs depend on per-program-type modeling
 *               that arrives later).
 *
 * Test BTF wiring: synthetic btf_ids 120..121 (see src/testing/selftest.rs):
 *   bpf_dynptr_from_skb = 120
 *   bpf_dynptr_from_xdp = 121
 *
 * Stack layout: dynptr at R10-16 (offsets -16, -8). Read dst / write
 * src scratch buffers at R10-32 onwards.
 *
 * REJECT cases intentionally omit .errstr — the harness accepts any
 * rejection reason when errstr is absent.
 */
