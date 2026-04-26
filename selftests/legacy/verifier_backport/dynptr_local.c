/*
 * Local dynptr backport (Phase 4 W4.2e).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source files: tools/testing/selftests/bpf/progs/dynptr_success.c,
 *               tools/testing/selftests/bpf/progs/dynptr_fail.c (inspiration).
 * Feature:      Local-kind bpf_dynptr created via `bpf_dynptr_from_mem`
 *               over a stack buffer; consumed via `bpf_dynptr_read` /
 *               `bpf_dynptr_write`. Local dynptrs are pure metadata
 *               (no acquire/release ref) so leaving them initialized at
 *               exit is fine.
 *
 * Test BTF wiring: synthetic btf_ids 117..119 (see src/testing/selftest.rs):
 *   bpf_dynptr_from_mem = 117
 *   bpf_dynptr_read     = 118
 *   bpf_dynptr_write    = 119
 *
 * Stack layout: 16-byte dynptr at R10-16 (offsets -16, -8). 8-byte
 * scratch buffer at R10-24 (offset -24). Where two dynptrs are
 * needed, the second goes at R10-32 (offsets -32, -24) and the
 * scratch at R10-40.
 *
 * REJECT cases intentionally omit .errstr — the harness accepts any
 * rejection reason when errstr is absent.
 */
