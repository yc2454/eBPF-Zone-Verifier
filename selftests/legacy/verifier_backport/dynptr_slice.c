/*
 * dynptr_slice / slice_rdwr backport (Phase 4 W4.2g).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source files: tools/testing/selftests/bpf/progs/dynptr_success.c,
 *               tools/testing/selftests/bpf/progs/dynptr_fail.c (inspiration).
 * Feature:      bpf_dynptr_slice / slice_rdwr return a pointer into
 *               the dynptr's backing memory (or to a scratch buffer
 *               on the slow path). The pointer is nullable; mem_size
 *               is taken from the scratch-buffer size arg.
 *
 * Test BTF wiring: synthetic btf_ids 122..123 (see src/testing/selftest.rs):
 *   bpf_dynptr_slice      = 122
 *   bpf_dynptr_slice_rdwr = 123
 *
 * Stack layout: dynptr at R10-16 (offsets -16, -8). Backing buf for
 * Local dynptrs at R10-24 (8 bytes). Scratch for slice at R10-32
 * (8 bytes).
 *
 * REJECT cases intentionally omit .errstr — the harness accepts any
 * rejection reason when errstr is absent.
 */
