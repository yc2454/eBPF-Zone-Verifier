/*
 * Backport of tools/testing/selftests/bpf/progs/verifier_gotol.c (v6.15).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source file:  selftests/progs/verifier_gotol.c
 * Feature:      gotol (32-bit unconditional jump), v6.7.
 *               BPF_JMP32 | BPF_JA | BPF_K with imm = signed 32-bit
 *               displacement (vs classic BPF_JMP | BPF_JA which encodes a
 *               signed 16-bit displacement in `off`).
 * Opcode:       0x06 = BPF_JMP32(0x06) | BPF_JA(0x00) | BPF_K(0x00).
 *
 * Upstream has 2 tests; only gotol_small_imm is backported here.
 * gotol_large_imm uses .rept 40000 to force a jump target >16 bits away,
 * which isn't practical to expand by hand in the old struct bpf_test
 * format. A future convert_tests.c extension (or a fill_* helper akin to
 * bpf_fill_ja) could add coverage for the large-displacement case.
 *
 * See ../verifier_backport/README.md for translation shortcuts.
 *
 * Pre-W1.2 expectation: decoder rejects opcode 0x06 as unknown.
 * Post-W1.2: ACCEPT.
 */

{
	"gotol, small_imm",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_ktime_get_ns),	/* 0 */
	BPF_JMP_IMM(BPF_JEQ, BPF_REG_0, 0, 4),					/* 1: if r0==0 goto l0 (->6) */
	BPF_RAW_INSN(0x06, 0, 0, 0, 1),						/* 2: gotol l1 (->4) */
	BPF_RAW_INSN(0x06, 0, 0, 0, 3),						/* 3: l2: gotol l3 (->7) */
	BPF_MOV64_IMM(BPF_REG_0, 1),						/* 4: l1: r0 = 1 */
	BPF_RAW_INSN(0x06, 0, 0, 0, -3),					/* 5: gotol l2 (->3) */
	BPF_MOV64_IMM(BPF_REG_0, 2),						/* 6: l0: r0 = 2 */
	BPF_EXIT_INSN(),							/* 7: l3: exit */
	},
	.result = ACCEPT,
},
