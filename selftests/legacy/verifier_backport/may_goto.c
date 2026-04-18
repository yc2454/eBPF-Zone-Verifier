/*
 * Backport of tools/testing/selftests/bpf/progs/verifier_may_goto_1.c (v6.15).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source file:  selftests/progs/verifier_may_goto_1.c
 * Feature:      may_goto / BPF_JCOND (v6.8). Decode-only skeleton in
 *               Phase 1; full 8M-iteration counter semantics land in
 *               Phase 3.
 * Opcode:       0xe5 = BPF_JMP(0x05) | BPF_JCOND(0xe0) | BPF_K(0x00)
 *               off = signed 16-bit displacement, imm = 0.
 *
 * Skipped upstream content:
 *   - verifier_may_goto_1.c: the two "batch with offsets 2/0" variants
 *     have identical insn streams; they differ only in __arch_* and
 *     __xlated(...) assertions on the post-verifier lowered program,
 *     which our framework doesn't model. Merged into one case.
 *   - verifier_may_goto_2.c: a single C-level test exercising `can_loop`
 *     whose may_goto insns are emitted by clang, not hand-written. Not
 *     backportable without running clang.
 *
 * Post-W1.3 expectation: the 4 cases below REJECT with an
 * UnsupportedModernFeature-flavored error, per the Phase 1 plan (decode
 * skeleton only, no semantics). When Phase 3 wires in the counter, they
 * should flip to ACCEPT.
 *
 * Pre-W1.3 expectation: all 4 error with UnknownOpcode on 0xe5.
 */

{
	"may_goto 0",
	.insns = {
	BPF_RAW_INSN(0xe5, 0, 0, 0, 0),		/* may_goto +0 */
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_RAW_INSN(0xe5, 0, 0, 0, 0),		/* may_goto +0 */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_RAW_TRACEPOINT,
},
{
	"batch 2 of may_goto 0",
	.insns = {
	BPF_RAW_INSN(0xe5, 0, 0, 0, 0),
	BPF_RAW_INSN(0xe5, 0, 0, 0, 0),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_RAW_INSN(0xe5, 0, 0, 0, 0),
	BPF_RAW_INSN(0xe5, 0, 0, 0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_RAW_TRACEPOINT,
},
{
	"may_goto batch with offsets 2/1/0",
	.insns = {
	BPF_RAW_INSN(0xe5, 0, 0, 2, 0),
	BPF_RAW_INSN(0xe5, 0, 0, 1, 0),
	BPF_RAW_INSN(0xe5, 0, 0, 0, 0),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_RAW_INSN(0xe5, 0, 0, 2, 0),
	BPF_RAW_INSN(0xe5, 0, 0, 1, 0),
	BPF_RAW_INSN(0xe5, 0, 0, 0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_RAW_TRACEPOINT,
},
{
	"may_goto batch with offsets 2/0",
	.insns = {
	BPF_RAW_INSN(0xe5, 0, 0, 2, 0),
	BPF_RAW_INSN(0xe5, 0, 0, 0, 0),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_MOV64_IMM(BPF_REG_0, 2),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_RAW_TRACEPOINT,
},
