/*
 * Open-coded iterator backport (Phase 3 W3.2d).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source file:  tools/testing/selftests/bpf/progs/iters.c (inspiration).
 * Feature:      open-coded iterators bpf_iter_{num,task,css,bits} via
 *               kfunc calls (BPF_PSEUDO_KFUNC_CALL, src_reg=2, imm=btf_id).
 *               Kernel iterators appeared in v6.4; task/css/bits followed
 *               in v6.6-v6.10.
 *
 * Test BTF wiring: selftest harness registers the 12 iter kfunc names at
 * synthetic btf_ids 100..111 (see src/testing/selftest.rs). Ordering is:
 *   num:  new=100,  next=101,  destroy=102
 *   task: new=103,  next=104,  destroy=105
 *   css:  new=106,  next=107,  destroy=108
 *   bits: new=109,  next=110,  destroy=111
 *
 * Not included (deferred to later workstreams):
 *   - Loop cases exercising *_next NULL convergence. W3.2c subsumption
 *     covers iter_id-matching Active slots; a representative loop test
 *     belongs with the Phase 4 BTF-typed element-return upgrade where
 *     the loop body can actually dereference the element pointer.
 *   - bpf_for_each_map_elem: callback-style, lives in W3.4.
 *
 * W3.2d expectation: all 7 cases hit their declared outcome with no FPs.
 * REJECT cases intentionally omit .errstr — the harness accepts any
 * rejection reason when errstr is absent, keeping the test resilient to
 * future error-message polish.
 */

{
	"iter_num basic new+destroy",
	.insns = {
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -8),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 100),	/* bpf_iter_num_new */
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -8),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 102),	/* bpf_iter_num_destroy */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
{
	"iter_num missing destroy",
	.insns = {
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -8),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 100),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
{
	"iter_num destroy without init",
	.insns = {
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -8),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 102),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
{
	"iter_num double init",
	.insns = {
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -8),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 100),
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -8),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 100),	/* double init */
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -8),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 102),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
{
	"iter_task basic new+destroy",
	.insns = {
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -40),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 103),
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -40),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 105),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
{
	"iter_css basic new+destroy",
	.insns = {
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -24),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 106),
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -24),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 108),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
{
	"iter_bits basic new+destroy",
	.insns = {
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -16),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 109),
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_10),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -16),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 111),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
