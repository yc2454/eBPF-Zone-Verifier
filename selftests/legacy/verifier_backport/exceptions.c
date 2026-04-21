/*
 * bpf_throw / exception-frame backport (Phase 3 W3.3b).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source file:  tools/testing/selftests/bpf/progs/exceptions.c (inspiration).
 * Feature:      bpf_throw kfunc (v6.7, commit f18b03faba44) and the
 *               exception-callback registration kfunc. Programs may call
 *               bpf_throw() to terminate execution; if a callback is
 *               installed, control transfers there, otherwise the program
 *               unwinds with return 0.
 *
 * Test BTF wiring: selftest harness registers the 2 kfunc names at
 * synthetic btf_ids:
 *   bpf_throw                    = 112
 *   bpf_set_exception_callback   = 113
 *
 * W3.3b models bpf_throw as terminal (no in-program successor) and
 * bpf_set_exception_callback as a no-op register write — the callback
 * target is a PSEUDO_FUNC register that we cannot resolve until W3.4
 * wires callback-frame plumbing, but since throw is terminal the
 * unresolved handler is not observable.
 *
 * Not included (deferred):
 *   - Exception-handler execution trace (requires PSEUDO_FUNC support
 *     from W3.4 to resolve the subprog entry PC).
 *   - Cookie-propagation to the handler's R1 argument.
 */

{
	"bpf_throw terminates the program",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 0),			/* cookie */
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 112),	/* bpf_throw */
	BPF_MOV64_IMM(BPF_REG_0, 0),			/* unreachable */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
{
	"bpf_set_exception_callback accepted as no-op",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 0),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 113),	/* bpf_set_exception_callback */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
{
	"set_exception_callback then throw",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 0),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 113),	/* bpf_set_exception_callback */
	BPF_MOV64_IMM(BPF_REG_1, 7),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 2, 0, 112),	/* bpf_throw */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_TRACING,
},
