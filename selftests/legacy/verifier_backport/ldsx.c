/*
 * Backport of tools/testing/selftests/bpf/progs/verifier_ldsx.c (v6.15).
 *
 * Source tag:    v6.15 (see selftests/SOURCE_TAG)
 * Source file:   selftests/progs/verifier_ldsx.c
 * Feature:       LDSX (sign-extending load), BPF_LDX | BPF_MEMSX | size, v6.6.
 * Opcodes used:  0x91 = LDXSX B, 0x89 = LDXSX H, 0x81 = LDXSX W.
 *
 * See ../verifier_backport/README.md for the translation shortcuts taken
 * (dropped __retval, __log_level, __msg internal-state checks, BE branches;
 * modern SEC() names collapsed to underlying prog types; hardcoded offsets).
 *
 * Today (pre-W1.1) every case errors with "unsupported opcode". After W1.1
 * the 6 non-ctx cases should ACCEPT and the 8 ctx cases should REJECT with
 * an "invalid bpf_context access"-flavored message.
 */

/* --- core LDSX: sign-extend round-trip through stack (3 cases) --- */

{
	"LDSX, S8",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 0x3fe),
	BPF_STX_MEM(BPF_DW, BPF_REG_10, BPF_REG_1, -8),
	BPF_RAW_INSN(0x91, BPF_REG_0, BPF_REG_10, -8, 0),	/* r0 = (s8)*(s8 *)(r10 - 8) */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"LDSX, S16",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 0x3fffe),
	BPF_STX_MEM(BPF_DW, BPF_REG_10, BPF_REG_1, -8),
	BPF_RAW_INSN(0x89, BPF_REG_0, BPF_REG_10, -8, 0),	/* r0 = (s16)*(s16 *)(r10 - 8) */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"LDSX, S32",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 0xfffffffe),
	BPF_STX_MEM(BPF_DW, BPF_REG_10, BPF_REG_1, -8),
	BPF_RAW_INSN(0x81, BPF_REG_0, BPF_REG_10, -8, 0),	/* r0 = (s32)*(s32 *)(r10 - 8) */
	BPF_ALU64_IMM(BPF_RSH, BPF_REG_0, 1),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},

/* --- LDSX + range propagation via bpf_get_prandom_u32 (3 cases) --- */

{
	"LDSX, S8 range checking, privileged",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_STX_MEM(BPF_DW, BPF_REG_10, BPF_REG_0, -8),
	BPF_RAW_INSN(0x91, BPF_REG_1, BPF_REG_10, -8, 0),	/* r1 = (s8)*(s8 *)(r10 - 8) */
	/* expect r1 carries s8 range [-128, 127]; both branches below are dead */
	BPF_JMP_IMM(BPF_JSGT, BPF_REG_1, 0x7f, 4),
	BPF_JMP_IMM(BPF_JSLT, BPF_REG_1, -0x80, 3),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_0, 2),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"LDSX, S16 range checking",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_STX_MEM(BPF_DW, BPF_REG_10, BPF_REG_0, -8),
	BPF_RAW_INSN(0x89, BPF_REG_1, BPF_REG_10, -8, 0),	/* r1 = (s16)*(s16 *)(r10 - 8) */
	BPF_JMP_IMM(BPF_JSGT, BPF_REG_1, 0x7fff, 4),
	BPF_JMP_IMM(BPF_JSLT, BPF_REG_1, -0x8000, 3),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_0, 2),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"LDSX, S32 range checking",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_STX_MEM(BPF_DW, BPF_REG_10, BPF_REG_0, -8),
	BPF_RAW_INSN(0x81, BPF_REG_1, BPF_REG_10, -8, 0),	/* r1 = (s32)*(s32 *)(r10 - 8) */
	BPF_JMP_IMM(BPF_JSGT, BPF_REG_1, 0x7fffffff, 4),
	BPF_JMP_IMM(BPF_JSLT, BPF_REG_1, -0x80000000LL, 3),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_0, 2),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},

/* --- LDSX on xdp_md ctx fields (3 cases) --- */

{
	"LDSX, xdp s32 xdp_md->data",
	.insns = {
	BPF_RAW_INSN(0x81, BPF_REG_2, BPF_REG_1, 0, 0),		/* offsetof(xdp_md, data) = 0 */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "invalid bpf_context access",
	.prog_type = BPF_PROG_TYPE_XDP,
},
{
	"LDSX, xdp s32 xdp_md->data_end",
	.insns = {
	BPF_RAW_INSN(0x81, BPF_REG_2, BPF_REG_1, 4, 0),		/* offsetof(xdp_md, data_end) = 4 */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "invalid bpf_context access",
	.prog_type = BPF_PROG_TYPE_XDP,
},
{
	"LDSX, xdp s32 xdp_md->data_meta",
	.insns = {
	BPF_RAW_INSN(0x81, BPF_REG_2, BPF_REG_1, 8, 0),		/* offsetof(xdp_md, data_meta) = 8 */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "invalid bpf_context access",
	.prog_type = BPF_PROG_TYPE_XDP,
},

/* --- LDSX on __sk_buff ctx fields via tcx (sched_cls), 3 cases --- */

{
	"LDSX, tcx s32 __sk_buff->data",
	.insns = {
	BPF_RAW_INSN(0x81, BPF_REG_2, BPF_REG_1, 76, 0),	/* offsetof(__sk_buff, data) = 76 */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "invalid bpf_context access",
	.prog_type = BPF_PROG_TYPE_SCHED_CLS,
},
{
	"LDSX, tcx s32 __sk_buff->data_end",
	.insns = {
	BPF_RAW_INSN(0x81, BPF_REG_2, BPF_REG_1, 80, 0),	/* offsetof(__sk_buff, data_end) = 80 */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "invalid bpf_context access",
	.prog_type = BPF_PROG_TYPE_SCHED_CLS,
},
{
	"LDSX, tcx s32 __sk_buff->data_meta",
	.insns = {
	BPF_RAW_INSN(0x81, BPF_REG_2, BPF_REG_1, 84, 0),	/* offsetof(__sk_buff, data_meta) = 84 */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "invalid bpf_context access",
	.prog_type = BPF_PROG_TYPE_SCHED_CLS,
},

/* --- LDSX on __sk_buff via flow_dissector (2 cases) --- */

{
	"LDSX, flow_dissector s32 __sk_buff->data",
	.insns = {
	BPF_RAW_INSN(0x81, BPF_REG_2, BPF_REG_1, 76, 0),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "invalid bpf_context access",
	.prog_type = BPF_PROG_TYPE_FLOW_DISSECTOR,
},
{
	"LDSX, flow_dissector s32 __sk_buff->data_end",
	.insns = {
	BPF_RAW_INSN(0x81, BPF_REG_2, BPF_REG_1, 80, 0),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "invalid bpf_context access",
	.prog_type = BPF_PROG_TYPE_FLOW_DISSECTOR,
},
