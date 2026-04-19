/*
 * Backport of tools/testing/selftests/bpf/progs/verifier_movsx.c (v6.15).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source file:  selftests/progs/verifier_movsx.c
 * Feature:      MOVSX (sign-extending register move), v6.6.
 * Opcodes used: 0xbc = ALU|MOV|X (32-bit), 0xbf = ALU64|MOV|X (64-bit).
 *               MOVSX shares the opcode byte with regular MOV; the `off`
 *               field selects the sign-extend source width:
 *                 off = 8  -> (s8)
 *                 off = 16 -> (s16)
 *                 off = 32 -> (s32)  (64-bit form only)
 *
 * See ../verifier_backport/README.md for the translation shortcuts taken.
 *
 * Today (pre-W1.1) every case errors "unsupported opcode 0xbc/0xbf with
 * non-zero off" once the decoder learns to reject instead of panic, or
 * similar. After W1.1 the 13 success cases should ACCEPT and the 2
 * failure cases REJECT with the indicated message flavor.
 */

/* --- core MOVSX (5 cases) --- */

{
	"MOV32SX, S8",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_0, 0xff23),
	BPF_RAW_INSN(0xbc, BPF_REG_0, BPF_REG_0, 8, 0),	/* w0 = (s8)w0 */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"MOV32SX, S16",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_0, 0xff23),
	BPF_RAW_INSN(0xbc, BPF_REG_0, BPF_REG_0, 16, 0),	/* w0 = (s16)w0 */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"MOV64SX, S8",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_0, 0x1fe),
	BPF_RAW_INSN(0xbf, BPF_REG_0, BPF_REG_0, 8, 0),	/* r0 = (s8)r0 */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"MOV64SX, S16",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_0, 0xf0f23),
	BPF_RAW_INSN(0xbf, BPF_REG_0, BPF_REG_0, 16, 0),	/* r0 = (s16)r0 */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"MOV64SX, S32",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_0, 0xfffffffe),
	BPF_RAW_INSN(0xbf, BPF_REG_0, BPF_REG_0, 32, 0),	/* r0 = (s32)r0 */
	BPF_ALU64_IMM(BPF_RSH, BPF_REG_0, 1),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},

/* --- 32-bit MOVSX + range propagation (3 cases) --- */

{
	"MOV32SX, S8, range_check",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_RAW_INSN(0xbc, BPF_REG_1, BPF_REG_0, 8, 0),	/* w1 = (s8)w0 */
	BPF_JMP32_IMM(BPF_JSGT, BPF_REG_1, 0x7f, 4),
	BPF_JMP32_IMM(BPF_JSLT, BPF_REG_1, -0x80, 3),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_0, 2),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"MOV32SX, S16, range_check",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_RAW_INSN(0xbc, BPF_REG_1, BPF_REG_0, 16, 0),	/* w1 = (s16)w0 */
	BPF_JMP32_IMM(BPF_JSGT, BPF_REG_1, 0x7fff, 4),
	BPF_JMP32_IMM(BPF_JSLT, BPF_REG_1, -0x80ff, 3),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_0, 2),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"MOV32SX, S16, range_check 2",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 65535),
	BPF_RAW_INSN(0xbc, BPF_REG_2, BPF_REG_1, 16, 0),	/* w2 = (s16)w1 */
	BPF_ALU64_IMM(BPF_RSH, BPF_REG_2, 1),
	BPF_JMP_IMM(BPF_JNE, BPF_REG_2, 0x7fffffff, 2),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},

/* --- 64-bit MOVSX + range propagation (3 cases) --- */

{
	"MOV64SX, S8, range_check",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_RAW_INSN(0xbf, BPF_REG_1, BPF_REG_0, 8, 0),	/* r1 = (s8)r0 */
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
	"MOV64SX, S16, range_check",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_RAW_INSN(0xbf, BPF_REG_1, BPF_REG_0, 16, 0),	/* r1 = (s16)r0 */
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
	"MOV64SX, S32, range_check",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_RAW_INSN(0xbf, BPF_REG_1, BPF_REG_0, 32, 0),	/* r1 = (s32)r0 */
	BPF_JMP_IMM(BPF_JSGT, BPF_REG_1, 0x7fffffff, 4),
	BPF_JMP_IMM(BPF_JSLT, BPF_REG_1, -0x80000000LL, 3),
	BPF_MOV64_IMM(BPF_REG_0, 1),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_0, 2),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},

/* --- MOV64SX, S16 on R10: sign-extending the frame pointer (1 case) --- */

{
	"MOV64SX, S16, R10 Sign Extension",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 553656332),
	BPF_STX_MEM(BPF_W, BPF_REG_10, BPF_REG_1, -8),
	BPF_RAW_INSN(0xbf, BPF_REG_1, BPF_REG_10, 16, 0),	/* r1 = (s16)r10 */
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, -8),
	BPF_MOV64_IMM(BPF_REG_2, 3),
	BPF_JMP_REG(BPF_JLE, BPF_REG_2, BPF_REG_1, 0),
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_trace_printk),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "R1 type=scalar expected=",
},

/* --- MOV32SX, S8, var_off u32_max: expected infinite loop detection --- */

{
	"MOV32SX, S8, var_off u32_max",
	.insns = {
	BPF_LDX_MEM(BPF_B, BPF_REG_3, BPF_REG_10, -387),
	BPF_RAW_INSN(0xbc, BPF_REG_7, BPF_REG_3, 8, 0),	/* w7 = (s8)w3 */
	BPF_JMP32_IMM(BPF_JGE, BPF_REG_7, 0x2533823b, -3),
	BPF_MOV32_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "infinite loop detected",
},

/* --- MOV32SX var_off paths that should ACCEPT under priv (2 cases) --- */

{
	"MOV32SX, S8, var_off not u32_max, positive after s8 extension",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_MOV64_REG(BPF_REG_3, BPF_REG_0),
	BPF_ALU64_IMM(BPF_AND, BPF_REG_3, 0xf),
	BPF_RAW_INSN(0xbc, BPF_REG_7, BPF_REG_3, 8, 0),	/* w7 = (s8)w3 */
	BPF_JMP32_IMM(BPF_JSGE, BPF_REG_7, 16, 2),
	BPF_MOV32_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_10, 1),		/* priv: skipped; unpriv: forbidden */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"MOV32SX, S8, var_off not u32_max, negative after s8 extension",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_MOV64_REG(BPF_REG_3, BPF_REG_0),
	BPF_ALU64_IMM(BPF_AND, BPF_REG_3, 0xf),
	BPF_ALU64_IMM(BPF_OR, BPF_REG_3, 0x80),
	BPF_RAW_INSN(0xbc, BPF_REG_7, BPF_REG_3, 8, 0),	/* w7 = (s8)w3 */
	BPF_JMP32_IMM(BPF_JSGE, BPF_REG_7, -5, 2),
	BPF_MOV32_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_10, 1),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},

/* --- unsigned range_check after MOVSX (2 cases) --- */

{
	"MOV64SX, S8, unsigned range_check",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_ALU64_IMM(BPF_AND, BPF_REG_0, 0x1),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_0, 0xfe),
	BPF_RAW_INSN(0xbf, BPF_REG_0, BPF_REG_0, 8, 0),	/* r0 = (s8)r0 */
	BPF_JMP_IMM(BPF_JLT, BPF_REG_0, -2, 2),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"MOV32SX, S8, unsigned range_check",
	.insns = {
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32),
	BPF_ALU32_IMM(BPF_AND, BPF_REG_0, 0x1),
	BPF_ALU32_IMM(BPF_ADD, BPF_REG_0, 0xfe),
	BPF_RAW_INSN(0xbc, BPF_REG_0, BPF_REG_0, 8, 0),	/* w0 = (s8)w0 */
	BPF_JMP32_IMM(BPF_JLT, BPF_REG_0, 0xfffffffe, 2),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
