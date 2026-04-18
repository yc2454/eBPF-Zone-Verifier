/*
 * Backport of tools/testing/selftests/bpf/progs/verifier_load_acquire.c (v6.15).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source file:  selftests/progs/verifier_load_acquire.c
 * Feature:      BPF_LOAD_ACQ (load-acquire atomic), v6.11.
 * Encoding:     class=BPF_STX(0x03), mode=BPF_ATOMIC(0xc0); imm=BPF_LOAD_ACQ(0x100).
 *               Opcode bytes:
 *                 B:  0xd3   H:  0xcb   W:  0xc3   DW: 0xdb
 *               dst = destination register, src = address register, off = disp.
 *
 * Scope reductions (see ../verifier_backport/README.md):
 *   - Dropped the misaligned-access case (needs BPF_F_ANY_ALIGNMENT flag).
 *   - Dropped sk_reuseport ("from sock pointer"); ctx/pkt/flow_keys already
 *     cover the BPF_ATOMIC-from-typed-ptr rejection path.
 *
 * Pre-W1.4: tests error either on the atomic imm (0x100 unknown) or on
 * an unrelated existing atomic-decoder path. Post-W1.4 the 4 core cases
 * should ACCEPT, the ctx/pkt/flow_keys cases REJECT with a type-specific
 * message, and the register/non-pointer/uninit cases REJECT on existing
 * pointer/init checks.
 */

/* --- core load-acquire: stored-then-loaded round-trip on stack (4 cases) --- */

{
	"load-acquire, 8-bit",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_1, 0x12),
	BPF_STX_MEM(BPF_B, BPF_REG_10, BPF_REG_1, -1),
	BPF_RAW_INSN(0xd3, BPF_REG_0, BPF_REG_10, -1, 0x100),	/* w0 = load_acquire((u8 *)(r10 - 1)) */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"load-acquire, 16-bit",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_1, 0x1234),
	BPF_STX_MEM(BPF_H, BPF_REG_10, BPF_REG_1, -2),
	BPF_RAW_INSN(0xcb, BPF_REG_0, BPF_REG_10, -2, 0x100),	/* w0 = load_acquire((u16 *)(r10 - 2)) */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"load-acquire, 32-bit",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_1, 0x12345678),
	BPF_STX_MEM(BPF_W, BPF_REG_10, BPF_REG_1, -4),
	BPF_RAW_INSN(0xc3, BPF_REG_0, BPF_REG_10, -4, 0x100),	/* w0 = load_acquire((u32 *)(r10 - 4)) */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"load-acquire, 64-bit",
	.insns = {
	BPF_LD_IMM64(BPF_REG_1, 0x1234567890abcdefULL),
	BPF_STX_MEM(BPF_DW, BPF_REG_10, BPF_REG_1, -8),
	BPF_RAW_INSN(0xdb, BPF_REG_0, BPF_REG_10, -8, 0x100),	/* r0 = load_acquire((u64 *)(r10 - 8)) */
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},

/* --- register validity rejections (3 cases) --- */

{
	"load-acquire with uninitialized src_reg",
	.insns = {
	BPF_RAW_INSN(0xdb, BPF_REG_0, BPF_REG_2, 0, 0x100),	/* r0 = load_acquire((u64 *)(r2 + 0)) */
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "R2 !read_ok",
},
{
	"load-acquire with non-pointer src_reg",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 0),
	BPF_RAW_INSN(0xdb, BPF_REG_0, BPF_REG_1, 0, 0x100),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "R1 invalid mem access 'scalar'",
},
{
	"load-acquire with invalid register R15",
	.insns = {
	BPF_RAW_INSN(0xdb, BPF_REG_0, 15, 0, 0x100),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "R15 is invalid",
},

/* --- load-acquire from typed pointers (3 cases) --- */

{
	"load-acquire from ctx pointer",
	.insns = {
	BPF_RAW_INSN(0xd3, BPF_REG_0, BPF_REG_1, 0, 0x100),	/* w0 = load_acquire((u8 *)(r1 + 0)) */
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "BPF_ATOMIC loads from R1 ctx is not allowed",
	/* default prog_type (SOCKET_FILTER) -> ctx is __sk_buff */
},
{
	"load-acquire from pkt pointer",
	.insns = {
	BPF_LDX_MEM(BPF_W, BPF_REG_2, BPF_REG_1, 0),		/* r2 = xdp_md->data */
	BPF_LDX_MEM(BPF_W, BPF_REG_3, BPF_REG_1, 4),		/* r3 = xdp_md->data_end */
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_2),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, 8),
	BPF_JMP_REG(BPF_JGE, BPF_REG_1, BPF_REG_3, 1),
	BPF_RAW_INSN(0xd3, BPF_REG_0, BPF_REG_2, 0, 0x100),	/* w0 = load_acquire((u8 *)r2) */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "BPF_ATOMIC loads from R2 pkt is not allowed",
	.prog_type = BPF_PROG_TYPE_XDP,
},
{
	"load-acquire from flow_keys pointer",
	.insns = {
	/* flow_dissector ctx is __sk_buff; offsetof(__sk_buff, flow_keys) = 144 */
	BPF_LDX_MEM(BPF_DW, BPF_REG_2, BPF_REG_1, 144),
	BPF_RAW_INSN(0xd3, BPF_REG_0, BPF_REG_2, 0, 0x100),	/* w0 = load_acquire((u8 *)r2) */
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "BPF_ATOMIC loads from R2 flow_keys is not allowed",
	.prog_type = BPF_PROG_TYPE_FLOW_DISSECTOR,
},
