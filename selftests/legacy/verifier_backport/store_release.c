/*
 * Backport of tools/testing/selftests/bpf/progs/verifier_store_release.c (v6.15).
 *
 * Source tag:   v6.15 (see selftests/SOURCE_TAG)
 * Source file:  selftests/progs/verifier_store_release.c
 * Feature:      BPF_STORE_REL (store-release atomic), v6.11.
 * Encoding:     class=BPF_STX(0x03), mode=BPF_ATOMIC(0xc0); imm=BPF_STORE_REL(0x110).
 *               Opcode bytes:
 *                 B:  0xd3   H:  0xcb   W:  0xc3   DW: 0xdb
 *               dst = address register, src = value register, off = disp.
 *
 * Scope reductions (see ../verifier_backport/README.md):
 *   - Dropped misaligned-access case (needs BPF_F_ANY_ALIGNMENT).
 *   - Dropped sk_reuseport "to sock pointer" (uncommon prog type;
 *     ctx/pkt/flow_keys already cover typed-ptr rejection).
 *
 * Pre-W1.4: B/H variants hit UnknownOpcode; W/DW variants hit
 * UnknownAtomicOp on imm 0x110. Both are graceful decode errors.
 * Post-W1.4: core cases ACCEPT, typed-ptr cases REJECT with specific
 * messages, register-validity cases REJECT on existing checks.
 */

/* --- core store-release: round-trip via stack (4 cases) --- */

{
	"store-release, 8-bit",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_1, 0x12),
	BPF_RAW_INSN(0xd3, BPF_REG_10, BPF_REG_1, -1, 0x110),	/* store_release((u8 *)(r10 - 1), w1) */
	BPF_LDX_MEM(BPF_B, BPF_REG_0, BPF_REG_10, -1),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"store-release, 16-bit",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_1, 0x1234),
	BPF_RAW_INSN(0xcb, BPF_REG_10, BPF_REG_1, -2, 0x110),
	BPF_LDX_MEM(BPF_H, BPF_REG_0, BPF_REG_10, -2),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"store-release, 32-bit",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_1, 0x12345678),
	BPF_RAW_INSN(0xc3, BPF_REG_10, BPF_REG_1, -4, 0x110),
	BPF_LDX_MEM(BPF_W, BPF_REG_0, BPF_REG_10, -4),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"store-release, 64-bit",
	.insns = {
	BPF_LD_IMM64(BPF_REG_1, 0x1234567890abcdefULL),
	BPF_RAW_INSN(0xdb, BPF_REG_10, BPF_REG_1, -8, 0x110),
	BPF_LDX_MEM(BPF_DW, BPF_REG_0, BPF_REG_10, -8),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},

/* --- register validity rejections (4 cases) --- */

{
	"store-release with uninitialized src_reg",
	.insns = {
	BPF_RAW_INSN(0xdb, BPF_REG_10, BPF_REG_2, -8, 0x110),	/* store_release((u64 *)(r10 - 8), r2) */
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "R2 !read_ok",
},
{
	"store-release with uninitialized dst_reg",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 0),
	BPF_RAW_INSN(0xdb, BPF_REG_2, BPF_REG_1, -8, 0x110),	/* store_release((u64 *)(r2 - 8), r1) */
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "R2 !read_ok",
},
{
	"store-release with non-pointer dst_reg",
	.insns = {
	BPF_MOV64_IMM(BPF_REG_1, 0),
	BPF_RAW_INSN(0xdb, BPF_REG_1, BPF_REG_1, 0, 0x110),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "R1 invalid mem access 'scalar'",
},
{
	"store-release with invalid register R15",
	.insns = {
	BPF_RAW_INSN(0xdb, 15, BPF_REG_1, 0, 0x110),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "R15 is invalid",
},

/* --- typed-pointer rejections (3 cases) --- */

{
	"store-release to ctx pointer",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_0, 0),
	/* offsetof(__sk_buff, cb[0]) = 48 */
	BPF_RAW_INSN(0xd3, BPF_REG_1, BPF_REG_0, 48, 0x110),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "BPF_ATOMIC stores into R1 ctx is not allowed",
},
{
	"store-release to pkt pointer",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_0, 0),
	BPF_LDX_MEM(BPF_W, BPF_REG_2, BPF_REG_1, 0),		/* r2 = xdp_md->data */
	BPF_LDX_MEM(BPF_W, BPF_REG_3, BPF_REG_1, 4),		/* r3 = xdp_md->data_end */
	BPF_MOV64_REG(BPF_REG_1, BPF_REG_2),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_1, 8),
	BPF_JMP_REG(BPF_JGE, BPF_REG_1, BPF_REG_3, 1),
	BPF_RAW_INSN(0xd3, BPF_REG_2, BPF_REG_0, 0, 0x110),	/* store_release((u8 *)r2, w0) */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "BPF_ATOMIC stores into R2 pkt is not allowed",
	.prog_type = BPF_PROG_TYPE_XDP,
},
{
	"store-release to flow_keys pointer",
	.insns = {
	BPF_MOV32_IMM(BPF_REG_0, 0),
	/* offsetof(__sk_buff, flow_keys) = 144 */
	BPF_LDX_MEM(BPF_DW, BPF_REG_2, BPF_REG_1, 144),
	BPF_RAW_INSN(0xd3, BPF_REG_2, BPF_REG_0, 0, 0x110),
	BPF_EXIT_INSN(),
	},
	.result = REJECT,
	.errstr = "BPF_ATOMIC stores into R2 flow_keys is not allowed",
	.prog_type = BPF_PROG_TYPE_FLOW_DISSECTOR,
},

/* --- priv-accept leak scenarios (2 cases) --- */

{
	"store-release, leak pointer to stack",
	.insns = {
	BPF_RAW_INSN(0xdb, BPF_REG_10, BPF_REG_1, -8, 0x110),	/* store_release((u64 *)(r10 - 8), r1=ctx) */
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
},
{
	"store-release, leak pointer to map",
	.insns = {
	BPF_MOV64_REG(BPF_REG_6, BPF_REG_1),			/* 0: r6 = ctx */
	BPF_LD_MAP_FD(BPF_REG_1, 0),				/* 1-2: r1 = map_hash_8b */
	BPF_MOV64_IMM(BPF_REG_2, 0),				/* 3 */
	BPF_STX_MEM(BPF_DW, BPF_REG_10, BPF_REG_2, -8),		/* 4 */
	BPF_MOV64_REG(BPF_REG_2, BPF_REG_10),			/* 5 */
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_2, -8),			/* 6 */
	BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_map_lookup_elem),	/* 7 */
	BPF_JMP_IMM(BPF_JEQ, BPF_REG_0, 0, 1),			/* 8: if r0==0 goto l0 */
	BPF_RAW_INSN(0xdb, BPF_REG_0, BPF_REG_6, 0, 0x110),	/* 9: store_release((u64 *)r0, r6) */
	BPF_MOV64_IMM(BPF_REG_0, 0),				/* 10: l0 */
	BPF_EXIT_INSN(),					/* 11 */
	},
	.fixup_map_hash_8b = { 1 },
	.result = ACCEPT,
},
