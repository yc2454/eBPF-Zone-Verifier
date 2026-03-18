{
	"pcc motivating: var add packet access (zone ok, kernel reject)",
	.insns = {
	BPF_LDX_MEM(BPF_W, BPF_REG_2, BPF_REG_1,
		    offsetof(struct __sk_buff, data)),
	BPF_LDX_MEM(BPF_W, BPF_REG_3, BPF_REG_1,
		    offsetof(struct __sk_buff, data_end)),
	BPF_MOV64_REG(BPF_REG_6, BPF_REG_2),
	BPF_MOV64_REG(BPF_REG_0, BPF_REG_6),
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_0, 8),
	BPF_JMP_REG(BPF_JGT, BPF_REG_0, BPF_REG_3, 7),
	BPF_LDX_MEM(BPF_B, BPF_REG_4, BPF_REG_6, 0),
	BPF_ALU64_IMM(BPF_AND, BPF_REG_4, 3),
	BPF_MOV64_REG(BPF_REG_5, BPF_REG_6),
	BPF_ALU64_REG(BPF_ADD, BPF_REG_5, BPF_REG_4),
	BPF_LDX_MEM(BPF_W, BPF_REG_0, BPF_REG_5, 0),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	BPF_MOV64_IMM(BPF_REG_0, 0),
	BPF_EXIT_INSN(),
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_SCHED_CLS,
},

{
	"pcc: var add + constant skip (add-imm, zone ok, interval reject)",
	// After variable-length field, skip 1 fixed byte before reading u32 payload.
	// Guard: data + 8 <= data_end
	// Safety: worst case r4=3, r5 = data+3+1 = data+4, load 4 bytes → data+8 <= data_end ✓
	.insns = {
	BPF_LDX_MEM(BPF_W, BPF_REG_2, BPF_REG_1,
		    offsetof(struct __sk_buff, data)),         // [0] r2 = data
	BPF_LDX_MEM(BPF_W, BPF_REG_3, BPF_REG_1,
		    offsetof(struct __sk_buff, data_end)),      // [1] r3 = data_end
	BPF_MOV64_REG(BPF_REG_0, BPF_REG_2),                 // [2] r0 = r2
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_0, 8),                // [3] r0 += 8
	BPF_JMP_REG(BPF_JGT, BPF_REG_0, BPF_REG_3, 8),      // [4] if r0 > r3 goto +8 (pc=13)
	BPF_LDX_MEM(BPF_B, BPF_REG_4, BPF_REG_2, 0),        // [5] r4 = *(u8*)(r2+0)
	BPF_ALU64_IMM(BPF_AND, BPF_REG_4, 3),                // [6] r4 &= 3
	BPF_MOV64_REG(BPF_REG_5, BPF_REG_2),                 // [7] r5 = r2 (data)
	BPF_ALU64_REG(BPF_ADD, BPF_REG_5, BPF_REG_4),       // [8] r5 += r4 (VAR ADD)
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_5, 1),                // [9] r5 += 1  (IMM ADD)
	BPF_LDX_MEM(BPF_W, BPF_REG_0, BPF_REG_5, 0),        // [10] r0 = *(u32*)(r5+0) LOAD
	BPF_MOV64_IMM(BPF_REG_0, 0),                          // [11] r0 = 0
	BPF_EXIT_INSN(),                                       // [12] exit
	BPF_MOV64_IMM(BPF_REG_0, 0),                          // [13] r0 = 0 (fail)
	BPF_EXIT_INSN(),                                       // [14] exit
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_SCHED_CLS,
},

{
	"pcc: var add + mov rename (mov-rename, zone ok, interval reject)",
	// After variable add, copy pointer to r6 before loading.
	// Guard: data + 7 <= data_end
	// Safety: worst case r4=3, r5 = data+3, r6 = r5, load 4 bytes → data+7 <= data_end ✓
	.insns = {
	BPF_LDX_MEM(BPF_W, BPF_REG_2, BPF_REG_1,
		    offsetof(struct __sk_buff, data)),         // [0] r2 = data
	BPF_LDX_MEM(BPF_W, BPF_REG_3, BPF_REG_1,
		    offsetof(struct __sk_buff, data_end)),      // [1] r3 = data_end
	BPF_MOV64_REG(BPF_REG_0, BPF_REG_2),                 // [2] r0 = r2
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_0, 7),                // [3] r0 += 7
	BPF_JMP_REG(BPF_JGT, BPF_REG_0, BPF_REG_3, 8),      // [4] if r0 > r3 goto +8 (pc=13)
	BPF_LDX_MEM(BPF_B, BPF_REG_4, BPF_REG_2, 0),        // [5] r4 = *(u8*)(r2+0)
	BPF_ALU64_IMM(BPF_AND, BPF_REG_4, 3),                // [6] r4 &= 3
	BPF_MOV64_REG(BPF_REG_5, BPF_REG_2),                 // [7] r5 = r2 (data)
	BPF_ALU64_REG(BPF_ADD, BPF_REG_5, BPF_REG_4),       // [8] r5 += r4 (VAR ADD)
	BPF_MOV64_REG(BPF_REG_6, BPF_REG_5),                 // [9] r6 = r5  (MOV RENAME)
	BPF_LDX_MEM(BPF_W, BPF_REG_0, BPF_REG_6, 0),        // [10] r0 = *(u32*)(r6+0) LOAD
	BPF_MOV64_IMM(BPF_REG_0, 0),                          // [11] r0 = 0
	BPF_EXIT_INSN(),                                       // [12] exit
	BPF_MOV64_IMM(BPF_REG_0, 0),                          // [13] r0 = 0 (fail)
	BPF_EXIT_INSN(),                                       // [14] exit
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_SCHED_CLS,
},

{
	"pcc: double var add (3-step chain, zone ok, interval reject)",
	// Two independent variable-length fields before u32 payload.
	// Guard: data + 11 <= data_end
	// Safety: worst case r4=3, r7=3, r5 = data+3+3 = data+6,
	//         load 4 bytes → data+10 <= data_end. Guard gives data+11, safe with slack.
	.insns = {
	BPF_LDX_MEM(BPF_W, BPF_REG_2, BPF_REG_1,
		    offsetof(struct __sk_buff, data)),         // [0]  r2 = data
	BPF_LDX_MEM(BPF_W, BPF_REG_3, BPF_REG_1,
		    offsetof(struct __sk_buff, data_end)),      // [1]  r3 = data_end
	BPF_MOV64_REG(BPF_REG_0, BPF_REG_2),                 // [2]  r0 = r2
	BPF_ALU64_IMM(BPF_ADD, BPF_REG_0, 11),               // [3]  r0 += 11
	BPF_JMP_REG(BPF_JGT, BPF_REG_0, BPF_REG_3, 10),     // [4]  if r0 > r3 goto +10 (pc=15)
	BPF_LDX_MEM(BPF_B, BPF_REG_4, BPF_REG_2, 0),        // [5]  r4 = *(u8*)(r2+0)
	BPF_ALU64_IMM(BPF_AND, BPF_REG_4, 3),                // [6]  r4 &= 3         [0,3]
	BPF_LDX_MEM(BPF_B, BPF_REG_7, BPF_REG_2, 1),        // [7]  r7 = *(u8*)(r2+1)
	BPF_ALU64_IMM(BPF_AND, BPF_REG_7, 3),                // [8]  r7 &= 3         [0,3]
	BPF_MOV64_REG(BPF_REG_5, BPF_REG_2),                 // [9]  r5 = r2 (data)
	BPF_ALU64_REG(BPF_ADD, BPF_REG_5, BPF_REG_4),       // [10] r5 += r4 (VAR ADD 1)
	BPF_ALU64_REG(BPF_ADD, BPF_REG_5, BPF_REG_7),       // [11] r5 += r7 (VAR ADD 2)
	BPF_LDX_MEM(BPF_W, BPF_REG_0, BPF_REG_5, 0),        // [12] r0 = *(u32*)(r5+0) LOAD
	BPF_MOV64_IMM(BPF_REG_0, 0),                          // [13] r0 = 0
	BPF_EXIT_INSN(),                                       // [14] exit
	BPF_MOV64_IMM(BPF_REG_0, 0),                          // [15] r0 = 0  (fail target)
	BPF_EXIT_INSN(),                                       // [16] exit
	},
	.result = ACCEPT,
	.prog_type = BPF_PROG_TYPE_SCHED_CLS,
},
