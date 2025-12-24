// src/bpf_to_ast.rs
use crate::ast::{AluOp, CmpOp, Instr, Operand, Program, Width, MemSize};
use crate::bpf_insn::RawBpfInsn;
use crate::domain::Var;

#[derive(Debug)]
pub struct LowerError {
    pub pc: usize,
    pub code: u8,
    pub msg: String,
}

fn reg_to_var(r: u8) -> Var {
    match r {
        0 => Var::R0,
        1 => Var::R1,
        2 => Var::R2,
        3 => Var::R3,
        4 => Var::R4,
        5 => Var::R5,
        6 => Var::R6,
        7 => Var::R7,
        8 => Var::R8,
        9 => Var::R9,
        10 => Var::R10,
        _ => panic!("invalid BPF register {}", r),
    }
}

fn branch_target(pc: usize, off: i16, len: usize, code: u8) -> Result<usize, LowerError> {
    // eBPF branch encoding: target = pc + 1 + off
    let t = pc as isize + 1 + off as isize;
    if t < 0 || (t as usize) >= len {
        return Err(LowerError {
            pc,
            code,
            msg: format!("branch target out of range: {}", t),
        });
    }
    Ok(t as usize)
}

pub fn lower_raw_to_program(raw: &[RawBpfInsn]) -> Result<Program, LowerError> {
    let mut instrs = Vec::with_capacity(raw.len());

    let mut pc: usize = 0;
    while pc < raw.len() {
        let insn = &raw[pc];
        let dst = reg_to_var(insn.dst);
        let src = reg_to_var(insn.src);

        // 0x18: LDIMM64 
        // Special case: takes two instruction slots.
        if insn.code == 0x18 {
            if pc + 1 >= raw.len() {
                return Err(LowerError {
                    pc,
                    code: insn.code,
                    msg: "LDIMM64 at end of stream missing continuation slot".to_string(),
                });
            }

            let cont = &raw[pc + 1];

            // The continuation slot should have code 0x00 in typical encodings.
            // If it's not, fail fast so we don't silently desync.
            if cont.code != 0x00 {
                return Err(LowerError {
                    pc,
                    code: cont.code,
                    msg: format!(
                        "LDIMM64 continuation slot had unexpected opcode 0x{:02x}",
                        cont.code
                    ),
                });
            }

            let low: u32 = insn.imm as u32;
            let high: u32 = cont.imm as u32;
            let imm_u64: u64 = (low as u64) | ((high as u64) << 32);

            // Best-effort: keep it as i64 when it fits; otherwise keep bits (wrap).
            // (For your current string literals, this will be positive and safe.)
            let imm_i64: i64 = imm_u64 as i64;

            // Slot pc: actual load
            instrs.push(Instr::Alu {
                width: Width::W64,
                op: AluOp::Mov,
                dst,
                src: Operand::Imm(imm_i64),
            });

            // Slot pc+1: emit a semantic no-op so AST PCs stay aligned with raw PCs.
            // Self-move is a good no-op in your current semantics.
            instrs.push(Instr::Alu {
                width: Width::W64,
                op: AluOp::Mov,
                dst: Var::R0,
                src: Operand::Reg(Var::R0),
            });

            pc += 2;
            continue;
        }

        let ir: Instr = match insn.code {
            // --- ALU64 ---

            // 0xbf: rX = rY   (ALU64 | MOV | X)
            0xbf => Instr::Alu {
                width: Width::W64,
                op: AluOp::Mov,
                dst,
                src: Operand::Reg(src),
            },

            // 0xb7: rX = imm  (ALU64 | MOV | K)
            0xb7 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Mov,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x07: rX += imm (ALU64 | ADD | K)
            0x07 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Add,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x0f: rX += rY  (ALU64 | ADD | X)
            0x0f => Instr::Alu {
                width: Width::W64,
                op: AluOp::Add,
                dst,
                src: Operand::Reg(src),
            },

            // 0x54: AND32 imm  (wX &= imm32)
            0x54 => Instr::Alu {
                width: Width::W32,
                op: AluOp::And,
                dst,
                src: Operand::Imm((insn.imm as u32) as i64), // u32 mask
            },

            // 0x57: rX &= imm (ALU64 | AND | K)
            0x57 => Instr::Alu {
                width: Width::W64,
                op: AluOp::And,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // --- JMP ---

            // 0x95: exit (JMP | EXIT)
            0x95 => Instr::Exit,

            // 0x55: JNE imm (if dst != imm goto target)
            0x55 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::Ne,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0xbd: if rX <= rY goto +off (JMP | JLE | X)  (unsigned compare)
            0xbd => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::ULe,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0xb4: wX = imm  (ALU32 | MOV | K)  == mov32 imm (zero-extend)
            0xb4 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Mov,
                dst,
                // IMPORTANT: mov32 uses u32 then zero-extends to 64
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0xb5: if rX >= imm goto +off (JMP | JGE | K)
            0xb5 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::UGe,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            }

            // 0x16: JEQ32 imm  if (u32)dst == (u32)imm goto target
            0x16 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst, // dst field is the left operand for jumps
                    op: CmpOp::Eq,
                    right: Operand::Imm((insn.imm as u32) as i64),
                    target,
                }
            }

            // 0x05: JA (unconditional jump): goto pc + 1 + off
            0x05 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::Jmp { target }
            }

            // --- LD/LDX --- (minimal support for your current 0x61 case)

            // 0x61: LDXW dst = *(u32 *)(src + off)
            // In objdump: "w1 = *(u32 *)(r8 + 0x4c)"
            0x61 => Instr::Load {
                size: MemSize::U32,
                dst,
                base: src,
                off: insn.off as i16,
            },

            // 0x6b: STXH *(u16 *)(dst + off) = src
            // In objdump: "*(u16 *)(r10 - 0xc4) = w1"
            0x6b => Instr::Store {
                size: MemSize::U16,
                base: dst,               // for stores, dst is the base register
                off: insn.off,
                src,                     // value comes from src register
            },

            // 0x63: STXW *(u32 *)(dst + off) = src
            0x63 => Instr::Store {
                size: MemSize::U32,
                base: dst,        // dst field is the base register for stores
                off: insn.off,
                src,              // src field is the value register
            },

            // 0x73: STXB *(u8 *)(dst + off) = src
            0x73 => Instr::Store {
                size: MemSize::U8,
                base: dst,           // dst field is the base register for stores
                off: insn.off as i16,
                src,                 // src field is the value register
            },

            // 0x7b: STXDW *(u64 *)(dst + off) = src
            0x7b => Instr::Store {
                size: MemSize::U64,
                base: dst,
                off: insn.off,
                src,
            },

            // 0x85: call imm (JMP | CALL)
            0x85 => Instr::Call {
                helper: insn.imm as u32,
            },

            // Optional: guard against stray continuation opcodes outside 0x18
            0x00 => {
                return Err(LowerError {
                    pc,
                    code: insn.code,
                    msg: "unexpected opcode 0x00 (LDIMM64 continuation without prefix?)".to_string(),
                });
            }

            other => {
                return Err(LowerError {
                    pc,
                    code: other,
                    msg: format!("unsupported opcode 0x{:02x} at pc {}", other, pc),
                });
            }
        };

        instrs.push(ir);
        pc += 1;
    }

    Ok(Program { instrs })
}
