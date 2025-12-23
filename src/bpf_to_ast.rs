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

    for (pc, insn) in raw.iter().enumerate() {
        let dst = reg_to_var(insn.dst);
        let src = reg_to_var(insn.src);

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

            // 0xbd: if rX <= rY goto +off (JMP | JLE | X)  (unsigned compare)
            0xbd => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    left: dst,
                    op: CmpOp::ULe,
                    right: Operand::Reg(src),
                    target,
                }
            }

            // (Optional, but you’ll want it soon)
            // 0xb5: if rX >= imm goto +off (JMP | JGE | K)
            0xb5 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    left: dst,
                    op: CmpOp::UGe,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
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

            other => {
                return Err(LowerError {
                    pc,
                    code: other,
                    msg: format!("unsupported opcode 0x{:02x} at pc {}", other, pc),
                });
            }
        };

        instrs.push(ir);
    }

    Ok(Program { instrs })
}
