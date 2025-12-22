// src/bpf_to_ast.rs
use crate::ast::{Instr, Program};
use crate::domain::Var;
use crate::bpf_insn::RawBpfInsn;

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

pub fn lower_raw_to_program(raw: &[RawBpfInsn]) -> Result<Program, LowerError> {
    let mut instrs = Vec::with_capacity(raw.len());

    for (pc, insn) in raw.iter().enumerate() {
        let dst = reg_to_var(insn.dst);
        let src = reg_to_var(insn.src);

        let ir = match insn.code {
            // rX = rY   (ALU64 | MOV | X)   0xbf
            0xbf => Instr::MovReg { dst, src },

            // rX += imm (ALU64 | ADD | K)   0x07
            0x07 => Instr::AddImm { dst, imm: insn.imm as i64 },

            // rX += rY  (ALU64 | ADD | X)   0x0f
            0x0f => Instr::AddReg { dst, src },

            // rX &= imm (ALU64 | AND | K)  0x57
            0x57 => Instr::AndImmMask { dst, mask: insn.imm as u32 },

            // exit      (JMP | EXIT)       0x95
            0x95 => Instr::Exit,

            // not yet supported: loads, stores, more jumps, helpers, etc.
            other => {
                return Err(LowerError {
                    pc,
                    code: other,
                    msg: format!("unsupported opcode 0x{:02x} at pc {}", other, pc),
                })
            }
        };

        instrs.push(ir);
    }

    Ok(Program { instrs })
}
