// src/bpf_to_ast.rs
use crate::ast::{AluOp, CmpOp, EndianOp, Instr, MapLoadKind, 
    MemSize, Operand, PacketLoadMode, Program, Width, AtomicOp};
use crate::parsing::bpf_insn::RawBpfInsn;
use crate::analysis::machine::reg::Reg;
use std::collections::HashSet;

#[derive(Debug)]
pub enum LowerErrorKind {
    UnknownOpcode,
    InvalidLDIMM64,
    BranchTargetOutOfRange,
    CallTargetOutOfBounds,
    InvalidSrcReg,
    UnknownAtomicOp,
    CallUsedReservedFields,
    InvalidRegister
}

#[derive(Debug)]
pub struct LowerError {
    pub pc: usize,
    pub code: u8,
    pub msg: String,
    pub kind: LowerErrorKind
}

fn reg_to_var(insn: &RawBpfInsn, r: u8, pc: usize) -> Result<Reg, LowerError> {
    match r {
        0 => Ok(Reg::R0),
        1 => Ok(Reg::R1),
        2 => Ok(Reg::R2),
        3 => Ok(Reg::R3),
        4 => Ok(Reg::R4),
        5 => Ok(Reg::R5),
        6 => Ok(Reg::R6),
        7 => Ok(Reg::R7),
        8 => Ok(Reg::R8),
        9 => Ok(Reg::R9),
        10 => Ok(Reg::R10),
        _ => Err(LowerError { pc, code: insn.code, msg: "invalid register".to_string(), kind: LowerErrorKind::InvalidRegister })
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
            kind: LowerErrorKind::BranchTargetOutOfRange
        });
    }
    Ok(t as usize)
}

pub fn lower_raw_to_program(raw: &[RawBpfInsn]) -> Result<Program, LowerError> {
    let mut instrs = Vec::with_capacity(raw.len());
    let mut invalid_pc_set = HashSet::new();
    let mut pc: usize = 0;

    while pc < raw.len() {
        let insn = &raw[pc];
        let dst = reg_to_var(insn, insn.dst, pc)?;
        let src = reg_to_var(insn, insn.src, pc)?;

        if insn.code == 0x18 {
            if (src != Reg::R0 && src != Reg::R1) || insn.off != 0 {
                return Err(
                    LowerError { 
                        pc, 
                        code: insn.code, 
                        msg: "invalid BPF_LD_IMM insn: src_reg or off must be 0".to_string(), 
                        kind: LowerErrorKind::InvalidLDIMM64 
                    });
            }
            if pc + 1 >= raw.len() { 
                return Err(LowerError {
                    pc,
                    code: insn.code,
                    msg: "unexpected end of instructions after LDDW".to_string(),
                    kind: LowerErrorKind::InvalidLDIMM64
                });
            }
            let cont = &raw[pc + 1];
            if cont.code != 0x00 { 
                return Err(LowerError {
                    pc,
                    code: cont.code,
                    msg: "expected continuation instruction after LDDW".to_string(),
                    kind: LowerErrorKind::InvalidLDIMM64
                });
            }
            if cont.code != 0 || cont.dst != 0 || cont.src != 0 || cont.off != 0 { 
                return Err(LowerError {
                    pc,
                    code: cont.code,
                    msg: "invalid BPF_LD_IMM insn: next insn fields must be 0".to_string(),
                    kind: LowerErrorKind::InvalidLDIMM64
                });
            }

            let low: u32 = insn.imm as u32;
            let high: u32 = cont.imm as u32;
            let imm_u64: u64 = (low as u64) | ((high as u64) << 32);
            let imm_i64: i64 = imm_u64 as i64;

            // AST 1: The Load
            match src {
                Reg::R0 => {
                    instrs.push(Instr::Alu {
                        width: Width::W64,
                        op: AluOp::Mov,
                        dst,
                        src: Operand::Imm(imm_i64),
                    });
                },
                Reg::R1 => {
                    if cont.imm != 0 {
                        return Err(LowerError {
                            pc,
                            code: insn.code,
                            msg: "invalid BPF_LD_IMM insn: imm must be 0".to_string(),
                            kind: LowerErrorKind::InvalidLDIMM64
                        });
                    }
                    instrs.push(Instr::LoadMap { 
                        dst, 
                        kind: MapLoadKind::MapPtr, 
                        map_fd: imm_i64 as i32, 
                        off: 0 
                    });
                },
                Reg::R2 => {
                    instrs.push(Instr::LoadMap { 
                        dst, 
                        kind: MapLoadKind::MapValue, 
                        map_fd: imm_i64 as i32, 
                        off: 0 
                    });
                },
                _ => return Err(LowerError {
                    pc,
                    code: cont.code,
                    msg: "invalid BPF_LD_IMM insn: invalid source reg".to_string(),
                    kind: LowerErrorKind::InvalidLDIMM64
                })
            }
            
            // AST 2: The No-Op (Maps to 'pc + 1')
            // We record this PC. If we reach here later, it's an error
            invalid_pc_set.insert(pc + 1);

            instrs.push(Instr::Alu {
                width: Width::W64,
                op: AluOp::Mov,
                dst: Reg::R0,
                src: Operand::Reg(Reg::R0),
            });

            pc += 2;
            continue;
        }

        let ir: Instr = match insn.code {
            // --- ALU64 ---

            // 0xbc: MOV32 reg  (w_dst = w_src)
            0xbc => Instr::Alu {
                width: Width::W32,
                op: AluOp::Mov,
                dst,
                src: Operand::Reg(src),
            },

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

            // 0x04: ADD32_K  w_dst += imm
            0x04 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Add,
                dst,
                // imm is signed; keep sign so "w2 += -1" behaves like subtract 1
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x0c: ADD32_X  w_dst += w_src
            0x0c => Instr::Alu {
                width: Width::W32,
                op: AluOp::Add,
                dst,
                src: Operand::Reg(src),
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

            // 0x1f: SUB64_X  (dst -= src)
            0x1f => Instr::Alu {
                width: Width::W64,
                op: AluOp::Sub,
                dst,
                src: Operand::Reg(src),
            },

            // 0x14: SUB32_K  w_dst -= imm
            0x14 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Sub,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x17: SUB64_K  r_dst -= imm
            0x17 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Sub,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x1c: SUB32_X  w_dst -= w_src
            0x1c => Instr::Alu {
                width: Width::W32,
                op: AluOp::Sub,
                dst,
                src: Operand::Reg(src),
            },

            // 0x24: MUL32_K  w_dst *= imm
            0x24 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Mul,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x2c: MUL32_X  w_dst *= w_src
            0x2c => Instr::Alu {
                width: Width::W32,
                op: AluOp::Mul,
                dst,
                src: Operand::Reg(src),
            },

            // 0x27: MUL64_K  r_dst *= imm
            0x27 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Mul,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x2f: MUL64_X  r_dst *= r_src
            0x2f => Instr::Alu {
                width: Width::W64,
                op: AluOp::Mul,
                dst,
                src: Operand::Reg(src),
            },

            // 0x37: DIV64_K  r_dst /= imm
            0x37 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Div,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x3f: DIV64_X  r_dst /= r_src
            0x3f => Instr::Alu {
                width: Width::W64,
                op: AluOp::Div,
                dst,
                src: Operand::Reg(src),
            },

            // 0x34: DIV32_K  w_dst /= imm
            0x34 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Div,
                dst,
                // Zero-extend 32-bit immediate for division
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0x3c: DIV32_X  w_dst /= w_src
            0x3c => Instr::Alu {
                width: Width::W32,
                op: AluOp::Div,
                dst,
                src: Operand::Reg(src),
            },

            // 0x4f: OR64_X r_dst |= r_src
            0x4f => Instr::Alu {
                width: Width::W64,
                op: AluOp::Or,
                dst,
                src: Operand::Reg(src),
            },

            // 0x5c: AND32_X  w_dst &= w_src
            0x5c => Instr::Alu {
                width: Width::W32,
                op: AluOp::And,
                dst,
                src: Operand::Reg(src),
            },

            // 0x5f: AND64_X r_dst &= r_src
            0x5f => Instr::Alu {
                width: Width::W64,
                op: AluOp::And,
                dst,
                src: Operand::Reg(src),
            },

            // 0x6f: LSH64_X r_dst <<= r_src
            0x6f => Instr::Alu {
                width: Width::W64,
                op: AluOp::Shl,
                dst,
                src: Operand::Reg(src),
            },

            // 0x7f: RSH64_X r_dst >>= r_src
            0x7f => Instr::Alu {
                width: Width::W64,
                op: AluOp::Shr,
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

            // 0x44: OR32_K  (w_dst |= imm)
            0x44 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Or,
                dst,
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0x4c: OR32_X  w_dst |= w_src
            0x4c => Instr::Alu {
                width: Width::W32,
                op: AluOp::Or,
                dst,
                src: Operand::Reg(src),
            },

            // 0x47: OR64_K  r_dst |= imm
            0x47 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Or,
                dst,
                // immediate is effectively used as an unsigned bitmask
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0x64: LSH32_K  (w_dst <<= imm)
            0x64 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Shl,
                dst,
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0x6c: LSH32_X  (w_dst <<= w_src)
            0x6c => Instr::Alu {
                width: Width::W32,
                op: AluOp::Shl,
                dst,
                src: Operand::Reg(src),
            },

            // 0x67: LSH64 imm  (rX <<= imm)
            0x67 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Shl,
                dst,
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0x74: RSH32_K  w_dst >>= imm (logical)
            0x74 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Shr,
                dst,
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0x77: RSH64 imm  (logical) (rX >>= imm)
            0x77 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Shr,
                dst,
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0x7c: RSH32_X  w_dst >>= w_src
            0x7c => Instr::Alu {
                width: Width::W32,
                op: AluOp::Shr,
                dst,
                src: Operand::Reg(src),
            },

            // 0x84: NEG32 (w_dst = -w_dst)
            0x84 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Neg,
                dst,
                src: Operand::Imm(0), // Neg is unary; src is ignored/dummy
            },

            // 0x87: NEG64 (dst = -dst)
            0x87 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Neg,
                dst: dst,
                src: Operand::Imm(0), // Unary op, src is ignored
            },

            // 0x94: MOD32_K  w_dst %= imm
            0x94 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Mod,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x9c: MOD32_X  w_dst %= w_src
            0x9c => Instr::Alu {
                width: Width::W32,
                op: AluOp::Mod,
                dst,
                src: Operand::Reg(src),
            },

            0x97 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Mod,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x9f: MOD64_X  r_dst %= r_src
            0x9f => Instr::Alu {
                width: Width::W64,
                op: AluOp::Mod,
                dst,
                src: Operand::Reg(src),
            },

            // 0xa4: XOR32_K  w_dst ^= imm
            0xa4 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Xor,
                dst,
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0xac: XOR32_X  w_dst ^= w_src
            0xac => Instr::Alu {
                width: Width::W32,
                op: AluOp::Xor,
                dst,
                src: Operand::Reg(src),
            },

            // 0xa7: XOR64_K  r_dst ^= imm
            0xa7 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Xor,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0xaf: XOR64_X  r_dst ^= r_src
            0xaf => Instr::Alu {
                width: Width::W64,
                op: AluOp::Xor,
                dst,
                src: Operand::Reg(src),
            },

            // 0xc4: ARSH32_K  w_dst s>>= imm
            0xc4 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Arsh,
                dst,
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0xcc: ARSH32_X  w_dst s>>= w_src
            0xcc => Instr::Alu {
                width: Width::W32,
                op: AluOp::Arsh,
                dst,
                src: Operand::Reg(src),
            },

            // 0xc7: ARSH64_K  r_dst s>>= imm
            0xc7 => Instr::Alu {
                width: Width::W64,
                op: AluOp::Arsh,
                dst,
                src: Operand::Imm((insn.imm as u32) as i64),
            },

            // 0xcf: ARSH64_X  r_dst s>>= r_src
            0xcf => Instr::Alu {
                width: Width::W64,
                op: AluOp::Arsh,
                dst,
                src: Operand::Reg(src),
            },

            // --- ENDIAN ---
            // 0xd4: BPF_END: endian conversion on dst.
            0xd4 => Instr::Endian {
                width: Width::W32,
                dst: dst,
                op: EndianOp::ToLe,
                size: insn.imm as u32,
            },

            // 0xdc: BPF_END: endian conversion on dst.
            0xdc => Instr::Endian { 
                width: Width::W32,
                dst: dst,
                op: EndianOp::ToBe,
                size: insn.imm as u32,
            },

            // 0xd7: END_LE_64 (dst = to_le_64(dst))
            // Supports imm = 16, 32, 64
            // 0xd7 => Instr::Endian {
            //     width: Width::W64,
            //     dst: dst,
            //     op: EndianOp::ToLe,
            //     size: insn.imm as u32,
            // },

            // --- JMP ---
            // 0x95: exit (JMP | EXIT)
            0x95 => Instr::Exit,

            // 0x15: JEQ imm (if dst == imm goto target)
            0x15 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::Eq,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0x1d: JEQ_X (if dst == src goto target, 64-bit)
            0x1d => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::Eq,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x1e: JEQ32_X (if (u32)dst == (u32)src goto target)
            0x1e => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::Eq,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x25: JGT_K (if dst > imm, 64-bit)
            0x25 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::UGt,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0x26: JGT32_K  (if (u32)dst > (u32)imm goto target)
            //
            // MVP semantics: we lower to UGt, but transfer_if does no refinement
            // for UGt, so this only creates the branch structure and keeps DBM
            // unchanged on both paths (sound for unsigned comparison).
            0x26 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::UGt,
                    right: Operand::Imm(insn.imm as u32 as i64),
                    target,
                }
            },

            // 0x2d: JGT_X (if dst > src goto target)
            0x2d => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::UGt,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x2e: JGT_X (if dst > (u32)src goto target)
            0x2e => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::UGt,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x35: JGE_K (if u64(dst) >= u64(imm) goto target)
            0x35 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::UGe,
                    // The immediate is sign-extended from i32 to i64, 
                    // but the comparison treats the bits as unsigned.
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0x36: JGE_K_32 (if (u32)dst >= imm32)
            0x36 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::UGe,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0x3d: JGE_X (if dst >= src goto target, 64-bit)
            0x3d => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::UGe,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x3e: JGE32_X (if (u32)dst >= (u32)src goto target)
            0x3e => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::UGe,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x45: JSET_K (if (u64)dst & imm)
            0x45 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::Test,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0x46: JSET_K_32 (if (u32)dst & imm32)
            0x46 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::Test,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                } 
            },

            // 0x4d: JSET_X_64 (if (u64)dst & (u64)src)
            // Class: BPF_JMP (0x05) | Op: BPF_JSET (0x40) | Src: BPF_X (0x08)
            0x4d => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::Test,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x4e: JSET_X_32 (if (u32)dst & (u32)src)
            0x4e => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::Test, 
                    right: Operand::Reg(src),
                    target,
                }
            },

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

            // 0x56: JNE32 imm  (if (u32)dst != (u32)imm goto target)
            0x56 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::Ne,
                    right: Operand::Imm((insn.imm as u32) as i64),
                    target,
                }
            }

            // 0x5d: JNE_X (if dst != src goto target)
            0x5d => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::Ne,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x5e: JNE32_X  (if (u32)dst != (u32)src goto target)
            0x5e => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::Ne,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x65: JSGT_K (if s64(dst) > s64(imm) goto target)
            0x65 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::SGt,
                    // insn.imm is i32, casting to i64 sign-extends it correctly
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0x66: JSGT32_K  (if (s32)dst > (s32)imm goto target)
            0x66 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::UGt,                    // “no-refinement” bucket
                    right: Operand::Imm(insn.imm as i32 as i64),
                    target,
                }
            },

            // 0x6d: JSGT_X (if s64(dst) > s64(src) goto target)
            0x6d => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::SGt,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x6e: JSGT32_X (if (s32)dst > (s32)src goto target)
            0x6e => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::SGt,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x75: JSGE_K_64 (if (s64)dst >= imm)
            // Class: BPF_JMP (0x05) | Op: BPF_JSGE (0x70) | Src: BPF_K (0x00)
            0x75 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::SGe,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0x76: JSGE_K_32 (if (s32)dst >= imm32)
            0x76 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::SGe,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0x7d: JSGE_X_64 (if (s64)dst >= (s64)src)
            0x7d => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::SGe,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0x7e: JSGE_X_32 (if (s32)dst >= (s32)src)
            0x7e => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::SGe,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0xa5: JLT_K (if dst < imm goto target, unsigned 64-bit)
            0xa5 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::ULt,
                    // BPF immediates are sign-extended to 64-bit before comparison,
                    // even for unsigned checks (e.g. comparing against -1 / UMAX).
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0xa6: JLT32_K  (if (u32)dst < (u32)imm goto target)
            0xa6 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::ULt,
                    right: Operand::Imm((insn.imm as u32) as i64),
                    target,
                }
            },

            // 0xad: JLT_X (if dst < src goto target)
            0xad => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::ULt,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0xae: JLT32_X  (if (u32)dst < (u32)src goto target)
            //
            // MVP semantics: we treat this as an unsigned <.
            // transfer_if already *does not refine* for JMP32 with reg RHS,
            // so this only creates the branch and keeps zones unchanged.
            0xae => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::ULt,
                    right: Operand::Reg(src),
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

            // 0xb5: if rX <= imm goto +off (JMP | JLE | K)  (unsigned compare)
            0xb5 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::ULe,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            }

            // 0xb6: JLE32_K (if (u32)dst <= (u32)imm goto target)
            0xb6 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::ULe,
                    // Treat immediate as unsigned 32-bit
                    right: Operand::Imm((insn.imm as u32) as i64),
                    target,
                }
            },

            // 0xbe: JLE32_X (if (u32)dst <= (u32)src goto target)
            0xbe => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::ULe,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0xc5: JSLT_K_64 (if (s64)dst < imm)
            0xc5 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::SLt,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0xc6: JSLT32_K (if (s32)dst < (s32)imm goto target)
            0xc6 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::SLt,
                    // insn.imm is i32; casting to i64 preserves sign, which is what we want
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0xcd: JSLT_X_64 (if (s64)dst < (s64)src goto target)
            0xcd => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::SLt,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0xce: JSLT32_X (if (s32)dst < (s32)src goto target)
            0xce => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::SLt,
                    right: Operand::Reg(src),
                    target,
                }
            },

            // 0xd5: JSLE_K_64 (if (s64)dst <= imm)
            0xd5 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::SLe,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0xd6: JSLE32_K (if (s32)dst <= (s32)imm goto target)
            0xd6 => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::SLe,
                    right: Operand::Imm(insn.imm as i64),
                    target,
                }
            },

            // 0xde: JSLE32_X (if (s32)dst <= (s32)src goto target)
            0xde => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W32,
                    left: dst,
                    op: CmpOp::SLe,
                    right: Operand::Reg(src),
                    target,
                }
            },

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

            // 0x69: LDXH dst = *(u16 *)(src + off)
            0x69 => Instr::Load {
                size: MemSize::U16,
                dst,
                base: src,
                off: insn.off as i16,
            },

            // 0x71: LDXB dst = *(u8 *)(src + off)
            0x71 => Instr::Load {
                size: MemSize::U8,
                dst,
                base: src,
                off: insn.off as i16,
            },

            // 0x79: LDXDW dst = *(u64 *)(src + off)
            0x79 => Instr::Load {
                size: MemSize::U64,
                dst,
                base: src,
                off: insn.off as i16,
            },

            // 0x62: BPF_ST | BPF_MEM | BPF_W ( *(u32 *)(dst + off) = imm )
            0x62 => Instr::Store {
                size: MemSize::U32,
                base: dst,
                off: insn.off as i16,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x63: STXW *(u32 *)(dst + off) = src
            0x63 => Instr::Store {
                size: MemSize::U32,
                base: dst,        // dst field is the base register for stores
                off: insn.off,
                src: Operand::Reg(src),              // src field is the value register
            },

            // 0x6a: BPF_ST | BPF_MEM | BPF_H ( *(u16 *)(dst + off) = imm )
            0x6a => Instr::Store {
                size: MemSize::U16,
                base: dst,
                off: insn.off as i16,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x6b: STXH *(u16 *)(dst + off) = src
            0x6b => Instr::Store {
                size: MemSize::U16,
                base: dst,               // for stores, dst is the base register
                off: insn.off,
                src: Operand::Reg(src),                     // value comes from src register
            },

            // 0x72: BPF_ST | BPF_MEM | BPF_B ( *(u8 *)(dst + off) = imm )
            0x72 => Instr::Store {
                size: MemSize::U8,
                base: dst,
                off: insn.off as i16,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x73: STXB *(u8 *)(dst + off) = src
            0x73 => Instr::Store {
                size: MemSize::U8,
                base: dst,           // dst field is the base register for stores
                off: insn.off as i16,
                src: Operand::Reg(src),                 // src field is the value register
            },

            // 0x7a: ST_MEM_DW ( *(u64 *)(dst + off) = imm32 )
            0x7a => Instr::Store {
                size: MemSize::U64,
                base: dst,                         // Base address register (e.g., r10)
                off: insn.off as i16,                          // Offset (e.g., -8)
                src: Operand::Imm(insn.imm as i64) // The value to write (sign-extended to 64-bit)
            },

            // 0x7b: STXDW *(u64 *)(dst + off) = src
            0x7b => Instr::Store {
                size: MemSize::U64,
                base: dst,
                off: insn.off,
                src: Operand::Reg(src),
            },

            // 0x85: call imm (JMP | CALL)
            0x85 => {
                if insn.off != 0 || insn.dst != 0 {
                    return Err(LowerError {
                        pc,
                        code: insn.code,
                        // "BPF_CALL uses reserved fields" is the exact kernel error
                        msg: "BPF_CALL uses reserved fields".to_string(), 
                        kind: LowerErrorKind::CallUsedReservedFields
                    });
                }
                if src == Reg::R0 {
                    // Standard Helper Call
                    Instr::Call {
                        helper: insn.imm as u32,
                    }
                } else if src == Reg::R1 {
                    // BPF_PSEUDO_CALL (BPF-to-BPF Call)
                    // imm is a 32-bit PC-relative offset
                    let next_pc = pc as i64 + 1;
                    let offset = insn.imm as i64;
                    let target = next_pc + offset;

                    // Verify bounds
                    if target < 0 || target >= raw.len() as i64 {
                        return Err(LowerError { 
                            pc, 
                            code: 0x85, 
                            msg: "Call target out of bounds".to_string() ,
                            kind: LowerErrorKind::CallTargetOutOfBounds
                        })
                    }

                    Instr::CallRel { target: target as usize }
                } else {
                    return Err(LowerError { 
                        pc, 
                        code: 0x85, 
                        msg: "Invalid src register for call".to_string(),
                        kind: LowerErrorKind::InvalidSrcReg
                    })
                }
            }

            // 0xDB (64-bit) and 0xC3 (32-bit)
            0xDB | 0xC3 => {
                let size = if insn.code == 0xDB { MemSize::U64 } else { MemSize::U32 };
                
                // 1. Check for Complex Ops (XCHG, CMPXCHG)
                // These specific values are hardcoded in the kernel spec.
                let (op, fetch) = match insn.imm {
                    // BPF_ADD (0x00) with/without Fetch (0x01)
                    0x00 => (AtomicOp::Add, false),
                    0x01 => (AtomicOp::Add, true),
                    
                    // BPF_OR (0x40)
                    0x40 => (AtomicOp::Or, false),
                    0x41 => (AtomicOp::Or, true),

                    // BPF_AND (0x50)
                    0x50 => (AtomicOp::And, false),
                    0x51 => (AtomicOp::And, true),

                    // BPF_XOR (0xA0)
                    0xA0 => (AtomicOp::Xor, false),
                    0xA1 => (AtomicOp::Xor, true),

                    // BPF_XCHG (0xE1) - Always implies Fetch
                    0xE1 => (AtomicOp::Xchg, true),

                    // BPF_CMPXCHG (0xF1) - Always implies Fetch
                    0xF1 => (AtomicOp::CmpXchg, true),

                    _ => return Err(
                        LowerError { 
                            pc, 
                            code: insn.code, 
                            msg: format!("unknown atomic opcode imm: 0x{:x}", insn.imm), 
                            kind: LowerErrorKind::UnknownAtomicOp
                        }
                    ),
                };

                Instr::Atomic {
                    op,
                    size,
                    fetch,
                    base: dst,     // In BPF STX, 'dst' is the memory pointer
                    off: insn.off,
                    src,           // In BPF STX, 'src' is the value
                }
            }

            // --- LEGACY PACKET LOADS (LD_ABS) ---
            0x20 => Instr::LoadPacket { 
                size: MemSize::U32, mode: PacketLoadMode::Abs, offset_imm: insn.imm, src: None },
            0x28 => Instr::LoadPacket { 
                size: MemSize::U16, mode: PacketLoadMode::Abs, offset_imm: insn.imm, src: None },
            0x30 => Instr::LoadPacket { 
                size: MemSize::U8,  mode: PacketLoadMode::Abs, offset_imm: insn.imm, src: None },

            // --- LEGACY PACKET LOADS (LD_IND) ---
            0x40 => Instr::LoadPacket { 
                size: MemSize::U32, mode: PacketLoadMode::Ind, offset_imm: insn.imm, src: Some(src) },
            0x48 => Instr::LoadPacket { 
                size: MemSize::U16, mode: PacketLoadMode::Ind, offset_imm: insn.imm, src: Some(src) },
            0x50 => Instr::LoadPacket { 
                size: MemSize::U8,  mode: PacketLoadMode::Ind, offset_imm: insn.imm, src: Some(src) },

            // Guard against stray continuation opcodes outside 0x18
            0x00 => {
                return Err(LowerError {
                    pc,
                    code: insn.code,
                    msg: "unexpected opcode 0x00 (LDIMM64 continuation without prefix?)".to_string(),
                    kind: LowerErrorKind::InvalidLDIMM64
                });
            }

            other => {
                return Err(LowerError {
                    pc,
                    code: other,
                    msg: format!("unsupported opcode 0x{:02x} at pc {}", other, pc),
                    kind: LowerErrorKind::UnknownOpcode
                });
            }
        };

        instrs.push(ir);
        pc += 1;
    }

    Ok(Program { instrs, invalid_pc_set })
}
