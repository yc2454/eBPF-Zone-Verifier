// src/bpf_to_ast.rs
use crate::ast::{AluOp, CmpOp, Instr, Operand, Program, Width, MemSize, EndianKind};
use crate::parsing::bpf_insn::RawBpfInsn;
use crate::zone::domain::Reg;

#[derive(Debug)]
pub struct LowerError {
    pub pc: usize,
    pub code: u8,
    pub msg: String,
}

fn reg_to_var(r: u8) -> Reg {
    match r {
        0 => Reg::R0,
        1 => Reg::R1,
        2 => Reg::R2,
        3 => Reg::R3,
        4 => Reg::R4,
        5 => Reg::R5,
        6 => Reg::R6,
        7 => Reg::R7,
        8 => Reg::R8,
        9 => Reg::R9,
        10 => Reg::R10,
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
    let mut pc_map = Vec::new();
    let mut pc: usize = 0;

    while pc < raw.len() {
        // 1. Push Raw PC for the PRIMARY instruction
        pc_map.push(pc);

        let insn = &raw[pc];
        let dst = reg_to_var(insn.dst);
        let src = reg_to_var(insn.src);

        if insn.code == 0x18 {
            if pc + 1 >= raw.len() { 
                return Err(LowerError {
                    pc,
                    code: insn.code,
                    msg: "unexpected end of instructions after LDDW".to_string(),
                });
            }
            let cont = &raw[pc + 1];
            if cont.code != 0x00 { 
                return Err(LowerError {
                    pc,
                    code: cont.code,
                    msg: "expected continuation instruction after LDDW".to_string(),
                });
            }

            let low: u32 = insn.imm as u32;
            let high: u32 = cont.imm as u32;
            let imm_u64: u64 = (low as u64) | ((high as u64) << 32);
            let imm_i64: i64 = imm_u64 as i64;

            // AST 1: The Load (Maps to 'pc')
            instrs.push(Instr::Alu {
                width: Width::W64,
                op: AluOp::Mov,
                dst,
                src: Operand::Imm(imm_i64),
            });

            // AST 2: The No-Op (Maps to 'pc + 1')
            // CRITICAL FIX: We must record the PC for this second instruction!
            pc_map.push(pc + 1); 

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

            // 0x14: SUB32_K  w_dst -= imm   (you may already have this)
            0x14 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Sub,
                dst,
                src: Operand::Imm(insn.imm as i64),
            },

            // 0x1c: SUB32_X  w_dst -= w_src   ← new
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

            // 0x84: NEG32 (w_dst = -w_dst)
            0x84 => Instr::Alu {
                width: Width::W32,
                op: AluOp::Neg,
                dst,
                src: Operand::Imm(0), // Neg is unary; src is ignored/dummy
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
            // 0xdc: BPF_END: endian conversion on dst.
            // src (insn.src) encodes LE vs BE; imm encodes width (16/32/64).
            // In your objdump you see: "r4 = be16 r4"  (imm == 16, BE).
            0xdc => {
                let bits = insn.imm as u32;
                let kind = match bits {
                    16 => EndianKind::Be16,
                    32 => EndianKind::Be32,
                    64 => EndianKind::Be64,
                    _ => {
                        return Err(LowerError {
                            pc,
                            code: insn.code,
                            msg: format!("unsupported endian width imm={} for opcode 0xdc", bits),
                        });
                    }
                };

                // MVP: ignore LE vs BE; we only handle BE semantics,
                // and we approximate via range constraints in semantics.
                Instr::Endian { dst, kind }
            }

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

            // 0x2e: JLT_X (if dst < src goto target)
            0x2e => {
                let target = branch_target(pc, insn.off, raw.len(), insn.code)?;
                Instr::If {
                    width: Width::W64,
                    left: dst,
                    op: CmpOp::ULt,
                    right: Operand::Reg(src),
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
                    op: CmpOp::UGt, // MVP: Map to unsigned bucket (no refinement)
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

            // 0x6b: STXH *(u16 *)(dst + off) = src
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

            // 0xdb: ATOMIC_ADD_64 (lock *(u64 *)(dst + off) += src)
            0xdb => Instr::AtomicAdd {
                size: MemSize::U64,
                base: dst,
                off: insn.off,
                src, 
            },

            // 0xc3: ATOMIC_ADD_32 (lock *(u32 *)(dst + off) += src)
            0xc3 => Instr::AtomicAdd {
                size: MemSize::U32,
                base: dst,
                off: insn.off,
                src,
            },

            // Guard against stray continuation opcodes outside 0x18
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

    Ok(Program { instrs, name: "".to_string(), pc_map, section_idx: 0 })
}
