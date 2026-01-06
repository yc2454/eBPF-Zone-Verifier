// src/ast.rs
use std::fmt;

use crate::domain::Reg;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operand {
    Reg(Reg),
    Imm(i64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Width {
    W32,
    W64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AluOp {
    Add,
    Sub,
    And,
    Or,
    Xor,
    Mov,
    Shl,
    Shr,
    Arsh,   // arithmetic right shift
    Mul,
    Mod,
    // later: Div, Neg, etc.
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    UGe, ULe, UGt, ULt,
    Eq, Ne,
    // later: SGe, SLe, SGt, SLt
}

#[derive(Debug, Clone, Copy)]
pub enum EndianKind {
    Be16,
    Be32,
    Be64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemSize {
    U8,
    U16,
    U32,
    U64,
}

#[derive(Debug, Clone, Copy)]
pub enum Instr {
    /// rX = arg0 (your synthetic entry source)
    MovArg0 { dst: Reg },

    /// dst = ALU(dst, src/imm)   (includes MOV as AluOp::Mov)
    /// Width matters for BPF (wX vs rX). For now you can keep it and ignore in zones.
    Alu {
        width: Width,
        op: AluOp,
        dst: Reg,
        src: Operand,
    },

    /// Endian conversion on a register (BPF_END)
    Endian {
        dst: Reg,
        kind: EndianKind,
    },

    /// if left (op) right goto target; else fallthrough
    If {
        width: Width,
        left: Reg,
        op: CmpOp,
        right: Operand,
        target: usize,
    },

    /// Unconditional jump to an absolute PC target.
    Jmp {
        target: usize,
    },

    /// dst = *(size *)(base + off)
    /// For now: treat as "unknown scalar into dst" unless base==r10 and you want stack checks.
    Load {
        size: MemSize,
        dst: Reg,
        base: Reg,
        off: i16,
    },

    /// *(size *)(base + off) = src
    Store {
        size: MemSize,
        base: Reg,
        off: i16,
        src: Reg,
    },

    Call {
        helper: u32,
    },

    Exit,
}

#[derive(Clone, Copy, Debug)]
pub enum ProgramKind {
    Tc,
    Xdp,
    // later: CgroupSkb, CgroupSock, Lsm, Kprobe, …
}

#[derive(Debug)]
pub struct Program {
    pub instrs: Vec<Instr>,
    pub pc_map: Vec<usize>,
}

impl fmt::Display for Instr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Instr::*;
        match *self {
            MovArg0 { dst } =>
                write!(f, "{} = arg0", dst.name()),

            Alu { width, op, dst, src } => {
                let op_str = match op {
                    AluOp::Add  => "+",
                    AluOp::Sub  => "-",
                    AluOp::And  => "&",
                    AluOp::Or   => "|",
                    AluOp::Xor  => "^",
                    AluOp::Mov  => "=",
                    AluOp::Shl  => "<<",
                    AluOp::Shr  => ">>",
                    AluOp::Arsh => "s>>",
                    AluOp::Mul  => "*",
                    AluOp::Mod  => "%",
                };

                let src_str = match src {
                    Operand::Reg(r) => r.name().to_string(),
                    Operand::Imm(i) => format!("{}", i),
                };

                // dst.name() is "r0", "r1", ...
                let base = dst.name();         // e.g. "r1"
                let idx  = &base[1..];         // e.g. "1"

                // LHS uses width: "w1" or "r1"
                let lhs = match width {
                    Width::W32 => format!("w{}", idx),
                    Width::W64 => format!("r{}", idx),
                };

                // MOV is special: just `w1 = r6` or `r3 = 5`
                if let AluOp::Mov = op {
                    return write!(f, "{} = {}", lhs, src_str);
                }

                // everything else: `w1 = r1 + 3`
                write!(f, "{} = {} {} {}", lhs, dst.name(), op_str, src_str)
            }

            Endian { dst, kind } => {
                let kind_str = match kind {
                    EndianKind::Be16 => "be16",
                    EndianKind::Be32 => "be32",
                    EndianKind::Be64 => "be64",
                };
                write!(f, "{} = endian_{}", dst.name(), kind_str)
            },

            If { width, left, op, right, target } => {
                let op_str = match op {
                    CmpOp::UGe => ">=u",
                    CmpOp::ULe => "<=u",
                    CmpOp::UGt => ">u",
                    CmpOp::ULt => "<u",
                    CmpOp::Eq  => "==",
                    CmpOp::Ne  => "!=",
                };
                let right_str = match right {
                    Operand::Reg(r) => r.name().to_string(),
                    Operand::Imm(i) => format!("{}", i),
                };
                let width_str = match width {
                    Width::W32 => "w",
                    Width::W64 => "r",
                };
                write!(f, "if {} {} {} {} goto {}", left.name(), op_str, right_str, width_str, target)
            },

            Jmp { target } =>
                write!(f, "goto {}", target),

            Load { size, dst, base, off } => {
                let size_str = match size {
                    MemSize::U8  => "u8",
                    MemSize::U16 => "u16",
                    MemSize::U32 => "u32",
                    MemSize::U64 => "u64",
                };
                write!(f, "{} = *({} *)({} + {})", dst.name(), size_str, base.name(), off)
            },

            Store { size, base, off, src } => {
                let size_str = match size {
                    MemSize::U8  => "u8",
                    MemSize::U16 => "u16",
                    MemSize::U32 => "u32",
                    MemSize::U64 => "u64",
                };
                write!(f, "*({} *)({} + {}) = {}", size_str, base.name(), off, src.name())
            },

            Call { helper } =>
                write!(f, "call {}", helper),

            Exit =>
                write!(f, "exit"),
        }
    }
}
