// src/ast.rs
use std::fmt;

use crate::domain::Var;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operand {
    Reg(Var),
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
    // later: Mul, Div, Mod, Arsh, Neg, etc.
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
    MovArg0 { dst: Var },

    /// dst = ALU(dst, src/imm)   (includes MOV as AluOp::Mov)
    /// Width matters for BPF (wX vs rX). For now you can keep it and ignore in zones.
    Alu {
        width: Width,
        op: AluOp,
        dst: Var,
        src: Operand,
    },

    /// Endian conversion on a register (BPF_END)
    Endian {
        dst: Var,
        kind: EndianKind,
    },

    /// if left (op) right goto target; else fallthrough
    If {
        width: Width,
        left: Var,
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
        dst: Var,
        base: Var,
        off: i16,
    },

    /// *(size *)(base + off) = src
    Store {
        size: MemSize,
        base: Var,
        off: i16,
        src: Var,
    },

    Call {
        helper: u32,
    },

    Exit,
}


#[derive(Debug)]
pub struct Program {
    pub instrs: Vec<Instr>,
}

impl fmt::Display for Instr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Instr::*;
        match *self {
            MovArg0 { dst } =>
                write!(f, "{} = arg0", dst.name()),

            Alu { width, op, dst, src } => {
                let op_str = match op {
                    AluOp::Add => "+",
                    AluOp::Sub => "-",
                    AluOp::And => "&",
                    AluOp::Or  => "|",
                    AluOp::Xor => "^",
                    AluOp::Mov => "=",
                    AluOp::Shl => "<<",
                    AluOp::Shr => ">>",
                };
                let src_str = match src {
                    Operand::Reg(r) => r.name().to_string(),
                    Operand::Imm(i) => format!("{}", i),
                };
                let width_str = match width {
                    Width::W32 => "w",
                    Width::W64 => "r",
                };
                write!(f, "{}{} {} {} {}", width_str, dst.name(), op_str, dst.name(), src_str)
            },

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
