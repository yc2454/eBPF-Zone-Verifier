// src/ast/instr.rs

use super::{
    AluOp, AtomicOp, CmpOp, EndianOp, MapLoadKind, MemSize, Operand, PacketLoadMode, Width,
};
use crate::analysis::machine::reg::Reg;
use std::collections::HashSet;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instr {
    #[allow(dead_code)]
    MovArg0 {
        dst: Reg,
    },
    Alu {
        width: Width,
        op: AluOp,
        dst: Reg,
        src: Operand,
    },
    Endian {
        dst: Reg,
        width: Width,
        op: EndianOp,
        size: u32,
    },
    If {
        width: Width,
        left: Reg,
        op: CmpOp,
        right: Operand,
        target: usize,
    },
    Jmp {
        target: usize,
    },
    Load {
        size: MemSize,
        dst: Reg,
        base: Reg,
        off: i16,
    },
    Store {
        size: MemSize,
        base: Reg,
        off: i16,
        src: Operand,
    },
    Atomic {
        op: AtomicOp,
        size: MemSize,
        fetch: bool,
        base: Reg,
        off: i16,
        src: Reg,
    },
    Call {
        helper: u32,
    },
    CallRel {
        target: usize,
    },
    LoadPacket {
        size: MemSize,
        mode: PacketLoadMode,
        offset_imm: i32,
        src: Option<Reg>,
    },
    LoadMap {
        dst: Reg,
        kind: MapLoadKind,
        map_fd: i32,
        off: i32,
    },
    Exit,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub instrs: Vec<Instr>,
    pub invalid_pc_set: HashSet<usize>,
}

impl fmt::Display for Instr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Instr::*;
        match *self {
            MovArg0 { dst } => write!(f, "{} = arg0", dst.name()),
            Alu {
                width,
                op,
                dst,
                src,
            } => {
                let op_str = match op {
                    AluOp::Add => "+",
                    AluOp::Sub => "-",
                    AluOp::And => "&",
                    AluOp::Or => "|",
                    AluOp::Xor => "^",
                    AluOp::Mov => "=",
                    AluOp::Shl => "<<",
                    AluOp::Shr => ">>",
                    AluOp::Arsh => "s>>",
                    AluOp::Mul => "*",
                    AluOp::Mod => "%",
                    AluOp::Div => "/",
                    AluOp::Neg => "-",
                    AluOp::Rsh => ">>",
                    AluOp::Lsh => "<<",
                };
                let src_str = match src {
                    Operand::Reg(r) => r.name().to_string(),
                    Operand::Imm(i) => format!("0x{:016x}", i),
                };
                let base = dst.name();
                let idx = &base[1..];
                let lhs = match width {
                    Width::W32 => format!("w{}", idx),
                    Width::W64 => format!("r{}", idx),
                };
                if let AluOp::Mov = op {
                    return write!(f, "{} = {}", lhs, src_str);
                }
                write!(f, "{} = {} {} {}", lhs, dst.name(), op_str, src_str)
            }
            Endian {
                dst,
                width: _,
                op,
                size,
            } => {
                let kind_str = match (op, size) {
                    (EndianOp::ToBe, 16) => "be16",
                    (EndianOp::ToBe, 32) => "be32",
                    (EndianOp::ToBe, 64) => "be64",
                    (EndianOp::ToLe, 16) => "le16",
                    (EndianOp::ToLe, 32) => "le32",
                    (EndianOp::ToLe, 64) => "le64",
                    _ => "unknown",
                };
                write!(f, "{} = endian_{}", dst.name(), kind_str)
            }
            If {
                width,
                left,
                op,
                right,
                target,
            } => {
                let op_str = match op {
                    CmpOp::UGe => ">=u",
                    CmpOp::ULe => "<=u",
                    CmpOp::UGt => ">u",
                    CmpOp::ULt => "<u",
                    CmpOp::Eq => "==",
                    CmpOp::Ne => "!=",
                    CmpOp::SLt => "<",
                    CmpOp::SGt => ">",
                    CmpOp::SLe => "<=",
                    CmpOp::SGe => ">=",
                    CmpOp::Test => "&",
                };
                let right_str = match right {
                    Operand::Reg(r) => r.name().to_string(),
                    Operand::Imm(i) => format!("0x{:016x}", i),
                };
                let width_str = match width {
                    Width::W32 => "32",
                    Width::W64 => "64",
                };
                write!(
                    f,
                    "if {} {}{} {} goto {}",
                    left.name(),
                    op_str,
                    width_str,
                    right_str,
                    target
                )
            }
            Jmp { target } => write!(f, "goto {}", target),
            Load {
                size,
                dst,
                base,
                off,
            } => {
                let size_str = match size {
                    MemSize::U8 => "u8",
                    MemSize::U16 => "u16",
                    MemSize::U32 => "u32",
                    MemSize::U64 => "u64",
                };
                write!(
                    f,
                    "{} = *({} *)({} + {})",
                    dst.name(),
                    size_str,
                    base.name(),
                    off
                )
            }
            Store {
                size,
                base,
                off,
                src,
            } => {
                let size_str = match size {
                    MemSize::U8 => "u8",
                    MemSize::U16 => "u16",
                    MemSize::U32 => "u32",
                    MemSize::U64 => "u64",
                };
                let src_str = match src {
                    Operand::Reg(r) => r.name().to_string(),
                    Operand::Imm(i) => format!("0x{:016x}", i),
                };
                write!(
                    f,
                    "*({} *)({} + {}) = {}",
                    size_str,
                    base.name(),
                    off,
                    src_str
                )
            }
            Atomic {
                op,
                size,
                base,
                off,
                src,
                fetch: _,
            } => {
                let size_str = match size {
                    MemSize::U8 => "u8",
                    MemSize::U16 => "u16",
                    MemSize::U32 => "u32",
                    MemSize::U64 => "u64",
                };
                let op_str = match op {
                    AtomicOp::Add => "+",
                    AtomicOp::Or => "||",
                    AtomicOp::And => "&&",
                    AtomicOp::CmpXchg => "cmpxchg",
                    AtomicOp::Xor => "^",
                    AtomicOp::Xchg => "xchg",
                };
                write!(
                    f,
                    "lock *({} *)({} {} {}) += {}",
                    size_str,
                    base.name(),
                    op_str,
                    off,
                    src.name()
                )
            }
            Call { helper } => write!(f, "call {}", helper),
            CallRel { target } => write!(f, "call {}", target),
            LoadPacket { .. } => write!(f, "ld_abs or ld_ind"),
            LoadMap { map_fd, .. } => write!(f, "load map {}", map_fd),
            Exit => write!(f, "exit"),
        }
    }
}
