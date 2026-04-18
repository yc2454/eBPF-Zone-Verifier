// src/ast/mod.rs

pub mod instr;
pub mod prog;

pub use self::instr::{CallKind, Instr, Program};
pub use self::prog::{AttachKind, ContextKind, ProgramKind};

use crate::analysis::machine::reg::Reg;

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
#[allow(dead_code)]
pub enum AluOp {
    Add,
    Sub,
    And,
    Or,
    Xor,
    Mov,
    Shl,
    Shr,
    Arsh,
    Mul,
    Mod,
    Div,
    Neg,
    Rsh,
    Lsh,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    UGe,
    ULe,
    UGt,
    ULt,
    Eq,
    Ne,
    SLt,
    SGt,
    SLe,
    SGe,
    Test, // BPF_JSET
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EndianOp {
    ToBe,
    ToLe,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemSize {
    U8,
    U16,
    U32,
    U64,
}

impl MemSize {
    pub fn bytes(&self) -> usize {
        match self {
            MemSize::U8 => 1,
            MemSize::U16 => 2,
            MemSize::U32 => 4,
            MemSize::U64 => 8,
        }
    }

    pub fn unbounded_scalar_bounds(&self) -> (i64, i64) {
        match self {
            MemSize::U8 => (0, u8::MAX as i64),
            MemSize::U16 => (0, u16::MAX as i64),
            MemSize::U32 => (0, u32::MAX as i64),
            MemSize::U64 => (i64::MIN, i64::MAX),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PacketLoadMode {
    Abs,
    Ind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MapLoadKind {
    /// BPF_PSEUDO_MAP_FD: r1 = map_fd
    MapPtr,
    /// BPF_PSEUDO_MAP_VALUE: r2 = map_fd + offset (points into map value)
    MapValue,
    /// BPF_PSEUDO_FUNC (src=4): r4 = callback function pointer (another subprog)
    PseudoFunc { subprog_pc: u32 },
    /// BPF_PSEUDO_BTF_ID (src=3): r3 = per-cpu var / ksym address via BTF id
    PseudoBtfId { btf_id: u32 },
    /// BPF_PSEUDO_MAP_IDX (src=5): map index in the aux table (pre-relocation)
    PseudoMapIdx,
    /// BPF_PSEUDO_MAP_IDX_VALUE (src=6): map value via index (pre-relocation)
    PseudoMapIdxValue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomicOp {
    Add,
    Or,
    And,
    Xor,
    Xchg,
    CmpXchg,
}
