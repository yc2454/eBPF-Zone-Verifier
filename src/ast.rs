// src/ast.rs
use std::fmt;

use crate::domain::Var;

#[derive(Debug, Clone, Copy)]
pub enum Instr {
    /// rX = arg0   (modeling call result)
    MovArg0     { dst: Var },

    /// rX = rY
    MovReg      { dst: Var, src: Var },

    /// rX += imm
    AddImm      { dst: Var, imm: i64 },

    /// rX += rY
    AddReg      { dst: Var, src: Var },

    /// if rX >= imm goto target_pc
    IfGeImm     { reg: Var, imm: i64, target: usize },

    /// wX &= mask  (we abstract as 0 <= X <= mask)
    AndImmMask  { dst: Var, mask: u32 },

    /// r0 = *(u8 *)(base + 0)
    LoadStackU8 { base: Var },

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

            MovReg { dst, src } =>
                write!(f, "{} = {}", dst.name(), src.name()),

            AddImm { dst, imm } =>
                write!(f, "{} += {}", dst.name(), imm),

            AddReg { dst, src } =>
                write!(f, "{} += {}", dst.name(), src.name()),

            IfGeImm { reg, imm, target } =>
                write!(f, "if {} >= {} goto {}", reg.name(), imm, target),

            AndImmMask { dst, mask } =>
                write!(f, "{} &= {}", dst.name(), mask),

            LoadStackU8 { base } =>
                write!(f, "r0 = *(u8 *)({} + 0)", base.name()),

            Exit =>
                write!(f, "exit"),
        }
    }
}
