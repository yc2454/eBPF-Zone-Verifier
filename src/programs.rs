// src/programs.rs
use crate::ast::{Instr, Program};
use crate::domain::Var;

pub struct NamedProgram {
    pub name: &'static str,
    pub build: fn() -> Program,
}

pub fn registry() -> &'static [NamedProgram] {
    &[
        NamedProgram { name: "canonical_relational_guard", build: canonical_relational_guard },
        NamedProgram { name: "unsafe_no_constraints",      build: unsafe_no_constraints },
        NamedProgram { name: "safe_via_mask_small_offset", build: safe_via_mask_small_offset },
        NamedProgram { name: "merge_two_offsets_join",     build: merge_two_offsets_join },
        NamedProgram { name: "addreg_const_offset_demo",   build: addreg_const_offset_demo },
    ]
}

pub fn names() -> impl Iterator<Item = &'static str> {
    registry().iter().map(|p| p.name)
}

pub fn get(name: &str) -> Option<Program> {
    registry().iter().find(|p| p.name == name).map(|p| (p.build)())
}

fn canonical_relational_guard() -> Program {
    let r0 = Var::R0;
    let r1 = Var::R1;
    let r2 = Var::R2;
    let r10 = Var::R10;

    Program {
        instrs: vec![
            Instr::MovArg0 { dst: r0 },
            Instr::MovReg  { dst: r1, src: r0 },
            Instr::IfUgeImm { reg: r1, imm: 16, target: 7 },
            Instr::MovReg  { dst: r2, src: r10 },
            Instr::AddImm  { dst: r2, imm: -16 },
            Instr::AddReg  { dst: r2, src: r0 },
            Instr::LoadStackU8 { base: r2 },
            Instr::Exit,
        ],
    }
}

fn unsafe_no_constraints() -> Program {
    let r0 = Var::R0;
    let r2 = Var::R2;
    let r10 = Var::R10;

    Program {
        instrs: vec![
            Instr::MovArg0 { dst: r0 },
            Instr::MovReg  { dst: r2, src: r10 },
            Instr::AddImm  { dst: r2, imm: -16 },
            Instr::AddReg  { dst: r2, src: r0 },
            Instr::LoadStackU8 { base: r2 },
            Instr::Exit,
        ],
    }
}

fn safe_via_mask_small_offset() -> Program {
    let r0 = Var::R0;
    let r2 = Var::R2;
    let r10 = Var::R10;

    Program {
        instrs: vec![
            Instr::MovArg0     { dst: r0 },
            Instr::AndImmMask  { dst: r0, mask: 7 },
            Instr::MovReg      { dst: r2, src: r10 },
            Instr::AddImm      { dst: r2, imm: -8 },
            Instr::AddReg      { dst: r2, src: r0 },
            Instr::LoadStackU8 { base: r2 },
            Instr::Exit,
        ],
    }
}

fn merge_two_offsets_join() -> Program {
    let z = Var::Zero;
    let r0 = Var::R0;
    let r2 = Var::R2;
    let r10 = Var::R10;

    Program {
        instrs: vec![
            Instr::MovArg0    { dst: r0 },
            Instr::AndImmMask { dst: r0, mask: 1 },
            Instr::IfUgeImm    { reg: r0, imm: 1, target: 6 },

            Instr::MovReg     { dst: r2, src: r10 },
            Instr::AddImm     { dst: r2, imm: -16 },
            Instr::IfUgeImm    { reg: z, imm: 0, target: 8 },

            Instr::MovReg     { dst: r2, src: r10 },
            Instr::AddImm     { dst: r2, imm: -32 },

            Instr::AddReg      { dst: r2, src: r0 },
            Instr::LoadStackU8 { base: r2 },
            Instr::Exit,
        ],
    }
}

fn addreg_const_offset_demo() -> Program {
    let z  = Var::Zero;
    let r0 = Var::R0;
    let r1 = Var::R1;
    let r2 = Var::R2;

    Program {
        instrs: vec![
            Instr::MovArg0     { dst: r0 },
            Instr::MovReg      { dst: r1, src: r0 },
            Instr::AndImmMask  { dst: r1, mask: 7 },

            Instr::MovReg      { dst: r2, src: z },
            Instr::AddImm      { dst: r2, imm: 3 },

            Instr::AddReg      { dst: r2, src: r1 },
            Instr::Exit,
        ],
    }
}
