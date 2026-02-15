// src/programs.rs

use crate::ast::{AluOp, CmpOp, Instr, MemSize, Operand, Program, Width};
use crate::analysis::machine::reg::Reg;

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
        NamedProgram { name: "masked_copy_index",          build: masked_copy_index },
    ]
}

pub fn names() -> impl Iterator<Item = &'static str> {
    registry().iter().map(|p| p.name)
}

pub fn get(name: &str) -> Option<Program> {
    registry().iter().find(|p| p.name == name).map(|p| (p.build)())
}

// ---- Tiny “macros” (as helper constructors) ---------------------------------

#[inline]
fn mov_r(dst: Reg, src: Reg) -> Instr {
    Instr::Alu { width: Width::W64, op: AluOp::Mov, dst, src: Operand::Reg(src) }
}

#[inline]
fn mov_i(dst: Reg, imm: i64) -> Instr {
    Instr::Alu { width: Width::W64, op: AluOp::Mov, dst, src: Operand::Imm(imm) }
}

#[inline]
fn add_r(dst: Reg, src: Reg) -> Instr {
    Instr::Alu { width: Width::W64, op: AluOp::Add, dst, src: Operand::Reg(src) }
}

#[inline]
fn add_i(dst: Reg, imm: i64) -> Instr {
    Instr::Alu { width: Width::W64, op: AluOp::Add, dst, src: Operand::Imm(imm) }
}

#[inline]
fn and_i(dst: Reg, imm: i64) -> Instr {
    Instr::Alu { width: Width::W64, op: AluOp::And, dst, src: Operand::Imm(imm) }
}

#[inline]
fn if_uge_i(left: Reg, imm: i64, target: usize) -> Instr {
    Instr::If { left, width: Width::W64, op: CmpOp::UGe, right: Operand::Imm(imm), target }
}

#[inline]
fn if_uge_r(left: Reg, right: Reg, target: usize) -> Instr {
    Instr::If { left, width: Width::W64, op: CmpOp::UGe, right: Operand::Reg(right), target }
}

#[inline]
fn load_u8(dst: Reg, base: Reg, off: i16) -> Instr {
    Instr::Load { size: MemSize::U8, dst, base, off }
}

// -----------------------------------------------------------------------------

// masked_copy_index
//
// r0 = arg0
// r0 &= 31
// r1 = r0
// r2 = r10
// r2 += -32
// r2 += r1
// r0 = *(u8 *)(r2 + 0)
// exit
//
// Safe due to relational fact r1 == r0 and r0 ∈ [0,31].
// Requires propagating equality across copy.
fn masked_copy_index() -> Program {
    Program {
        instrs: vec![
            Instr::MovArg0 { dst: Reg::R0 },
            and_i(Reg::R0, 31),
            mov_r(Reg::R1, Reg::R0),
            mov_r(Reg::R2, Reg::R10),
            add_i(Reg::R2, -32),
            add_r(Reg::R2, Reg::R1),
            load_u8(Reg::R0, Reg::R2, 0),
            Instr::Exit,
        ],
        pc_map: vec![],
    }
}

// canonical_relational_guard
//
// r0 = arg0
// r1 = r0
// if r1 >= 16 goto exit
// r2 = r10
// r2 += -16
// r2 += r0
// r0 = *(u8 *)(r2 + 0)
// exit
//
// Bound is enforced via r1 but used via r0.
// Requires preserving r1 == r0 across the branch.
fn canonical_relational_guard() -> Program {
    let r0 = Reg::R0;
    let r1 = Reg::R1;
    let r2 = Reg::R2;

    Program {
        instrs: vec![
            Instr::MovArg0 { dst: r0 },
            mov_r(r1, r0),
            if_uge_i(r1, 16, 7), // if r1 >= 16 goto pc 7 (Exit)
            mov_r(r2, Reg::R10),
            add_i(r2, -16),
            add_r(r2, r0),
            load_u8(r0, r2, 0),
            Instr::Exit,
        ],
        pc_map: vec![],
    }
}

// unsafe_no_constraints
//
// r0 = arg0
// r2 = r10
// r2 += -16
// r2 += r0
// r0 = *(u8 *)(r2 + 0)
// exit
//
// r0 is unconstrained; stack offset unbounded.
// Genuinely unsafe.
fn unsafe_no_constraints() -> Program {
    let r0 = Reg::R0;
    let r2 = Reg::R2;

    Program {
        instrs: vec![
            Instr::MovArg0 { dst: r0 },
            mov_r(r2, Reg::R10),
            add_i(r2, -16),
            add_r(r2, r0),
            load_u8(r0, r2, 0),
            Instr::Exit,
        ],
        pc_map: vec![],
    }
}

// safe_via_mask_small_offset
//
// r0 = arg0
// r0 &= 7
// r2 = r10
// r2 += -8
// r2 += r0
// r0 = *(u8 *)(r2 + 0)
// exit
//
// Interval-friendly example.
// Kernel verifier typically accepts this.
fn safe_via_mask_small_offset() -> Program {
    let r0 = Reg::R0;
    let r2 = Reg::R2;

    Program {
        instrs: vec![
            Instr::MovArg0 { dst: r0 },
            and_i(r0, 7),
            mov_r(r2, Reg::R10),
            add_i(r2, -8),
            add_r(r2, r0),
            load_u8(r0, r2, 0),
            Instr::Exit,
        ],
        pc_map: vec![],
    }
}

// merge_two_offsets_join
//
// r0 = arg0
// r0 &= 1
// if r0 >= 1 goto L1
//   r2 = r10
//   r2 += -16
//   goto L2
// L1:
//   r2 = r10
//   r2 += -32
// L2:
// r2 += r0
// r0 = *(u8 *)(r2 + 0)
// exit
//
// Each path is safe; join requires reasoning across branches.
fn merge_two_offsets_join() -> Program {
    let z  = Reg::Zero;
    let r0 = Reg::R0;
    let r2 = Reg::R2;

    Program {
        instrs: vec![
            Instr::MovArg0 { dst: r0 },
            and_i(r0, 1),
            if_uge_i(r0, 1, 6), // if r0 >= 1 goto pc 6

            mov_r(r2, Reg::R10),
            add_i(r2, -16),
            // unconditional jump via (0 >= 0) to pc 8
            if_uge_i(z, 0, 8),

            mov_r(r2, Reg::R10),
            add_i(r2, -32),

            add_r(r2, r0),
            load_u8(r0, r2, 0),
            Instr::Exit,
        ],
        pc_map: vec![],
    }
}

// addreg_const_offset_demo
//
// r0 = arg0
// r1 = r0
// r1 &= 7
// r2 = 0
// r2 += 3
// r2 += r1
// exit
//
// No memory access.
// Demonstrates rx = ry + rz transfer semantics.
fn addreg_const_offset_demo() -> Program {
    let z  = Reg::Zero;
    let r0 = Reg::R0;
    let r1 = Reg::R1;
    let r2 = Reg::R2;

    Program {
        instrs: vec![
            Instr::MovArg0 { dst: r0 },
            mov_r(r1, r0),
            and_i(r1, 7),

            // r2 = 0
            mov_r(r2, z),
            // r2 += 3
            add_i(r2, 3),
            // r2 += r1
            add_r(r2, r1),

            Instr::Exit,
        ],
        pc_map: vec![],
    }
}
