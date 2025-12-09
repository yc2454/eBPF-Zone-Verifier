// src/main.rs
mod dbm;
mod domain;
mod ast;
mod exec;

use ast::{Instr, Program};
use dbm::Dbm;
use domain::{Var, VAR_ENV};
use exec::{ExecContext, analyze_program};

fn main() {
    let zero = Var::Zero;
    let r0   = Var::R0;
    let r1   = Var::R1;
    let r2   = Var::R2;
    let r3   = Var::R3;
    let r10  = Var::R10;

    let entry_dbm = Dbm::new(VAR_ENV.len());

    // 0: r0 = arg0
    // 1: w0 &= 15
    // 2: r1 = r0
    // 3: if r1 >= 16 goto 8
    // 4: r2 = r1
    // 5: r3 = r10
    // 6: r3 += -16
    // 7: r3 += r2
    // 8: r0 = *(u8 *)(r3 + 0)
    // 9: exit

    let prog = Program {
        instrs: vec![
            Instr::MovArg0 { dst: r0 },
            Instr::AndImmMask { dst: r0, mask: 15 },
            Instr::MovReg { dst: r1, src: r0 },
            Instr::IfGeImm { reg: r1, imm: 16, target: 8 },
            Instr::MovReg { dst: r2, src: r1 },
            Instr::MovReg { dst: r3, src: r10 },
            Instr::AddImm { dst: r3, imm: -16 },
            Instr::AddReg { dst: r3, src: r2 },
            Instr::LoadStackU8 { base: r3 },
            Instr::Exit,
        ],
    };

    let ctx = ExecContext {
        zero,
        r10,
        stack_min: -512,
        stack_max: -1,
    };

    println!("=== Analyzing program ===");
    analyze_program(&ctx, &prog, entry_dbm);
}
