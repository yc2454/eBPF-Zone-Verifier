use crate::dbm::{Dbm, DbmEntry};
use crate::domain::{
    Var, VarEnv,
    assign_zero, assign_eq, assign_add_const, assume_less_than,
};
use serde::Serialize;
use std::fs::File;
use std::io::Write;

#[derive(Debug, Clone)]
pub enum Instr {
    AssignZero { x: Var },
    AssignEq { x: Var, y: Var },
    AssignAddConst { x: Var, y: Var, c: i64 },
    AssumeLessThan { x: Var, c: i64 },
}

#[derive(Debug, Serialize)]
pub struct DbmSnapshot {
    pub pc: usize,
    pub entries: Vec<DbmEntry>,
}

#[derive(Debug, Serialize)]
pub struct Trace {
    pub label: String,
    pub snapshots: Vec<DbmSnapshot>,
}

pub fn run_program(env: &VarEnv, instrs: &[Instr], label: &str) {
    let mut dbm = Dbm::new(env.len());
    let zero = env.idx("0").expect("env must contain constant 0");

    println!("=== Program: {label} ===");
    println!("Initial zone:");
    dbm.pretty_print(env);
    println!("---");

    for (pc, instr) in instrs.iter().enumerate() {
        println!("pc {pc}: {instr:?}");

        match *instr {
            Instr::AssignZero { x } => {
                assign_zero(&mut dbm, x, zero);
            }
            Instr::AssignEq { x, y } => {
                assign_eq(&mut dbm, x, y);
            }
            Instr::AssignAddConst { x, y, c } => {
                assign_add_const(&mut dbm, x, y, c);
            }
            Instr::AssumeLessThan { x, c } => {
                assume_less_than(&mut dbm, x, zero, c);
            }
        }

        dbm.pretty_print(env);
        println!("---");

        if dbm.is_inconsistent() {
            println!("Zone became INCONSISTENT at pc = {pc}, stopping.");
            println!();
            return;
        }
    }

    println!("Final zone is consistent.");
    println!();
}

/// Example 1: Interval narrowing on a single variable.
///   r0 = 0;
///   r1 = r0 + 10;      // r1 = 10
///   assume(r1 < 20);   // no change (already 10)
///   assume(r1 < 15);   // still no change
pub fn program_interval_narrowing(env: &VarEnv) -> Vec<Instr> {
    let r0 = env.idx("r0").unwrap();
    let r1 = env.idx("r1").unwrap();

    vec![
        Instr::AssignZero { x: r0 },
        Instr::AssignAddConst { x: r1, y: r0, c: 10 },
        Instr::AssumeLessThan { x: r1, c: 20 },
        Instr::AssumeLessThan { x: r1, c: 15 },
    ]
}

/// Example 2: Relational constraints between two vars.
///   r0 = 0;
///   r1 = r0 + 3;       // r1 = 3
///   r2 = r1 + 7;       // r2 = 10
///   assume(r2 < 12);   // keeps upper bound tight on r2, and propagates to r1/r0 via DBM.
pub fn program_two_var_chain(env: &VarEnv) -> Vec<Instr> {
    let r0 = env.idx("r0").unwrap();
    let r1 = env.idx("r1").unwrap();
    let r2 = env.idx("r2").unwrap();

    vec![
        Instr::AssignZero { x: r0 },
        Instr::AssignAddConst { x: r1, y: r0, c: 3 },
        Instr::AssignAddConst { x: r2, y: r1, c: 7 },
        Instr::AssumeLessThan { x: r2, c: 12 },
    ]
}

/// Example 3: Inconsistent constraints.
///   r0 = 0;
///   assume(r0 < 0);   // impossible
pub fn program_inconsistent(env: &VarEnv) -> Vec<Instr> {
    let r0 = env.idx("r0").unwrap();

    vec![
        Instr::AssignZero { x: r0 },
        Instr::AssumeLessThan { x: r0, c: 0 },
    ]
}

/// Example 4: Alias chain + offset:
///   r0 = 0;
///   r1 = r0;
///   r2 = r1 + 5;
///   r1 = r2;          // creates equalities that force a cycle: r1 = r2 = r0 + 5
///   assume(r2 < 4);   // should make the zone inconsistent, because r2 = 5 and r2 < 4.
pub fn program_alias_and_conflict(env: &VarEnv) -> Vec<Instr> {
    let r0 = env.idx("r0").unwrap();
    let r1 = env.idx("r1").unwrap();
    let r2 = env.idx("r2").unwrap();

    vec![
        Instr::AssignZero { x: r0 },
        Instr::AssignEq { x: r1, y: r0 },
        Instr::AssignAddConst { x: r2, y: r1, c: 5 },
        Instr::AssignEq { x: r1, y: r2 },
        Instr::AssumeLessThan { x: r2, c: 4 },
    ]
}

/// New: run and **record** DBM snapshots at each PC, then dump to JSON.
pub fn run_program_with_trace(env: &VarEnv, instrs: &[Instr], label: &str, out_path: &str) {
    let mut dbm = Dbm::new(env.len());
    let zero = env.idx("0").expect("env must contain constant 0");

    let mut snapshots = Vec::new();

    // Snapshot at "pc = 0" (before any instruction)
    snapshots.push(DbmSnapshot {
        pc: 0,
        entries: dbm.to_compact_entries(),
    });

    for (step_idx, instr) in instrs.iter().enumerate() {
        let pc = step_idx + 1; // pc = 1..=len(instrs) after each instr

        match *instr {
            Instr::AssignZero { x } => {
                assign_zero(&mut dbm, x, zero);
            }
            Instr::AssignEq { x, y } => {
                assign_eq(&mut dbm, x, y);
            }
            Instr::AssignAddConst { x, y, c } => {
                assign_add_const(&mut dbm, x, y, c);
            }
            Instr::AssumeLessThan { x, c } => {
                assume_less_than(&mut dbm, x, zero, c);
            }
        }

        snapshots.push(DbmSnapshot {
            pc,
            entries: dbm.to_compact_entries(),
        });

        if dbm.is_inconsistent() {
            break;
        }
    }

    let trace = Trace {
        label: label.to_string(),
        snapshots,
    };

    // Serialize to JSON and write to file
    let json = serde_json::to_string_pretty(&trace)
        .expect("failed to serialize trace to JSON");

    let mut file = File::create(out_path)
        .expect("failed to create trace file");
    file.write_all(json.as_bytes())
        .expect("failed to write trace JSON");
}

