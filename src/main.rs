// src/main.rs
mod dbm;
mod domain;
mod ast;
mod exec;
mod programs;
mod kcheck;

use dbm::Dbm;
use domain::{Var, VAR_ENV};
use exec::{ExecContext, analyze_program};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() <= 1 || args[1] == "list" {
        println!("Usage: cargo run -- <program_name>");
        println!("Available programs:");
        for n in programs::names() {
            println!("  {}", n);
        }
        return;
    }

    let chosen = &args[1];
    let prog = match programs::get(chosen) {
        Some(p) => p,
        None => {
            println!("Unknown program: {}", chosen);
            println!("Available programs:");
            for n in programs::names() {
                println!("  {}", n);
            }
            return;
        }
    };

    let ctx = ExecContext {
        zero: Var::Zero,
        r10: Var::R10,
        stack_min: -512,
        stack_max: -1,
    };

    let entry_dbm = Dbm::new(VAR_ENV.len());

    println!("=== Analyzing program: {} ===", chosen);
    let _states = analyze_program(&ctx, &prog, entry_dbm);
}
