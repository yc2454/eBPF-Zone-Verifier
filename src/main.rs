// src/main.rs

mod ast;
mod dbm;
mod domain;
mod exec;
mod programs;
mod kernel_semantics;
mod check;
mod utils;

use crate::ast::Program;
use crate::dbm::Dbm;
use crate::domain::{Var, VAR_ENV};
use crate::exec::{analyze_program, ExecContext};

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- list");
    eprintln!("  cargo run -- analyze <program_name>");
    eprintln!("  cargo run -- check <program_name>");
}

fn get_program(name: &str) -> Program {
    programs::get(name).unwrap_or_else(|| {
        eprintln!("Unknown program: {}", name);
        eprintln!("Available programs:");
        for n in programs::names() {
            eprintln!("  {}", n);
        }
        std::process::exit(1);
    })
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        usage();
        return;
    }

    if args[1] == "list" {
        for n in programs::names() {
            println!("{}", n);
        }
        return;
    }

    if args.len() < 3 {
        usage();
        return;
    }

    let cmd = &args[1];
    let name = &args[2];
    let prog = get_program(name);

    let ctx = ExecContext {
        zero: Var::Zero,
        r10: Var::R10,
        stack_min: -512,
        stack_max: -1,
    };

    let entry = Dbm::new(VAR_ENV.len());

    if cmd == "analyze" {
        println!("=== Analyzing program: {} ===", name);
        let _cert = analyze_program(&ctx, &prog, entry);
        return;
    }

    if cmd == "check" {
        println!("=== Analyzing program: {} ===", name);
        let cert = analyze_program(&ctx, &prog, entry);

        println!("\n=== Kernel-sim checking: {} ===", name);
        match check::check_certificate_against_kernel_sim(&ctx, &prog, &cert) {
            Ok(()) => println!("CHECK OK"),
            Err(e) => {
                println!("CHECK FAILED: {}", e.format());
                std::process::exit(1);
            }
        }
        return;
    }

    usage();
}
