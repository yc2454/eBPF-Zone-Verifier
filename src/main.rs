// src/main.rs

mod ast;
mod dbm;
mod domain;
mod exec;
mod programs;
mod kernel_semantics;
mod check;
mod utils;
mod bpf_insn;
mod bpf_to_ast;
mod elf_loader;
mod stats;
mod ctx_model;
mod btf;
mod analysis;
mod loop_check;

use crate::analysis::context;
use crate::ast::Program;
use crate::dbm::Dbm;
use crate::domain::{Reg, REG_ENV, assign_zero};
use crate::exec::{analyze_program, ExecContext};
use crate::utils::load_program_from_elf;
use std::collections::HashMap;
use crate::elf_loader::{load_maps, load_relocations};

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- list");
    eprintln!("  cargo run -- analyze <program_name>");
    eprintln!("  cargo run -- check <program_name>");
    eprintln!("  cargo run -- elf-analyze <elf_path> <section_name>");
    eprintln!("  cargo run -- elf-check  <elf_path> <section_name>");
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

/// Common execution context for all runs.
fn default_exec_ctx() -> ExecContext {
    ExecContext {
        zero: Reg::Zero,
        r10: Reg::R10,
        stack_min: -512,
        stack_max: -1,
        map_defs: Vec::new(),
        pc_to_map_idx: HashMap::new(),
    }
}

fn make_entry_state(ctx: &ExecContext) -> Dbm {
    let mut dbm = Dbm::new(REG_ENV.len());

    // zero variable is always 0
    // (DBM constructor usually sets all diagonals to 0, so this is already ok)

    // r10 starts as “offset 0 from fp”
    assign_zero(&mut dbm, ctx.r10, ctx.zero);

    dbm
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        usage();
        return;
    }

    let cmd = &args[1];

    // Existing commands on hand-written AST programs
    if cmd == "list" {
        for n in programs::names() {
            println!("{}", n);
        }
        return;
    }

    // Commands that need a second argument (program name or path)
    if args.len() < 3 {
        usage();
        return;
    }

    let ctx = default_exec_ctx();
    let mut cctx = context::default_exec_ctx();
    let stats = &mut stats::AnalysisStats::default();
    let entry = make_entry_state(&ctx);

    match cmd.as_str() {
        // old flow: programs.rs
        "analyze" => {
            let name = &args[2];
            let prog = get_program(name);
            println!("=== Analyzing program: {} ===", name);
            let _cert = analyze_program(&ctx, &prog, entry, stats);
        }

        "check" => {
            let name = &args[2];
            let prog = get_program(name);

            println!("=== Analyzing program: {} ===", name);
            let cert = analyze_program(&ctx, &prog, entry, stats);

            println!("\n=== Kernel-sim checking: {} ===", name);
            match check::check_certificate_against_kernel_sim(&ctx, &prog, &cert) {
                Ok(()) => println!("CHECK OK"),
                Err(e) => {
                    println!("CHECK FAILED: {}", e.format());
                    std::process::exit(1);
                }
            }
        }

        "elf-analyze" => {
            if args.len() < 4 {
                usage();
                return;
            }
            let path = &args[2];
            let section = &args[3];

            println!("=== ELF analyze: file='{}', section='{}' ===", path, section);
            // 1. Load Maps
            let map_defs = 
                load_maps(path).unwrap_or_default();
            for (i, m) in map_defs.iter().enumerate() {
                println!("Map {}: '{}' (ValSize: {}, TypeID: {:?})", 
                        i, m.name, m.value_size, m.btf_val_type_id);
            }
            // 2. Load Relocations
            let pc_to_map_idx = 
                load_relocations(path, &map_defs, section).unwrap_or_default();
            let btf_bytes = elf_loader::load_section_bytes(path, ".BTF", false).unwrap_or_default();
    
            let btf_ctx = if !btf_bytes.is_empty() {
                crate::btf::parse_btf(&btf_bytes).unwrap_or_else(|e| {
                    println!("BTF Parse Error: {}", e);
                    crate::btf::BtfContext::new()
                })
            } else {
                println!("No .BTF section found.");
                crate::btf::BtfContext::new()
            };

            cctx.map_defs = map_defs;
            cctx.pc_to_map_idx = pc_to_map_idx;
            cctx.btf = btf_ctx;

            let prog = load_program_from_elf(path, section);
            println!("Program size: {} instructions", prog.instrs.len());

            // // 4. CHECK FOR LOOPS (The Kernel Verifier Step)
            // if let Err(e) = crate::loop_check::check_for_loops(&prog) {
            //     println!("Error: {}", e);
            //     println!("Analysis aborted because the program contains loops.");
            //     return;
            // }
            // println!("Loop check passed (DAG confirmed).");

            let _cert = analysis::analyze_program(&cctx, &prog, entry, stats);

            println!("=== Analysis complete ===");
        }

        "elf-check" => {
            if args.len() < 4 {
                usage();
                return;
            }
            let path = &args[2];
            let section = &args[3];

            println!("=== ELF check: file='{}', section='{}' ===", path, section);
            let prog = load_program_from_elf(path, section);

            let cert = analyze_program(&ctx, &prog, entry, stats);

            println!("\n=== Kernel-sim checking (ELF): file='{}', section='{}' ===", path, section);
            match check::check_certificate_against_kernel_sim(&ctx, &prog, &cert) {
                Ok(()) => println!("CHECK OK"),
                Err(e) => {
                    println!("CHECK FAILED: {}", e.format());
                    std::process::exit(1);
                }
            }
        }

        _ => {
            usage();
        }
    }
}
