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
mod batch;

use crate::ast::Program;
use crate::dbm::Dbm;
use crate::domain::{Var, VAR_ENV, assign_zero};
use crate::exec::{analyze_program, ExecContext};

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
        zero: Var::Zero,
        r10: Var::R10,
        stack_min: -512,
        stack_max: -1,
    }
}

/// Load a Program from an ELF section by:
///   ELF -> bytes -> RawBpfInsn -> Program (via bpf_to_ast).
fn load_program_from_elf(path: &str, section: &str) -> Program {
    let bytes = elf_loader::load_bpf_insn_stream_section(path, section)
        .unwrap_or_else(|e| {
            eprintln!("Failed to load ELF section '{}': {e:?}", section);
            std::process::exit(1);
        });

    let raw_insns = bpf_insn::decode_insns(&bytes);
    println!(
        "Loaded section '{}' from '{}': {} bytes, {} instructions",
        section,
        path,
        bytes.len(),
        raw_insns.len()
    );

    match bpf_to_ast::lower_raw_to_program(&raw_insns) {
        Ok(prog) => prog,
        Err(e) => {
            eprintln!(
                "Lowering ELF → AST failed at pc {} (opcode 0x{:02x}): {}",
                e.pc, e.code, e.msg
            );
            std::process::exit(1);
        }
    }
}


fn make_entry_state(ctx: &ExecContext) -> Dbm {
    let mut dbm = Dbm::new(VAR_ENV.len());

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
            let prog = load_program_from_elf(path, section);

            let _cert = analyze_program(&ctx, &prog, entry, stats);

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
