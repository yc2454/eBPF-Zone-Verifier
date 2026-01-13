// src/main.rs

mod ast;
mod analysis;
mod parsing;
mod zone;
mod misc;

use crate::analysis::context::{ExecContext, default_exec_ctx};
use crate::zone::dbm::Dbm;
use crate::zone::domain::{REG_ENV, assign_zero};
use crate::misc::utils::load_program_from_elf;
use crate::parsing::elf_loader::{load_maps, load_relocations};
use crate::parsing::elf_loader;
use crate::parsing::btf;

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- list");
    eprintln!("  cargo run -- analyze <program_name>");
    eprintln!("  cargo run -- check <program_name>");
    eprintln!("  cargo run -- elf-analyze <elf_path> <section_name>");
    eprintln!("  cargo run -- elf-check  <elf_path> <section_name>");
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

    // Commands that need a second argument (program name or path)
    if args.len() < 3 {
        usage();
        return;
    }

    let ctx = default_exec_ctx();
    let mut cctx = default_exec_ctx();
    let entry = make_entry_state(&ctx);

    match cmd.as_str() {

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
                btf::parse_btf(&btf_bytes).unwrap_or_else(|e| {
                    println!("BTF Parse Error: {}", e);
                    btf::BtfContext::new()
                })
            } else {
                println!("No .BTF section found.");
                btf::BtfContext::new()
            };

            cctx.map_defs = map_defs;
            cctx.pc_to_map_idx = pc_to_map_idx;
            cctx.btf = btf_ctx;

            let prog = load_program_from_elf(path, section);
            println!("Program size: {} instructions", prog.instrs.len());

            let _cert = analysis::analyze_program(&cctx, &prog, entry);

            println!("=== Analysis complete ===");
        }

        _ => {
            usage();
        }
    }
}
