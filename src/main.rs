// src/main.rs - Enhanced for multi-program ELF files

mod ast;
mod analysis;
mod parsing;
mod zone;
mod misc;

use crate::analysis::context::{ExecContext, default_exec_ctx};
use crate::zone::dbm::Dbm;
use crate::zone::domain::{REG_ENV, assign_zero};
use crate::misc::utils::load_program_from_elf;
use crate::parsing::elf_loader::{load_maps, load_relocations, load_raw_programs, list_section_names};
use crate::parsing::elf_loader;
use crate::parsing::btf;
use crate::parsing::bpf_insn::decode_insns;
use crate::parsing::bpf_to_ast::lower_raw_to_program;

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- elf-list     <elf_path>                 # List all sections and programs");
    eprintln!("  cargo run -- elf-analyze  <elf_path> <section_name>  # Analyze a section by name");
    eprintln!("  cargo run -- elf-analyze-func <elf_path> <func_name> # Analyze a function by name");
    eprintln!("");
    eprintln!("Examples:");
    eprintln!("  cargo run -- elf-list ./bpf_host.o");
    eprintln!("  cargo run -- elf-analyze ./bpf_host.o tc");
    eprintln!("  cargo run -- elf-analyze-func ./bpf_host.o cil_from_netdev");
}

fn make_entry_state(ctx: &ExecContext) -> Dbm {
    let mut dbm = Dbm::new(REG_ENV.len());
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

    match cmd.as_str() {
        // ============================================================
        // NEW COMMAND: List all sections and programs in an ELF
        // ============================================================
        "elf-list" => {
            if args.len() < 3 {
                eprintln!("Error: Missing ELF path");
                usage();
                return;
            }
            let path = &args[2];

            println!("=== ELF Contents: '{}' ===\n", path);

            // 1. List Sections
            println!("--- SECTIONS ---");
            match list_section_names(path) {
                Ok(sections) => {
                    for (i, name) in sections.iter().enumerate() {
                        // Filter out non-code sections
                        if !name.is_empty() && !name.starts_with('.') {
                            println!("  [{}] {}", i, name);
                        }
                    }
                    println!("\n  (Showing non-dot sections. Use section name with elf-analyze)");
                }
                Err(e) => eprintln!("  Error listing sections: {:?}", e),
            }

            // 2. List Programs (Functions from Symbol Table)
            println!("\n--- BPF PROGRAMS (Functions) ---");
            match load_raw_programs(path) {
                Ok(progs) => {
                    if progs.is_empty() {
                        println!("  No function symbols found.");
                        println!("  Try using section names directly with elf-analyze.");
                    } else {
                        for (i, p) in progs.iter().enumerate() {
                            let insn_count = p.data.len() / 8;
                            println!("  [{}] {} ({} instructions, {} bytes)", 
                                     i, p.name, insn_count, p.data.len());
                        }
                        println!("\n  Use function name with elf-analyze-func");
                    }
                }
                Err(e) => eprintln!("  Error loading programs: {:?}", e),
            }

            // 3. List Maps
            println!("\n--- BPF MAPS ---");
            match load_maps(path) {
                Ok(maps) => {
                    if maps.is_empty() {
                        println!("  No maps found.");
                    } else {
                        for (i, m) in maps.iter().enumerate() {
                            println!("  [{}] {} (key: {} bytes, value: {} bytes)", 
                                     i, m.name, m.key_size, m.value_size);
                        }
                    }
                }
                Err(e) => eprintln!("  Error loading maps: {:?}", e),
            }

            println!("\n=== Done ===");
        }

        // ============================================================
        // EXISTING: Analyze by section name
        // ============================================================
        "elf-analyze" => {
            if args.len() < 4 {
                eprintln!("Error: Missing arguments");
                usage();
                return;
            }
            let path = &args[2];
            let section = &args[3];

            println!("=== ELF analyze: file='{}', section='{}' ===", path, section);
            
            let ctx = default_exec_ctx();
            let mut cctx = default_exec_ctx();
            let entry = make_entry_state(&ctx);

            // 1. Load Maps
            let map_defs = load_maps(path).unwrap_or_default();
            println!("Loaded {} maps", map_defs.len());
            for (i, m) in map_defs.iter().enumerate() {
                println!("  Map {}: '{}' (ValSize: {}, TypeID: {:?})", 
                        i, m.name, m.value_size, m.btf_val_type_id);
            }

            // 2. Load Relocations
            let pc_to_map_idx = load_relocations(path, &map_defs, section).unwrap_or_default();
            println!("Loaded {} relocations", pc_to_map_idx.len());

            // 3. Load BTF
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

            // 4. Load and Analyze Program
            let prog = load_program_from_elf(path, section);
            println!("Program size: {} instructions", prog.instrs.len());

            let _cert = analysis::analyze_program(&cctx, &prog, entry);

            println!("=== Analysis complete ===");
        }

        // ============================================================
        // NEW: Analyze by function name (for multi-function ELFs)
        // ============================================================
        "elf-analyze-func" => {
            if args.len() < 4 {
                eprintln!("Error: Missing arguments");
                usage();
                return;
            }
            let path = &args[2];
            let func_name = &args[3];

            println!("=== ELF analyze function: file='{}', func='{}' ===", path, func_name);

            // 1. Find the function in the ELF
            let progs = match load_raw_programs(path) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("Error loading programs: {:?}", e);
                    return;
                }
            };

            let target_prog = progs.iter().find(|p| p.name == *func_name);
            if target_prog.is_none() {
                eprintln!("Error: Function '{}' not found.", func_name);
                eprintln!("Available functions:");
                for p in &progs {
                    eprintln!("  - {}", p.name);
                }
                return;
            }
            let target_prog = target_prog.unwrap();
            
            println!("Found function '{}' ({} bytes, {} instructions)", 
                     func_name, target_prog.data.len(), target_prog.data.len() / 8);

            let ctx = default_exec_ctx();
            let mut cctx = default_exec_ctx();
            let entry = make_entry_state(&ctx);

            // 2. Load Maps
            let map_defs = load_maps(path).unwrap_or_default();
            println!("Loaded {} maps", map_defs.len());

            // 3. Find the section containing this function for relocations
            // We need to find which section this function belongs to
            let sections = list_section_names(path).unwrap_or_default();
            let section_name = if target_prog.section_idx < sections.len() {
                &sections[target_prog.section_idx]
            } else {
                "unknown"
            };
            println!("Function is in section: '{}'", section_name);

            // 4. Load Relocations for that section
            let pc_to_map_idx = load_relocations(path, &map_defs, section_name).unwrap_or_default();
            println!("Loaded {} relocations", pc_to_map_idx.len());

            // 5. Load BTF
            let btf_bytes = elf_loader::load_section_bytes(path, ".BTF", false).unwrap_or_default();
            let btf_ctx = if !btf_bytes.is_empty() {
                btf::parse_btf(&btf_bytes).unwrap_or_else(|e| {
                    println!("BTF Parse Error: {}", e);
                    btf::BtfContext::new()
                })
            } else {
                btf::BtfContext::new()
            };

            cctx.map_defs = map_defs;
            cctx.pc_to_map_idx = pc_to_map_idx;
            cctx.btf = btf_ctx;

            // 6. Decode and Analyze
            // Use the raw bytes from the function
            let raw_insns = decode_insns(&target_prog.data);
            let prog = match lower_raw_to_program(&raw_insns) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("Error lowering to AST: {:?}", e);
                    return;
                }
            };

            println!("Program size: {} instructions", prog.instrs.len());

            let _cert = analysis::analyze_program(&cctx, &prog, entry);

            println!("=== Analysis complete ===");
        }

        _ => {
            eprintln!("Unknown command: {}", cmd);
            usage();
        }
    }
}
