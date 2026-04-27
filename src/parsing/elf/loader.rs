use crate::ast::{Program, ProgramKind};
use crate::parsing::bpf_to_ast;
use crate::parsing::elf::{
    BpfMapDef, RelocInfo, combine_function_with_subprogs, combine_program_with_subprogs,
    discover_bpf_call_targets,
};
use anyhow::{Context, Result};
use std::collections::HashMap;
use std::fs;
use std::path::Path;

pub const OBJ_PROG_TYPE_JSON: &str = "./obj_prog_type.json";

type RawJsonMap = HashMap<String, Option<String>>;

/// Load a Program from an ELF section by:
///   ELF -> bytes -> RawBpfInsn -> Program (via bpf_to_ast).
/// Returns Ok(Program) on success, Err(String) on failure.
pub fn try_load_program_from_elf(
    path: &str,
    section: &str,
    pc_to_reloc: Option<&HashMap<usize, crate::parsing::elf::RelocInfo>>,
) -> Result<Program, String> {
    let bytes = crate::parsing::elf::prog::load_bpf_insn_stream_section(path, section)
        .map_err(|e| format!("Failed to load ELF section '{}': {:?}", section, e))?;

    let mut raw_insns = crate::parsing::bpf_insn::decode_insns(&bytes);

    // Apply relocations if provided
    if let Some(relocs) = pc_to_reloc {
        crate::parsing::elf::reloc::apply_relocs(&mut raw_insns, relocs);
    }

    println!(
        "Loaded section '{}' from '{}': {} bytes, {} instructions",
        section,
        path,
        bytes.len(),
        raw_insns.len()
    );

    bpf_to_ast::lower_raw_to_program(&raw_insns).map_err(|e| {
        format!(
            "Lowering ELF → AST failed at pc {} (opcode 0x{:02x}): {}",
            e.pc, e.code, e.msg
        )
    })
}

/// Load a Program for a specific function within an ELF section.
/// Uses STT_FUNC symbol information to extract only that function's bytes.
pub fn try_load_function_from_elf(
    path: &str,
    section: &str,
    func_name: &str,
    pc_to_reloc: Option<&HashMap<usize, crate::parsing::elf::RelocInfo>>,
) -> Result<Program, String> {
    let bytes =
        crate::parsing::elf::prog::load_function_bytes(path, section, func_name).map_err(|e| {
            format!(
                "Failed to load function '{}' from '{}': {:?}",
                func_name, section, e
            )
        })?;

    let mut raw_insns = crate::parsing::bpf_insn::decode_insns(&bytes);

    // Apply relocations if provided
    // Note: relocations need to be adjusted for function offset
    if let Some(relocs) = pc_to_reloc {
        crate::parsing::elf::reloc::apply_relocs(&mut raw_insns, relocs);
    }

    println!(
        "Loaded function '{}' from section '{}': {} bytes, {} instructions",
        func_name,
        section,
        bytes.len(),
        raw_insns.len()
    );

    bpf_to_ast::lower_raw_to_program(&raw_insns).map_err(|e| {
        format!(
            "Lowering ELF → AST failed at pc {} (opcode 0x{:02x}): {}",
            e.pc, e.code, e.msg
        )
    })
}

/// Load a Program from an ELF section, combining with any cross-section subprograms.
/// If the section has cross-section calls, subprograms are appended and call targets fixed.
/// Returns (Program, relocations) on success.
pub fn try_load_combined_program_from_elf(
    path: &str,
    section: &str,
    maps: &[BpfMapDef],
) -> Result<(Program, HashMap<usize, RelocInfo>), String> {
    // Check if section has cross-section calls
    let cross_section_targets = discover_bpf_call_targets(path, section)
        .map_err(|e| format!("Failed to discover BPF call targets: {:?}", e))?;

    if cross_section_targets.is_empty() {
        // No cross-section calls - use existing behavior
        let pc_to_reloc =
            crate::parsing::elf::reloc::load_relocations(path, maps, section).unwrap_or_default();
        let prog = try_load_program_from_elf(path, section, Some(&pc_to_reloc))?;
        return Ok((prog, pc_to_reloc));
    }

    // Has cross-section calls - combine program with subprograms
    println!(
        "Section '{}' has {} cross-section call target(s), combining with subprograms",
        section,
        cross_section_targets.len()
    );
    for target in &cross_section_targets {
        println!(
            "  -> {}::{} (offset {}, size {})",
            target.section, target.func_name, target.offset_in_section, target.size
        );
    }

    let combined = combine_program_with_subprogs(path, maps, section)
        .map_err(|e| format!("Failed to combine program with subprogs: {:?}", e))?;

    println!(
        "Combined program: {} instructions, {} subprograms appended",
        combined.raw_insns.len(),
        combined.func_offsets.len()
    );
    for (name, pc) in &combined.func_offsets {
        println!("  Function '{}' at PC {}", name, pc);
    }

    let prog = bpf_to_ast::lower_raw_to_program(&combined.raw_insns).map_err(|e| {
        format!(
            "Lowering combined ELF → AST failed at pc {} (opcode 0x{:02x}): {}",
            e.pc, e.code, e.msg
        )
    })?;

    Ok((prog, combined.pc_to_reloc))
}

/// Phase 7 wrap-up: load a single SEC()'d entry function plus all
/// subprograms it transitively calls.
///
/// Returns `(Program, relocations, func_offsets)` where `func_offsets`
/// maps each loaded function name to its PC in the combined program.
/// The entry function lives at PC 0; appended subprogs follow.
pub fn try_load_function_with_subprogs_from_elf(
    path: &str,
    section: &str,
    func_name: &str,
    maps: &[BpfMapDef],
) -> Result<(Program, HashMap<usize, RelocInfo>, HashMap<String, usize>), String> {
    let combined = combine_function_with_subprogs(path, maps, section, func_name)
        .map_err(|e| format!("Failed to combine function with subprogs: {:?}", e))?;

    if combined.raw_insns.is_empty() {
        return Err(format!(
            "Function '{}' not found in section '{}'",
            func_name, section
        ));
    }

    let prog = bpf_to_ast::lower_raw_to_program(&combined.raw_insns).map_err(|e| {
        format!(
            "Lowering combined ELF → AST failed at pc {} (opcode 0x{:02x}): {}",
            e.pc, e.code, e.msg
        )
    })?;

    Ok((prog, combined.pc_to_reloc, combined.func_offsets))
}

/// Lookup program kind for a single object file.
/// - `obj_path` may be a full path; we try exact match, then basename.
/// - Missing key or null => Unknown.
pub fn program_kind_for_object(obj_path: &Path) -> Result<ProgramKind> {
    let json_str = fs::read_to_string(OBJ_PROG_TYPE_JSON)
        .with_context(|| format!("failed to read {}", OBJ_PROG_TYPE_JSON))?;

    let raw: RawJsonMap =
        serde_json::from_str(&json_str).context("failed to parse obj_prog_type.json")?;

    let key_exact = obj_path.to_string_lossy();
    let key_base = obj_path
        .file_name()
        .map(|s| s.to_string_lossy())
        .unwrap_or_else(|| key_exact.clone());

    let opt_label = raw
        .get(key_exact.as_ref())
        .or_else(|| raw.get(key_base.as_ref()))
        .or_else(|| {
            // Fuzzy match: if an entry ends with key_base, use it.
            // This handles clang-18_-O1_bpf_lxc.o vs bpf_lxc.o
            raw.iter()
                .find(|(k, _)| k.ends_with(key_base.as_ref()))
                .map(|(_, v)| v)
        });

    match opt_label {
        Some(Some(label)) => Ok(ProgramKind::from_section(label)),
        _ => Err(anyhow::anyhow!(
            "program kind not found for object {:?}",
            obj_path
        )),
    }
}
