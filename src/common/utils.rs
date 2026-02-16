use crate::ast::{Program, ProgramKind};
use crate::parsing::bpf_insn;
use crate::parsing::bpf_to_ast;
use crate::parsing::elf_loader;
use crate::zone::dbm::INF;
use anyhow::{Context, Result};
use std::collections::HashMap;
use std::fs;
use std::path::Path;

// Bounds for finite constraints inside the DBM.
// We never store anything > POS_BOUND or < NEG_BOUND.
const POS_BOUND: i64 = INF / 2;
const NEG_BOUND: i64 = -POS_BOUND;

#[inline]
pub fn clamp_upper_bound(c: i64) -> i64 {
    // We represent "no constraint" as INF.
    // For x - y <= c with huge positive c, we can treat it as no constraint.
    if c > POS_BOUND {
        INF
    } else if c < NEG_BOUND {
        // Very strong negative bound; weaken to NEG_BOUND
        NEG_BOUND
    } else {
        c
    }
}

#[inline]
pub fn clamped_add(a: i64, b: i64) -> i64 {
    // Safe addition for Floyd–Warshall.
    // If either side is INF, or the sum overflows, treat as INF (no useful bound).
    if a >= INF || b >= INF {
        return INF;
    }
    match a.checked_add(b) {
        Some(sum) => clamp_upper_bound(sum),
        None => INF,
    }
}

/// Load a Program from an ELF section by:
///   ELF -> bytes -> RawBpfInsn -> Program (via bpf_to_ast).
pub fn load_program_from_elf(path: &str, section: &str) -> Program {
    let bytes = elf_loader::load_bpf_insn_stream_section(path, section).unwrap_or_else(|e| {
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

pub const OBJ_PROG_TYPE_JSON: &str = "./obj_prog_type.json";

type RawJsonMap = HashMap<String, Option<String>>;

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
