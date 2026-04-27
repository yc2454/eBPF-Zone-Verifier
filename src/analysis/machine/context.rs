// src/analysis/context.rs
use crate::ast::{AttachKind, ProgramKind};
use crate::parsing::btf::BtfContext;
use crate::parsing::elf::{BpfMapDef, RelocInfo};
use std::collections::HashMap;

/// Per-argument entry-state typing for a struct_ops subprog (W6.4a).
///
/// Captured by the runner once a `SEC("struct_ops*")` subprog has been
/// matched against its ops-struct member binding (see
/// `src/parsing/elf/struct_ops.rs` + `BtfContext::resolve_struct_ops_method`).
/// `analyze_program_full` consumes this when seeding R1..Rn in place of
/// the default `R1 = PtrToCtx`.
#[derive(Debug, Clone)]
pub enum EntryArg {
    Scalar,
    /// Trusted pointer to a named kernel struct. The string is interned
    /// via `intern_btf_type_name` so it satisfies the `&'static str`
    /// requirement of `RegType::PtrToBtfId`.
    TrustedPtrBtfId(&'static str),
}

/// Intern a kernel struct/union name resolved from BTF into a `&'static
/// str`. Returns the interned literal *only* for names with a registered
/// memory-region layout in `mem_region_model::BPF_MAP_FIELDS` and friends.
/// For any other name, returns `"unknown"` — the sentinel that
/// `transfer/memory/access.rs` recognizes to skip per-field bounds
/// checking (because we have no layout to check against).
///
/// Why "unknown" by default: the access pass treats a known PtrToBtfId
/// type as "I have a layout for this struct, prove the access is in
/// bounds" — and rejects when the layout lookup fails. For struct_ops
/// args (and any other resolved-from-BTF pointer we don't have a layout
/// for) we want the kernel-verifier behavior of "typed pointer, no
/// per-field validation" rather than a hard reject. As we add
/// mem_region_model entries for specific kernel structs, move them out
/// of the catch-all by adding an explicit arm here.
///
/// Why a fixed table instead of a runtime interner: every entry here is
/// referenced from `RegType::PtrToBtfId { type_name: &'static str, .. }`,
/// and we deliberately avoid a leak-based interner.
pub fn intern_btf_type_name(_name: &str) -> &'static str {
    // No specific mem_region_model entries exist for struct_ops args yet
    // (sock, tcp_sock, task_struct, ...). When one is added, add a
    // matching arm below; until then, the catch-all is correct.
    "unknown"
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum VerificationMode {
    Priviledged,
    Unprivileged,
}

#[derive(Clone, Debug)]
pub struct ExecContext {
    pub map_defs: Vec<BpfMapDef>,
    pub pc_to_reloc: HashMap<usize, RelocInfo>,
    pub btf: BtfContext,
    pub prog_kind: ProgramKind,
    pub attach_kind: AttachKind,
    pub flags: u32,
    pub mode: VerificationMode,
    pub kfunc: Option<String>,
    /// W6.4a struct_ops entry-state typing. When `prog_kind` is
    /// `StructOps` and the runner has matched the subprog to its
    /// ops-struct member, this holds one [`EntryArg`] per kernel-passed
    /// argument (R1, R2, ...). `analyze_program_full` overrides the
    /// default `R1 = PtrToCtx` with these. None means "no struct_ops
    /// binding available" — fall back to the default.
    pub entry_args: Option<Vec<EntryArg>>,
}

pub fn default_exec_ctx() -> ExecContext {
    ExecContext {
        map_defs: Vec::new(),
        pc_to_reloc: HashMap::new(),
        btf: BtfContext::new(),
        prog_kind: ProgramKind::Unknown,
        attach_kind: AttachKind::Unknown,
        flags: 0,
        mode: VerificationMode::Priviledged,
        kfunc: None,
        entry_args: None,
    }
}

impl ExecContext {
    pub fn has_flag(&self, flag: u32) -> bool {
        self.flags & flag != 0
    }

    pub fn is_privileged(&self) -> bool {
        matches!(self.mode, VerificationMode::Priviledged)
    }
}
