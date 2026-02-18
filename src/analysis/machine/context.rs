// src/analysis/context.rs
use crate::ast::{AttachKind, ProgramKind};
use crate::parsing::btf::BtfContext;
use crate::parsing::elf::{BpfMapDef, RelocInfo};
use std::collections::HashMap;

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
