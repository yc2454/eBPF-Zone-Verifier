// src/stats.rs
#[derive(Debug, Default, Clone)]
pub struct AnalysisStats {
    /// True if we saw something that makes this program unsafe.
    pub dangerous: bool,

    /// Optional, more fine-grained flags if you want.
    pub unsafe_stack_load: bool,
    pub unsafe_stack_store: bool,
    pub dbm_inconsistent: bool,
    pub unsupported_opcode: bool,

    pub abort: bool,
}

impl AnalysisStats {
    pub fn mark_unsafe_load(&mut self) {
        self.dangerous = true;
        self.unsafe_stack_load = true;
    }

    pub fn mark_unsafe_store(&mut self) {
        self.dangerous = true;
        self.unsafe_stack_store = true;
    }

    pub fn mark_dbm_inconsistent(&mut self) {
        self.dangerous = true;
        self.dbm_inconsistent = true;
    }

    pub fn mark_unsupported_opcode(&mut self) {
        self.dangerous = true;
        self.unsupported_opcode = true;
    }
}
