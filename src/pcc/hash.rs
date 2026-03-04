use std::hash::{Hash, Hasher};

use crate::ast::Program;

pub fn program_hash(prog: &Program) -> String {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    prog.instrs.len().hash(&mut hasher);
    for insn in &prog.instrs {
        format!("{insn:?}").hash(&mut hasher);
    }
    let mut invalid: Vec<usize> = prog.invalid_pc_set.iter().copied().collect();
    invalid.sort_unstable();
    invalid.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}
