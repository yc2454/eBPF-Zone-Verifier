use std::hash::{Hash, Hasher};

use crate::ast::Program;

/// FNV-1a 64-bit hasher with fixed constants.
struct StableHasher(u64);

impl StableHasher {
    const OFFSET_BASIS: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;

    fn new() -> Self {
        StableHasher(Self::OFFSET_BASIS)
    }
}

impl Hasher for StableHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 ^= b as u64;
            self.0 = self.0.wrapping_mul(Self::PRIME);
        }
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

pub fn program_hash(prog: &Program) -> String {
    let mut hasher = StableHasher::new();
    prog.instrs.len().hash(&mut hasher);
    for insn in &prog.instrs {
        format!("{insn:?}").hash(&mut hasher);
    }
    let mut invalid: Vec<usize> = prog.invalid_pc_set.iter().copied().collect();
    invalid.sort_unstable();
    invalid.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}
