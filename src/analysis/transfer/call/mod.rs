// src/analysis/transfer/call/mod.rs

pub mod checks;
pub mod compat;
pub mod kfunc;
pub mod side_effects;
pub mod signatures;
pub mod transfer;
pub mod validators;

// Re-export public transfer functions
pub(crate) use kfunc::transfer_kfunc;
pub(crate) use transfer::transfer_call;
pub(crate) use transfer::transfer_call_rel;
