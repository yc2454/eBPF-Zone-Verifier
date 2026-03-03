// Abstract domains for numerical analysis
//
// This module contains different abstract domains:
// - zone: Difference Bound Matrix (relational constraints x - y <= c)
// - interval: Simple per-register interval bounds (kernel verifier style)
// - tnum: Tristate numbers for bit-level tracking
// - numeric: Unified enum wrapper for switching between domains

pub mod interval;
pub mod numeric;
pub mod annotation;
pub mod tnum;
pub mod zone;

// Re-export the unified domain type

// Re-export zone components at top level for backwards compatibility
// TODO: Remove these once all code migrates to the new abstraction
pub use zone::dbm;
pub use zone::ops as domain;
