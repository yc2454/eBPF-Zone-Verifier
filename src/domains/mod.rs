// Abstract domains for numerical analysis
//
// This module contains different abstract domains:
// - zone: Difference Bound Matrix (relational constraints x - y <= c)
// - interval: Simple per-register interval bounds (kernel verifier style)
// - tnum: Tristate numbers for bit-level tracking
// - numeric: Unified enum wrapper for switching between domains

pub mod interval;
pub mod numeric;
pub mod tnum;
pub mod zone;

// Stable aliases: zone::dbm and zone::ops are also accessible as domains::dbm / domains::domain.
pub use zone::dbm;
pub use zone::ops as domain;
