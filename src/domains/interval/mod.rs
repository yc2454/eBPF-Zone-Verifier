// Interval abstract domain (kernel verifier style)
//
// This module implements a simple interval domain that tracks per-register
// bounds without relational constraints. This matches the kernel BPF verifier's
// approach more closely than the Zone domain.

pub mod ops;
mod state;

pub use state::{IntervalState, PtrOffset, new_scalar_id};
