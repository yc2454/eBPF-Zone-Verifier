// Interval abstract domain (kernel verifier style)
//
// This module implements a simple interval domain that tracks per-register
// bounds without relational constraints. This matches the kernel BPF verifier's
// approach more closely than the Zone domain.

mod state;
pub mod ops;

pub use state::IntervalState;
pub use ops::*;
