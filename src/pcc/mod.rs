//! Proof-Carrying Code (PCC) module for certificate-aided analysis.
//!
//! This module is intentionally split into two verification phases:
//!
//! 1. `validate`: structural validation of a certificate against a program.
//! 2. `checker`: per-edge semantic checking.
//! 3. `injector`: applies verified facts to successor state.
//!
//! Important separation:
//! - `validate` answers: "Is this certificate well-formed and compatible with
//!   this program shape?"
//! - `checker` answers: "For this concrete predecessor/successor transition,
//!   does the annotation proof hold under current abstract state and transfer
//!   semantics?"
//! - `injector` answers: "Given verified facts, what narrow state refinements
//!   are safe to apply?"
//!
//! Unknown/invalid annotations are handled fail-closed: they do not broaden
//! analysis behavior and baseline verifier semantics remain authoritative.

mod checker;
mod generator;
mod hash;
mod injector;
mod model;
mod validate;

pub use checker::check_proof;
pub use generator::generate_certificate;
pub use hash::program_hash;
pub use injector::apply_verified_refinements;
#[allow(unused_imports)]
pub use model::{ProgramCertificate, ProofStep};
pub use validate::validate_certificate_for_program;
