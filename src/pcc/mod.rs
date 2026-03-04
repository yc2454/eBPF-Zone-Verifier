//! Proof-Carrying Code (PCC) module for certificate-aided analysis.
//!
//! This module is intentionally split into two verification phases:
//!
//! 1. `validate`: structural validation of a certificate against a program.
//! 2. `checker`: per-edge semantic checking and narrow refinement application.
//!
//! Important separation:
//! - `validate` answers: "Is this certificate well-formed and compatible with
//!   this program shape?"
//! - `checker` answers: "For this concrete predecessor/successor transition,
//!   does the annotation proof hold under current abstract state and transfer
//!   semantics?"
//!
//! Unknown/invalid annotations are handled fail-closed: they do not broaden
//! analysis behavior and baseline verifier semantics remain authoritative.

mod checker;
mod generator;
mod hash;
mod model;
mod validate;

pub use checker::apply_certificate_aided_refinement;
pub use generator::generate_prototype_certificate_from_zone;
pub use hash::program_hash;
pub use model::ProgramCertificate;
pub use validate::validate_certificate_for_program;
