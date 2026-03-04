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
//!   does the obligation proof hold under current abstract state and transfer
//!   semantics?"
//!
//! Unknown/invalid obligations are handled fail-closed: they do not broaden
//! analysis behavior and baseline verifier semantics remain authoritative.

mod checker;
mod hash;
mod model;
mod v1;
mod validate;

pub use checker::apply_certificate_aided_refinement;
pub use hash::program_hash;
pub use model::ProgramCertificate;
pub use v1::generate_v1_obligations_from_zone;
pub use validate::validate_certificate_for_program;
