//! Selftest runner for the canonical (post-6.2) upstream BPF selftest format.
//!
//! Upstream tests at this point are real BPF C programs that compile to ELF
//! via `clang -target bpf`. The flow is:
//!
//!   `progs/verifier_*.c` ─► clang ─► `.o` (BPF ELF, multiple SEC programs)
//!                       └─► [`attrs::scrape`] ─► `__success`/`__failure`/`__retval`/…
//!
//! per SEC program in the ELF:
//!   verifier verdict ─compare─► scraped expectation
//!
//! No JSON, no insn-level translation — the ELF is the canonical artifact
//! and our existing [`crate::parsing::elf`] machinery already reads it.
//!
//! For the genuinely-old `struct bpf_test`-style corpus that pre-dates this
//! format, see [`crate::testing::legacy_selftest`].

pub mod attrs;
pub mod baseline;
pub mod clang;
pub mod expectations;
pub mod runner;
pub mod sec;
