//! BTF parsing and the `BtfContext` query API.
//!
//! Originally a single 2400-line `btf.rs`, split into:
//!   * [`types`] — type defs, kind constants, free helpers
//!   * [`context`] — `BtfContext` impls (lookup / fields / kptr / funcs / datasec)
//!   * [`parse`] — `parse_btf` (full BTF section → `BtfContext`)
//!   * [`map_defs`] — `parse_btf_map_defs` (raw walk for `.maps` discovery)
//!
//! Pure code-motion vs. the pre-split file — no semantic changes. External
//! call sites continue to use `crate::parsing::btf::*` thanks to the
//! re-exports below.

#![allow(dead_code)]

mod context;
pub mod map_defs;
pub mod parse;
pub mod types;

#[cfg(test)]
mod tests;

// Re-export every public surface so `crate::parsing::btf::Foo` keeps working.
pub use map_defs::parse_btf_map_defs;
pub use parse::parse_btf;
pub use types::{
    BTF_KIND_ARRAY, BTF_KIND_CONST, BTF_KIND_DATASEC, BTF_KIND_DECL_TAG, BTF_KIND_ENUM,
    BTF_KIND_ENUM64, BTF_KIND_FLOAT, BTF_KIND_FUNC, BTF_KIND_FUNC_PROTO, BTF_KIND_FWD,
    BTF_KIND_INT, BTF_KIND_PTR, BTF_KIND_RESTRICT, BTF_KIND_STRUCT, BTF_KIND_TYPEDEF,
    BTF_KIND_TYPE_TAG, BTF_KIND_UNION, BTF_KIND_VAR, BTF_KIND_VOLATILE, BTF_MAGIC, BtfContext,
    BtfFieldInfo, BtfFieldKind, BtfMember, BtfType, ContainsInfo, DatasecEntry, DeclTag,
    GlobalFuncArg, SpecialField, SpecialFieldKind, StructOpsArg,
};
