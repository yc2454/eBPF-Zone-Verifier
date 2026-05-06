//! BTF parsing and the `BtfContext` query API.
//!
//! Originally a single 2400-line `btf.rs`, split into:
//!   * [`types`] — type defs, kind constants, free helpers
//!   * [`context`] — `BtfContext` impls (lookup / fields / kptr / funcs / datasec)
//!   * [`parse`] — `parse_btf` (full BTF section → `BtfContext`)
//!   * [`map_defs`] — `parse_btf_map_defs` (BTF-driven map-def discovery)

mod context;
mod map_defs;
mod parse;
mod types;

#[cfg(test)]
mod tests;

pub use map_defs::parse_btf_map_defs;
pub use parse::parse_btf;
pub use types::{
    BTF_KIND_FUNC_PROTO, BtfContext, BtfFieldKind, BtfMember, BtfType, GlobalFuncArg,
    SpecialFieldKind, StructOpsArg,
};
