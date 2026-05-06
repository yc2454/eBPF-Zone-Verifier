//! `BtfContext` constructors plus the trivial DECL_TAG / kfunc / TYPE_TAG
//! accessors. The bulk of the impl lives in sibling modules:
//!
//!   * [`lookup`] — string + type-id walking primitives.
//!   * [`fields`] — struct-member resolution, special-field collection.
//!   * [`kptr`] — kptr-tagged pointer classification on the parsed map.
//!   * [`funcs`] — struct_ops / global subprog / exception-cb resolution.
//!   * [`datasec`] — DATASEC iteration + ELF-driven offset patching.

pub(super) mod datasec;
pub(super) mod fields;
pub(super) mod funcs;
pub(super) mod kptr;
pub(super) mod lookup;

use std::collections::{HashMap, HashSet};

use super::types::*;

impl BtfContext {
    pub fn new() -> Self {
        BtfContext::default()
    }

    /// Construct a BtfContext from just `types` and `strings`, with an empty
    /// decl_tag / kfunc registry. Used by synthetic tests.
    pub fn from_types_and_strings(types: HashMap<u32, BtfType>, strings: Vec<u8>) -> Self {
        BtfContext {
            types,
            strings,
            decl_tags: Vec::new(),
            kfuncs: HashMap::new(),
            hidden_subprogs: HashSet::new(),
            special_fields_cache: Default::default(),
        }
    }

    /// All DECL_TAGs attached to `target_type_id` (whole-type or any member).
    pub fn decl_tags_for(&self, target_type_id: u32) -> impl Iterator<Item = &DeclTag> {
        self.decl_tags
            .iter()
            .filter(move |t| t.target_type_id == target_type_id)
    }

    /// Returns the FUNC btf_id of a registered kfunc by name, if any.
    /// Currently exercised only by the BTF parser tests; production
    /// callers go through `kfunc_name` (the reverse direction).
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn lookup_kfunc(&self, name: &str) -> Option<u32> {
        self.kfuncs.get(name).copied()
    }

    /// Reverse lookup: given a kfunc FUNC btf_id, return its registered
    /// name. Linear in the kfunc-registry size — only called on kfunc
    /// call sites, of which there are few. Used by call transfer to
    /// dispatch on well-known kfunc names (e.g. `bpf_iter_num_new`).
    pub fn kfunc_name(&self, btf_id: u32) -> Option<&str> {
        self.kfuncs
            .iter()
            .find(|(_, id)| **id == btf_id)
            .map(|(name, _)| name.as_str())
    }

    /// Directly register a kfunc name → btf_id mapping. Used by the
    /// test harness to seed the registry without parsing a real BTF
    /// blob with DECL_TAGs; production code populates `kfuncs` during
    /// `parse_btf`.
    pub fn register_kfunc(&mut self, name: &str, btf_id: u32) {
        self.kfuncs.insert(name.to_string(), btf_id);
    }

    /// If `type_id` names a BTF_KIND_TYPE_TAG, returns the tag name and the
    /// inner type it wraps. Used by later phases to recognize `__kptr`,
    /// `__rcu`, `__percpu`, etc. Currently only exercised by the BTF
    /// parser tests; classify_kptr_pointer walks TYPE_TAGs internally.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn type_tag_name(&self, type_id: u32) -> Option<(&str, u32)> {
        let ty = self.types.get(&type_id)?;
        if ty.kind() != BTF_KIND_TYPE_TAG {
            return None;
        }
        let name = self.get_string(ty.name_off)?;
        Some((name, ty.size_or_type))
    }
}
