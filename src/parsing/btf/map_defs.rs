//! BTF-driven map-def discovery for libbpf-style `.maps`-section maps.
//!
//! Walks the parsed [`BtfContext`] looking for `BTF_KIND_VAR`s whose
//! target struct has the libbpf `__type(key, …)` / `__type(value, …)` /
//! `__uint(type, …)` / `__uint(max_entries, …)` member shape, and emits
//! one [`BpfMapDef`] per recognized map. Kptr-tagged value fields are
//! lifted via [`BtfContext::extract_value_kptr_fields`].

use log::info;

use crate::parsing::elf::{BpfMapDef, KptrField};

use super::parse::parse_btf;
use super::types::*;

/// `__uint(name, val)` lowers to `PTR -> ARRAY[val]` in BTF: the value
/// is encoded as the array element count. Returns the count if `type_id`
/// matches that shape (after peeling modifiers), else None.
fn extract_btf_uint(ctx: &BtfContext, type_id: u32) -> Option<u32> {
    let id = ctx.peel_modifiers(type_id);
    let ptr = ctx.types.get(&id)?;
    if ptr.kind() != BTF_KIND_PTR {
        return None;
    }
    let arr_id = ctx.peel_modifiers(ptr.size_or_type);
    let arr = ctx.types.get(&arr_id)?;
    if arr.kind() != BTF_KIND_ARRAY {
        return None;
    }
    // ARRAY's parsed member[0] carries (elem_type=type_id, nelems=offset).
    Some(arr.members.first()?.offset)
}

pub fn parse_btf_map_defs(bytes: &[u8]) -> Result<Vec<BpfMapDef>, String> {
    let ctx = parse_btf(bytes)?;
    let mut map_defs = Vec::new();
    info!(target: "app", "Scanning {} BTF types for Maps...", ctx.types.len());

    for ty in ctx.types.values() {
        if ty.kind() != BTF_KIND_VAR {
            continue;
        }
        let name = ctx.read_string(ty.name_off).unwrap_or("").to_string();
        // Peel typedef wrappers around the var's declared type to reach
        // the underlying struct definition.
        let def_id = ctx.peel_modifiers(ty.size_or_type);
        let Some(def_t) = ctx.types.get(&def_id) else {
            continue;
        };
        if def_t.kind() != BTF_KIND_STRUCT {
            continue;
        }

        let mut is_map = false;
        let mut value_size = 0;
        let mut key_size = 0;
        let mut max_entries = 0;
        let mut map_type = 0u32;
        let mut map_flags = 0u32;
        let mut btf_val_type_id: Option<u32> = None;

        for member in &def_t.members {
            let m_name = ctx.read_string(member.name_off).unwrap_or("");
            if m_name == "key" || m_name == "value" || m_name == "values" {
                is_map = true;
                // libbpf encodes `__type(value, T)` as a pointer to T;
                // peel one PTR layer to get the value type itself.
                let mut actual_type_id = member.type_id;
                if let Some(field_t) = ctx.types.get(&actual_type_id)
                    && field_t.kind() == BTF_KIND_PTR
                {
                    actual_type_id = field_t.size_or_type;
                }
                let size = ctx.type_size_bytes(actual_type_id);
                if m_name == "value" {
                    value_size = size;
                    btf_val_type_id = Some(actual_type_id);
                } else if m_name == "values" {
                    // For map-in-map (ARRAY_OF_MAPS/HASH_OF_MAPS), the "values"
                    // field points to inner maps. The value_size is the size of
                    // a map pointer (4 bytes).
                    value_size = 4;
                } else {
                    key_size = size;
                }
            } else if m_name == "type" {
                if let Some(val) = extract_btf_uint(&ctx, member.type_id) {
                    map_type = val;
                    // Valueless map kinds (ARENA, RINGBUF, USER_RINGBUF,
                    // CGRP_STORAGE …) declare only `type` + `max_entries`
                    // and never appear with a `key`/`value` member, so
                    // without this the libbpf-style `.maps` section
                    // parser sees an all-zero record and the BTF
                    // merger drops the map silently.
                    is_map = true;
                }
            } else if m_name == "max_entries" {
                if let Some(val) = extract_btf_uint(&ctx, member.type_id) {
                    max_entries = val;
                }
            } else if m_name == "value_size" {
                // Alternative way to specify value size using __uint.
                is_map = true;
                if let Some(val) = extract_btf_uint(&ctx, member.type_id) {
                    value_size = val;
                }
            } else if m_name == "key_size" {
                is_map = true;
                if let Some(val) = extract_btf_uint(&ctx, member.type_id) {
                    key_size = val;
                }
            } else if m_name == "map_flags" {
                // `__uint(map_flags, BPF_F_RDONLY_PROG)` — encoded as
                // pointer-to-array with nelems = flag value, same as
                // type/max_entries above.
                if let Some(val) = extract_btf_uint(&ctx, member.type_id) {
                    map_flags = val;
                }
            }
        }

        // Valueless maps (ARENA / RINGBUF / USER_RINGBUF / CGRP_STORAGE)
        // legitimately have value_size == 0; for everything else require
        // value_size > 0 to avoid picking up unrelated BTF structs that
        // happen to have a `type` member.
        let is_valueless_map = matches!(
            map_type,
            27 | 31 | 32 | 33 // RINGBUF, USER_RINGBUF, CGRP_STORAGE, ARENA
        );
        if is_map && (value_size > 0 || is_valueless_map) {
            let kptr_fields: Vec<KptrField> = btf_val_type_id
                .map(|id| ctx.extract_value_kptr_fields(id))
                .unwrap_or_default();
            if !kptr_fields.is_empty() {
                info!(target: "app", "[BTF] Map '{}' has {} kptr field(s): {:?}",
                    name, kptr_fields.len(), kptr_fields);
            }
            info!(target: "app", "[BTF] Found Map: '{}' (Type: {}, KeySize: {}, ValSize: {}, MaxEntries: {}, TypeID: {:?})",
                name, map_type, key_size, value_size, max_entries, btf_val_type_id);
            map_defs.push(BpfMapDef {
                name: name.clone(),
                type_: map_type,
                key_size,
                value_size,
                max_entries,
                map_flags,
                btf_val_type_id,
                initial_data: None,
                inner_map_idx: None,
                kptr_fields,
                extern_var_offsets: Vec::new(),
            });
        }
    }

    Ok(map_defs)
}
