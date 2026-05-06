//! Lightweight raw-bytes BTF walker dedicated to map-def discovery in
//! `.maps` / `.bss.<name>` sections. Operates over `BtfTypeRaw` rather
//! than the full `BtfContext` because it runs during ELF load, before
//! the structured context is built.
//!
//! Note: `classify_kptr_field` / `extract_kptr_fields*` here duplicate
//! `BtfContext::classify_kptr_pointer` / `collect_kptr_fields_at`
//! intentionally (different input shape). A future cleanup can fold the
//! two together by deferring kptr extraction until after BtfContext is
//! built.

use std::convert::TryInto;

use log::info;

use crate::parsing::elf::{BpfMapDef, KptrField, KptrFieldKind};

use super::types::*;

#[derive(Debug, Clone)]
struct BtfTypeRaw {
    name_off: u32,
    info: u32,
    size_or_type: u32,
    data: Vec<u8>,
}

impl BtfTypeRaw {
    fn kind(&self) -> u8 {
        ((self.info >> 24) & 0x1f) as u8
    }
    fn vlen(&self) -> u32 {
        self.info & 0xffff
    }
}

/// Classify a struct member's type_id as a kptr field by walking the
/// chain of TYPE_TAGs / modifiers around the PTR.
///
/// The kernel emits two equivalent encodings for `struct foo __kptr *fld`
/// depending on where `__attribute__((btf_type_tag("kptr")))` lands:
///   (a) TYPE_TAG("kptr") -> PTR -> STRUCT foo
///   (b) PTR -> TYPE_TAG("kptr") -> STRUCT foo
/// Both are accepted. Returns `(KptrFieldKind, pointee_struct_btf_id)`
/// when the field is a kptr; `None` otherwise.
fn classify_kptr_field(
    types: &[BtfTypeRaw],
    field_type_id: u32,
    get_str: &impl Fn(u32) -> String,
) -> Option<(KptrFieldKind, u32)> {
    let kind_from_tag = |name: &str| -> Option<KptrFieldKind> {
        match name {
            "kptr" => Some(KptrFieldKind::Ref),
            "kptr_untrusted" => Some(KptrFieldKind::Unref),
            "rcu" => Some(KptrFieldKind::Rcu),
            "percpu_kptr" => Some(KptrFieldKind::Percpu),
            "uptr" => Some(KptrFieldKind::Uptr),
            _ => None,
        }
    };

    // Peel modifiers + outer TYPE_TAGs until we either find a PTR or
    // give up. Track the most-recently-seen kptr tag.
    let mut kind: Option<KptrFieldKind> = None;
    let mut curr = field_type_id;
    for _ in 0..16 {
        let t = types.get(curr as usize)?;
        match t.kind() {
            BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT => {
                curr = t.size_or_type;
            }
            BTF_KIND_TYPE_TAG => {
                let tag = get_str(t.name_off);
                if let Some(k) = kind_from_tag(&tag) {
                    kind = Some(k);
                }
                curr = t.size_or_type;
            }
            BTF_KIND_PTR => break,
            _ => return None,
        }
    }
    let ptr_t = types.get(curr as usize)?;
    if ptr_t.kind() != BTF_KIND_PTR {
        return None;
    }
    let mut pointee = ptr_t.size_or_type;

    // Peel modifiers + inner TYPE_TAGs to reach the pointee struct,
    // and pick up a kptr tag if it lives on the inner side.
    for _ in 0..16 {
        let t = match types.get(pointee as usize) {
            Some(t) => t,
            None => break,
        };
        match t.kind() {
            BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT => {
                pointee = t.size_or_type;
            }
            BTF_KIND_TYPE_TAG => {
                let tag = get_str(t.name_off);
                if let Some(k) = kind_from_tag(&tag) {
                    kind = Some(k);
                }
                pointee = t.size_or_type;
            }
            _ => break,
        }
    }

    kind.map(|k| (k, pointee))
}

/// Walk the members of `value_type_id` (expected STRUCT/UNION) and
/// collect every kptr-typed field. Field offsets are returned in bytes.
///
/// Recurses into nested struct/union members so a `__uptr` (or other
/// kptr-tagged) field inside an inner struct is reported with its absolute
/// offset within the outer value type. Mirrors the kernel's
/// `btf_find_struct_field` recursion via `BTF_FIELDS_F_RECUR` —
/// uptr_failure.c::uptr_write_nested writes through `v->nested.udata`,
/// which is reachable only via this recursion.
fn extract_kptr_fields(
    types: &[BtfTypeRaw],
    value_type_id: u32,
    get_str: &impl Fn(u32) -> String,
) -> Vec<KptrField> {
    let mut out = Vec::new();
    extract_kptr_fields_recurse(types, value_type_id, 0, get_str, &mut out, 0);
    out
}

fn extract_kptr_fields_recurse(
    types: &[BtfTypeRaw],
    value_type_id: u32,
    base_byte_off: u32,
    get_str: &impl Fn(u32) -> String,
    out: &mut Vec<KptrField>,
    depth: u32,
) {
    // Bound recursion so a pathological BTF can't blow the stack. The
    // kernel uses MAX_RESOLVE_DEPTH = 32 in similar walks; 8 is plenty
    // for realistic map values.
    if depth > 8 {
        return;
    }
    let Some(t) = types.get(value_type_id as usize) else {
        return;
    };
    // Peel typedef chain to the underlying struct.
    let mut t = t;
    let mut peel = 0;
    while matches!(
        t.kind(),
        BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT
    ) && peel < 8
    {
        match types.get(t.size_or_type as usize) {
            Some(inner) => {
                t = inner;
                peel += 1;
            }
            None => return,
        }
    }
    if t.kind() != BTF_KIND_STRUCT && t.kind() != BTF_KIND_UNION {
        return;
    }
    let nmembers = t.vlen() as usize;
    let mut cur = 0usize;
    for _ in 0..nmembers {
        if cur + 12 > t.data.len() {
            break;
        }
        let _name_off = u32::from_le_bytes(t.data[cur..cur + 4].try_into().unwrap());
        let m_type_id = u32::from_le_bytes(t.data[cur + 4..cur + 8].try_into().unwrap());
        let m_offset_bits = u32::from_le_bytes(t.data[cur + 8..cur + 12].try_into().unwrap());
        cur += 12;
        // Bottom 24 bits are the bit offset for non-bitfield members
        // in BPF_F_BITFIELD_SIZE_GT_0; for full-width pointer/struct
        // members the offset is byte-aligned and the upper bits are zero.
        let bit_off = m_offset_bits & 0x00ff_ffff;
        let member_byte_off = base_byte_off + bit_off / 8;
        if let Some((kind, pointee_btf_id)) = classify_kptr_field(types, m_type_id, get_str) {
            out.push(KptrField {
                offset: member_byte_off,
                kind,
                pointee_btf_id,
            });
            continue;
        }
        // Not a kptr/uptr-tagged pointer at this slot — but if it's a
        // nested struct/union, recurse so any kptr-tagged fields inside
        // contribute with their absolute offset relative to the outer
        // value type.
        let mut inner_id = m_type_id;
        let mut peel = 0;
        while let Some(inner_t) = types.get(inner_id as usize) {
            if !matches!(
                inner_t.kind(),
                BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT
            ) || peel >= 8
            {
                break;
            }
            inner_id = inner_t.size_or_type;
            peel += 1;
        }
        if let Some(inner_t) = types.get(inner_id as usize)
            && matches!(inner_t.kind(), BTF_KIND_STRUCT | BTF_KIND_UNION)
        {
            extract_kptr_fields_recurse(
                types,
                inner_id,
                member_byte_off,
                get_str,
                out,
                depth + 1,
            );
        }
    }
}

pub fn parse_btf_map_defs(bytes: &[u8]) -> Result<Vec<BpfMapDef>, String> {
    if bytes.len() < 24 {
        return Err("BTF too short".into());
    }

    let hdr_len = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
    let type_off = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    let type_len = u32::from_le_bytes(bytes[12..16].try_into().unwrap());
    let str_off = u32::from_le_bytes(bytes[16..20].try_into().unwrap());
    let str_len = u32::from_le_bytes(bytes[20..24].try_into().unwrap());

    let type_start = (hdr_len + type_off) as usize;
    let type_end = type_start + type_len as usize;
    let str_start = (hdr_len + str_off) as usize;
    let str_end = str_start + str_len as usize;

    if type_end > bytes.len() || str_end > bytes.len() {
        return Err("BTF sections out of bounds".into());
    }

    // Parse Types purely for Map Discovery
    let mut types = Vec::new();
    types.push(BtfTypeRaw {
        name_off: 0,
        info: 0,
        size_or_type: 0,
        data: vec![],
    }); // ID 0

    let mut cursor = type_start;
    while cursor < type_end {
        if cursor + 12 > bytes.len() {
            break;
        }

        let name_off = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
        let info = u32::from_le_bytes(bytes[cursor + 4..cursor + 8].try_into().unwrap());
        let size_or_type = u32::from_le_bytes(bytes[cursor + 8..cursor + 12].try_into().unwrap());
        cursor += 12;

        let kind = ((info >> 24) & 0x1f) as u8;
        let vlen = (info & 0xffff) as usize;

        let extra = match kind {
            BTF_KIND_INT => 4,
            BTF_KIND_ARRAY => 12,
            BTF_KIND_STRUCT | BTF_KIND_UNION => vlen * 12,
            BTF_KIND_ENUM => vlen * 8,
            BTF_KIND_FUNC_PROTO => vlen * 8,
            BTF_KIND_VAR => 4,
            BTF_KIND_DATASEC => vlen * 12,
            BTF_KIND_DECL_TAG => 4,
            BTF_KIND_ENUM64 => vlen * 12,
            _ => 0,
        };

        if cursor + extra > bytes.len() {
            break;
        }
        let data = bytes[cursor..cursor + extra].to_vec();
        cursor += extra;

        types.push(BtfTypeRaw {
            name_off,
            info,
            size_or_type,
            data,
        });
    }

    let get_str = |off: u32| -> String {
        let start = str_start + off as usize;
        if start >= bytes.len() {
            return String::new();
        }
        let slice = &bytes[start..];
        slice
            .iter()
            .take_while(|&&c| c != 0)
            .map(|&c| c as char)
            .collect()
    };

    // Helper to extract __uint values from BTF map definitions
    // __uint(name, val) creates a pointer to an array[val] in BTF
    fn extract_btf_uint(types: &[BtfTypeRaw], type_id: u32) -> Option<u32> {
        let mut curr_id = type_id;
        let mut depth = 0;

        while depth < 5 && (curr_id as usize) < types.len() {
            let t = &types[curr_id as usize];
            match t.kind() {
                BTF_KIND_PTR => {
                    // Follow the pointer
                    curr_id = t.size_or_type;
                }
                BTF_KIND_ARRAY => {
                    // The value is encoded in nelems
                    if t.data.len() >= 12 {
                        let nelems = u32::from_le_bytes(t.data[8..12].try_into().unwrap());
                        return Some(nelems);
                    }
                    return None;
                }
                BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT => {
                    curr_id = t.size_or_type;
                }
                _ => return None,
            }
            depth += 1;
        }
        None
    }

    fn get_resolved_size(types: &[BtfTypeRaw], type_id: u32, depth: u32) -> u32 {
        if depth > 5 || type_id == 0 || (type_id as usize) >= types.len() {
            return 0;
        }
        let t = &types[type_id as usize];
        match t.kind() {
            BTF_KIND_INT | BTF_KIND_STRUCT | BTF_KIND_UNION | BTF_KIND_FLOAT | BTF_KIND_ENUM => {
                t.size_or_type
            }
            BTF_KIND_ARRAY => {
                if t.data.len() >= 12 {
                    let elem_t = u32::from_le_bytes(t.data[0..4].try_into().unwrap());
                    let nelems = u32::from_le_bytes(t.data[8..12].try_into().unwrap());
                    get_resolved_size(types, elem_t, depth + 1) * nelems
                } else {
                    0
                }
            }
            BTF_KIND_PTR => 8,
            BTF_KIND_TYPEDEF | BTF_KIND_VOLATILE | BTF_KIND_CONST | BTF_KIND_RESTRICT
            | BTF_KIND_VAR | BTF_KIND_TYPE_TAG => {
                get_resolved_size(types, t.size_or_type, depth + 1)
            }
            _ => 0,
        }
    }

    let mut map_defs = Vec::new();
    info!(target: "app", "Scanning {} BTF types for Maps...", types.len());

    for t in types.iter() {
        if t.kind() == BTF_KIND_VAR {
            let name = get_str(t.name_off);
            let def_id = t.size_or_type;

            if (def_id as usize) < types.len() {
                // Follow typedef chain to get to the underlying type
                let mut resolved_t = &types[def_id as usize];
                while resolved_t.kind() == BTF_KIND_TYPEDEF
                    && (resolved_t.size_or_type as usize) < types.len()
                {
                    let resolved_id = resolved_t.size_or_type;
                    resolved_t = &types[resolved_id as usize];
                }
                let def_t = resolved_t;
                if def_t.kind() == BTF_KIND_STRUCT {
                    let mut is_map = false;
                    let mut value_size = 0;
                    let mut key_size = 0;
                    let mut max_entries = 0;
                    let mut map_type = 0u32;
                    let mut map_flags = 0u32;
                    let mut btf_val_type_id = None; // STORE THIS!

                    let members = def_t.vlen() as usize;
                    let mut m_cursor = 0;

                    for _ in 0..members {
                        if m_cursor + 12 > def_t.data.len() {
                            break;
                        }
                        let m_name_off = u32::from_le_bytes(
                            def_t.data[m_cursor..m_cursor + 4].try_into().unwrap(),
                        );
                        let m_type_id = u32::from_le_bytes(
                            def_t.data[m_cursor + 4..m_cursor + 8].try_into().unwrap(),
                        );
                        m_cursor += 12;

                        let m_name = get_str(m_name_off);
                        if m_name == "key" || m_name == "value" || m_name == "values" {
                            is_map = true;

                            let mut actual_type_id = m_type_id;
                            if (actual_type_id as usize) < types.len() {
                                let field_t = &types[actual_type_id as usize];
                                if field_t.kind() == BTF_KIND_PTR {
                                    actual_type_id = field_t.size_or_type;
                                }
                            }
                            let size = get_resolved_size(&types, actual_type_id, 0);

                            if m_name == "value" {
                                value_size = size;
                                btf_val_type_id = Some(actual_type_id);
                            } else if m_name == "values" {
                                // For map-in-map (ARRAY_OF_MAPS/HASH_OF_MAPS), the "values" field
                                // points to inner maps. The value_size is the size of a map pointer (4 bytes).
                                value_size = 4;
                            } else {
                                key_size = size;
                            }
                        } else if m_name == "type" {
                            // Extract map type from the BTF
                            // The member type might be a PTR to an ARRAY where nelems encodes the value
                            if let Some(val) = extract_btf_uint(&types, m_type_id) {
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
                            // Extract max_entries - similar encoding as type
                            if let Some(val) = extract_btf_uint(&types, m_type_id) {
                                max_entries = val;
                            }
                        } else if m_name == "value_size" {
                            // Alternative way to specify value size using __uint
                            is_map = true;
                            if let Some(val) = extract_btf_uint(&types, m_type_id) {
                                value_size = val;
                            }
                        } else if m_name == "key_size" {
                            // Alternative way to specify key size using __uint
                            is_map = true;
                            if let Some(val) = extract_btf_uint(&types, m_type_id) {
                                key_size = val;
                            }
                        } else if m_name == "map_flags" {
                            // `__uint(map_flags, BPF_F_RDONLY_PROG)` — encoded as
                            // pointer-to-array with nelems = flag value, same as
                            // type/max_entries above.
                            if let Some(val) = extract_btf_uint(&types, m_type_id) {
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
                        let kptr_fields = btf_val_type_id
                            .map(|id| extract_kptr_fields(&types, id, &get_str))
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
                            initial_data: None, // No initial data here
                            inner_map_idx: None,
                            kptr_fields,
                            extern_var_offsets: Vec::new(),
                        });
                    }
                }
            }
        }
    }

    Ok(map_defs)
}
