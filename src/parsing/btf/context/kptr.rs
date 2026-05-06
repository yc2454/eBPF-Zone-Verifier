//! HashMap-based kptr-tagged pointer classification on the parsed
//! `BtfContext`. Mirrors the raw-vec equivalent in
//! [`super::super::map_defs`] (used at parse time, before BtfContext
//! exists). Both should eventually fold into one — see the refactor
//! notes — but kept distinct for now to preserve baseline.

use crate::parsing::elf::{KptrField, KptrFieldKind};

use super::super::types::*;

impl BtfContext {
    /// HashMap-based reimpl of `classify_kptr_field`. Walks a type chain
    /// of modifiers + TYPE_TAGs around an outer `BTF_KIND_PTR`, picking
    /// up the most-recently-seen kptr tag (kptr / kptr_untrusted / rcu /
    /// percpu_kptr / uptr) on either side of the PTR. Returns
    /// `(kptr-field-kind, pointee-btf-id)` if the chain ends in a typed
    /// pointer carrying a kptr-style tag, else None.
    fn classify_kptr_pointer(&self, field_type_id: u32) -> Option<(KptrFieldKind, u32)> {
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
        let mut kind: Option<KptrFieldKind> = None;
        let mut curr = field_type_id;
        for _ in 0..16 {
            let t = self.types.get(&curr)?;
            match t.kind() {
                BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT => {
                    curr = t.size_or_type;
                }
                BTF_KIND_TYPE_TAG => {
                    if let Some(name) = self.get_string(t.name_off)
                        && let Some(k) = kind_from_tag(name)
                    {
                        kind = Some(k);
                    }
                    curr = t.size_or_type;
                }
                BTF_KIND_PTR => break,
                _ => return None,
            }
        }
        let ptr_t = self.types.get(&curr)?;
        if ptr_t.kind() != BTF_KIND_PTR {
            return None;
        }
        let mut pointee = ptr_t.size_or_type;
        for _ in 0..16 {
            let Some(t) = self.types.get(&pointee) else {
                break;
            };
            match t.kind() {
                BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT => {
                    pointee = t.size_or_type;
                }
                BTF_KIND_TYPE_TAG => {
                    if let Some(name) = self.get_string(t.name_off)
                        && let Some(k) = kind_from_tag(name)
                    {
                        kind = Some(k);
                    }
                    pointee = t.size_or_type;
                }
                _ => break,
            }
        }
        kind.map(|k| (k, pointee))
    }

    /// Walk every kptr-tagged pointer reachable through a map's value
    /// type and return one `KptrField` per hit, with offsets relative
    /// to the value's start. Used by the BTF-driven map_def loader so
    /// `.maps`-section maps carry the same kptr metadata as DATASEC
    /// maps (see [`Self::extract_datasec_kptr_fields`]).
    pub fn extract_value_kptr_fields(&self, value_type_id: u32) -> Vec<KptrField> {
        let mut out = Vec::new();
        self.collect_kptr_fields_at(value_type_id, 0, &mut out, 0);
        out
    }

    /// Walk every kptr-tagged pointer reachable through `type_id` and
    /// emit a `KptrField` at `base_offset + relative_offset` for each.
    /// Recurses into structs/unions (member offsets) and arrays
    /// (per-element stride).
    fn collect_kptr_fields_at(
        &self,
        type_id: u32,
        base_offset: u32,
        out: &mut Vec<KptrField>,
        depth: u32,
    ) {
        if depth > 8 {
            return;
        }
        // Direct kptr pointer — including chains through outer modifiers.
        if let Some((kind, pointee_btf_id)) = self.classify_kptr_pointer(type_id) {
            out.push(KptrField {
                offset: base_offset,
                kind,
                pointee_btf_id,
            });
            return;
        }
        let id = self.peel_modifiers(type_id);
        let Some(t) = self.types.get(&id) else {
            return;
        };
        match t.kind() {
            BTF_KIND_STRUCT | BTF_KIND_UNION => {
                for m in &t.members {
                    let member_byte_off = base_offset + m.offset / 8;
                    self.collect_kptr_fields_at(m.type_id, member_byte_off, out, depth + 1);
                }
            }
            BTF_KIND_ARRAY => {
                let Some(arr) = t.members.first() else {
                    return;
                };
                let elem_type = arr.type_id;
                let nelems = arr.offset;
                let elem_size = self.type_size_bytes(elem_type);
                if elem_size == 0 || nelems == 0 {
                    return;
                }
                for i in 0..nelems {
                    let off = base_offset + i * elem_size;
                    self.collect_kptr_fields_at(elem_type, off, out, depth + 1);
                }
            }
            _ => {}
        }
    }

    /// Extract every kptr-tagged field reachable through a
    /// `BTF_KIND_DATASEC`'s VAR entries. Used by the data-section map
    /// loader (`load_data_section_maps`) so that `private(NAME) static
    /// struct foo __kptr * x` (and nested struct/array variants) carry
    /// the same `kptr_fields` metadata as the explicit `.maps`-section
    /// `struct __cpumask_map_value { struct bpf_cpumask __kptr * cpumask; }`
    /// path. Without this, `bpf_kptr_xchg(&global_mask, …)` rejects with
    /// "Invalid argument type" because `kptr_field_at` finds no field
    /// at the data-section offset.
    pub fn extract_datasec_kptr_fields(&self, datasec_id: u32) -> Vec<KptrField> {
        let mut out = Vec::new();
        for entry in self.datasec_entries(datasec_id) {
            let Some((_name, target_id)) = self.var_info(entry.var_id) else {
                continue;
            };
            self.collect_kptr_fields_at(target_id, entry.offset, &mut out, 0);
        }
        out
    }
}
