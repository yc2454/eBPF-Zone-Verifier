//! Struct/union member resolution at byte offsets, plus the
//! special-field collector used for `bpf_spin_lock` / `bpf_list_head` /
//! `bpf_rb_root` etc. discovery on map values and DATASECs.

use super::super::types::*;

impl BtfContext {
    /// Look up a struct/union member at an exact byte offset and
    /// classify it for the verifier's load-typing path.
    ///
    /// Returns `None` only when no member starts exactly at
    /// `byte_offset` (or the type isn't a struct/union). Otherwise the
    /// `BtfFieldInfo` carries:
    ///   - `name` of the field (for the per-(struct, field) trusted
    ///     allowlist consulted at the load site),
    ///   - `kind` describing how the verifier should type a load or an
    ///     `&base->field` arithmetic.
    ///
    /// Used by `update_load_types` to type loads from `PtrToBtfId{X}` at
    /// known offsets, and by the pointer-arithmetic path to type
    /// interior pointers `&base->field` to embedded sub-structs.
    /// Like `field_at_offset`, but additionally descends through any
    /// NAMED embedded struct/union members whose [start, start+size)
    /// range contains `byte_offset`. The kernel's `btf_struct_access`
    /// walks embedded struct members; programs frequently emit a
    /// single `Load[ptr+N]` for a multi-level field access like
    /// `sock->sk_cgrp_data.cgroup` (offset 664 in tcp_sock,
    /// `sk_cgrp_data` is a named embedded struct, `.cgroup` is at
    /// offset 0 within it).
    ///
    /// Kept distinct from `field_at_offset` because some callers
    /// (kfunc validators on `&task->cpus_mask` etc.) want the OUTER
    /// named member's identity; this variant always returns the leaf.
    pub fn field_at_offset_descend(
        &self,
        struct_id: u32,
        byte_offset: u32,
    ) -> Option<BtfFieldInfo<'_>> {
        // Fast path: exact-offset hit, descend only when needed.
        if let Some(info) = self.field_at_offset(struct_id, byte_offset)
            && !matches!(info.kind, BtfFieldKind::Embedded { .. })
        {
            return Some(info);
        }
        let id = self.peel_modifiers(struct_id);
        let ty = self.types.get(&id)?;
        if !matches!(ty.kind(), BTF_KIND_STRUCT | BTF_KIND_UNION) {
            return None;
        }
        let bit_offset = byte_offset.checked_mul(8)?;
        // Find the member whose [start_bits, start_bits+size_bits)
        // covers bit_offset. Iterate in reverse so a strictly-inner
        // member wins over a same-start outer (matters for
        // anonymous-union ABI patterns where multiple members share
        // offset 0).
        let member = ty.members.iter().rev().find(|m| {
            if m.offset > bit_offset {
                return false;
            }
            let size_bytes = self.type_size_bytes(m.type_id);
            if size_bytes == 0 {
                return m.offset == bit_offset;
            }
            m.offset + size_bytes * 8 > bit_offset
        })?;
        let inner_id = self.peel_modifiers(member.type_id);
        if let Some(inner_ty) = self.types.get(&inner_id)
            && matches!(inner_ty.kind(), BTF_KIND_STRUCT | BTF_KIND_UNION)
        {
            let inner_byte_offset = byte_offset - member.offset / 8;
            if let Some(info) = self.field_at_offset_descend(inner_id, inner_byte_offset) {
                return Some(info);
            }
        }
        None
    }

    pub fn field_at_offset(
        &self,
        struct_id: u32,
        byte_offset: u32,
    ) -> Option<BtfFieldInfo<'_>> {
        let id = self.peel_modifiers(struct_id);
        let ty = self.types.get(&id)?;
        if !matches!(ty.kind(), BTF_KIND_STRUCT | BTF_KIND_UNION) {
            return None;
        }
        let bit_offset = byte_offset.checked_mul(8)?;
        let member = ty.members.iter().find(|m| m.offset == bit_offset)?;
        let field_name = self.get_string(member.name_off).unwrap_or("");

        // Anonymous member at the same offset: descend into the
        // nested struct/union to find a deeper-named field. The kernel
        // UAPI uses this pattern via `__bpf_md_ptr(type, name)`, which
        // wraps `name` in an anonymous union for ABI compatibility (e.g.
        // `sk_reuseport_md.sk`, `bpf_iter__sockmap.sk`). field_at_offset
        // would otherwise stop at the union's Embedded kind and miss
        // the typed pointer member.
        if field_name.is_empty() {
            let inner_id = self.peel_modifiers(member.type_id);
            if let Some(inner_ty) = self.types.get(&inner_id)
                && matches!(inner_ty.kind(), BTF_KIND_STRUCT | BTF_KIND_UNION)
            {
                let inner_byte_offset = byte_offset - (bit_offset / 8);
                if let Some(info) = self.field_at_offset(inner_id, inner_byte_offset) {
                    return Some(info);
                }
            }
        }

        // Walk the member's type chain, recording any BTF_KIND_TYPE_TAG
        // along the way (the kernel's `__rcu`, `__percpu`, `__user`
        // attributes lower to TYPE_TAG entries the BPF backend
        // preserves). The chain's terminal kind tells us whether this
        // is a pointer field, an embedded struct, or a scalar.
        let mut cur = member.type_id;
        let mut tags: Vec<&'static str> = Vec::new();
        for _ in 0..16 {
            let Some(t) = self.types.get(&cur) else { break };
            match t.kind() {
                BTF_KIND_TYPE_TAG => {
                    if let Some(n) = self.get_string(t.name_off) {
                        // Tag names are short, well-known kernel
                        // strings (`rcu`, `percpu`, `user`, …); leak
                        // once so the consumer can compare with `==`.
                        tags.push(Box::leak(n.to_string().into_boxed_str()));
                    }
                    cur = t.size_or_type;
                }
                BTF_KIND_TYPEDEF
                | BTF_KIND_CONST
                | BTF_KIND_VOLATILE
                | BTF_KIND_RESTRICT => {
                    cur = t.size_or_type;
                }
                BTF_KIND_PTR => {
                    // Walk through any TYPE_TAG / TYPEDEF / CONST /
                    // VOLATILE / RESTRICT on the pointee so we recover
                    // a STRUCT/UNION's name when the BTF chain is e.g.
                    // `PTR -> TYPE_TAG("rcu") -> STRUCT sock` (kernel
                    // emits `__rcu`-tagged pointer fields this way).
                    // Tags collected here also propagate up to `tags`
                    // so the load site can lift them into PtrFlags.
                    let mut p = t.size_or_type;
                    let mut pointee_name: Option<String> = None;
                    for _ in 0..16 {
                        let Some(pt) = self.types.get(&p) else { break };
                        match pt.kind() {
                            BTF_KIND_TYPE_TAG => {
                                if let Some(n) = self.get_string(pt.name_off) {
                                    tags.push(Box::leak(n.to_string().into_boxed_str()));
                                }
                                p = pt.size_or_type;
                            }
                            BTF_KIND_TYPEDEF
                            | BTF_KIND_CONST
                            | BTF_KIND_VOLATILE
                            | BTF_KIND_RESTRICT => {
                                p = pt.size_or_type;
                            }
                            // STRUCT/UNION definitions and FWD
                            // declarations both name the pointee. FWD
                            // is what vmlinux BTF emits for kernel
                            // structs whose layout the BPF prog
                            // doesn't reference (e.g. `struct sock`
                            // is FWD-only when the program just
                            // passes the pointer through). We still
                            // get a usable type_name for kfunc
                            // matching.
                            BTF_KIND_STRUCT | BTF_KIND_UNION | BTF_KIND_FWD => {
                                pointee_name =
                                    self.get_string(pt.name_off).map(|s| s.to_string());
                                break;
                            }
                            _ => break,
                        }
                    }
                    return Some(BtfFieldInfo {
                        name: field_name,
                        kind: BtfFieldKind::Pointer { pointee_name, tags },
                    });
                }
                BTF_KIND_STRUCT | BTF_KIND_UNION => {
                    let name = self.get_string(t.name_off).map(|s| s.to_string());
                    return Some(BtfFieldInfo {
                        name: field_name,
                        kind: BtfFieldKind::Embedded { type_name: name, tags },
                    });
                }
                BTF_KIND_INT | BTF_KIND_ENUM | BTF_KIND_ENUM64 | BTF_KIND_FLOAT => {
                    return Some(BtfFieldInfo {
                        name: field_name,
                        kind: BtfFieldKind::Scalar,
                    });
                }
                BTF_KIND_ARRAY => {
                    return Some(BtfFieldInfo {
                        name: field_name,
                        kind: BtfFieldKind::Other,
                    });
                }
                _ => break,
            }
        }
        Some(BtfFieldInfo {
            name: field_name,
            kind: BtfFieldKind::Other,
        })
    }

    /// Looks up a struct member at a specific byte offset.
    /// Returns the Type ID of that member if found.
    pub fn resolve_field_type_id(&self, struct_id: u32, byte_offset: u32) -> Option<u32> {
        let bit_offset = byte_offset * 8;

        if let Some(ty) = self.types.get(&struct_id) {
            match ty.kind() {
                BTF_KIND_STRUCT | BTF_KIND_UNION => {
                    for member in &ty.members {
                        // Exact match for now
                        if member.offset == bit_offset {
                            return Some(member.type_id);
                        }
                    }
                }
                // Handle typedefs/const/volatile by peeling the wrapper
                BTF_KIND_TYPEDEF | BTF_KIND_VOLATILE | BTF_KIND_CONST | BTF_KIND_RESTRICT => {
                    return self.resolve_field_type_id(ty.size_or_type, byte_offset);
                }
                _ => {}
            }
        }
        None
    }

    /// Find the struct/union member that begins exactly at `byte_offset`.
    /// Returns the member's declared name. Used by the struct_ops binding
    /// resolver to translate a relocation offset into a method name.
    pub fn member_name_at_offset(&self, struct_id: u32, byte_offset: u32) -> Option<&str> {
        let id = self.peel_modifiers(struct_id);
        let ty = self.types.get(&id)?;
        if !matches!(ty.kind(), BTF_KIND_STRUCT | BTF_KIND_UNION) {
            return None;
        }
        let bit = byte_offset * 8;
        let m = ty.members.iter().find(|m| m.offset == bit)?;
        self.get_string(m.name_off)
    }

    /// Find all special fields in a struct type. Also supports DATASEC
    /// types (used for synthetic data-section maps like `.bss.<name>`):
    /// each VAR's resolved struct name is checked against
    /// [`SpecialFieldKind::from_type_name`], with the offset taken from
    /// the DATASEC entry (already in bytes).
    pub fn find_special_fields(&self, type_id: u32) -> Vec<SpecialField> {
        if let Some(cached) = self
            .special_fields_cache
            .lock()
            .unwrap()
            .get(&type_id)
        {
            return cached.clone();
        }
        let fields = self.find_special_fields_uncached(type_id);
        self.special_fields_cache
            .lock()
            .unwrap()
            .insert(type_id, fields.clone());
        fields
    }

    fn find_special_fields_uncached(&self, type_id: u32) -> Vec<SpecialField> {
        let mut fields = Vec::new();

        let Some(ty) = self.types.get(&type_id) else {
            return fields;
        };

        // DATASEC: each member is a VAR pointing at a struct/typedef.
        // The kernel treats `.bss.<name>` as a single map value; each VAR
        // declared in that section becomes a special field at its DATASEC
        // offset if the VAR's type is one of the recognized special types
        // (bpf_spin_lock, bpf_rb_root, …). Used by `private(name)`-style
        // globals in tests like `refcounted_kptr.c`.
        if ty.kind() == BTF_KIND_DATASEC {
            for entry in self.datasec_entries(type_id) {
                let Some((_var_name, target_id)) = self.var_info(entry.var_id) else {
                    continue;
                };
                // `__contains` decl_tag is attached to the VAR (clang
                // routes the variable-decl attribute there); inherited
                // by every array element / nested-struct walk below.
                let contains = self
                    .decl_tags_for(entry.var_id)
                    .find_map(|t| self.parse_contains_tag(&t.name));
                self.collect_special_fields_at(
                    target_id,
                    entry.offset,
                    contains.as_ref(),
                    &mut fields,
                    0,
                );
            }
            return fields;
        }

        for (member_idx, member) in ty.members.iter().enumerate() {
            let Some(member_type) = self.types.get(&member.type_id) else {
                continue;
            };
            let Some(name) = self.get_string(member_type.name_off) else {
                continue;
            };

            if let Some(kind) = SpecialFieldKind::from_type_name(name) {
                // `__contains` decl_tags on a struct member (e.g.
                // `struct map_value { ...; struct bpf_list_head head
                // __contains(foo, node2); };`) attach to the parent
                // struct's btf_id with `component_idx == member_idx`.
                let contains = self
                    .decl_tags_for(type_id)
                    .filter(|t| t.component_idx == member_idx as i32)
                    .find_map(|t| self.parse_contains_tag(&t.name));
                fields.push(SpecialField {
                    kind,
                    offset: member.offset / 8,
                    size: member_type.size_or_type,
                    contains,
                });
            }
        }

        fields
    }

    /// Recursively walk a BTF type at `base_offset`, emitting one
    /// `SpecialField` per recognized special-field struct
    /// (`bpf_spin_lock`, `bpf_list_head`, `bpf_rb_root`, ...) reached
    /// at any depth.
    ///
    /// Drives the DATASEC scan in `find_special_fields`: tolerates
    /// nested struct (`private(D) struct head_nested ghead_nested;`
    /// where `head_nested.inner.{lock,head}` carry the special
    /// fields) and array layouts (`bpf_list_head ghead_array[N]`).
    /// `inherited_contains` carries the VAR's `__contains` decl_tag
    /// down through array elements; for nested STRUCT members the
    /// per-member decl_tag wins (matches the kernel's
    /// component_idx-keyed attachment).
    fn collect_special_fields_at(
        &self,
        type_id: u32,
        base_offset: u32,
        inherited_contains: Option<&ContainsInfo>,
        out: &mut Vec<SpecialField>,
        depth: u32,
    ) {
        // Cap recursion as a defensive bound — graph nodes never need
        // more than 2-3 levels (DATASEC → struct → inner struct).
        if depth > 8 {
            return;
        }
        let resolved_id = self.peel_modifiers(type_id);
        let Some(ty) = self.types.get(&resolved_id) else {
            return;
        };

        // Recognized special-field struct (terminal).
        if let Some(name) = self.get_string(ty.name_off)
            && let Some(kind) = SpecialFieldKind::from_type_name(name)
        {
            out.push(SpecialField {
                kind,
                offset: base_offset,
                size: ty.size_or_type,
                contains: inherited_contains.cloned(),
            });
            return;
        }

        match ty.kind() {
            BTF_KIND_ARRAY => {
                let Some(arr) = ty.members.first() else { return };
                let elem_id = self.peel_modifiers(arr.type_id);
                let nelems = arr.offset;
                let Some(elem_ty) = self.types.get(&elem_id) else { return };
                let elem_size = elem_ty.size_or_type;
                if elem_size == 0 || nelems == 0 {
                    return;
                }
                for i in 0..nelems {
                    self.collect_special_fields_at(
                        elem_id,
                        base_offset + i * elem_size,
                        inherited_contains,
                        out,
                        depth + 1,
                    );
                }
            }
            BTF_KIND_STRUCT | BTF_KIND_UNION => {
                for (member_idx, member) in ty.members.iter().enumerate() {
                    let member_byte_off = base_offset + member.offset / 8;
                    // Per-member decl_tag overrides the VAR-inherited
                    // one when present (struct member's __contains).
                    let member_contains = self
                        .decl_tags_for(resolved_id)
                        .filter(|t| t.component_idx == member_idx as i32)
                        .find_map(|t| self.parse_contains_tag(&t.name));
                    let next_contains = member_contains
                        .as_ref()
                        .or(inherited_contains);
                    let next_contains_clone = next_contains.cloned();
                    self.collect_special_fields_at(
                        member.type_id,
                        member_byte_off,
                        next_contains_clone.as_ref(),
                        out,
                        depth + 1,
                    );
                }
            }
            _ => {}
        }
    }

    /// Parse a `"contains:<struct>:<member>"` decl_tag name into a
    /// resolved [`ContainsInfo`]. Returns `None` if the prefix doesn't
    /// match, the named struct isn't in BTF, or the member doesn't
    /// exist in that struct. The member must be a `bpf_list_node` /
    /// `bpf_rb_node` field; we don't enforce that here (the kernel
    /// does), but the offset reported is the member's byte offset.
    fn parse_contains_tag(&self, tag: &str) -> Option<ContainsInfo> {
        let body = tag.strip_prefix("contains:")?;
        let (struct_name, member_name) = body.split_once(':')?;
        // The named struct may have been stripped by clang when it is
        // referenced only through the decl_tag string and never used as
        // a value type (rbtree_btf_fail__add_wrong_type.c). Preserve the
        // name regardless; node_offset becomes None and the offset gate
        // is skipped, leaving the struct-name comparison as the only
        // structural check.
        let node_offset = self
            .find_struct_by_name(struct_name)
            .and_then(|sid| self.types.get(&sid))
            .and_then(|ty| {
                ty.members
                    .iter()
                    .find(|m| self.get_string(m.name_off) == Some(member_name))
            })
            .map(|m| m.offset / 8);
        Some(ContainsInfo {
            struct_name: struct_name.to_string(),
            node_offset,
        })
    }
}
