#![allow(dead_code)]

// src/btf.rs
use crate::parsing::elf::{BpfMapDef, KptrField, KptrFieldKind};
use log::info;
use std::collections::HashMap;
use std::convert::TryInto;

const BTF_MAGIC: u16 = 0xEB9F;

// Kinds
pub const BTF_KIND_INT: u8 = 1;
pub const BTF_KIND_PTR: u8 = 2;
pub const BTF_KIND_ARRAY: u8 = 3;
pub const BTF_KIND_STRUCT: u8 = 4;
pub const BTF_KIND_UNION: u8 = 5;
pub const BTF_KIND_ENUM: u8 = 6;
pub const BTF_KIND_FWD: u8 = 7;
pub const BTF_KIND_TYPEDEF: u8 = 8;
pub const BTF_KIND_VOLATILE: u8 = 9;
pub const BTF_KIND_CONST: u8 = 10;
pub const BTF_KIND_RESTRICT: u8 = 11;
pub const BTF_KIND_FUNC: u8 = 12;
pub const BTF_KIND_FUNC_PROTO: u8 = 13;
pub const BTF_KIND_VAR: u8 = 14;
pub const BTF_KIND_DATASEC: u8 = 15;
pub const BTF_KIND_FLOAT: u8 = 16;
pub const BTF_KIND_DECL_TAG: u8 = 17;
pub const BTF_KIND_TYPE_TAG: u8 = 18;
pub const BTF_KIND_ENUM64: u8 = 19;

// -----------------------------------------------------------------------------
// PART 1: Public Interface for Analyzer (The "Context" view)
// -----------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialFieldKind {
    SpinLock,
    Timer,
    ListHead,
    ListNode,
    RbRoot,
    RbNode,
    Refcount,
    // Future types...
}

#[derive(Debug, Clone)]
pub struct SpecialField {
    pub kind: SpecialFieldKind,
    pub offset: u32, // byte offset
    pub size: u32,
}

impl SpecialFieldKind {
    fn from_type_name(name: &str) -> Option<Self> {
        match name {
            "bpf_spin_lock" => Some(Self::SpinLock),
            "bpf_timer" => Some(Self::Timer),
            "bpf_list_head" => Some(Self::ListHead),
            "bpf_list_node" => Some(Self::ListNode),
            "bpf_rb_root" => Some(Self::RbRoot),
            "bpf_rb_node" => Some(Self::RbNode),
            "bpf_refcount" => Some(Self::Refcount),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BtfMember {
    pub name_off: u32,
    pub type_id: u32,
    pub offset: u32, // Offset in bits
}

#[derive(Debug, Clone)]
pub struct BtfType {
    pub id: u32,
    pub name_off: u32,
    pub info: u32,
    pub size_or_type: u32,
    pub members: Vec<BtfMember>,
}

impl BtfType {
    pub fn kind(&self) -> u8 {
        ((self.info >> 24) & 0x1f) as u8
    }
}

/// A BTF_KIND_DECL_TAG: an annotation attached to a type (or a specific struct
/// member / function argument). Used by the kernel to register kfuncs, mark
/// map-value fields as `__kptr`/`__rcu`/`__uptr`, and carry CO-RE hints.
#[derive(Debug, Clone)]
pub struct DeclTag {
    pub name: String,
    pub target_type_id: u32,
    /// -1 for whole-type tags; otherwise the 0-based member/argument index.
    pub component_idx: i32,
}

#[derive(Clone, Default, Debug)]
pub struct BtfContext {
    pub types: HashMap<u32, BtfType>,
    pub strings: Vec<u8>,
    /// All DECL_TAGs parsed from the BTF section. Populated by `parse_btf`.
    decl_tags: Vec<DeclTag>,
    /// Index of kfunc FUNC types by name: name -> FUNC btf_id. A FUNC is
    /// considered a kfunc when it carries a DECL_TAG whose name is "kfunc"
    /// or "bpf_kfunc".
    kfuncs: HashMap<String, u32>,
}

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
        }
    }

    /// All DECL_TAGs attached to `target_type_id` (whole-type or any member).
    pub fn decl_tags_for(&self, target_type_id: u32) -> impl Iterator<Item = &DeclTag> {
        self.decl_tags
            .iter()
            .filter(move |t| t.target_type_id == target_type_id)
    }

    /// Returns the FUNC btf_id of a registered kfunc by name, if any.
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
    /// `__rcu`, `__percpu`, etc.
    pub fn type_tag_name(&self, type_id: u32) -> Option<(&str, u32)> {
        let ty = self.types.get(&type_id)?;
        if ty.kind() != BTF_KIND_TYPE_TAG {
            return None;
        }
        let name = self.get_string(ty.name_off)?;
        Some((name, ty.size_or_type))
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

    /// Helper to check if a type ID effectively resolves to a Pointer.
    pub fn is_pointer(&self, mut type_id: u32) -> bool {
        let mut depth = 0;
        while let Some(ty) = self.types.get(&type_id) {
            let kind = ty.kind();
            match kind {
                BTF_KIND_PTR => return true,
                BTF_KIND_TYPEDEF | BTF_KIND_VOLATILE | BTF_KIND_CONST | BTF_KIND_RESTRICT => {
                    type_id = ty.size_or_type;
                }
                _ => return false,
            }
            depth += 1;
            if depth > 10 {
                break;
            } // Prevent loops
        }
        false
    }

    /// Find all special fields in a struct type
    pub fn find_special_fields(&self, type_id: u32) -> Vec<SpecialField> {
        let mut fields = Vec::new();

        let Some(ty) = self.types.get(&type_id) else {
            return fields;
        };

        for member in &ty.members {
            let Some(member_type) = self.types.get(&member.type_id) else {
                continue;
            };
            let Some(name) = self.get_string(member_type.name_off) else {
                continue;
            };

            if let Some(kind) = SpecialFieldKind::from_type_name(name) {
                fields.push(SpecialField {
                    kind,
                    offset: member.offset / 8,
                    size: member_type.size_or_type,
                });
            }
        }

        fields
    }

    /// Public read of an interned BTF string by its byte offset into the
    /// string blob. Returns the C-string up to the first NUL.
    pub fn read_string(&self, offset: u32) -> Option<&str> {
        self.get_string(offset)
    }

    fn get_string(&self, offset: u32) -> Option<&str> {
        let start = offset as usize;
        if start >= self.strings.len() {
            return None;
        }
        let end = self.strings[start..].iter().position(|&b| b == 0)? + start;
        std::str::from_utf8(&self.strings[start..end]).ok()
    }

    /// Find a STRUCT (or UNION) BTF type by its declared name. Linear
    /// scan — only called once per struct_ops program at entry-state
    /// setup, so the cost is irrelevant. Returns the BTF type id.
    pub fn find_struct_by_name(&self, name: &str) -> Option<u32> {
        for ty in self.types.values() {
            if !matches!(ty.kind(), BTF_KIND_STRUCT | BTF_KIND_UNION) {
                continue;
            }
            if self.get_string(ty.name_off) == Some(name) {
                return Some(ty.id);
            }
        }
        None
    }

    /// Peel TYPEDEF / CONST / VOLATILE / RESTRICT wrappers and return the
    /// underlying type id. Stops on the first non-wrapper kind. Bounded
    /// to 16 hops as a defensive cycle guard.
    pub fn peel_modifiers(&self, mut type_id: u32) -> u32 {
        for _ in 0..16 {
            let Some(ty) = self.types.get(&type_id) else {
                return type_id;
            };
            match ty.kind() {
                BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT => {
                    type_id = ty.size_or_type;
                }
                _ => return type_id,
            }
        }
        type_id
    }

    /// If `type_id` (after peeling modifiers) is a `PTR -> X` chain,
    /// return `X` (also peeled). Otherwise None.
    pub fn pointee(&self, type_id: u32) -> Option<u32> {
        let id = self.peel_modifiers(type_id);
        let ty = self.types.get(&id)?;
        if ty.kind() != BTF_KIND_PTR {
            return None;
        }
        Some(self.peel_modifiers(ty.size_or_type))
    }

    /// Return the declared name of a STRUCT / UNION type, peeling any
    /// modifier wrappers first. Returns None for unnamed types or
    /// non-struct kinds.
    pub fn struct_name(&self, type_id: u32) -> Option<&str> {
        let id = self.peel_modifiers(type_id);
        let ty = self.types.get(&id)?;
        if !matches!(ty.kind(), BTF_KIND_STRUCT | BTF_KIND_UNION) {
            return None;
        }
        self.get_string(ty.name_off)
    }

    /// Resolve the parameter list of a single struct_ops member.
    ///
    /// Walks `struct <struct_name> { ... <member_name>; ... }`, finds the
    /// member, peels its `PTR -> FUNC_PROTO` chain, and returns one
    /// `StructOpsArg` per parameter.
    ///
    /// Returns None if any of the following are true:
    ///   * the struct isn't in BTF,
    ///   * no member matches `member_name`,
    ///   * the member doesn't resolve to a `PTR -> FUNC_PROTO`.
    ///
    /// Why a method-by-method resolver instead of pre-computing all of
    /// them: only programs whose section is `SEC("struct_ops/...")` need
    /// this, and there are few of them per ELF — the linear cost is
    /// negligible against the verifier itself.
    pub fn resolve_struct_ops_method(
        &self,
        struct_name: &str,
        member_name: &str,
    ) -> Option<Vec<StructOpsArg>> {
        let struct_id = self.find_struct_by_name(struct_name)?;
        let struct_ty = self.types.get(&struct_id)?;

        let member = struct_ty
            .members
            .iter()
            .find(|m| self.get_string(m.name_off) == Some(member_name))?;

        // Member type is `PTR -> FUNC_PROTO`. Peel the PTR.
        let func_proto_id = self.pointee(member.type_id)?;
        let func_proto = self.types.get(&func_proto_id)?;
        if func_proto.kind() != BTF_KIND_FUNC_PROTO {
            return None;
        }

        let args = func_proto
            .members
            .iter()
            .map(|p| self.classify_param(p.type_id))
            .collect();
        Some(args)
    }

    /// Does the named struct_ops member return void? Returns None if the
    /// member or its FUNC_PROTO can't be resolved. The kernel verifier
    /// relaxes the "R0 must be initialized at exit" check for void
    /// return types, so the runner needs to know this to type the exit
    /// state correctly.
    pub fn struct_ops_method_returns_void(
        &self,
        struct_name: &str,
        member_name: &str,
    ) -> Option<bool> {
        let struct_id = self.find_struct_by_name(struct_name)?;
        let struct_ty = self.types.get(&struct_id)?;
        let member = struct_ty
            .members
            .iter()
            .find(|m| self.get_string(m.name_off) == Some(member_name))?;
        let proto_id = self.pointee(member.type_id)?;
        let proto = self.types.get(&proto_id)?;
        if proto.kind() != BTF_KIND_FUNC_PROTO {
            return None;
        }
        // BTF encodes void return as type id 0.
        Some(proto.size_or_type == 0)
    }

    /// Classification of a global-subprog argument from BTF, used to
    /// emit the kernel's "Caller passes invalid args" / "FWD size
    /// cannot be determined" / "expected ..." errors and to seed the
    /// callee's R1..R5 with declared types when verifying its body.
    ///
    /// Distinct from `StructOpsArg`: struct_ops's TrustedPtr is a
    /// kernel-typed pointer, whereas a global subprog's pointer arg is
    /// the kernel verifier's `PTR_TO_MEM | PTR_MAYBE_NULL` — bounded
    /// by the pointee's BTF size, callee must null-check.
    pub fn resolve_global_func_args(&self, func_name: &str) -> Option<Vec<GlobalFuncArg>> {
        let func_ty = self.types.values().find(|ty| {
            ty.kind() == BTF_KIND_FUNC && self.get_string(ty.name_off) == Some(func_name)
        })?;
        let proto = self.types.get(&func_ty.size_or_type)?;
        if proto.kind() != BTF_KIND_FUNC_PROTO {
            return None;
        }
        Some(
            proto
                .members
                .iter()
                .map(|p| self.classify_global_func_arg(p.type_id))
                .collect(),
        )
    }

    fn classify_global_func_arg(&self, type_id: u32) -> GlobalFuncArg {
        let id = self.peel_modifiers(type_id);
        let Some(ty) = self.types.get(&id) else {
            return GlobalFuncArg::Scalar;
        };
        match ty.kind() {
            BTF_KIND_INT | BTF_KIND_ENUM | BTF_KIND_ENUM64 | BTF_KIND_FLOAT => {
                GlobalFuncArg::Scalar
            }
            BTF_KIND_PTR => {
                let pointee_id = self.peel_modifiers(ty.size_or_type);
                let Some(pointee) = self.types.get(&pointee_id) else {
                    // Unresolved pointee — typically `void *`, also
                    // possible for opaque kernel types we don't have
                    // BTF for. The kernel relies on DECL_TAG
                    // annotations (`__arg_ctx`, `__arg_nullable`,
                    // ...) to refine; without those we can't
                    // distinguish ctx-typed from mem-typed `void *`.
                    // Be permissive at the caller boundary: a
                    // PermissivePtr accepts ctx, any mem pointer, or
                    // NULL. Body verification loses some checks but
                    // we don't false-reject legitimate `void *ctx`
                    // global subprogs (test_global_func_ctx_args).
                    return GlobalFuncArg::PermissivePtr;
                };
                match pointee.kind() {
                    // FWD: struct declared but not defined — the kernel
                    // can't determine its size, which is what test
                    // global_func14 asserts.
                    BTF_KIND_FWD => GlobalFuncArg::PtrToFwd {
                        name: self.get_string(pointee.name_off).unwrap_or("?").to_string(),
                    },
                    BTF_KIND_STRUCT | BTF_KIND_UNION => {
                        let pname = self.get_string(pointee.name_off).unwrap_or("");
                        if is_ctx_struct_name(pname) {
                            GlobalFuncArg::PtrToCtx
                        } else {
                            GlobalFuncArg::PtrToMem {
                                mem_size: pointee.size_or_type,
                            }
                        }
                    }
                    BTF_KIND_INT | BTF_KIND_ENUM | BTF_KIND_ENUM64 | BTF_KIND_FLOAT => {
                        GlobalFuncArg::PtrToMem {
                            mem_size: pointee.size_or_type,
                        }
                    }
                    _ => GlobalFuncArg::PtrToMem { mem_size: 0 },
                }
            }
            _ => GlobalFuncArg::Scalar,
        }
    }

    /// Returns true iff a BTF_KIND_FUNC by this name has GLOBAL linkage
    /// (vs STATIC or EXTERN). Encoded in FUNC.info bits 0..16
    /// (`BTF_FUNC_GLOBAL = 1`). The kernel verifies global subprogs
    /// independently against their declared signature; static subprogs
    /// inherit the caller's concrete types.
    pub fn is_global_func(&self, func_name: &str) -> bool {
        let Some(func_ty) = self.types.values().find(|ty| {
            ty.kind() == BTF_KIND_FUNC && self.get_string(ty.name_off) == Some(func_name)
        }) else {
            return false;
        };
        (func_ty.info & 0xffff) == 1
    }

    /// True if the named function's declared return type is `void`
    /// (BTF type id 0 in the FUNC_PROTO `size_or_type`). Used to
    /// reject global subprogs declared with a void return —
    /// "function 'foo' doesn't return scalar".
    pub fn func_returns_void(&self, func_name: &str) -> bool {
        let Some(func_ty) = self.types.values().find(|ty| {
            ty.kind() == BTF_KIND_FUNC && self.get_string(ty.name_off) == Some(func_name)
        }) else {
            return false;
        };
        let Some(proto) = self.types.get(&func_ty.size_or_type) else {
            return false;
        };
        proto.kind() == BTF_KIND_FUNC_PROTO && proto.size_or_type == 0
    }

    /// Resolve a subprog's parameter list directly from its BTF FUNC entry.
    ///
    /// clang -target bpf emits a `BTF_KIND_FUNC` for every defined function
    /// in the source, naming it and pointing at the FUNC_PROTO that captured
    /// its declared signature. For struct_ops method implementations the
    /// declared signature matches the ops-struct member's function pointer
    /// type, so this gives us the same answer as walking
    /// `<ops_struct>.<member>` — without needing to know which member the
    /// subprog is bound to. The binding lives in the `.struct_ops`
    /// relocation table; resolving via the FUNC entry sidesteps that
    /// dependency entirely.
    ///
    /// Returns None if no FUNC by that name exists or it doesn't point at
    /// a FUNC_PROTO.
    pub fn resolve_func_args(&self, func_name: &str) -> Option<Vec<StructOpsArg>> {
        let func_ty = self.types.values().find(|ty| {
            ty.kind() == BTF_KIND_FUNC && self.get_string(ty.name_off) == Some(func_name)
        })?;
        // FUNC.size_or_type is the FUNC_PROTO btf_id.
        let proto = self.types.get(&func_ty.size_or_type)?;
        if proto.kind() != BTF_KIND_FUNC_PROTO {
            return None;
        }
        Some(
            proto
                .members
                .iter()
                .map(|p| self.classify_param(p.type_id))
                .collect(),
        )
    }

    /// Find a BTF_KIND_DATASEC by section name (e.g. ".struct_ops",
    /// ".struct_ops.link", ".rodata", ".bss"). Returns the BTF type id.
    pub fn find_datasec(&self, section_name: &str) -> Option<u32> {
        for ty in self.types.values() {
            if ty.kind() != BTF_KIND_DATASEC {
                continue;
            }
            if self.get_string(ty.name_off) == Some(section_name) {
                return Some(ty.id);
            }
        }
        None
    }

    /// Iterate the variables of a DATASEC. Returns an empty iterator if the
    /// id isn't a DATASEC.
    pub fn datasec_entries(&self, datasec_id: u32) -> Vec<DatasecEntry> {
        let Some(ty) = self.types.get(&datasec_id) else {
            return Vec::new();
        };
        if ty.kind() != BTF_KIND_DATASEC {
            return Vec::new();
        }
        ty.members
            .iter()
            .map(|m| DatasecEntry {
                var_id: m.type_id,
                offset: m.offset,
                size: m.name_off, // we packed size into name_off — see parse_btf
            })
            .collect()
    }

    /// Resolve a BTF_KIND_VAR into `(var_name, target_type_id)`. Returns None
    /// if the id isn't a VAR.
    pub fn var_info(&self, var_id: u32) -> Option<(&str, u32)> {
        let ty = self.types.get(&var_id)?;
        if ty.kind() != BTF_KIND_VAR {
            return None;
        }
        let name = self.get_string(ty.name_off)?;
        Some((name, ty.size_or_type))
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

    fn classify_param(&self, type_id: u32) -> StructOpsArg {
        let id = self.peel_modifiers(type_id);
        let Some(ty) = self.types.get(&id) else {
            return StructOpsArg::Scalar;
        };
        match ty.kind() {
            BTF_KIND_PTR => match self.struct_name(ty.size_or_type) {
                Some(name) => StructOpsArg::TrustedPtr(name.to_string()),
                None => StructOpsArg::OpaquePtr,
            },
            BTF_KIND_INT | BTF_KIND_ENUM | BTF_KIND_ENUM64 | BTF_KIND_FLOAT => {
                StructOpsArg::Scalar
            }
            _ => StructOpsArg::Scalar,
        }
    }
}

/// One variable inside a BTF_KIND_DATASEC.
#[derive(Debug, Clone)]
pub struct DatasecEntry {
    /// BTF type id of the variable (BTF_KIND_VAR). Use
    /// [`BtfContext::var_info`] to resolve it to `(name, target_type_id)`.
    pub var_id: u32,
    /// Byte offset of the variable within the section.
    pub offset: u32,
    /// Size in bytes of the variable.
    pub size: u32,
}

/// One resolved parameter of a struct_ops member's FUNC_PROTO.
///
/// `Scalar` covers integers, enums, floats — anything that lowers
/// to a register-width value the verifier treats as a scalar.
///
/// `TrustedPtr(name)` is a pointer to a named struct/union; the name
/// is the BTF type name (e.g. "sock", "tcp_sock", "task_struct").
/// The W6.4a entry-state plumbing maps this to
/// `RegType::PtrToBtfId { type_name, flags: TRUSTED }` after interning
/// through a small static table of well-known kernel struct names.
///
/// `OpaquePtr` is a pointer to anything else — function pointers,
/// pointers to primitives, void *. Caller decides whether to widen
/// to a generic UNTRUSTED PtrToBtfId or scalar.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StructOpsArg {
    Scalar,
    TrustedPtr(String),
    OpaquePtr,
}

/// Classification of one parameter in a global subprog's BTF FUNC_PROTO.
/// Drives the W6.5 "global function arg validation" path: caller-side
/// type matching, callee-side R1..R5 entry-state seeding, and the
/// `FWD size cannot be determined` rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GlobalFuncArg {
    /// Integer / enum / float. Caller must pass a scalar; callee
    /// receives a generic `ScalarValue` at entry.
    Scalar,
    /// Pointer to a sized struct/union/scalar with byte size `mem_size`.
    /// Caller may pass any compatible memory pointer; callee receives
    /// `PtrToAllocMemOrNull { mem_size }` and must null-check before
    /// dereferencing — this is what produces the kernel's
    /// "invalid mem access 'mem_or_null'" rejection inside the callee.
    PtrToMem { mem_size: u32 },
    /// Pointer to a recognized BPF context struct (`__sk_buff`,
    /// `xdp_md`, `pt_regs`, ...). Caller must pass `PtrToCtx`; the
    /// callee receives the same. Distinct from `PtrToMem` because the
    /// kernel allows ctx-typed global subprog args without
    /// MAYBE_NULL semantics — the ctx is always non-null.
    PtrToCtx,
    /// Pointer to a forward-declared struct (`struct S;` with no
    /// definition). Size is unknown to BTF, so the kernel rejects
    /// with "reference type('FWD S') size cannot be determined".
    PtrToFwd { name: String },
    /// `void *` or other unresolved pointer target — typically used
    /// with kernel `__arg_ctx` / `__arg_nullable` DECL_TAG
    /// annotations we don't yet parse. Caller accepts any pointer
    /// kind plus NULL; callee receives PtrToCtx (the most common
    /// real meaning) so body access is liberal but not pointer-leaky.
    PermissivePtr,
}

/// Names of struct types the kernel treats as a BPF program context
/// when used as a pointer arg of a global subprog. Drives the
/// caller-side "PtrToCtx is admissible" check in W6.5. Mirrors the
/// kernel's per-prog-type ctx struct allowlist (kept loose: any
/// recognized name is accepted regardless of the calling prog kind —
/// a tighter check would require per-prog-type plumbing we defer).
fn is_ctx_struct_name(name: &str) -> bool {
    matches!(
        name,
        "__sk_buff"
            | "xdp_md"
            | "pt_regs"
            | "bpf_user_pt_regs_t"
            | "bpf_perf_event_data"
            | "bpf_raw_tracepoint_args"
            | "bpf_sock"
            | "bpf_sock_addr"
            | "bpf_sock_ops"
            | "bpf_sysctl"
            | "sk_msg_md"
            | "sk_reuseport_md"
            | "bpf_sockopt"
            | "bpf_sk_lookup"
    )
}

/// Parses the .BTF section into a structured Context for analysis
pub fn parse_btf(bytes: &[u8]) -> Result<BtfContext, String> {
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

    let strings = bytes[str_start..str_end].to_vec();
    let mut types = HashMap::new();
    let mut decl_tags = Vec::new();
    let mut cursor = type_start;
    let mut type_id = 1;

    while cursor < type_end {
        if cursor + 12 > type_end {
            break;
        }

        let name_off = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
        let info = u32::from_le_bytes(bytes[cursor + 4..cursor + 8].try_into().unwrap());
        let size_or_type = u32::from_le_bytes(bytes[cursor + 8..cursor + 12].try_into().unwrap());
        cursor += 12;

        let kind = ((info >> 24) & 0x1f) as u8;
        let vlen = (info & 0xffff) as usize;
        let mut members = Vec::new();

        // Extract extra data based on Kind
        match kind {
            BTF_KIND_STRUCT | BTF_KIND_UNION => {
                for _ in 0..vlen {
                    if cursor + 12 > type_end {
                        break;
                    }
                    let m_name = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
                    let m_type =
                        u32::from_le_bytes(bytes[cursor + 4..cursor + 8].try_into().unwrap());
                    let m_off =
                        u32::from_le_bytes(bytes[cursor + 8..cursor + 12].try_into().unwrap());
                    cursor += 12;
                    members.push(BtfMember {
                        name_off: m_name,
                        type_id: m_type,
                        offset: m_off,
                    });
                }
            }
            BTF_KIND_INT => {
                cursor += 4;
            }
            BTF_KIND_ARRAY => {
                cursor += 12;
            }
            BTF_KIND_VAR => {
                // VAR header carries the var's name (in `name_off`) and the
                // var's BTF type id (in `size_or_type`); the trailing 4 bytes
                // are linkage (BTF_VAR_STATIC / GLOBAL_ALLOCATED / EXTERN),
                // which we don't currently consume.
                cursor += 4;
            }
            BTF_KIND_DATASEC => {
                // Each entry is `struct btf_var_secinfo { u32 type; u32 offset;
                // u32 size }` — 12 bytes. Stash into `members` reusing the
                // existing slot: type_id = secinfo.type, offset = byte offset
                // within the section, name_off = secinfo.size (we repurpose
                // the unused name slot to carry the size — DATASEC entries
                // are unnamed in BTF, so name_off would otherwise be 0).
                // Callers use the helper `datasec_entries()` to read these
                // back without remembering the field reuse.
                for _ in 0..vlen {
                    if cursor + 12 > type_end {
                        break;
                    }
                    let s_type = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
                    let s_off =
                        u32::from_le_bytes(bytes[cursor + 4..cursor + 8].try_into().unwrap());
                    let s_size =
                        u32::from_le_bytes(bytes[cursor + 8..cursor + 12].try_into().unwrap());
                    cursor += 12;
                    members.push(BtfMember {
                        name_off: s_size,
                        type_id: s_type,
                        offset: s_off,
                    });
                }
            }
            BTF_KIND_ENUM64 => {
                cursor += vlen * 12;
            }
            BTF_KIND_ENUM => {
                cursor += vlen * 8;
            }
            BTF_KIND_FUNC_PROTO => {
                // Each param is `struct btf_param { u32 name_off; u32 type; }`.
                // Return type is in `size_or_type` (already captured above).
                // We reuse `members` to carry the params: `BtfMember.name_off` →
                // param name, `BtfMember.type_id` → param type, `offset` is unused
                // for FUNC_PROTO (set to 0). This keeps BtfType uniform without
                // adding a parallel `params` field.
                for _ in 0..vlen {
                    if cursor + 8 > type_end {
                        break;
                    }
                    let p_name = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap());
                    let p_type =
                        u32::from_le_bytes(bytes[cursor + 4..cursor + 8].try_into().unwrap());
                    cursor += 8;
                    members.push(BtfMember {
                        name_off: p_name,
                        type_id: p_type,
                        offset: 0,
                    });
                }
            }
            BTF_KIND_DECL_TAG => {
                if cursor + 4 <= type_end {
                    let component_idx = i32::from_le_bytes(
                        bytes[cursor..cursor + 4].try_into().unwrap(),
                    );
                    // Defer resolving the tag name string until after the
                    // full strings blob is installed on BtfContext.
                    decl_tags.push(DeclTag {
                        name: String::new(), // filled in below
                        target_type_id: size_or_type,
                        component_idx,
                    });
                    // Stash the name_off on the last decl_tag via a sentinel:
                    // we use a fresh field on the parsed type (below) to
                    // carry the string offset. Simpler: look up strings now.
                    let last = decl_tags.last_mut().unwrap();
                    let start = name_off as usize;
                    if start < strings.len() {
                        if let Some(end) =
                            strings[start..].iter().position(|&b| b == 0).map(|e| e + start)
                        {
                            if let Ok(s) = std::str::from_utf8(&strings[start..end]) {
                                last.name = s.to_string();
                            }
                        }
                    }
                    cursor += 4;
                }
            }
            _ => {}
        }

        types.insert(
            type_id,
            BtfType {
                id: type_id,
                name_off,
                info,
                size_or_type,
                members,
            },
        );

        type_id += 1;
    }

    // Build the kfunc registry: FUNC types targeted by a DECL_TAG whose name
    // is "kfunc" or "bpf_kfunc" get indexed by the FUNC's own name.
    let mut kfuncs: HashMap<String, u32> = HashMap::new();
    for tag in &decl_tags {
        if tag.name != "kfunc" && tag.name != "bpf_kfunc" {
            continue;
        }
        let Some(func_ty) = types.get(&tag.target_type_id) else {
            continue;
        };
        if func_ty.kind() != BTF_KIND_FUNC {
            continue;
        }
        let start = func_ty.name_off as usize;
        if start >= strings.len() {
            continue;
        }
        let Some(end) = strings[start..].iter().position(|&b| b == 0).map(|e| e + start) else {
            continue;
        };
        let Ok(name) = std::str::from_utf8(&strings[start..end]) else {
            continue;
        };
        kfuncs.insert(name.to_string(), tag.target_type_id);
    }

    Ok(BtfContext {
        types,
        strings,
        decl_tags,
        kfuncs,
    })
}

// -----------------------------------------------------------------------------
// PART 2: Helper Interface for Map Loader (Your existing logic)
// -----------------------------------------------------------------------------

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
fn extract_kptr_fields(
    types: &[BtfTypeRaw],
    value_type_id: u32,
    get_str: &impl Fn(u32) -> String,
) -> Vec<KptrField> {
    let mut out = Vec::new();
    let Some(t) = types.get(value_type_id as usize) else {
        return out;
    };
    // Peel typedef chain to the underlying struct.
    let mut t = t;
    let mut depth = 0;
    while matches!(
        t.kind(),
        BTF_KIND_TYPEDEF | BTF_KIND_CONST | BTF_KIND_VOLATILE | BTF_KIND_RESTRICT
    ) && depth < 8
    {
        match types.get(t.size_or_type as usize) {
            Some(inner) => {
                t = inner;
                depth += 1;
            }
            None => return out,
        }
    }
    if t.kind() != BTF_KIND_STRUCT && t.kind() != BTF_KIND_UNION {
        return out;
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
        if let Some((kind, pointee_btf_id)) = classify_kptr_field(types, m_type_id, get_str) {
            // Bottom 24 bits are the bit offset for non-bitfield members
            // in BPF_F_BITFIELD_SIZE_GT_0; for kptr fields (full pointers)
            // the offset is byte-aligned and the upper bits are zero.
            let bit_off = m_offset_bits & 0x00ff_ffff;
            out.push(KptrField {
                offset: bit_off / 8,
                kind,
                pointee_btf_id,
            });
        }
    }
    out
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
                        });
                    }
                }
            }
        }
    }

    Ok(map_defs)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a minimal BTF blob exercising DECL_TAG + kfunc registry + TYPE_TAG.
    ///
    /// Layout:
    ///   id 1: FUNC     name="my_kfunc"
    ///   id 2: DECL_TAG name="kfunc",   target=1, component_idx=-1
    ///   id 3: INT      name="inner",   size=4
    ///   id 4: TYPE_TAG name="__kptr",  inner=3
    fn synthetic_btf() -> Vec<u8> {
        // String table. Offsets matter.
        //   0  ""
        //   1  "my_kfunc\0"   (9 bytes)
        //  10  "kfunc\0"      (6 bytes)
        //  16  "__kptr\0"     (7 bytes)
        //  23  "inner\0"      (6 bytes) -> end 29
        let mut strings: Vec<u8> = Vec::new();
        strings.push(0);
        strings.extend_from_slice(b"my_kfunc\0");
        strings.extend_from_slice(b"kfunc\0");
        strings.extend_from_slice(b"__kptr\0");
        strings.extend_from_slice(b"inner\0");
        assert_eq!(strings.len(), 29);

        let mut types: Vec<u8> = Vec::new();
        let push_hdr = |out: &mut Vec<u8>, name_off: u32, info: u32, size_or_type: u32| {
            out.extend_from_slice(&name_off.to_le_bytes());
            out.extend_from_slice(&info.to_le_bytes());
            out.extend_from_slice(&size_or_type.to_le_bytes());
        };

        // Type 1: FUNC "my_kfunc"
        push_hdr(&mut types, 1, (BTF_KIND_FUNC as u32) << 24, 0);
        // Type 2: DECL_TAG "kfunc" target=1, extra i32 component_idx = -1
        push_hdr(&mut types, 10, (BTF_KIND_DECL_TAG as u32) << 24, 1);
        types.extend_from_slice(&(-1i32).to_le_bytes());
        // Type 3: INT "inner" size=4, extra 4 bytes of int encoding (zeros ok)
        push_hdr(&mut types, 23, (BTF_KIND_INT as u32) << 24, 4);
        types.extend_from_slice(&0u32.to_le_bytes());
        // Type 4: TYPE_TAG "__kptr" inner=3
        push_hdr(&mut types, 16, (BTF_KIND_TYPE_TAG as u32) << 24, 3);

        let hdr_len: u32 = 24;
        let type_len = types.len() as u32;
        let str_len = strings.len() as u32;

        let mut out = Vec::new();
        out.extend_from_slice(&0xEB9Fu16.to_le_bytes()); // magic
        out.push(1); // version
        out.push(0); // flags
        out.extend_from_slice(&hdr_len.to_le_bytes());
        out.extend_from_slice(&0u32.to_le_bytes()); // type_off
        out.extend_from_slice(&type_len.to_le_bytes());
        out.extend_from_slice(&type_len.to_le_bytes()); // str_off = after types
        out.extend_from_slice(&str_len.to_le_bytes());
        out.extend_from_slice(&types);
        out.extend_from_slice(&strings);
        out
    }

    #[test]
    fn parse_decl_tag_populates_kfunc_registry() {
        let blob = synthetic_btf();
        let ctx = parse_btf(&blob).expect("parse");

        // kfunc registered by FUNC name
        assert_eq!(ctx.lookup_kfunc("my_kfunc"), Some(1));
        assert!(ctx.lookup_kfunc("nonexistent").is_none());

        // decl_tags_for returns the tag attached to the FUNC
        let tags: Vec<_> = ctx.decl_tags_for(1).collect();
        assert_eq!(tags.len(), 1);
        assert_eq!(tags[0].name, "kfunc");
        assert_eq!(tags[0].component_idx, -1);

        // No tags on unrelated types
        assert_eq!(ctx.decl_tags_for(3).count(), 0);
    }

    #[test]
    fn type_tag_name_returns_tag_and_inner() {
        let ctx = parse_btf(&synthetic_btf()).expect("parse");
        let (name, inner) = ctx.type_tag_name(4).expect("type tag");
        assert_eq!(name, "__kptr");
        assert_eq!(inner, 3);
        // Non-TYPE_TAG ids return None
        assert!(ctx.type_tag_name(1).is_none());
        assert!(ctx.type_tag_name(3).is_none());
    }
}
