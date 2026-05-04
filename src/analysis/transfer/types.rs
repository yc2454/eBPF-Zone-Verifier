// src/analysis/transfer/types.rs
//
// Type update logic for all instruction types

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{PtrFlags, RegType, TypeState, new_ptr_id};
use crate::parsing::elf::KptrFieldKind;
use crate::analysis::machine::stack_state::StackState;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, MapLoadKind, MemSize, Operand, Width};
use crate::common::constants;
use crate::common::ctx_model::{CtxFieldKind, validate_ctx_access};
use crate::domains::numeric::NumericDomain;

/// True if R2 (the lookup-elem key pointer) points at a stack slot
/// whose value is a known constant strictly less than `map_def.max_entries`.
/// Mirrors kernel's array-map "lookup with const in-bounds key returns
/// non-null" specialization (closes verifier_array_access::*_no_nullness).
fn const_key_in_bounds(
    state: &State,
    map_def: &crate::parsing::elf::BpfMapDef,
) -> bool {
    let level = match state.types.get(Reg::R2) {
        RegType::PtrToStack { frame_level } => frame_level,
        _ => return false,
    };
    let off = match state.domain.get_distance_fixed(Reg::R2, Reg::R10) {
        Some(o) => o,
        None => return false,
    };
    let slot = match state.stack_at(level).get_slot(off as i16) {
        Some(s) => s,
        None => return false,
    };
    if slot.size.bytes() as u32 != map_def.key_size {
        return false;
    }
    if !slot.tnum.is_const() {
        return false;
    }
    slot.tnum.value < map_def.max_entries as u64
}

fn update_packet_ptr_type_after_alu(types: &mut TypeState, domain: &NumericDomain, dst: Reg) {
    // Check offset from anchor: dst - @data
    // Use get_distance_interval to support both zone and interval domains
    let (_, max_offset) = domain.get_distance_interval(dst, Reg::AnchorData);
    if max_offset <= constants::MAX_PACKET_OFF {
        types.set(dst, RegType::PtrToPacket);
    } else {
        types.set(dst, RegType::ScalarValue);
    }
}

/// Extracts a fixed i64 value from an operand (immediate or register with known value)
fn get_operand_fixed_value(domain: &NumericDomain, src: &Operand) -> Option<i64> {
    match src {
        Operand::Imm(k) => Some(*k),
        Operand::Reg(r) => domain.get_fixed_value(*r),
    }
}

/// Updates PtrToMapValue offset by delta, returning new type
fn adjust_map_value_offset(ty: RegType, delta: Option<i64>) -> RegType {
    match ty {
        RegType::PtrToMapValue {
            id,
            offset,
            map_idx,
        } => {
            let new_offset = match (offset, delta) {
                (Some(o), Some(d)) => Some(o + d),
                _ => None, // Unknown if either is unknown
            };
            RegType::PtrToMapValue {
                id,
                offset: new_offset,
                map_idx,
            }
        }
        other => other,
    }
}

/// Unified handler for pointer arithmetic (Add/Sub) type updates
fn update_ptr_arithmetic_type(
    env: &VerifierEnv,
    types: &mut TypeState,
    domain: &NumericDomain,
    dst: Reg,
    dst_ty: RegType,
    src: &Operand,
    is_add: bool, // true = Add, false = Sub
) {
    let delta = get_operand_fixed_value(domain, src);
    let signed_delta = if is_add { delta } else { delta.map(|d| -d) };

    match dst_ty {
        RegType::PtrToMapValue { .. } => {
            types.set(dst, adjust_map_value_offset(dst_ty, signed_delta));
        }
        RegType::PtrToMapObject { .. } => {
            // Only allow adding/subtracting 0
            if signed_delta != Some(0) {
                types.set(dst, RegType::ScalarValue);
            }
            // else: type unchanged (adding 0 is a no-op)
        }
        RegType::PtrToStack { frame_level } => {
            types.set(dst, RegType::PtrToStack { frame_level });
        }
        RegType::PtrToOwnedKptr {
            ref_id,
            offset,
            non_owning,
        } => {
            // Kernel `verifier.c` v6.15 ~L15170: PTR_TO_BTF_ID|MEM_ALLOC
            // preserves type through pointer arithmetic; `reg->off` is
            // bumped by the constant delta. Required for graph-add
            // kfuncs that pass `&n->node` (PtrToOwnedKptr + 16) — the
            // member offset must reach the validator without being
            // demoted to Scalar. Release sinks (`bpf_obj_drop`,
            // `bpf_kptr_xchg`) reject non-zero offsets in the post-call
            // gate, mirroring kernel "must have zero offset when passed
            // to release func" (verifier.c ~L13242).
            let new_offset = match signed_delta {
                Some(d) => offset.saturating_add(d.clamp(i32::MIN as i64, i32::MAX as i64) as i32),
                None => offset, // unknown delta: keep type, offset unchanged
            };
            types.set(
                dst,
                RegType::PtrToOwnedKptr {
                    ref_id,
                    offset: new_offset,
                    non_owning,
                },
            );
        }
        RegType::PtrToArena { ref_id, mem_size } => {
            // Kernel `verifier.c` ~L15191 (v6.15): when dst is
            // PTR_TO_ARENA, "Any arithmetic operations are allowed on
            // arena pointers" and the function returns 0 without
            // changing dst's type. Add/Sub/Shl/Shr/And/Or/etc. all
            // preserve PtrToArena. This is what alloc_pages's
            // `pg - base; result >> 12` shape needs to verify.
            types.set(dst, RegType::PtrToArena { ref_id, mem_size });
        }
        RegType::PtrToCtx => {
            if signed_delta == Some(0) {
                types.set(dst, RegType::PtrToCtx);
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        }
        RegType::PtrToPacket => {
            if is_add {
                // For Add: check if immediate exceeds max offset
                if let Some(d) = delta {
                    if d >= constants::MAX_PACKET_OFF {
                        types.set(dst, RegType::ScalarValue);
                    }
                    // else: type unchanged, still PtrToPacket
                }
                // For Add with register: check if known value exceeds max
                else if let Operand::Reg(_) = src {
                    // delta is None means unknown - keep type unchanged
                }
            } else {
                // For Sub: use anchor-based bounds check
                update_packet_ptr_type_after_alu(types, domain, dst);
            }
        }
        RegType::PtrToPacketMeta => {
            // Use get_distance_interval to support both zone and interval domains
            let (_, max_offset) = domain.get_distance_interval(dst, Reg::AnchorDataMeta);
            if max_offset <= constants::MAX_PACKET_OFF {
                types.set(dst, RegType::PtrToPacketMeta);
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        }
        // W6.4a-followon: pointer arithmetic on a BTF-typed pointer (e.g.
        // `r1 = sk + 1296` to reach an embedded struct field) preserves
        // the type and trusted flags. Without this, struct_ops methods
        // that compute interior pointers via add/sub demoted to scalar
        // and the subsequent field access failed. The access check on
        // `type_name == "unknown"` already skips per-field bounds
        // validation; for layout-known names the access path enforces
        // bounds via mem_region_model.
        //
        // Phase 3 cluster B follow-on: when the offset matches an
        // *embedded* struct member of `type_name`, retype to that
        // member's struct (e.g. `&task->cpus_mask` →
        // `PtrToBtfId{cpumask, TRUSTED}`). This is what kfunc arg
        // matchers like `validate_ptr_to_cpumask` need to accept the
        // interior pointer. For non-named types (`"unknown"`,
        // `"struct"`) or unresolved offsets, fall back to preserving
        // the source type — matches the W6.4a-followon shape.
        RegType::PtrToBtfId {
            type_name,
            flags,
            ref_id,
        } => {
            // Pointer arithmetic on a refcounted BTF pointer drops the
            // ref_id: an interior pointer is no longer the
            // acquire-tracked owner, and releasing through it would
            // mismatch the original. Kernel matches.
            let _ = ref_id;
            let new_type_name = signed_delta
                .filter(|d| *d > 0 && *d < i64::from(i32::MAX))
                .and_then(|d| {
                    let struct_id = env.ctx.btf.find_struct_by_name(type_name)?;
                    let info = env
                        .ctx
                        .btf
                        .field_at_offset(struct_id, d as u32)?;
                    match info.kind {
                        crate::parsing::btf::BtfFieldKind::Embedded {
                            type_name: Some(name),
                            ..
                        } => Some(crate::analysis::machine::context::intern_btf_type_name_strict(
                            &name,
                        )),
                        _ => None,
                    }
                })
                .unwrap_or(type_name);
            types.set(
                dst,
                RegType::PtrToBtfId {
                    type_name: new_type_name,
                    flags,
                    ref_id: None,
                },
            );
        }
        _ => types.set(dst, RegType::ScalarValue),
    }
}

/// Handles scalar + pointer/scalar arithmetic type updates
fn handle_scalar_arithmetic_type(
    in_types: &TypeState,
    types: &mut TypeState,
    dst: Reg,
    src: &Operand,
    is_add: bool,
) {
    match src {
        Operand::Imm(_) => {
            types.set(dst, RegType::ScalarValue);
        }
        Operand::Reg(src_reg) => {
            let src_ty = in_types.get(*src_reg);
            if is_add {
                // scalar + pointer => pointer type (commutative)
                types.set(dst, src_ty);
            } else {
                // scalar - pointer => scalar (subtraction from scalar)
                types.set(dst, src_ty);
            }
        }
    }
}

/// Updates register types after an ALU operation.
pub(crate) fn update_alu_types(
    env: &VerifierEnv,
    in_types: &TypeState,
    types: &mut TypeState,
    domain: &NumericDomain,
    width: Width,
    op: AluOp,
    dst: Reg,
    src: &Operand,
    pc: usize,
) {
    if width == Width::W32 {
        types.set(dst, RegType::ScalarValue);
        return;
    }
    match op {
        AluOp::Mov => {
            match src {
                Operand::Reg(r) => {
                    let src_ty = in_types.get(*r);
                    // `bpf_addr_space_cast(as(1)→as(0))` is encoded as
                    // BPF_MOV | BPF_X with off=1, imm=1. The parser
                    // records its PCs; the kernel
                    // (`verifier.c` ~L15402, v6.15) does
                    // `mark_reg_unknown` then unconditionally sets
                    // `dst_reg->type = PTR_TO_ARENA` for this form,
                    // ignoring the source register's prior type. Mirror
                    // that here: the cast ignores src and produces a
                    // fresh PtrToArena.
                    if env.addr_space_cast_to_arena_pcs.contains(&pc) {
                        types.set(
                            dst,
                            RegType::PtrToArena {
                                ref_id: None,
                                mem_size: 1u64 << 32,
                            },
                        );
                    } else {
                        types.set(dst, src_ty);
                    }
                }
                Operand::Imm(_) => {
                    // Regular ALU MOV imm: look up a reloc at *this* pc only.
                    // LD_IMM64 (`r = imm64`) is handled via its own MapLoad
                    // opcode, so the legacy `pc+1` fallback would only ever
                    // misattribute a neighbouring insn's reloc to a single-slot
                    // ALU MOV (e.g. `r1 = 0` followed by an LD_IMM64-of-vals
                    // → r1 wrongly typed as PtrToMapValue at the call site).
                    let reloc = env.ctx.pc_to_reloc.get(&pc);

                    if let Some(info) = reloc {
                        if info.map_idx < env.ctx.map_defs.len() {
                            let map_name = &env.ctx.map_defs[info.map_idx].name;
                            // Data sections become PtrToMapValue
                            if map_name.starts_with(".rodata")
                                || map_name.starts_with(".data")
                                || map_name == ".bss"
                            {
                                types.set(
                                    dst,
                                    RegType::PtrToMapValue {
                                        id: new_ptr_id(),
                                        offset: Some(info.offset),
                                        map_idx: info.map_idx,
                                    },
                                );
                            } else {
                                types.set(dst, RegType::ScalarValue);
                            }
                        } else {
                            types.set(dst, RegType::ScalarValue);
                        }
                    } else {
                        types.set(dst, RegType::ScalarValue);
                    }
                }
            }
        }
        AluOp::Add | AluOp::Sub => {
            let dst_ty = in_types.get(dst);
            let is_add = op == AluOp::Add;

            if dst_ty.is_pointer() {
                update_ptr_arithmetic_type(env, types, domain, dst, dst_ty, src, is_add);
            } else {
                handle_scalar_arithmetic_type(in_types, types, dst, src, is_add);
            }
        }
        _ => {
            // Non-Add/Sub ALU ops normally demote dst to scalar. The
            // exception is PtrToArena: the kernel
            // (`verifier.c` ~L15191, v6.15) allows any arithmetic on
            // an arena pointer and the type stays PTR_TO_ARENA.
            // Preserves alloc_pages's `R1 = (pg - base) >> 12` chain
            // where the Shr after Sub keeps the arena type alive.
            let in_ty = in_types.get(dst);
            if matches!(in_ty, RegType::PtrToArena { .. }) {
                types.set(dst, in_ty);
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        }
    }
}

/// Updates register types after a Load operation.
pub(crate) fn update_load_types(
    env: &VerifierEnv,
    state: &mut State,
    size: usize,
    dst: Reg,
    base: Reg,
    off: i16,
) {
    let base_ty = state.types.get(base);
    match base_ty {
        RegType::PtrToCtx => {
            let kind = validate_ctx_access(env, off, size as i64);
            if let Some(info) = kind {
                match info.kind {
                    CtxFieldKind::PacketMeta => {
                        state.types.set(dst, RegType::PtrToPacketMeta);
                    }
                    CtxFieldKind::PacketStart => {
                        state.types.set(dst, RegType::PtrToPacket);
                    }
                    CtxFieldKind::PacketEnd => {
                        state.types.set(dst, RegType::PtrToPacketEnd);
                    }
                    CtxFieldKind::SockCommon => {
                        state
                            .types
                            .set(dst, RegType::PtrToSockCommonOrNull { ref_id: None });
                    }
                    CtxFieldKind::TrustedPtr {
                        type_name,
                        nullable,
                    } => {
                        if nullable {
                            state.types.set(
                                dst,
                                RegType::PtrToBtfIdOrNull {
                                    id: new_ptr_id(),
                                    type_name,
                                    flags: PtrFlags::TRUSTED,
                                    ref_id: None,
                                },
                            );
                        } else {
                            state.types.set(
                                dst,
                                RegType::PtrToBtfId {
                                    type_name,
                                    flags: PtrFlags::TRUSTED,
                                    ref_id: None,
                                },
                            );
                        }
                    }
                    _ => state.types.set(dst, RegType::ScalarValue),
                }
            } else {
                state.types.set(dst, RegType::ScalarValue);
            }
        }
        RegType::PtrToStack { .. } => {
            match state.domain.get_distance_fixed(base, Reg::R10) {
                Some(base_off) => {
                    let actual_slot = base_off + (off as i64);
                    if size == MemSize::U64.bytes() {
                        state
                            .types
                            .set(dst, state.stack().get_slot_type(actual_slot as i16));
                    } else {
                        state.types.set(dst, RegType::ScalarValue);
                    }
                }
                None => {
                    // Unknown stack offset - can't determine which slot we're reading
                    // Conservative: result is scalar (could be anything)
                    state.types.set(dst, RegType::ScalarValue);
                }
            }
        }
        RegType::PtrToMapValue {
            offset: map_off_opt,
            map_idx,
            ..
        } => {
            // Kptr field load: produce a typed pointer rather than a
            // scalar. Generic bounds and kptr-overlap rules already ran
            // in `check_load`; here we just synthesize the right reg
            // type when the access exactly matches a kptr slot.
            let final_off = crate::analysis::transfer::memory::map::resolve_const_map_off(
                state,
                base,
                map_off_opt,
                off,
            );
            let map_def = env.ctx.map_defs.get(map_idx);
            if let (Some(off_val), Some(map_def)) = (final_off, map_def)
                && let Some(field) = crate::analysis::transfer::memory::map::kptr_field_at(
                    map_def,
                    off_val,
                    size as i64,
                )
            {
                let flags = match field.kind {
                    KptrFieldKind::Unref => PtrFlags::UNTRUSTED,
                    KptrFieldKind::Ref => PtrFlags::MEM_ALLOC,
                    KptrFieldKind::Rcu => PtrFlags::RCU,
                    KptrFieldKind::Percpu => PtrFlags::PERCPU,
                    KptrFieldKind::Uptr => {
                        // `__uptr` loads yield a userspace-pointer value.
                        // No PtrToMapKptr* variant fits — the kernel types
                        // these as `PTR_TO_MEM | MEM_USER | PTR_MAYBE_NULL`
                        // and rejects deref-before-null-check
                        // ("invalid mem access 'mem_or_null'"). Until a
                        // dedicated reg type lands, fall through to
                        // ScalarValue: the two tests we're closing here
                        // (uptr_write{,_nested}) only exercise the store
                        // path. Load-side tests (uptr_no_null_check) stay
                        // FA for now and fall to a follow-up.
                        state.types.set(dst, RegType::ScalarValue);
                        return;
                    }
                };
                state.types.set(
                    dst,
                    RegType::PtrToMapKptrOrNull {
                        pointee_btf_id: field.pointee_btf_id,
                        ref_id: None,
                        flags,
                    },
                );
            } else {
                state.types.set(dst, RegType::ScalarValue);
            }
        }
        // Phase 3 cluster B follow-on: load `*(u64*)(base + off)` from
        // `PtrToBtfId{X, flags}` where X.fields[off] is a `PTR -> Y`.
        // The default load yields ScalarValue (preserves the existing
        // FA-safe behavior — kfunc validators reject Scalar where they
        // expected a typed pointer). For a small allowlist of known-
        // safe (struct, field_name) pairs the loaded value is typed as
        // `PtrToBtfId{Y, TRUSTED}` so the matching kfunc validators
        // accept it (`task->cpus_ptr`, `skb->sk` are the load
        // surfaces driving the nested_trust_success FRs).
        //
        // Type-tag-based promotion (kernel `__rcu` / `__percpu` …) is
        // intentionally *not* applied here yet — it would require
        // RCU-section tracking we don't model, and the upstream
        // selftest corpus has only one __success test that depends on
        // it (`test_read_cpumask`'s `cpus_ptr`, which the allowlist
        // covers explicitly). When we ship RCU lock tracking, swap
        // `tags` → `flags` and drop the static allowlist.
        // Phase 3 cluster B follow-on: BTF field-load typing for
        // any base whose static BTF type is known. PtrToBtfId
        // carries `type_name` directly. The acquire-tracked
        // specializations (`PtrToTask`, `PtrToCgroup`, `PtrToCpumask`)
        // are structurally pointers to the matching named struct for
        // field-access purposes — extract the implied name so
        // `task = bpf_get_current_task_btf(); task->bpf_storage`
        // resolves the same as `task` from a BPF_PROG entry arg.
        // Sock-family variants stay on the mem_region_model field
        // tables (richer per-field offsets); we don't divert them
        // here.
        ref t if size == MemSize::U64.bytes()
            && off >= 0
            && implied_btf_struct_name(t).is_some() =>
        {
            use crate::parsing::btf::BtfFieldKind;
            let type_name = implied_btf_struct_name(t).unwrap();
            let mut typed = false;
            if let Some(struct_id) = env.ctx.btf.find_struct_by_name(type_name)
                && let Some(info) = env.ctx.btf.field_at_offset(struct_id, off as u32)
                && let BtfFieldKind::Pointer {
                    pointee_name: Some(pointee),
                    ..
                } = info.kind
                && trusted_field_load(type_name, info.name)
            {
                let pointee_static =
                    crate::analysis::machine::context::intern_btf_type_name_strict(
                        &pointee,
                    );
                state.types.set(
                    dst,
                    RegType::PtrToBtfId {
                        type_name: pointee_static,
                        flags: PtrFlags::TRUSTED,
                        ref_id: None,
                    },
                );
                typed = true;
            }
            if !typed {
                state.types.set(dst, RegType::ScalarValue);
            }
        }
        _ => state.types.set(dst, RegType::ScalarValue),
    }
}

/// Allowlist of `(struct_name, field_name)` pairs whose loaded pointer
/// value is treated as `PtrToBtfId{<pointee>, TRUSTED}`. Mirrors the
/// kernel's per-field "safe field" allowlist for tracing programs —
/// the kernel encodes most of these via BTF `__rcu` / `btf_type_tag`
/// metadata that we don't yet thread through `RegType` flags. The
/// intent is conservative: only fields whose kernel BTF actually marks
/// safe-to-load belong here, so unrelated `__failure` selftests that
/// rely on a non-allowlisted field landing as ScalarValue (and thus
/// getting rejected by the kfunc validator) keep their rejection.
///
/// Each entry is "this load yields a trusted pointer typed as the
/// declared pointee struct". Promote-from-allowlist is the *only*
/// way a load gets a typed pointer today; remove an entry to
/// re-introduce the lax-Scalar fallback.
/// Map a register type to the BTF struct name whose layout describes
/// what the program accesses through it. Used by the BTF field-load
/// typing path to look up `(struct_name, field@offset)` for
/// trusted-load promotion. Returns None for pointer kinds the path
/// doesn't handle (sock variants use mem_region_model field tables;
/// PtrToCtx / PtrToStack / etc. don't apply).
fn implied_btf_struct_name(ty: &RegType) -> Option<&'static str> {
    match ty {
        RegType::PtrToBtfId { type_name, .. } => Some(type_name),
        RegType::PtrToTask { .. } => Some("task_struct"),
        RegType::PtrToCgroup { .. } => Some("cgroup"),
        RegType::PtrToCpumask { .. } => Some("cpumask"),
        _ => None,
    }
}

pub fn trusted_field_load(struct_name: &str, field_name: &str) -> bool {
    matches!(
        (struct_name, field_name),
        // task_struct.cpus_ptr — `cpumask_t *` carrying the task's
        // current CPU mask. Kernel marks PTR_TRUSTED on load (the
        // task's PCB is alive while the program holds a trusted
        // task pointer); KF_RCU consumers like
        // `bpf_cpumask_test_cpu` accept.
        ("task_struct", "cpus_ptr")
        // sk_buff.sk — `struct sock *`. Trusted while the skb is
        // trusted. Drives `nested_trust_success::test_skb_field`'s
        // `bpf_sk_storage_get(&map, skb->sk, …)` accepting path.
        | ("sk_buff", "sk")
        // LSM hook chains — fields kernel marks PTR_TRUSTED on load
        // from a trusted-rooted access (each entry corresponds to a
        // specific FR in local_storage.c). Adding more entries should
        // always cross-check against the matching `__failure` siblings
        // — see the cpumask reader/mutator split for the kind of FA
        // risk loose typing exposes.
        | ("linux_binprm", "file")  // bprm->file (exec)
        | ("file", "f_inode")        // bprm->file->f_inode (exec)
        | ("dentry", "d_inode")      // dentry->d_inode (inode_rename, unlink_hook)
        | ("socket", "sk")           // sock->sk (socket_bind, socket_post_create)
        | ("task_struct", "bpf_storage")  // task->bpf_storage (unlink_hook)
        | ("sock", "sk_bpf_storage")      // sk->sk_bpf_storage (socket_bind)
        | ("bpf_local_storage", "smap")   // local_storage->smap (unlink_hook, socket_bind)
        // Iter / direct-typed-ctx hooks. The BPF program holds a
        // typed ctx pointer directly; the kernel marks the embedded
        // sock pointer trusted while the iter is alive.
        // `bpf_iter__sockmap.sk` (verifier_sockmap_mutate::test_trace_iter):
        // `__bpf_md_ptr(struct sock *, sk)` at offset 0; pointee
        // resolves via the anonymous-union descent in `field_at_offset`.
        | ("bpf_iter__sockmap", "sk")
        // `sk_reuseport_md.sk` (verifier_sockmap_mutate::test_sk_reuseport):
        // `__bpf_md_ptr(struct bpf_sock *, sk)` — kernel marks bpf_sock
        // pointer trusted on load; SOCKMAP/SOCKHASH map-update accepts.
        | ("sk_reuseport_md", "sk")
        // `bpf_iter__bpf_map.map` (verifier_arena::iter_maps1):
        // `__bpf_md_ptr(struct bpf_map *, map)` — the iter ctx's
        // current map. Kernel marks it trusted while the iter is alive;
        // `bpf_arena_alloc_pages(map, ...)` accepts the loaded
        // `PtrToBtfId{bpf_map, TRUSTED}` as its `__map`-suffixed arg
        // (kernel `verifier.c` ~L13227 KF_ARG_PTR_TO_MAP).
        | ("bpf_iter__bpf_map", "map")
    )
}

/// Updates stack types after a Store operation.
/// `resolved_stack_offset` is the already-resolved stack slot (base_offset + insn_off),
/// or None if the base is not a stack pointer or offset is unknown.
pub(crate) fn update_store_types(
    stack: &mut StackState,
    src_type: RegType,
    size: MemSize,
    resolved_stack_offset: Option<i64>,
) {
    let stack_slot = resolved_stack_offset;

    if let Some(slot) = stack_slot {
        let slot = slot as i16;
        let byte_count = size.bytes() as i16; // U8=1, U16=2, U32=4, U64=8

        if size == MemSize::U64 {
            // Full 8-byte store preserves type info at the base slot
            stack.set_slot_type(slot, src_type, None);
            // Mark remaining bytes as initialized (but no type info)
            for i in 1..byte_count {
                stack.set_slot_type(slot + i, RegType::ScalarValue, None);
            }
        } else {
            // Partial store: mark all bytes as initialized, but poison type info
            for i in 0..byte_count {
                stack.set_slot_type(slot + i, RegType::ScalarValue, None);
            }
        }
    }
}

/// Checks if a helper invalidates packet pointers.
pub(crate) fn helper_invalidates_packets(helper: u32) -> bool {
    matches!(
        helper,
        constants::BPF_XDP_ADJUST_HEAD
            | constants::BPF_XDP_ADJUST_TAIL
            | constants::BPF_XDP_ADJUST_META
            | constants::BPF_SKB_PULL_DATA
            | constants::BPF_SKB_CHANGE_HEAD
            | constants::BPF_SKB_CHANGE_TAIL
            | constants::BPF_SKB_CHANGE_PROTO
            | constants::BPF_SKB_ADJUST_ROOM
            | constants::BPF_SKB_STORE_BYTES
            | constants::BPF_SKB_VLAN_PUSH
            | constants::BPF_SKB_VLAN_POP
    )
}

/// Updates register types after a helper Call.
pub(crate) fn update_call_types(
    env: &mut VerifierEnv,
    in_types: &TypeState,
    state: &mut State,
    helper: u32,
) {
    // Default to scalar value
    state.types.set(Reg::R0, RegType::ScalarValue);

    // Try the proto-driven path first (W4.1b). For helpers whose proto
    // populates `ret`/`flags`/`side_effects`, this sets R0 and handles
    // acquire/release uniformly so kfuncs can reuse the same applier.
    // Returns false for helpers still on the legacy per-id match below.
    let routed = if let Some(proto) =
        crate::analysis::transfer::call::signatures::get_helper_proto(helper)
    {
        crate::analysis::transfer::call::side_effects::apply_call_proto_r0(
            in_types, state, &proto,
        )
    } else {
        false
    };

    // Set R0 based on helper return type (legacy path for non-migrated helpers)
    if !routed {
    match helper {
        constants::BPF_MAP_LOOKUP_ELEM | constants::BPF_GET_LOCAL_STORAGE => {
            let map_idx = match in_types.get(Reg::R1) {
                RegType::PtrToMapObject { map_idx } => map_idx,
                RegType::PtrToMapValue { map_idx, .. } => map_idx, // Handles map-in-map lookups
                _ => 0,
            };
            let map_def_opt = env.ctx.map_defs.get(map_idx);
            if let Some(map_def) = map_def_opt {
                match map_def.type_ {
                    constants::BPF_MAP_TYPE_SOCKMAP | constants::BPF_MAP_TYPE_SOCKHASH => {
                        let id = state.acquire_ref();
                        state
                            .types
                            .set(Reg::R0, RegType::PtrToSocketOrNull { ref_id: Some(id) });
                    }
                    _ => {
                        // bpf_get_local_storage returns a guaranteed non-null
                        // pointer (cgroup_storage / per-cpu storage is always
                        // allocated by the kernel for the prog's attach
                        // target) — type R0 as PtrToMapValue directly so the
                        // user can dereference without an explicit null check,
                        // matching kernel behaviour.
                        if helper == constants::BPF_GET_LOCAL_STORAGE {
                            let id = new_ptr_id();
                            state.types.set(
                                Reg::R0,
                                RegType::PtrToMapValue {
                                    id,
                                    offset: Some(0),
                                    map_idx,
                                },
                            );
                            state.domain.init_map_value_ptr(Reg::R0);
                        } else if helper == constants::BPF_MAP_LOOKUP_ELEM
                            && matches!(
                                map_def.type_,
                                constants::BPF_MAP_TYPE_ARRAY
                                    | constants::BPF_MAP_TYPE_PERCPU_ARRAY
                            )
                            && const_key_in_bounds(state, map_def)
                        {
                            // Kernel: array-map lookups with a statically-known
                            // in-bounds key return PTR_TO_MAP_VALUE (non-null).
                            // verifier_array_access::*_no_nullness covers this.
                            let id = new_ptr_id();
                            state.types.set(
                                Reg::R0,
                                RegType::PtrToMapValue {
                                    id,
                                    offset: Some(0),
                                    map_idx,
                                },
                            );
                            state.domain.init_map_value_ptr(Reg::R0);
                        } else {
                            let id = new_ptr_id();
                            state
                                .types
                                .set(Reg::R0, RegType::PtrToMapValueOrNull { id, map_idx });
                        }
                    }
                }
            } else {
                state.types.set(Reg::R0, RegType::ScalarValue);
            }
        }

        // Socket lookup helpers - return PTR_TO_SOCKET_OR_NULL
        constants::BPF_SK_LOOKUP_TCP | constants::BPF_SK_LOOKUP_UDP => {
            let id = state.acquire_ref();
            state
                .types
                .set(Reg::R0, RegType::PtrToSocketOrNull { ref_id: Some(id) });
        }

        // The socket reference from bpf_get_listener_sock doesn't need to be released
        constants::BPF_GET_LISTENER_SOCK => {
            state
                .types
                .set(Reg::R0, RegType::PtrToSocketOrNull { ref_id: None });
        }

        // Copies ref id from argument
        constants::BPF_SK_FULLSOCK => {
            let ref_id = state.types.get(Reg::R1).get_ref_id();
            state
                .types
                .set(Reg::R0, RegType::PtrToSocketOrNull { ref_id });
        }

        constants::BPF_TCP_SOCK => {
            let id = state.types.get(Reg::R1).get_ref_id();
            state.types.set(Reg::R0, RegType::PtrToTcpSockOrNull { id });
        }

        // SKC lookup - returns PTR_TO_SOCK_COMMON_OR_NULL
        constants::BPF_SKC_LOOKUP_TCP => {
            let id = state.acquire_ref();
            state
                .types
                .set(Reg::R0, RegType::PtrToSockCommonOrNull { ref_id: Some(id) });
        }

        constants::BPF_SK_RELEASE => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state.release_ref(ref_id);
                state.invalidate_ref(ref_id);
            }
        }

        // SKC to TCP sock conversion - returns PTR_TO_TCP_SOCK_OR_NULL
        constants::BPF_SKC_TO_TCP_SOCK
        | constants::BPF_SKC_TO_TCP6_SOCK
        | constants::BPF_SKC_TO_TCP_TIMEWAIT_SOCK
        | constants::BPF_SKC_TO_TCP_REQUEST_SOCK => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state
                    .types
                    .set(Reg::R0, RegType::PtrToTcpSockOrNull { id: Some(ref_id) });
            }
        }

        // SKC to UDP/Unix - return SOCK_COMMON for now (simplified)
        constants::BPF_SKC_TO_UDP6_SOCK | constants::BPF_SKC_TO_UNIX_SOCK => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state.types.set(
                    Reg::R0,
                    RegType::PtrToSockCommonOrNull {
                        ref_id: Some(ref_id),
                    },
                );
            }
        }

        // *_storage_get: R0 = PtrToMapValueOrNull keyed off the map (R1),
        // not the optional initial-value arg (R3). Real programs commonly
        // pass NULL for R3 (e.g. bpf_dctcp_init), and the prior version of
        // this arm fell through to Scalar in that case. W7.1 fix.
        constants::BPF_SK_STORAGE_GET
        | constants::BPF_TASK_STORAGE_GET
        | constants::BPF_INODE_STORAGE_GET
        | constants::BPF_CGRP_STORAGE_GET => {
            let map_idx = match in_types.get(Reg::R1) {
                RegType::PtrToMapObject { map_idx } => map_idx,
                RegType::PtrToMapValue { map_idx, .. } => map_idx,
                _ => 0,
            };
            let id = new_ptr_id();
            state
                .types
                .set(Reg::R0, RegType::PtrToMapValueOrNull { id, map_idx });
        }

        // tail_call: R0 is undefined on failure path
        constants::BPF_TAIL_CALL => {
            state.types.set(Reg::R0, RegType::ScalarValue);
        }

        constants::BPF_SKB_LOAD_BYTES => {
            let mem_ptr_ty = in_types.get(Reg::R3);
            if let RegType::PtrToStack { frame_level } = mem_ptr_ty
                && let Some(off) = state.domain.get_distance_fixed(Reg::R3, Reg::R10)
            {
                let (_, hi) = state.domain.get_interval(Reg::R4);
                let len = if hi <= 0xFFFF { hi as i16 } else { 0 };
                if len > 0 {
                    // Mark the stack range as initialized scalars
                    for i in 0..len {
                        state.stack_at_mut(frame_level).set_slot_type(
                            (off + i as i64) as i16,
                            RegType::ScalarValue,
                            None,
                        );
                    }
                }
            }
        }

        constants::BPF_RINGBUF_RESERVE => {
            let (_, hi) = state.domain.get_interval(Reg::R2);
            state.types.set(
                Reg::R0,
                RegType::PtrToAllocMemOrNull {
                    id: new_ptr_id(),
                    mem_size: hi as u64,
                    ref_id: None,
                    dynptr_id: None,
                },
            );
        }

        _ => {
            state.types.set(Reg::R0, RegType::ScalarValue);
        }
    }
    } // end if !routed

    // Clobber caller-saved registers - they are NOT readable after the call.
    // W7.2: fastcall helpers (v6.13) preserve R1..R5 — skip the regtype
    // clobber so the values stay typed across the call. Paired with the
    // DBM/Tnum skip in `transfer.rs`.
    if !crate::analysis::transfer::call::signatures::is_fastcall_helper(helper) {
        for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            state.types.set(r, RegType::NotInit);
        }
    }

    // 3. Invalidate packet pointers if needed
    if helper_invalidates_packets(helper) {
        for r in Reg::ALL {
            match state.types.get(r) {
                RegType::PtrToPacket | RegType::PtrToPacketEnd => {
                    state.types.set(r, RegType::ScalarValue);
                }
                _ => {}
            }
        }
        state.stack_mut().invalidate_packet_pointers();
        state
            .frames
            .invalidate_caller_reg_type(|ty| ty.is_packet_ptr(), RegType::NotInit);
        // Slices derived from a packet dynptr (`bpf_dynptr_slice` /
        // `_slice_rdwr` over an skb/xdp dynptr) become invalid when
        // the helper mutates packet data. Kernel sweeps every reg +
        // stack slot whose dynptr_id matches a packet-source dynptr
        // (verifier.c v6.15 L913-919). Mirrors `dynptr_fail.c`
        // `xdp_invalid_data_slice1/2` and the skb counterparts.
        let packet_dids = state.collect_packet_dynptr_ids();
        for did in packet_dids {
            state.invalidate_dynptr_slices(did);
        }
    }
}

pub(crate) fn update_call_rel_types(state: &mut State) {
    state.types.set(Reg::R0, RegType::NotInit);
    state.types.set(
        Reg::R10,
        RegType::PtrToStack {
            frame_level: state.current_frame_level(),
        },
    );
}

pub(crate) fn update_packet_load_types(types: &mut TypeState) {
    // Clobber R1 - R5
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        types.set(r, RegType::NotInit);
    }

    // Set Result (R0)
    // The loaded data is placed in R0.
    types.set(Reg::R0, RegType::ScalarValue);
}

pub(crate) fn update_map_load_types(
    types: &mut TypeState,
    kind: MapLoadKind,
    map_fd: usize,
    dst: Reg,
    offset: i64,
    is_static_data_section: bool,
) {
    let new_type = match kind {
        MapLoadKind::MapPtr => RegType::PtrToMapObject { map_idx: map_fd },
        MapLoadKind::MapValue => RegType::PtrToMapValue {
            // Synthetic data sections (`.bss`, `.bss.<name>`, `.data`,
            // `.data.<name>`, `.rodata`, `.rodata.<name>`) load via
            // `BPF_PSEUDO_MAP_VALUE`, which the kernel does NOT mint a
            // fresh ptr_id for: every reload of `&alock` yields the
            // same identity. Required for `bpf_spin_lock` / `unlock` to
            // pair across two LD_IMM64s of the same `.bss.<name>`
            // global. Other map kinds (HASH/ARRAY etc.) keep fresh ids.
            id: if is_static_data_section { 0 } else { new_ptr_id() },
            map_idx: map_fd,
            offset: Some(offset),
        },
        // Modern kinds are filtered upstream in transfer_map_load; reaching
        // them here would be a bug.
        MapLoadKind::PseudoFunc { .. }
        | MapLoadKind::PseudoBtfId { .. }
        | MapLoadKind::PseudoMapIdx
        | MapLoadKind::PseudoMapIdxValue => {
            debug_assert!(
                false,
                "update_map_load_types reached with unsupported kind: {:?}",
                kind
            );
            return;
        }
    };

    types.set(dst, new_type);
}
