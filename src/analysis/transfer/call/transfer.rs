use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/call/transfer.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{PtrFlags, RegType};
use crate::analysis::machine::state::State;
use crate::analysis::transfer::types::{
    helper_invalidates_packets, update_call_rel_types, update_call_types,
};
use crate::ast::ProgramKind;
use crate::common::constants;
use crate::domains::interval::new_scalar_id;
use crate::domains::numeric::NumericDomain;
use crate::domains::tnum::Tnum;
use crate::parsing::btf::SpecialFieldKind;
use log::{debug, error, trace};

use super::checks::{check_mem_size_pairs, is_valid_helper_id, validate_helper_args};
use super::signatures::get_mem_size_pairs;

/// Transfer function for helper Call instructions.
pub(crate) fn transfer_call(env: &mut VerifierEnv, mut state: State, helper: u32) -> Vec<State> {
    let in_types = state.types.clone();
    let pc = state.pc;

    // =======================================================================
    // Check if helper ID is valid
    // =======================================================================
    if !is_valid_helper_id(helper) {
        env.fail(VerificationError::InvalidHelperId { pc, helper });
        return vec![];
    }

    // ========================================================================
    // Check if the call is forbidden under an active lock
    // ========================================================================
    if state.has_active_lock() && !allowed_while_in_active_lock(helper) {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R0 });
        return vec![];
    }

    // ========================================================================
    // Validate pointer-size pairs
    // ========================================================================
    debug!("[Verifier] pc {}: checking mem size pairs", pc);
    if !check_mem_size_pairs(env, &state, helper, pc) {
        return vec![];
    }

    // ========================================================================
    // Validate helper arguments BEFORE executing
    // ========================================================================
    debug!("[Verifier] pc {}: validating helper arguments", pc);
    validate_helper_args(env, &state, helper, &in_types, pc);

    // ========================================================================
    // SPECIAL CASES
    // ========================================================================

    // bpf_tail_call
    if helper == constants::BPF_TAIL_CALL {
        if state.has_unreleased_refs() {
            error!("Entering tail calls but has unreleased references!");
            env.fail(VerificationError::UnreleasedReference {});
            return vec![];
        }
        update_call_types(env, &in_types, &mut state, helper);

        for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            state.domain.forget(r);
        }

        state.pc += 1;
        return vec![state];
    }

    // Special check for sk_release: R1 must have a reference
    if helper == constants::BPF_SK_RELEASE && state.types.get(Reg::R1).get_ref_id().is_none() {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
        return vec![];
    }

    // bpf_spin_lock and bpf_spin_unlock
    if (helper == constants::BPF_SPIN_LOCK || helper == constants::BPF_SPIN_UNLOCK)
        && !check_and_handle_spin_lock(env, &mut state, helper)
    {
        return vec![];
    }

    // bpf_sock_map_update: only allowed in BPF_PROG_TYPE_SOCK_OPS programs
    if helper == constants::BPF_SOCK_MAP_UPDATE
        && !matches!(env.ctx.prog_kind, ProgramKind::SockOps)
    {
        env.fail(VerificationError::HelperNotAllowedForProgram {
            pc,
            helper,
            kind: env.ctx.prog_kind,
        });
        return vec![];
    }

    // bpf_d_path is restrictive
    if helper == constants::BPF_D_PATH {
        if !matches!(env.ctx.prog_kind, ProgramKind::Tracing | ProgramKind::Lsm) {
            env.fail(VerificationError::HelperNotAllowedForProgram {
                pc,
                helper,
                kind: env.ctx.prog_kind,
            });
            return vec![];
        } else if matches!(env.ctx.prog_kind, ProgramKind::Tracing)
            && matches!(env.ctx.kfunc.as_deref(), Some("d_path"))
        {
            env.fail(VerificationError::HelperNotAllowedForProgram {
                pc,
                helper,
                kind: env.ctx.prog_kind,
            });
            return vec![];
        }
    }

    // W3.4b: callback-taking helpers (bpf_loop / bpf_for_each_map_elem /
    // bpf_timer_set_callback) split into two successors:
    //   - "skip": helper returns to pc+1 with its normal return-value
    //     bounds; the callback body is not treated as executing along
    //     this path (abstractly: zero iterations).
    //   - "enter callback": push a callback-flagged frame at the
    //     subprog entry with typed args. On the callback's Exit we
    //     drop the path (see `transfer_exit`), so only the skip path
    //     carries helper post-state forward.
    if is_callback_helper(helper) {
        return transfer_callback_helper(env, state, &in_types, helper);
    }

    // bpf_get_local_storage doesn't not support type 1 map and flag must be 0
    if helper == constants::BPF_GET_LOCAL_STORAGE {
        if let RegType::PtrToMapObject { map_idx } = state.types.get(Reg::R1)
            && let Some(map_def) = env.ctx.map_defs.get(map_idx)
            && map_def.type_ == constants::BPF_MAP_TYPE_HASH
        {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        }
        if !state.domain.proven_zero(Reg::R2) {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R2 });
            return vec![];
        }
    }

    // ========================================================================
    // Normal helper handling
    // ========================================================================

    // 1. Update types
    update_call_types(env, &in_types, &mut state, helper);

    // 2. Apply return value bounds for specific helpers
    apply_return_bounds(&mut state, helper);

    // 2.1 Scalar ID for helper return value.
    // An unknown scalar R0 gets a fresh id so that copies of it can later
    // be linked and refined together (W2.1c).  Pointer or constant returns
    // don't need scalar linking.
    use crate::analysis::machine::reg_types::RegType;
    if state.types.get(Reg::R0) == RegType::ScalarValue
        && state.get_tnum(Reg::R0).is_unknown()
    {
        state.alloc_scalar_id(Reg::R0);
    } else {
        state.clear_scalar_id(Reg::R0);
    }

    // 2.5 Initialize memory buffers for PtrToUninitMem arguments
    initialize_uninit_mem_args(&mut state, &in_types, helper);

    // 3. Update DBM - forget caller-saved registers and reset Tnums
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        state.domain.forget(r);
        state.set_tnum(r, Tnum::unknown());
        state.clear_scalar_id(r);
    }

    // 4. Forget packet pointer DBM entries if they were invalidated
    if helper_invalidates_packets(helper) {
        for r in Reg::ALL {
            if r != Reg::R10 {
                match in_types.get(r) {
                    RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta => {
                        state.domain.forget(r);
                    }
                    _ => {}
                }
            }
        }
        state.domain.reset_packet_anchors();
    }

    // 5. Advance PC and return
    state.pc += 1;
    vec![state]
}

/// Initializes stack slots that were passed as PtrToUninitMem helper arguments.
fn initialize_uninit_mem_args(
    state: &mut State,
    in_types: &crate::analysis::machine::reg_types::TypeState,
    helper: u32,
) {
    use super::signatures::{ArgKind, get_helper_proto, get_mem_size_pairs};
    use crate::analysis::transfer::types::update_store_types;
    use crate::ast::MemSize;

    if let Some(sig) = get_helper_proto(helper) {
        for pair in get_mem_size_pairs(helper) {
            if let Some(ptr_arg_type) = sig.args.get(pair.ptr_reg.idx().saturating_sub(2))
                && matches!(ptr_arg_type, ArgKind::PtrToUninitMem)
            {
                if let RegType::PtrToStack { frame_level } = in_types.get(pair.ptr_reg) {
                    if let Some(off) = state.domain.get_distance_fixed(pair.ptr_reg, Reg::R10) {
                        let (_, max_size) = state.domain.get_interval(pair.size_reg);
                        {
                            if max_size != i64::MAX && max_size > 0 {
                                let max_bytes = (max_size as usize).min(512); // Bound to max stack size just in case
                                let stack = state.stack_at_mut(frame_level);
                                for i in 0..max_bytes {
                                    if let Ok(slot) = i16::try_from(off + i as i64) {
                                        update_store_types(
                                            stack,
                                            RegType::ScalarValue,
                                            MemSize::U8,
                                            Some(slot as i64),
                                        );
                                    }
                                }
                            }
                        }
                    } else {
                        trace!("Could not get fixed distance to R10");
                    }
                } else {
                    trace!(
                        "Arg is NOT PtrToStack, it is {:?}",
                        state.types.get(pair.ptr_reg)
                    );
                }
            }
        }
    }
}

/// Apply return value bounds based on helper semantics.
fn apply_return_bounds(state: &mut State, helper: u32) {
    state.domain.forget(Reg::R0);
    state.set_tnum(Reg::R0, Tnum::unknown());
    match helper {
        constants::BPF_REDIRECT => {
            state.domain.assume_ge_imm(Reg::R0, 0);
            state.domain.assume_le_imm(Reg::R0, 7);
        }
        constants::BPF_FIB_LOOKUP => {
            state.domain.assume_ge_imm(Reg::R0, 0);
            state.domain.assume_le_imm(Reg::R0, 8);
        }
        constants::BPF_MAP_UPDATE_ELEM
        | constants::BPF_MAP_DELETE_ELEM
        | constants::BPF_SKB_STORE_BYTES
        | constants::BPF_SKB_LOAD_BYTES
        | constants::BPF_XDP_ADJUST_HEAD
        | constants::BPF_L3_CSUM_REPLACE
        | constants::BPF_L4_CSUM_REPLACE
        | constants::BPF_GET_CURRENT_COMM
        | constants::BPF_SKB_VLAN_PUSH
        | constants::BPF_SKB_VLAN_POP
        | constants::BPF_SOCK_MAP_UPDATE => {
            // Returns 0 on success, or -errno
            state.domain.assume_le_imm(Reg::R0, 0);
            state.domain.assume_ge_imm(Reg::R0, -constants::MAX_ERRNO);
        }
        constants::BPF_GET_PRANDOM_U32
        | constants::BPF_GET_CGROUP_CLASS_ID
        | constants::BPF_GET_HASH_RECALC => {
            // Returns a positive u32
            state.domain.assume_ge_imm(Reg::R0, 0);
            state.domain.assume_le_imm(Reg::R0, 0xFFFF_FFFF);
            state.set_tnum(Reg::R0, Tnum::u32_unknown());
            // Assign scalar_id for tracking related scalars
            interval_set_scalar_id(&mut state.domain, Reg::R0);
        }
        constants::BPF_CSUM_DIFF => {
            // Returns a positive u32 (checksum) or negative error
            state.domain.assume_ge_imm(Reg::R0, -constants::MAX_ERRNO);
            state.domain.assume_le_imm(Reg::R0, 0xFFFF_FFFF);
            state.set_tnum(Reg::R0, Tnum::u32_unknown());
        }
        constants::BPF_GET_TASK_STACK => {
            let mem_size_pairs = get_mem_size_pairs(helper);
            let size_reg = mem_size_pairs[0].size_reg;
            let (_, hi) = state.domain.get_interval(size_reg);
            state.domain.assume_le_imm(Reg::R0, hi);
        }
        constants::BPF_GET_STACK => {
            let mem_size_pairs = get_mem_size_pairs(helper);
            let size_reg = mem_size_pairs[0].size_reg;
            let (_, hi) = state.domain.get_interval(size_reg);
            state.domain.assume_le_imm(Reg::R0, hi);
            state.domain.assume_ge_imm(Reg::R0, -constants::MAX_ERRNO);
        }
        constants::BPF_KFUNC_CALL_DUMMY => {
            // Assume unsupported external kfuncs return an unknown opaque pointer that can be dereferenced
            state.types.set(
                Reg::R0,
                RegType::PtrToBtfId {
                    type_name: "unknown",
                    flags: PtrFlags::UNTRUSTED,
                },
            );
        }
        _ => {}
    }
}

/// True when `helper` takes a callback pointer argument (W3.4b).
fn is_callback_helper(helper: u32) -> bool {
    matches!(
        helper,
        constants::BPF_LOOP
            | constants::BPF_FOR_EACH_MAP_ELEM
            | constants::BPF_TIMER_SET_CALLBACK
    )
}

/// Which register holds the callback pointer for `helper`.
fn callback_arg_reg(helper: u32) -> Reg {
    match helper {
        constants::BPF_LOOP => Reg::R2,
        constants::BPF_FOR_EACH_MAP_ELEM => Reg::R2,
        constants::BPF_TIMER_SET_CALLBACK => Reg::R2,
        _ => unreachable!(),
    }
}

/// Transfer for callback-taking helpers. Emits the skip successor (normal
/// helper post-state at pc+1) and the enter-callback successor (pushes a
/// callback frame at subprog_pc with typed args). See `is_callback_helper`.
fn transfer_callback_helper(
    env: &mut VerifierEnv,
    state: State,
    in_types: &crate::analysis::machine::reg_types::TypeState,
    helper: u32,
) -> Vec<State> {
    let pc = state.pc;
    let cb_reg = callback_arg_reg(helper);
    let RegType::PtrToCallback { subprog_pc } = state.types.get(cb_reg) else {
        env.fail(VerificationError::InvalidArgType { pc, reg: cb_reg });
        return vec![];
    };
    let cb_entry = subprog_pc as usize;

    // W3.4c: bpf_timer_set_callback must be registered with no held locks
    // and no unreleased refs — the callback runs asynchronously, so any
    // state the verifier is still tracking on the caller frame would be
    // leaked. (Other callback helpers are synchronous and rely on the
    // generic active-lock check in `transfer_call` above.)
    if helper == constants::BPF_TIMER_SET_CALLBACK
        && (state.has_active_lock() || state.has_unreleased_refs())
    {
        env.fail(VerificationError::InvalidArgType { pc, reg: cb_reg });
        return vec![];
    }

    // Successor A: skip the callback and emit the helper's post-state.
    let mut skip_state = state.clone();
    update_call_types(env, in_types, &mut skip_state, helper);
    apply_return_bounds(&mut skip_state, helper);
    if skip_state.types.get(Reg::R0) == RegType::ScalarValue
        && skip_state.get_tnum(Reg::R0).is_unknown()
    {
        skip_state.alloc_scalar_id(Reg::R0);
    } else {
        skip_state.clear_scalar_id(Reg::R0);
    }
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        skip_state.domain.forget(r);
        skip_state.set_tnum(r, Tnum::unknown());
        skip_state.clear_scalar_id(r);
    }
    skip_state.pc = pc + 1;

    // Successor B: enter the callback with a fresh frame. Bail with the
    // skip state only if we're already at the kernel's max call depth.
    if state.num_frames() >= 8 {
        return vec![skip_state];
    }

    let mut cb_state = state;
    cb_state.push_callback_frame(pc + 1, helper);
    update_call_rel_types(&mut cb_state);
    cb_state.domain.clear_packet_size_bounds();

    // Minimal arg typing: R1 is always a scalar (iteration index / map
    // pointer / map-elem pointer depending on helper); R2+ are left
    // unsupported for now so callbacks that dereference them REJECT.
    // Full per-helper arg typing lands alongside richer signature
    // validation in a follow-up.
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        cb_state.types.set(r, RegType::NotInit);
        cb_state.domain.forget(r);
        cb_state.set_tnum(r, Tnum::unknown());
        cb_state.clear_scalar_id(r);
    }
    cb_state.types.set(Reg::R1, RegType::ScalarValue);
    cb_state.domain.forget(Reg::R1);
    cb_state.set_tnum(Reg::R1, Tnum::unknown());
    cb_state.alloc_scalar_id(Reg::R1);

    cb_state.pc = cb_entry;

    vec![skip_state, cb_state]
}

fn allowed_while_in_active_lock(helper: u32) -> bool {
    match helper {
        constants::BPF_GET_PRANDOM_U32 => false,
        _ => true,
    }
}

/// Transfer function for relative Call (BPF-to-BPF function call) instructions.
pub(crate) fn transfer_call_rel(
    env: &mut VerifierEnv,
    mut state: State,
    target: usize,
) -> Vec<State> {
    let pc = state.pc;
    if state.num_frames() >= 8 {
        env.fail(VerificationError::MaxCallDepthExceeded { pc });
        return vec![];
    }

    state.push_frame(pc + 1);
    update_call_rel_types(&mut state);

    // Clear packet size bounds for the callee.
    // The kernel verifier tracks bounds per-function, so each function
    // starts with no proven packet size. This is important for cases where
    // the caller did a bounds check but the callee spills a fresh packet
    // pointer before doing its own check.
    state.domain.clear_packet_size_bounds();

    state.pc = target;

    vec![state]
}

fn check_and_handle_spin_lock(env: &mut VerifierEnv, state: &mut State, helper: u32) -> bool {
    let pc = state.pc;
    match state.types.get(Reg::R1) {
        RegType::PtrToMapValue {
            offset: _,
            map_idx,
            id,
        } => match env.ctx.map_defs.get(map_idx) {
            Some(map_def) => {
                if let Some(val_type_id) = map_def.btf_val_type_id {
                    if helper == constants::BPF_SPIN_LOCK {
                        if state.has_active_lock() {
                            env.fail(VerificationError::LockAlreadyHeld { pc });
                            return false;
                        }
                        let special_fields = env.ctx.btf.find_special_fields(val_type_id);
                        let lock_offset_op = special_fields
                            .iter()
                            .find(|f| f.kind == SpecialFieldKind::SpinLock)
                            .map(|f| f.offset);
                        if lock_offset_op.is_none() {
                            env.fail(VerificationError::InvalidBtfType);
                            return false;
                        } else {
                            let lock_offset = lock_offset_op.unwrap();
                            state.acquire_lock(id, lock_offset);
                        }
                    } else {
                        if !state.has_active_lock() {
                            env.fail(VerificationError::LockNotHeld { pc });
                            return false;
                        } else {
                            let lock = state.get_active_lock().unwrap();
                            if lock.ptr_id != id {
                                env.fail(VerificationError::LockNotHeld { pc });
                                return false;
                            }
                        }
                        state.release_lock();
                    }
                } else {
                    env.fail(VerificationError::InvalidBtfType);
                    return false;
                }
            }
            _ => {
                env.fail(VerificationError::MapNotFound { pc, map_idx });
                return false;
            }
        },
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return false;
        }
    }
    true
}

pub(crate) fn interval_set_scalar_id(domain: &mut NumericDomain, reg: Reg) {
    if let NumericDomain::Interval(ivl) = domain {
        ivl.get_bounds_mut(reg).scalar_id = Some(new_scalar_id());
    }
}

pub(crate) fn restore_interval_ptr_offset_from_return(
    domain: &mut NumericDomain,
    ret_type: &RegType,
    ret_interval_ptr_offset: (Option<i64>, Option<u64>, Option<i64>),
) {
    if let (Some(off), var_off_opt, range) = ret_interval_ptr_offset {
        use crate::domains::interval::PtrOffset;

        // Determine anchor from register type
        let anchor = match ret_type {
            RegType::PtrToPacket => Some(Reg::AnchorData),
            RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
            RegType::PtrToPacketEnd => Some(Reg::AnchorDataEnd),
            _ => None,
        };

        if let Some(anchor) = anchor {
            if let NumericDomain::Interval(ivl) = domain {
                let var_off = var_off_opt.unwrap_or(0);
                let ptr_offset = PtrOffset {
                    anchor,
                    off,
                    var_off,
                    range,
                };
                ivl.get_mut(Reg::R0).ptr_offset = Some(ptr_offset);
            }
        }
    }
}

pub(crate) fn restore_callee_interval_packet_info(
    domain: &mut NumericDomain,
    caller_types: &crate::analysis::machine::reg_types::TypeState,
    callee_saved_packet_info: Vec<(Reg, RegType, (Option<i64>, Option<u64>, Option<i64>))>,
) {
    for (reg, callee_type, (off_opt, var_off_opt, range)) in callee_saved_packet_info {
        if let (Some(off), Some(range_val)) = (off_opt, range) {
            let anchor = match callee_type {
                RegType::PtrToPacket => Some(Reg::AnchorData),
                RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
                _ => None,
            };

            if let Some(anchor) = anchor {
                if matches!(
                    caller_types.get(reg),
                    RegType::PtrToPacket | RegType::PtrToPacketMeta
                ) {
                    if let NumericDomain::Interval(ivl) = domain {
                        if let Some(caller_ptr_off) = ivl.get_ptr_offset(reg) {
                            if caller_ptr_off.anchor == anchor
                                && caller_ptr_off.off == off
                                && caller_ptr_off.var_off == var_off_opt.unwrap_or(0)
                            {
                                let caller_range = caller_ptr_off.range.unwrap_or(0);
                                if range_val > caller_range {
                                    let mut new_ptr_off = caller_ptr_off.clone();
                                    new_ptr_off.range = Some(range_val);
                                    ivl.get_mut(reg).ptr_offset = Some(new_ptr_off);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
