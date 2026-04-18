use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/memory/map.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::MapLoadKind;
use crate::common::constants;
use crate::domains::numeric::NumericDomain;
use crate::parsing::elf::BpfMapDef;
use log::error;

pub fn check_map_rw(env: &mut VerifierEnv, map_idx: usize, pc: usize, is_write: bool) {
    let flag_to_check = if is_write {
        constants::BPF_F_RDONLY_PROG
    } else {
        constants::BPF_F_WRONLY_PROG
    };
    let ctx = env.ctx;
    if let Some(map_def) = ctx.map_defs.get(map_idx) {
        if map_def.map_flags == flag_to_check {
            error!("Map read is forbidden!");
            env.fail(VerificationError::MapLoadForbidden { pc, map_idx });
        }
    } else {
        error!("Map not found!");
        env.fail(VerificationError::MapNotFound { pc, map_idx })
    }
}

pub fn check_btf_fields_access(
    env: &mut VerifierEnv,
    pc: usize,
    final_offset: i64,
    access_end: i64,
    size: i64,
    map_limit: i64,
    btf_id: u32,
) {
    let btf_fields = env.ctx.btf.find_special_fields(btf_id);
    for field in btf_fields {
        let field_end = field.offset + field.size;

        if final_offset < field_end.into() && access_end > field.offset.into() {
            error!("Cannot access BTF field");
            env.fail(VerificationError::UnsafeMapLoad {
                pc,
                off: final_offset,
                size,
                limit: map_limit,
            });
        }
    }
}

pub fn check_map_access(
    env: &mut VerifierEnv,
    state: &State,
    map_limit: i64,
    map_off_opt: Option<i64>,
    map_idx: usize,
    base: Reg,
    map_def: &BpfMapDef,
    insn_off: i16,
    size: i64,
    pc: usize,
) {
    // For interval domain, try to use PtrOffset for bounds checking
    if let NumericDomain::Interval(ref ivl) = state.domain {
        if interval_check_map_access(
            env, ivl, map_limit, map_idx, base, map_def, insn_off, size, pc,
        ) {
            return;
        }
    }

    zone_check_map_access(
        env,
        state,
        map_limit,
        map_off_opt,
        map_idx,
        base,
        map_def,
        insn_off,
        size,
        pc,
    );
}

fn interval_check_map_access(
    env: &mut VerifierEnv,
    ivl: &crate::domains::interval::IntervalState,
    map_limit: i64,
    _map_idx: usize,
    base: Reg,
    map_def: &BpfMapDef,
    insn_off: i16,
    size: i64,
    pc: usize,
) -> bool {
    if let Some(ptr_off) = ivl.get_ptr_offset(base) {
        // Use PtrOffset to get offset range from buffer start
        let min_off = ptr_off.min_offset() + (insn_off as i64);
        let max_off = ptr_off.max_offset() + (insn_off as i64) + size;

        if let Some(btf_id) = map_def.btf_val_type_id {
            check_btf_fields_access(env, pc, min_off, max_off, size, map_limit, btf_id);
            return true;
        }

        if min_off >= 0 && max_off <= map_limit {
            return true; // Access is safe
        } else {
            error!(
                "Unsafe variable map access at pc {}: range [{}, {}], limit {}",
                pc, min_off, max_off, map_limit
            );
            env.fail(VerificationError::UnsafeMapLoad {
                pc,
                off: min_off,
                size,
                limit: map_limit,
            });
            return true;
        }
    }
    false
}

fn zone_check_map_access(
    env: &mut VerifierEnv,
    state: &State,
    map_limit: i64,
    map_off_opt: Option<i64>,
    map_idx: usize,
    base: Reg,
    map_def: &BpfMapDef,
    insn_off: i16,
    size: i64,
    pc: usize,
) {
    // Zone domain or interval without PtrOffset: use scalar bounds
    let (dbm_min, dbm_max) = state.domain.get_interval(base);
    if dbm_min != i64::MIN && dbm_max != i64::MAX {
        let min_val = dbm_min;
        let max_val = dbm_max;
        let access_start = min_val + (insn_off as i64);
        let access_end = max_val + (insn_off as i64) + size;

        if let Some(btf_id) = map_def.btf_val_type_id {
            check_btf_fields_access(
                env,
                pc,
                insn_off.into(),
                access_end,
                size,
                map_limit,
                btf_id,
            );
            return;
        }

        if access_start >= 0 && access_end <= map_limit {
        } else {
            error!(
                "Unsafe variable map access at pc {}: range [{}, {}], limit {}",
                pc, access_start, access_end, map_limit
            );
            env.fail(VerificationError::UnsafeMapLoad {
                pc,
                off: access_start,
                size,
                limit: map_limit,
            });
        }
    } else if let Some(fixed_off) = map_off_opt {
        let final_offset = fixed_off + (insn_off as i64);
        let access_end = final_offset + size;

        if let Some(btf_id) = map_def.btf_val_type_id {
            check_btf_fields_access(env, pc, final_offset, access_end, size, map_limit, btf_id);
            return;
        }

        if final_offset >= 0 && access_end <= map_limit {
        } else {
            error!(
                "Unsafe map access at pc {}: off {} limit {}",
                pc, final_offset, map_limit
            );
            env.fail(VerificationError::UnsafeMapAccess { pc, size, map_idx });
        }
    } else {
        error!("Unbounded variable map access at pc {}", pc);
        env.fail(VerificationError::UnsafeMapLoad {
            pc,
            off: insn_off.into(),
            size,
            limit: map_limit,
        });
    }
}

pub(crate) fn transfer_map_load(
    env: &mut VerifierEnv,
    mut state: State,
    dst: Reg,
    kind: MapLoadKind,
    _map_fd: i32,
) -> Vec<State> {
    // Modern LD_IMM64 subtypes are recognized by the decoder but not yet
    // supported by the transfer domain. Fail cleanly here.
    let feature = match kind {
        MapLoadKind::MapPtr | MapLoadKind::MapValue => None,
        MapLoadKind::PseudoFunc { .. } => Some("LD_IMM64 BPF_PSEUDO_FUNC (callback pointer)"),
        MapLoadKind::PseudoBtfId { .. } => Some("LD_IMM64 BPF_PSEUDO_BTF_ID (ksym/percpu)"),
        MapLoadKind::PseudoMapIdx => Some("LD_IMM64 BPF_PSEUDO_MAP_IDX"),
        MapLoadKind::PseudoMapIdxValue => Some("LD_IMM64 BPF_PSEUDO_MAP_IDX_VALUE"),
    };
    if let Some(feature) = feature {
        env.fail(VerificationError::UnsupportedModernFeature {
            pc: state.pc,
            feature,
        });
        return vec![];
    }

    let reloc_info = env.ctx.pc_to_reloc.get(&state.pc);
    if let Some(reloc) = reloc_info {
        crate::analysis::transfer::types::update_map_load_types(
            &mut state.types,
            kind,
            reloc.map_idx,
            dst,
        );
        state.domain.forget(dst);
        state.pc += 2;
        vec![state]
    } else {
        env.fail(VerificationError::RelocationInfoMissing { pc: state.pc });
        vec![]
    }
}
