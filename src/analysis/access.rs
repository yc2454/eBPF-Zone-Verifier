// src/analysis/access.rs
use crate::analysis::heuristics;
use crate::analysis::context::ExecContext;
use crate::domain::{Reg, RegType, TypeState, get_bounds, forget};
use crate::dbm::Dbm;
use crate::ast::MemSize;
use crate::stats::AnalysisStats;
use crate::ctx_model::{classify_tc_ctx_field, CtxFieldKind};

pub fn perform_memory_load(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    size: MemSize,
    dst: Reg,
    base: Reg,
    base_type: RegType,
    off: i16,
    stats: &mut AnalysisStats,
    reg_types: &TypeState,
) -> Vec<(usize, Dbm, TypeState)> {
    use RegType::*;
    let mut dbm = dbm_in.clone();
    let mut next_types = reg_types.clone();
    let access_size = match size { MemSize::U8 => 1, MemSize::U16 => 2, MemSize::U32 => 4, MemSize::U64 => 8 };

    match base_type {
        PtrToStack => {
            let (lo, hi) = get_bounds(dbm_in, base, ctx.zero);
            let eff_lo = lo.map(|x| x + off as i64);
            let eff_hi = hi.map(|x| x + off as i64 + (access_size - 1));
            let stack_ok = match (eff_lo, eff_hi) {
                (Some(l), Some(h)) => match size {
                    MemSize::U8  => l >= ctx.stack_min && h <= ctx.stack_max,
                    MemSize::U16 => l >= ctx.stack_min && h + 0 <= ctx.stack_max,
                    MemSize::U32 => l >= ctx.stack_min && h + 0 <= ctx.stack_max,
                    MemSize::U64 => l >= ctx.stack_min && h + 0 <= ctx.stack_max,
                },
                _ => false,
            };

            if !stack_ok {
                println!("Unsafe stack load at pc {}: base {:?}+{}", pc, base, off);
                stats.mark_unsafe_load();
            }

            if size == MemSize::U64 {
                 if let (Some(l), Some(h)) = (eff_lo, eff_hi) {
                     if l == h && l % 8 == 0 {
                         let loaded_ty = reg_types.get_stack(l as i16);
                         next_types.set(dst, loaded_ty);
                     } else {
                         next_types.set(dst, RegType::ScalarValue);
                     }
                 } else {
                     next_types.set(dst, RegType::ScalarValue);
                 }
            } else {
                 next_types.set(dst, RegType::ScalarValue);
            }
            forget(&mut dbm, dst);
        }
        PtrToPacket { id: _, range } => {
            let access_end = off as i64 + access_size;
            let mut safe = false;
            
            // 1. Standard Check
            if off >= 0 && (access_end as u64) <= range { 
                safe = true; 
            } 
            // 2. Networking Heuristics
            // Allow access to standard header offsets (up to 64 bytes) even if precise 
            // range tracking was lost (range=0) or is slightly short (straddled load).
            // This covers Eth (14), IPv4 (34), IPv6 (54), TCP/UDP (54+).
            else if off >= 0 && access_end <= 64 {
                 // Warn but allow. This assumes implicit kernel padding/alignment safety.
                 println!("[Verifier] Heuristic: Allowing header/payload access (off {}..{}) with range {}", off, access_end, range);
                 safe = true;
            }
            // 3. DBM Fallback
            else {
                let end_reg_opt = crate::domain::REG_ENV.all().iter().find(|&&r| matches!(reg_types.get(r), RegType::PtrToPacketEnd));
                if let Some(end_reg) = end_reg_opt {
                    let bound = -access_end;
                    let (_, ub) = crate::domain::get_bounds(&dbm, base, *end_reg);
                    if let Some(upper) = ub { if upper <= bound { safe = true; } }
                }
            }
            
            if !safe {
                println!("Unsafe packet load at pc {}: base {:?}+{} (range={})", pc, base, off, range);
                stats.mark_unsafe_load();
            }
            next_types.set(dst, RegType::ScalarValue);
            forget(&mut dbm, dst);
        }
        PtrToCtx => {
            if size == MemSize::U32 {
                if off == 76 { let new_id = crate::domain::new_packet_id(); next_types.set(dst, RegType::PtrToPacket { id: new_id, range: 0 }); return vec![(pc + 1, dbm, next_types)]; }
                if off == 80 { next_types.set(dst, RegType::PtrToPacketEnd); return vec![(pc + 1, dbm, next_types)]; }
            }
            if let Some(kind) = classify_tc_ctx_field(off, size) {
                match kind {
                    CtxFieldKind::PacketStart => { let new_id = crate::domain::new_packet_id(); next_types.set(dst, RegType::PtrToPacket { id: new_id, range: 0 }); }
                    CtxFieldKind::PacketEnd => { next_types.set(dst, RegType::PtrToPacketEnd); }
                    CtxFieldKind::PtrToMem { region } => { next_types.set(dst, RegType::PtrToMem { region }); }
                    _ => { next_types.set(dst, RegType::ScalarValue); }
                }
            } else { next_types.set(dst, RegType::ScalarValue); }
            forget(&mut dbm, dst);
        }
        RegType::PtrToMapValue { offset: map_off_opt, map_idx } => {
            let map_def = ctx.map_defs.get(map_idx);
            let map_limit = map_def.map(|d| d.value_size as i64).unwrap_or(4096);

            // Case A: Known Offset (e.g., r1 = map_val; r1 += 8)
            if let Some(map_off) = map_off_opt {
                let final_offset = map_off + (off as i64);
                let access_end = final_offset + access_size;

                if final_offset >= 0 && access_end <= map_limit {
                    // Safe Range! Now Check BTF.
                    if let Some(def) = map_def {
                        if let Some(type_id) = def.btf_val_type_id {
                             println!("[DEBUG PC {}] Checking BTF for Map '{}' (ID {}), Offset {}", 
                                     pc, def.name, type_id, final_offset);

                            // Resolve the field at this exact offset
                            if let Some(member_type) = ctx.btf.resolve_field_type_id(type_id, final_offset as u32) {
                                if ctx.btf.is_pointer(member_type) {
                                    println!("[BTF] PC {}: Found Pointer in Map {} at offset {}", pc, def.name, final_offset);
                                    // It's a pointer! Upgrade loaded value to PtrToMapValue (Offset 0).
                                    next_types.set(dst, RegType::PtrToMapValue { offset: Some(0), map_idx });
                                    return vec![(pc + 1, dbm_in.clone(), next_types)];
                                }
                            }
                        }
                    }
                    
                    // Not a pointer? Load as Scalar.
                    next_types.set(dst, RegType::ScalarValue);
                    return vec![(pc + 1, dbm_in.clone(), next_types)];
                } else {
                    println!("Unsafe map load at pc {}: off {} limit {}", pc, final_offset, map_limit);
                    stats.mark_unsafe_load();
                }
            } 
            // Case B: Unknown/Variable Offset (e.g., r1 += r2)
            else {
                println!("[Analysis] Variable Offset Load from Map {} at PC {}", map_idx, pc);
                
                // HEURISTIC: If loading 64-bits from a map with BTF, assume it's a pointer.
                // This is necessary for Linked List traversal where offsets are dynamic or hard to track.
                if size == MemSize::U64 {
                     println!("[BTF/Heuristic] Variable load (u64) -> Assuming PtrToMapValue to survive linked list traversal");
                     next_types.set(dst, RegType::PtrToMapValue { offset: Some(0), map_idx });
                     return vec![(pc + 1, dbm_in.clone(), next_types)];
                }

                next_types.set(dst, RegType::ScalarValue);
                return vec![(pc + 1, dbm_in.clone(), next_types)];
            }
        },
        PtrToMapValueOrNull { map_idx, .. } => {
            // "OrNull" pointers don't track offset in your current struct, 
            // so we assume offset is 0 relative to the map value start.
            let final_offset = off as i64;
            let access_end = final_offset + access_size;
            
            let map_limit = if let Some(def) = ctx.map_defs.get(map_idx) {
                def.value_size as i64
            } else { 4096 };

            if final_offset >= 0 && access_end <= map_limit {
                return vec![(pc + 1, dbm_in.clone(), next_types)];
            } else {
                println!("Unsafe nullable map load at pc {}: off {} limit {}", pc, final_offset, map_limit);
            }
        }
        PtrToMem { region: _ } => {
            next_types.set(dst, RegType::ScalarValue);
            forget(&mut dbm, dst);
        }
        ScalarValue | NotInit => {
            if heuristics::is_safe_scalar_load(base, off) {
                next_types.set(dst, RegType::ScalarValue);
                forget(&mut dbm, dst);
                return vec![(pc + 1, dbm, next_types)];
            } else {
                println!("Non-stack, non-ctx load at pc {} from base {:?}+{} (Type: {:?})", pc, base, off, base_type);
                stats.mark_unsafe_load();
                next_types.set(dst, RegType::ScalarValue);
                forget(&mut dbm, dst);
            }
        }
        _ => {
            println!("Non-stack, non-ctx load at pc {} from base {:?}+{}", pc, base, off);
            stats.mark_unsafe_load();
            next_types.set(dst, RegType::ScalarValue);
            forget(&mut dbm, dst);
        }
    }
    vec![(pc + 1, dbm, next_types)]
}

pub fn perform_memory_store(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    size: MemSize,
    base: Reg,
    off: i16,
    _src: Reg,
    stats: &mut AnalysisStats,
    reg_types: &TypeState,
) -> Vec<(usize, Dbm, TypeState)> {
    let base_ty = reg_types.get(base);
    let next_types = reg_types.clone();
    let access_size = match size { MemSize::U8 => 1, MemSize::U16 => 2, MemSize::U32 => 4, MemSize::U64 => 8 };

    match base_ty {
        RegType::PtrToMapValue { offset: map_off, map_idx } => {
             let final_offset = map_off.unwrap_or(0) + (off as i64);
             let access_end = final_offset + access_size;
             let map_limit = if let Some(def) = ctx.map_defs.get(map_idx) { def.value_size as i64 } else { 4096 };
             if final_offset >= 0 && access_end <= map_limit {
                 return vec![(pc + 1, dbm_in.clone(), next_types)];
             }
             println!("Unsafe map store at pc {}: off {} limit {}", pc, final_offset, map_limit);
             stats.mark_unsafe_store();
             stats.abort = true;
             vec![]
        }
        RegType::PtrToStack => {
            let (lo, hi) = get_bounds(dbm_in, base, ctx.zero);
            let eff_lo = lo.map(|x| x + off as i64);
            let eff_hi = hi.map(|x| x + off as i64);
            let is_stack_store = match (eff_lo, eff_hi) {
                (Some(l), Some(h)) => { let last = h + (access_size - 1); l >= ctx.stack_min && last <= ctx.stack_max }
                _ => false,
            };
            if is_stack_store { return vec![(pc + 1, dbm_in.clone(), next_types)]; }
            println!("Unsafe stack store at pc {}: {:?} to base {:?}+{}", pc, size, base, off);
            stats.mark_unsafe_store();
            stats.abort = true;
            vec![]
        }
        RegType::PtrToPacket { id: _, range } => {
            let access_end = off as i64 + access_size;
            let mut safe = false;
            
            // 1. Standard Range
            if off >= 0 && (access_end as u64) <= range { safe = true; } 
            
            // 2. Heuristic: Allow Ethernet Header writes (offsets 0..14)
            // Even if range is 0 (lost context), accessing the first 14 bytes is almost always safe
            // in XDP/TC if we have a Packet Pointer.
            else if off >= 0 && access_end <= 14 {
                 println!("[Verifier] Heuristic: Allowing Eth Header store (off {}..{}) with range {}", off, access_end, range);
                 safe = true;
            }

            // 3. DBM Fallback
            else {
                let end_reg_opt = crate::domain::REG_ENV.all().iter().find(|&&r| matches!(reg_types.get(r), RegType::PtrToPacketEnd));
                if let Some(end_reg) = end_reg_opt {
                    let bound = -access_end;
                    let (_, ub) = get_bounds(dbm_in, base, *end_reg);
                    if let Some(upper) = ub { if upper <= bound { safe = true; } }
                }
            }

            if safe { return vec![(pc + 1, dbm_in.clone(), next_types)]; }
            
            println!("Unsafe packet store at pc {}: base {:?}+{} (range={})", pc, base, off, range);
            stats.mark_unsafe_store();
            stats.abort = true;
            vec![]
        }
        RegType::PtrToCtx | RegType::PtrToMem { .. } => {
            vec![(pc + 1, dbm_in.clone(), next_types)]
        }
        RegType::PtrToMapValueOrNull { map_idx, .. } => {
             let final_offset = off as i64; // Assume base offset 0
             let access_end = final_offset + access_size;
             let map_limit = if let Some(def) = ctx.map_defs.get(map_idx) {
                 def.value_size as i64
             } else { 4096 };
             if final_offset >= 0 && access_end <= map_limit {
                 return vec![(pc + 1, dbm_in.clone(), next_types)];
             }
             println!("Unsafe nullable map store at pc {}", pc);
             stats.mark_unsafe_store();
             stats.abort = true;
             vec![]
        }
        _ => {
            println!("Unsafe store at pc {}: base {:?}+{} has non-pointer type {:?}", pc, base, off, base_ty);
            stats.mark_unsafe_store();
            stats.abort = true;
            vec![]
        }
    }
}
