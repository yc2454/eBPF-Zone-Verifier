// src/analysis.rs

// Module Declarations (Look for files in src/analysis/)
pub mod context;
pub mod transfer;
pub mod access;
pub mod state;
pub mod heuristics;

use std::collections::VecDeque;
use crate::ast::{Instr, Program};
use crate::dbm::Dbm;
use crate::domain::{RegType, TypeState, REG_ENV, Reg};
use crate::stats::AnalysisStats;
use crate::utils::dbm_equals;

// Imports from our own sub-modules
use self::context::ExecContext;
use self::transfer::transfer_instr;
use self::state::{refine_branch_types, update_reg_types_for_instr};

pub fn analyze_program(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    stats: &mut AnalysisStats,
) -> Vec<Dbm> {
    let n = prog.instrs.len();
    let mut states: Vec<Option<Dbm>> = vec![None; n];
    let mut type_states: Vec<Option<TypeState>> = vec![None; n];
    
    // Initial State Setup
    let mut entry_types = TypeState::new_not_init();
    entry_types.set(Reg::R1, RegType::PtrToCtx);
    entry_types.set(ctx.r10, RegType::PtrToStack);
    entry_types.set(Reg::R0, RegType::ScalarValue);
    
    let mut worklist = VecDeque::new();
    states[0] = Some(entry_dbm);
    type_states[0] = Some(entry_types);
    worklist.push_back(0);

    while let Some(pc) = worklist.pop_front() {
        if stats.abort { 
            println!("Analysis aborted due to previous errors."); 
            break; 
        }

        let instr = &prog.instrs[pc];
        let raw_pc = prog.pc_map[pc]; 
        
        let in_dbm = states[pc].as_ref().unwrap();
        let in_types = type_states[pc].as_ref().unwrap().clone();
        
        println!("Instr: {} (Raw PC: {})", instr, raw_pc);

        // 1. Transfer Function (Compute Next State)
        let succs = transfer_instr(ctx, in_dbm, pc, instr, stats, &in_types);
        
        if stats.abort { 
            println!("Analysis aborted due to previous errors."); 
            break; 
        }

        for (succ_pc, succ_dbm, succ_types) in succs {
            if succ_pc >= n { continue; }
            
            let mut edge_types = succ_types;
            
            // 2. State Updates (Reg Types, Range Refinement, Stack Protection)
            // Skip update_reg_types for calls to preserve R0 return type
            if !matches!(instr, Instr::Call { .. }) {
                update_reg_types_for_instr(ctx, instr, &mut edge_types, &in_types, raw_pc);
            }
            
            println!("Instr: {} (Raw PC: {})", instr, raw_pc);
            
            // 3. Branch Refinement (Packet Ranges, Map Pointers)
            refine_branch_types(instr, succ_pc, &succ_dbm, &mut edge_types);

            // 4. Join / Fixpoint Check
            match (&mut states[succ_pc], &mut type_states[succ_pc]) {
                (slot_dbm @ None, slot_types @ None) => {
                    *slot_dbm = Some(succ_dbm);
                    *slot_types = Some(edge_types);
                    worklist.push_back(succ_pc);
                }
                (Some(existing_dbm), Some(existing_types)) => {
                    let joined_dbm = existing_dbm.join(&succ_dbm);
                    let dbm_changed = !dbm_equals(existing_dbm, &joined_dbm);
                    *existing_dbm = joined_dbm;

                    // Note: join_in_place contains the Aggressive Merge logic
                    let types_changed = existing_types.join_in_place(&edge_types);
                    
                    if dbm_changed || types_changed { 
                        worklist.push_back(succ_pc); 
                    }
                }
                _ => { 
                    panic!("Inconsistent state at pc {}", succ_pc); 
                }
            }
        }
    }
    
    states.into_iter().map(|opt| opt.unwrap_or_else(|| Dbm::new(REG_ENV.len()))).collect()
}
