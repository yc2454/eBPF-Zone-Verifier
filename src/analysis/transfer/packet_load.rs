use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::analysis::reg_types::RegType;
use crate::ast::{MemSize, PacketLoadMode};
use crate::zone::domain::{Reg, forget, assume_range};
use crate::analysis::transfer::common::check_reg_readable;
use crate::analysis::transfer::types::update_packet_load_types;

pub(crate) fn transfer_packet_load(
    env: &mut VerifierEnv,
    mut state: State,
    size: MemSize,
    _mode: PacketLoadMode,
    _offset_imm: i32,
    src: Option<Reg>,
) -> Vec<State> {
    // 1. Check R6 Context
    // Legacy instructions HARDCODE R6 as the context pointer.
    let r6_type = state.types.get(Reg::R6);
    if !matches!(r6_type, RegType::PtrToCtx) {
        // Fail: Legacy load requires R6 to be the context
        return vec![];
    }

    // 2. Handle Indirect Source (if present)
    if let Some(reg) = src {
        if !check_reg_readable(env, &state, reg) {
            return vec![];
        }
    }

    update_packet_load_types(&mut state.types);
    
    // We assume the load might succeed.
    // (In reality, these instructions include built-in bounds checks that
    // terminate the program if out-of-bounds. For verification, we assume 
    // the "success" path continues to the next instruction.)
    
    // Clear old constraints on R0 and set new range if width is small
    forget(&mut state.dbm, Reg::R0);
    
    match size {
        MemSize::U8  => assume_range(&mut state.dbm, Reg::R0, 0, 255),
        MemSize::U16 => assume_range(&mut state.dbm, Reg::R0, 0, 65535),
        MemSize::U32 => assume_range(&mut state.dbm, Reg::R0, 0, 4294967295),
        MemSize::U64 => {}, // Full range
    }

    state.pc += 1;
    vec![state]
}