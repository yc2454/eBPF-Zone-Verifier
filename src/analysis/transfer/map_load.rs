use crate::analysis::env::{VerifierEnv, VerificationError};
use crate::analysis::state::State;
use crate::ast::{MapLoadKind};
use crate::zone::domain::{Reg, forget};
use crate::analysis::transfer::types::update_map_load_types;

pub(crate) fn transfer_map_load(
    env: &mut VerifierEnv,
    mut state: State,
    dst: Reg,
    kind: MapLoadKind,
    map_fd: i32
) -> Vec<State> {
    // 1. Common Logic: Verify Map Exists
    if let Some(_map_def) = env.ctx.map_defs.get(map_fd as usize) {
        update_map_load_types(&mut state.types, kind, map_fd as usize, dst);
        forget(&mut state.dbm, dst);
        state.pc += 1;
        vec![state]
    } else {
        env.fail(VerificationError::MapNotFound { pc: state.pc, map_idx: map_fd as usize });
        return vec![]
    }
}
