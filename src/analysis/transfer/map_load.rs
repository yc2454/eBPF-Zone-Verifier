use crate::analysis::machine::env::{VerifierEnv, VerificationError};
use crate::analysis::machine::state::State;
use crate::ast::{MapLoadKind};
use crate::zone::domain::{Reg, forget};
use crate::analysis::transfer::types::update_map_load_types;

pub(crate) fn transfer_map_load(
    env: &mut VerifierEnv,
    mut state: State,
    dst: Reg,
    kind: MapLoadKind,
    _map_fd: i32
) -> Vec<State> {
    let reloc_info = env.ctx.pc_to_reloc.get(&state.pc);
    if let Some(reloc) = reloc_info {
        update_map_load_types(&mut state.types, kind, reloc.map_idx as usize, dst);
        forget(&mut state.dbm, dst);
        state.pc += 2;
        return vec![state];
    } else {
        env.fail(VerificationError::RelocationInfoMissing { pc: state.pc });
        return vec![]
    }
}
