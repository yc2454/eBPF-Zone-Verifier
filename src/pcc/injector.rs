use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use log::info;

use super::checker::VerifiedEntry;

fn apply_verified_packet_end_fact(
    succ_state: &mut State,
    i_idx: usize,
    j_idx: usize,
    c: i64,
    succ_pc: usize,
) {
    let Some(i) = Reg::idx_to_reg(i_idx) else {
        return;
    };
    let Some(j) = Reg::idx_to_reg(j_idx) else {
        return;
    };
    if j != Reg::AnchorDataEnd {
        return;
    }
    let Some(ivl) = succ_state.domain.as_interval_mut() else {
        return;
    };
    let Some(po) = ivl.get_ptr_offset(i).copied() else {
        return;
    };
    if po.anchor != Reg::AnchorData {
        return;
    }
    let proven_end_from_i = (-c).max(0);
    let proven_range = proven_end_from_i.saturating_sub(po.off);
    let reg = ivl.get_mut(i);
    if let Some(ref mut ptr_off) = reg.ptr_offset {
        ptr_off.range = Some(ptr_off.range.unwrap_or(proven_range).max(proven_range));
        info!(
            target: "pcc",
            "[PCC] pc={}: strengthened {}.range to {} (packet accessible beyond fixed offset +{})",
            succ_pc,
            i.name(),
            ptr_off.range.unwrap(),
            po.off,
        );
    }
}

/// Applies verifier-produced PCC facts to successor state.
///
/// Injection is intentionally narrow and fail-closed.
pub fn apply_verified_refinements(succ_state: &mut State, facts: &[VerifiedEntry]) {
    if facts.is_empty() {
        return;
    }
    let succ_pc = succ_state.pc;
    for fact in facts {
        apply_verified_packet_end_fact(succ_state, fact.i, fact.j, fact.bound, succ_pc);
    }
}
