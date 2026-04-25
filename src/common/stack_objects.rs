// src/common/stack_objects.rs
//
// Stack-resident opaque kernel objects.
//
// Some kernel-defined types are stack-allocated by the BPF program and passed
// by pointer to kfuncs that mutate them in place. The program treats their
// bodies as opaque — there are no field accessors — so we only need the byte
// footprint to reserve and annotate the right span of stack slots.
//
// Members so far:
//   - Open-coded iterators (Phase 3 W3.2): bpf_iter_num/_task/_css/_bits
//   - (Phase 4 W4.2 will add bpf_dynptr here.)
//
// Distinct from `mem_region_model`, which describes pointer-reachable kernel
// structs whose individual fields the program is allowed to read.

use crate::analysis::machine::stack_state::IterKind;

// ---------------------------------------------------------------------------
// Open-coded iterators (W3.2)
// ---------------------------------------------------------------------------
//
// Sizes are taken from `include/uapi/linux/bpf.h` in mainline
// (struct bpf_iter_num / _task / _css / _bits).

pub const BPF_ITER_NUM_SIZE: usize = 8;
pub const BPF_ITER_TASK_SIZE: usize = 40;
pub const BPF_ITER_CSS_SIZE: usize = 24;
pub const BPF_ITER_BITS_SIZE: usize = 16;

/// Stack footprint of an open-coded iterator struct, in bytes.
pub fn bpf_iter_size(kind: IterKind) -> usize {
    match kind {
        IterKind::Num => BPF_ITER_NUM_SIZE,
        IterKind::Task => BPF_ITER_TASK_SIZE,
        IterKind::Css => BPF_ITER_CSS_SIZE,
        IterKind::Bits => BPF_ITER_BITS_SIZE,
    }
}
