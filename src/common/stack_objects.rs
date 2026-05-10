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
//   - Open-coded iterators (Phase 3 ): bpf_iter_num/_task/_css/_bits
//   - Dynamic pointers (Phase 4 ): bpf_dynptr
//
// Distinct from `mem_region_model`, which describes pointer-reachable kernel
// structs whose individual fields the program is allowed to read.

use crate::analysis::machine::stack_state::IterKind;

// ---------------------------------------------------------------------------
// Open-coded iterators
// ---------------------------------------------------------------------------
//
// Sizes are taken from `include/uapi/linux/bpf.h` in mainline
// (struct bpf_iter_num / _task / _css / _bits).

pub const BPF_ITER_NUM_SIZE: usize = 8;
pub const BPF_ITER_TASK_SIZE: usize = 40;
pub const BPF_ITER_CSS_SIZE: usize = 24;
pub const BPF_ITER_BITS_SIZE: usize = 16;
/// `struct bpf_iter_task_vma` is opaque to programs (forward-declared in
/// `bpf_experimental.h`); BTF reports an 8-byte size. The kernel-side
/// state lives in a separate `bpf_iter_task_vma_kern` that the kfunc
/// implementations cast to.
pub const BPF_ITER_TASK_VMA_SIZE: usize = 8;
/// `struct bpf_iter_testmod_seq` (testmod-defined, 16 bytes:
/// `u64 :64; u64 :64;`).
pub const BPF_ITER_TESTMOD_SEQ_SIZE: usize = 16;
/// `struct bpf_iter_css_task` from kernel/bpf/task_iter.c
/// (`__u64 __opaque[1]` aligned 8 — program-visible footprint).
pub const BPF_ITER_CSS_TASK_SIZE: usize = 8;
/// `struct bpf_iter_kmem_cache` from mm/slab_common.c
/// (`__u64 __opaque[1]` aligned 8).
pub const BPF_ITER_KMEM_CACHE_SIZE: usize = 8;

/// Stack footprint of an open-coded iterator struct, in bytes.
pub fn bpf_iter_size(kind: IterKind) -> usize {
    match kind {
        IterKind::Num => BPF_ITER_NUM_SIZE,
        IterKind::Task => BPF_ITER_TASK_SIZE,
        IterKind::Css => BPF_ITER_CSS_SIZE,
        IterKind::Bits => BPF_ITER_BITS_SIZE,
        IterKind::TaskVma => BPF_ITER_TASK_VMA_SIZE,
        IterKind::TestmodSeq => BPF_ITER_TESTMOD_SEQ_SIZE,
        IterKind::CssTask => BPF_ITER_CSS_TASK_SIZE,
        IterKind::KmemCache => BPF_ITER_KMEM_CACHE_SIZE,
    }
}

// ---------------------------------------------------------------------------
// Dynamic pointers
// ---------------------------------------------------------------------------
//
// A dynptr occupies a fixed 16 bytes on the stack regardless of which
// `DynptrKind` it carries (matching the kernel's two-slot `STACK_DYNPTR`
// invariant). Programs treat the body as opaque — all access goes through
// `bpf_dynptr_*` kfuncs.

pub const BPF_DYNPTR_SIZE: usize = 16;
