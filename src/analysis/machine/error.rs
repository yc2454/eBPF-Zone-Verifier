use crate::analysis::flow::subprog::SubprogError;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::ast::ProgramKind;

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum VerificationError {
    StackOutOfBounds {
        pc: usize,
        off: i64,
        size: i64,
    },
    PointerOutOfBounds {
        pc: usize,
    },
    UninitializedStackRead {
        pc: usize,
        offset: i64,
    },
    InvalidStackRead {
        pc: usize,
        offset: i64,
    },
    UnsafePacketLoad {
        pc: usize,
        off: i16,
        size: i64,
    },
    UnsafePacketStore {
        pc: usize,
        off: i16,
        size: i64,
    },
    IllegalPacketStore {
        pc: usize,
        off: i16,
        size: i64,
    },
    UnsafeMapLoad {
        pc: usize,
        off: i64,
        size: i64,
        limit: i64,
    },
    UnsafeMapStore {
        pc: usize,
        off: i64,
        size: i64,
        limit: i64,
    },
    UnsafeMemoryStore {
        pc: usize,
        base: Reg,
        off: i16,
        size: i64,
    },
    UnsafeMemoryLoad {
        pc: usize,
        base: Reg,
        off: i16,
        size: i64,
    },
    MapStoreForbidden {
        pc: usize,
        map_idx: usize,
    },
    MapLoadForbidden {
        pc: usize,
        map_idx: usize,
    },
    UnsafeMapAccess {
        pc: usize,
        map_idx: usize,
        size: i64,
    },
    UnsafeGenericLoad {
        pc: usize,
        base: Reg,
        off: i16,
        base_type: RegType,
    },
    UnsafeMemoryRegionLoad {
        pc: usize,
        base: Reg,
        off: i16,
    },
    UnsafeCtxAccess {
        pc: usize,
        off: i16,
        size: i64,
    },
    UnsafeGenericStore {
        pc: usize,
        base: Reg,
        off: i16,
        base_type: RegType,
    },
    UnsafeSocketAccess {
        pc: usize,
        off: i16,
        size: i64,
    },
    DbmInconsistent {
        pc: usize,
    },
    ComplexityLimitExceeded {
        limit: usize,
    },
    RegisterNotReadable {
        pc: usize,
        reg: Reg,
    },
    RegisterNotWritable {
        pc: usize,
        reg: Reg,
    },
    CfgError(String),
    DivideByZero {
        pc: usize,
    },
    InvalidArgType {
        pc: usize,
        reg: Reg,
    },
    InvalidPointerArithmetic {
        pc: usize,
    },
    InvalidBPFLoadImmInsn {
        pc: usize,
    },
    MapNotFound {
        pc: usize,
        map_idx: usize,
    },
    BackEdge {
        pc: usize,
        target: usize,
    },
    MaxCallDepthExceeded {
        pc: usize,
    },
    MisalignedAccess {
        pc: usize,
        off: i64,
    },
    InvalidReturnCode {
        pc: usize,
    },
    MisalignedPacketAccess {
        pc: usize,
        off: i16,
        size: i64,
    },
    InvalidRegisterTypeState {
        pc: usize,
    },
    RegisterTypeConflict {
        pc: usize,
        reg: Reg,
        old: RegType,
        new: RegType,
    },
    UnreleasedReference,
    UnreleasedIterator,
    UnreleasedDynptr,
    DynptrOverwrite {
        pc: usize,
        off: i64,
    },
    InvalidBtfType,
    LockAlreadyHeld {
        pc: usize,
    },
    LockNotHeld {
        pc: usize,
    },
    UnreleasedLock,
    /// `bpf_rcu_read_unlock` called outside an RCU read-side section.
    RcuReadNotHeld {
        pc: usize,
    },
    /// Helper / kfunc marked `CallFlags::RCU` invoked while
    /// `state.rcu_read_depth == 0`.
    NotInRcuReadSection {
        pc: usize,
        helper: u32,
    },
    /// Program exit reached with one or more open RCU read-side sections.
    UnreleasedRcuRead,
    /// Helper / kfunc marked `CallFlags::SPIN_LOCK_HELD` invoked
    /// without an active spin_lock (W5.4). rbtree / list mutators
    /// require a held lock to prevent races on the per-map-value
    /// head/root.
    NotInSpinLockSection {
        pc: usize,
        helper: u32,
    },
    LoadAbsUnderLock {
        pc: usize,
    },
    RelocationInfoMissing {
        pc: usize,
    },
    SubprogError {
        e: SubprogError,
    },
    CannotReturnStackPointer {
        pc: usize,
    },
    SpillToCaller {
        pc: usize,
    },
    HelperNotAllowedForProgram {
        pc: usize,
        helper: u32,
        kind: ProgramKind,
    },
    /// Cluster E: LSM attach hook is on the kernel's disabled list
    /// (`getprocattr`, `setprocattr`, `ismaclabel`, `module_request`, ...).
    /// Reported at program load — there is no instruction PC.
    LsmHookDisabled {
        hook: String,
    },
    /// Kfunc proto carries a `prog_type_allowlist` (W6.3) and the
    /// program's `ProgramKind` is not in it. Mirrors the kernel
    /// verifier's per-kfunc `KF_PROG_TYPE_*` check (e.g. cgroup /
    /// cpumask / task families are gated to syscall / tracepoint /
    /// perf_event and reject from raw_tp).
    KfuncNotAllowedForProgram {
        pc: usize,
        btf_id: u32,
        kind: ProgramKind,
    },
    /// W6.4c: kfunc rejected because the calling subprog is wired
    /// into a struct_ops member that's not in the kfunc's allowed
    /// (ops_struct, member) set. E.g. `scx_bpf_select_cpu_dfl` is
    /// callable only from `sched_ext_ops.select_cpu`.
    KfuncNotAllowedForOpsMember {
        pc: usize,
        btf_id: u32,
        ops_struct: String,
        member: String,
    },
    PointerLeakage {
        pc: usize,
        offset: i64,
    },
    MapKeyOutOfBounds {
        pc: usize,
        key_min: i64,
        key_max: i64,
        max_entries: u32,
    },
    InvalidHelperId {
        pc: usize,
        helper: u32,
    },
    /// A valid-shape construct the verifier recognizes but has not implemented
    /// transfer semantics for yet (e.g. kfunc calls, BPF_PSEUDO_FUNC / BTF_ID
    /// LD_IMM64 subtypes added by kernels newer than 5.15).
    UnsupportedModernFeature {
        pc: usize,
        feature: &'static str,
    },
}

impl VerificationError {
    pub fn description(&self) -> String {
        match self {
            VerificationError::StackOutOfBounds { pc, off, size } => {
                format!(
                    "Stack out of bounds at pc {}: offset {}, size {}",
                    pc, off, size
                )
            }
            VerificationError::PointerOutOfBounds { pc } => {
                format!("Pointer out of bounds at pc {}", pc)
            }
            VerificationError::UninitializedStackRead { pc, offset } => {
                format!(
                    "Reading uninitialized stack slot at pc {}: offset {}",
                    pc, offset
                )
            }
            VerificationError::UnsafePacketLoad { pc, off, size } => {
                format!(
                    "Unsafe packet load at pc {}: offset {}, size {:?}",
                    pc, off, size
                )
            }
            VerificationError::UnsafePacketStore { pc, off, size } => {
                format!(
                    "Unsafe packet store at pc {}: offset {}, size {:?}",
                    pc, off, size
                )
            }
            VerificationError::IllegalPacketStore { pc, off, size } => {
                format!(
                    "Illegal packet store at pc {}: offset {}, size {:?}",
                    pc, off, size
                )
            }
            VerificationError::UnsafeMapLoad {
                pc,
                off,
                size,
                limit,
            } => {
                format!(
                    "Unsafe map load at pc {}: offset {}, size {:?}, limit {}",
                    pc, off, size, limit
                )
            }
            VerificationError::UnsafeMapStore {
                pc,
                off,
                size,
                limit,
            } => {
                format!(
                    "Unsafe map store at pc {}: offset {}, size {:?}, limit {}",
                    pc, off, size, limit
                )
            }
            VerificationError::UnsafeMapAccess { pc, map_idx, size } => {
                format!(
                    "Unsafe map store at pc {}: map index {}, size {:?}",
                    pc, map_idx, size
                )
            }
            VerificationError::UnsafeGenericLoad {
                pc,
                base,
                off,
                base_type,
            } => {
                format!(
                    "Unsafe generic load at pc {}: base {:?}+{} (type: {:?})",
                    pc, base, off, base_type
                )
            }
            VerificationError::UnsafeCtxAccess { pc, off, size } => {
                format!(
                    "Unsafe ctx access at pc {}: offset {}, size {:?}",
                    pc, off, size
                )
            }
            VerificationError::UnsafeGenericStore {
                pc,
                base,
                off,
                base_type,
            } => {
                format!(
                    "Unsafe generic store at pc {}: base {:?}+{} (type: {:?})",
                    pc, base, off, base_type
                )
            }
            VerificationError::DbmInconsistent { pc } => {
                format!("DBM inconsistent at pc {}", pc)
            }
            VerificationError::ComplexityLimitExceeded { limit } => {
                format!("Complexity limit of {} exceeded", limit)
            }
            VerificationError::CfgError(msg) => {
                format!("CFG error: {}", msg)
            }
            VerificationError::DivideByZero { pc } => {
                format!("Potential divide by zero at pc {}", pc)
            }
            VerificationError::UnsafeSocketAccess { pc, off, size } => {
                format!(
                    "Unsafe socket access at pc {}: offset {}, size {:?}",
                    pc, off, size
                )
            }
            VerificationError::UnsafeMemoryRegionLoad { pc, base, off } => {
                format!(
                    "Unsafe memory region load at pc {}: base {:?}, offset {}",
                    pc, base, off
                )
            }
            VerificationError::InvalidArgType { pc, reg } => {
                format!(
                    "Invalid argument type at pc {}: register: {}",
                    pc,
                    reg.name()
                )
            }
            VerificationError::InvalidPointerArithmetic { pc } => {
                format!("Invalid pointer arithmetic at pc {}", pc)
            }
            VerificationError::InvalidStackRead { pc, offset } => {
                format!("Invalid stack read at pc {} offset {}", pc, offset)
            }
            VerificationError::RegisterNotReadable { pc, reg } => {
                format!("pc {}: {:?} !read_ok", pc, reg)
            }
            VerificationError::RegisterNotWritable { pc, reg } => {
                format!("pc {}: {:?} !write_ok", pc, reg)
            }
            VerificationError::InvalidBPFLoadImmInsn { pc } => {
                format!("Invalid BPF_LD_IMM instruction at pc {}", pc)
            }
            VerificationError::MapNotFound { pc, map_idx } => {
                format!("Map with ID {} not found at pc {}", map_idx, pc)
            }
            VerificationError::BackEdge { pc, target } => {
                format!("Attempting to jump back to {} at pc {}", target, pc)
            }
            VerificationError::MaxCallDepthExceeded { pc } => {
                format!("Max call depth exceeded at pc {}", pc)
            }
            VerificationError::MisalignedAccess { pc, off } => {
                format!("Misaligned offset with offset {} at pc {}", off, pc)
            }
            VerificationError::InvalidReturnCode { pc } => {
                format!("Invalid return code at pc {}", pc)
            }
            VerificationError::MisalignedPacketAccess { pc, off, size } => {
                format!(
                    "Misaligned packet access at pc {}: offset {}, size {:?}",
                    pc, off, size
                )
            }
            VerificationError::InvalidRegisterTypeState { pc } => {
                format!("Invalid register type state at pc {}", pc)
            }
            VerificationError::MapStoreForbidden { pc, map_idx } => {
                format!("Attemp to write to read-only map {} at pc {}", map_idx, pc)
            }
            VerificationError::MapLoadForbidden { pc, map_idx } => {
                format!(
                    "Attemp to read from write-only map {} at pc {}",
                    map_idx, pc
                )
            }
            VerificationError::RegisterTypeConflict { pc, reg, old, new } => {
                format!(
                    "Register {} type conflict at pc {}: old: {:?}, new: {:?}",
                    reg.name(),
                    pc,
                    old,
                    new
                )
            }
            VerificationError::UnreleasedReference => "Unreleased reference in program".to_string(),
            VerificationError::UnreleasedIterator => "Unreleased open-coded iterator in program".to_string(),
            VerificationError::UnreleasedDynptr => "Unreleased dynptr in program".to_string(),
            VerificationError::DynptrOverwrite { pc, off } => format!(
                "Cannot overwrite referenced dynptr at pc {} (stack off {})",
                pc, off
            ),
            VerificationError::UnreleasedLock => "Unreleased lock in program".to_string(),
            VerificationError::InvalidBtfType => "Invalid BTF type".to_string(),
            VerificationError::LockAlreadyHeld { pc } => {
                format!("Lock already held at pc {}, cannot acquire again", pc)
            }
            VerificationError::LockNotHeld { pc } => {
                format!("Lock not held at pc {}, cannot release", pc)
            }
            VerificationError::RcuReadNotHeld { pc } => {
                format!("RCU read-side section not held at pc {}, cannot unlock", pc)
            }
            VerificationError::NotInRcuReadSection { pc, helper } => {
                format!(
                    "Helper {} at pc {} requires an RCU read-side critical section",
                    helper, pc
                )
            }
            VerificationError::UnreleasedRcuRead => {
                "Unreleased RCU read-side section in program".to_string()
            }
            VerificationError::NotInSpinLockSection { pc, helper } => {
                format!(
                    "Helper/kfunc {} at pc {} requires an active spin_lock",
                    helper, pc
                )
            }
            VerificationError::LoadAbsUnderLock { pc } => {
                format!("ld_abs with an active lock at pc {}", pc)
            }
            VerificationError::RelocationInfoMissing { pc } => {
                format!("Relocation info missing at pc {}", pc)
            }
            VerificationError::SubprogError { e } => {
                format!("Subprogram error: {}", e)
            }
            VerificationError::CannotReturnStackPointer { pc } => {
                format!("Cannot return stack pointer in R0 at pc {}", pc)
            }
            VerificationError::SpillToCaller { pc } => {
                format!("Spill to caller at pc {}", pc)
            }
            VerificationError::HelperNotAllowedForProgram { pc, helper, kind } => {
                format!(
                    "Helper {} not allowed for program {:?} at pc {}",
                    helper, kind, pc
                )
            }
            VerificationError::LsmHookDisabled { hook } => {
                format!("LSM attach target points to disabled hook '{}'", hook)
            }
            VerificationError::KfuncNotAllowedForProgram { pc, btf_id, kind } => {
                format!(
                    "Kfunc btf_id {} not allowed for program {:?} at pc {}",
                    btf_id, kind, pc
                )
            }
            VerificationError::KfuncNotAllowedForOpsMember {
                pc,
                btf_id,
                ops_struct,
                member,
            } => {
                format!(
                    "Kfunc btf_id {} not allowed in {}.{} at pc {}",
                    btf_id, ops_struct, member, pc
                )
            }
            VerificationError::UnsafeMemoryStore {
                pc,
                base,
                off,
                size,
            } => {
                format!(
                    "Unsafe memory store at pc {}: base {:?}, offset {}, size {}",
                    pc, base, off, size
                )
            }
            VerificationError::UnsafeMemoryLoad {
                pc,
                base,
                off,
                size,
            } => {
                format!(
                    "Unsafe memory load at pc {}: base {:?}, offset {}, size {}",
                    pc, base, off, size
                )
            }
            VerificationError::PointerLeakage { pc, offset } => {
                format!(
                    "Pointer leakage at pc {}: stack slot {} contains pointer that cannot be exposed to map",
                    pc, offset
                )
            }
            VerificationError::MapKeyOutOfBounds {
                pc,
                key_min,
                key_max,
                max_entries,
            } => {
                format!(
                    "Map key out of bounds at pc {}: key range [{}, {}], max_entries={}",
                    pc, key_min, key_max, max_entries
                )
            }
            VerificationError::InvalidHelperId { pc, helper } => {
                format!(
                    "Invalid helper ID {} at pc {}: exceeds maximum known helper ID",
                    helper, pc
                )
            }
            VerificationError::UnsupportedModernFeature { pc, feature } => {
                format!("Unsupported modern BPF feature at pc {}: {}", pc, feature)
            }
        }
    }
}
