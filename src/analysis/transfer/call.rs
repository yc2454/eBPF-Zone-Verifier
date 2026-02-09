// src/analysis/transfer/call.rs
//
// Call and CallRel instruction handling, helper validation

use crate::analysis::machine::env::{VerifierEnv, VerificationError};
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::transfer::types::update_call_rel_types;
use crate::ast::{ProgramKind, AttachKind};
use crate::zone::domain::{Reg, forget, assume_ge_const, assume_le_const, is_zero, nonneg, get_bounds, positive};
use crate::zone::tnum::{Tnum};
use crate::analysis::transfer::access::{self, AccessKind};
use crate::parsing::btf::SpecialFieldKind;
use crate::common::constants;
use log::{error, info, warn};

use super::types::{update_call_types, helper_invalidates_packets};
use super::common::check_regs_readable;

// ============================================================================
// BPF Argument Types
// ============================================================================

/// BPF helper function argument type constraints.
/// Based on Linux kernel's `enum bpf_arg_type` from include/linux/bpf.h
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BpfArgType {
    /// Unused argument in helper function
    DontCare,

    // ---- Map-related argument types ----
    /// const argument used as pointer to bpf_map
    ConstMapPtr,
    /// pointer to stack used as map key
    PtrToMapKey,
    /// pointer to stack used as map value
    PtrToMapValue,
    /// pointer to valid memory used to store a map value (output)
    PtrToUninitMapValue,

    // ---- Memory access argument types ----
    /// pointer to valid memory (stack, packet, map value)
    PtrToMem,
    /// pointer to memory that doesn't need to be initialized (helper fills it)
    PtrToUninitMem,

    // ---- Size argument types ----
    /// number of bytes accessed from memory
    ConstSize,
    /// number of bytes accessed from memory or 0
    ConstSizeOrZero,

    // ---- Context and general types ----
    /// pointer to context (sk_buff, xdp_md, etc.)
    PtrToCtx,
    /// any (initialized) argument is ok
    Anything,

    // ---- Socket types ----
    /// pointer to sock_common
    PtrToSockCommon,
    /// pointer to bpf_sock (fullsock)
    PtrToSocket,
    /// pointer to in-kernel sock_common or bpf-mirrored bpf_sock
    PtrToBTFIdSockCommon, 

    // ---- Stack types ----
    /// pointer to stack
    PtrToStack,

    // ---- Nullable variants ----
    /// PTR_TO_CTX | PTR_MAYBE_NULL
    PtrToCtxOrNull,
    /// PTR_TO_MEM | PTR_MAYBE_NULL
    PtrToMemOrNull,
    /// PTR_TO_STACK | PTR_MAYBE_NULL
    PtrToStackOrNull,
    /// PTR_TO_MAP_VALUE | PTR_MAYBE_NULL
    PtrToMapValueOrNull,

    // ---- Fixed-size pointer types ----
    /// pointer to initialized long/u64 value (helper reads from it)
    PtrToLong,
    // /// pointer to long/u64 that helper will write to (doesn't need to be initialized)
    // PtrToUninitLong,
    // /// PTR_TO_LONG | PTR_MAYBE_NULL
    // PtrToLongOrNull,
}

// ============================================================================
// Pointer-Size Pair Table
// ============================================================================

/// A pointer argument paired with its size argument.
#[derive(Debug, Clone, Copy)]
pub struct MemSizePair {
    pub ptr_reg: Reg,
    pub size_reg: Reg,
    /// If true, size can be 0 (and if ptr is NULL, size MUST be 0)
    pub allow_zero: bool,
}

impl MemSizePair {
    const fn new(ptr_reg: Reg, size_reg: Reg) -> Self {
        Self { ptr_reg, size_reg, allow_zero: false }
    }
    
    const fn new_nullable(ptr_reg: Reg, size_reg: Reg) -> Self {
        Self { ptr_reg, size_reg, allow_zero: true }
    }
}

// ============================================================================
// Helper Function Signatures
// ============================================================================

/// Maximum number of arguments for a BPF helper function.
pub const MAX_BPF_FUNC_ARGS: usize = 5;

/// Signature of a BPF helper function.
#[derive(Debug, Clone, Copy)]
pub struct HelperSignature {
    /// Argument types for R1-R5 (use DontCare for unused args)
    pub args: [BpfArgType; MAX_BPF_FUNC_ARGS],
}

impl HelperSignature {
    const fn new(args: [BpfArgType; MAX_BPF_FUNC_ARGS]) -> Self {
        Self { args }
    }

    /// Returns the number of actual arguments (non-DontCare)
    pub fn arg_count(&self) -> usize {
        self.args.iter()
            .take_while(|&&arg| arg != BpfArgType::DontCare)
            .count()
    }
}

// Convenience aliases
use BpfArgType::*;

/// Helper function signatures indexed by helper ID.
/// Returns None for unknown helpers.
pub fn get_helper_signature(helper: u32) -> Option<HelperSignature> {
    Some(match helper {
        // ---- Map operations ----
        constants::BPF_MAP_LOOKUP_ELEM => HelperSignature::new([
            ConstMapPtr,    // R1: map
            PtrToMapKey,    // R2: key
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_MAP_UPDATE_ELEM => HelperSignature::new([
            ConstMapPtr,    // R1: map
            PtrToMapKey,    // R2: key
            PtrToMapValue,  // R3: value
            Anything,       // R4: flags
            DontCare,
        ]),

        constants::BPF_MAP_DELETE_ELEM => HelperSignature::new([
            ConstMapPtr,    // R1: map
            PtrToMapKey,    // R2: key
            DontCare,
            DontCare,
            DontCare,
        ]),

        // ---- Tail call ----
        constants::BPF_TAIL_CALL => HelperSignature::new([
            PtrToCtx,       // R1: ctx
            ConstMapPtr,    // R2: prog_array_map
            Anything,       // R3: index
            DontCare,
            DontCare,
        ]),

        // ---- Socket/context helpers ----
        constants::BPF_GET_SOCKET_COOKIE => HelperSignature::new([
            PtrToCtx,       // R1: ctx
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_CSUM_UPDATE => HelperSignature::new([
            PtrToCtx,       // R1: skb
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_CSUM_DIFF => HelperSignature::new([
            PtrToMemOrNull,     // R1: from
            ConstSizeOrZero,    // R2: from_size
            PtrToMemOrNull,     // R3: to
            ConstSizeOrZero,    // R4: to_size
            Anything,           // R5: seed
        ]),

        constants::BPF_SKB_ECN_SET_CE => HelperSignature::new([
            PtrToCtxOrNull, // R1: skb (can be NULL)
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_GET_HASH_RECALC => HelperSignature::new([
            PtrToCtx,       // R1: ctx
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        // ---- SKB data access ----
        constants::BPF_SKB_LOAD_BYTES => HelperSignature::new([
            PtrToCtx,       // R1: skb
            Anything,       // R2: offset
            PtrToUninitMem, // R3: to (destination buffer)
            ConstSize,      // R4: len
            DontCare,
        ]),

        constants::BPF_SKB_STORE_BYTES => HelperSignature::new([
            PtrToCtx,       // R1: skb
            Anything,       // R2: offset
            PtrToMem,       // R3: from (source buffer)
            ConstSize,      // R4: len
            DontCare,
        ]),

        // ---- Redirect ----
        constants::BPF_REDIRECT => HelperSignature::new([
            Anything,       // R1: ifindex
            Anything,       // R2: flags
            DontCare,
            DontCare,
            DontCare,
        ]),

        // ---- XDP helpers ----
        constants::BPF_XDP_ADJUST_HEAD => HelperSignature::new([
            PtrToCtx,       // R1: xdp_md
            Anything,       // R2: delta
            DontCare,
            DontCare,
            DontCare,
        ]),

        // ---- Socket lookup ----
        constants::BPF_SKC_LOOKUP_TCP => HelperSignature::new([
            PtrToCtx,       // R1: ctx
            PtrToMem,       // R2: tuple
            Anything,       // R3: tuple_size
            DontCare,
            DontCare,
        ]),

        constants::BPF_SK_LOOKUP_TCP => HelperSignature::new([
            PtrToCtx,       // R1: ctx
            PtrToMem,       // R2: tuple
            ConstSize,       // R3: tuple_size
            Anything,       // R4: netns
            Anything,       // R5: flags
        ]),

        constants::BPF_SK_LOOKUP_UDP => HelperSignature::new([
            PtrToCtx,       // R1: ctx
            PtrToMem,       // R2: tuple
            ConstSize,       // R3: tuple_size
            Anything,       // R4: netns
            Anything,       // R5: flags
        ]),

        constants::BPF_SK_RELEASE => HelperSignature::new([
            PtrToSocket,       // R1: socket
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_SKC_TO_UDP6_SOCK => HelperSignature::new([
            PtrToSocket,       // R1: socket
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_SK_FULLSOCK => HelperSignature::new([
            PtrToSockCommon,       // R1: sock_common
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_TCP_SOCK => HelperSignature::new([
            PtrToSockCommon,
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),
        
        // ---- Socket storage helpers ----
        constants::BPF_SK_STORAGE_GET => HelperSignature::new([
            ConstMapPtr,
            PtrToBTFIdSockCommon,
            PtrToMapValueOrNull,
            Anything,
            DontCare,
        ]),

        // ---- FIB lookup ----
        constants::BPF_FIB_LOOKUP => HelperSignature::new([
            PtrToCtx,       // R1: ctx
            PtrToMem,       // R2: params (bpf_fib_lookup struct)
            Anything,       // R3: plen
            Anything,       // R4: flags
            DontCare,
        ]),

        constants::BPF_PROBE_READ_USER => HelperSignature::new([
            PtrToUninitMem,     // R1: dst
            ConstSizeOrZero,    // R2: size
            Anything,           // R3: unsafe_ptr (user address)
            DontCare,
            DontCare,
        ]),

        constants::BPF_PROBE_READ_KERNEL => HelperSignature::new([
            PtrToUninitMem,     // R1: dst (output buffer)
            ConstSizeOrZero,    // R2: size
            Anything,           // R3: unsafe_ptr (kernel address, not validated)
            DontCare,
            DontCare,
        ]),

        // ---- Spin lock related ---- 
        constants::BPF_SPIN_LOCK => HelperSignature::new([
            Anything,
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_SPIN_UNLOCK => HelperSignature::new([
            Anything,
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        // ---- Miscellaneous ----
        constants::BPF_GET_PRANDOM_U32 => HelperSignature::new([
            DontCare,
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_TRACE_PRINTK => HelperSignature::new([
            PtrToMem,    // R1: fmt string
            ConstSize,   // R2: fmt_size (MUST BE > 0)
            Anything,    // R3: arg1
            Anything,    // R4: arg2
            Anything,    // R5: arg3
        ]),

        constants::BPF_STRTOUL => HelperSignature::new([
            PtrToMem,
            ConstSize,
            Anything,
            PtrToLong,
            DontCare,
        ]),

        constants::BPF_GET_CGROUP_CLASS_ID => HelperSignature::new([
            PtrToCtx,
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        _ => return None,
    })
}

/// Returns all pointer-size pairs for a given helper.
/// Returns empty slice if helper has no such pairs (e.g., map ops use fixed sizes).
pub fn get_mem_size_pairs(helper: u32) -> &'static [MemSizePair] {
    use Reg::*;
    
    // Define static arrays for each helper pattern
    static PROBE_READ: [MemSizePair; 1] = [
        MemSizePair::new_nullable(R1, R2),
    ];
    
    static SKB_LOAD_BYTES: [MemSizePair; 1] = [
        MemSizePair::new(R3, R4),
    ];
    
    static SKB_STORE_BYTES: [MemSizePair; 1] = [
        MemSizePair::new(R3, R4),
    ];
    
    static CSUM_DIFF: [MemSizePair; 2] = [
        MemSizePair::new_nullable(R1, R2),
        MemSizePair::new_nullable(R3, R4),
    ];

    static SK_LOOKUP_TCP: [MemSizePair; 1] = [
        MemSizePair::new(R2, R3)
    ];
    
    static SK_LOOKUP_UDP: [MemSizePair; 1] = [
        MemSizePair::new(R2, R3)
    ];
    
    static EMPTY: [MemSizePair; 0] = [];
    
    match helper {
        constants::BPF_PROBE_READ_USER |
        constants::BPF_PROBE_READ_KERNEL => &PROBE_READ,
        
        constants::BPF_SKB_LOAD_BYTES => &SKB_LOAD_BYTES,
        
        constants::BPF_SKB_STORE_BYTES => &SKB_STORE_BYTES,
        
        constants::BPF_CSUM_DIFF => &CSUM_DIFF,

        constants::BPF_SK_LOOKUP_TCP => &SK_LOOKUP_TCP,
        
        constants::BPF_SK_LOOKUP_UDP => &SK_LOOKUP_UDP,
        
        _ => &EMPTY,
    }
}

/// Returns true if the helper rejects packet pointers for the given argument index.
fn helper_rejects_packet_for_arg(helper: u32, arg_index: usize) -> bool {
    match helper {
        // bpf_skb_store_bytes: R3 (from buffer) cannot be packet pointer
        // because the helper modifies packet data, causing pointer invalidation
        constants::BPF_SKB_STORE_BYTES => arg_index == 2,
        
        // Add other helpers with similar restrictions here
        _ => false,
    }
}

/// For helpers with PTR_OR_NULL args, returns the index of the paired size argument.
fn get_nullable_ptr_size_pair(helper: u32, ptr_arg_index: usize) -> Option<usize> {
    match helper {
        // bpf_csum_diff: R1=from (PTR_OR_NULL) paired with R2=from_size,
        //                R3=to (PTR_OR_NULL) paired with R4=to_size
        constants::BPF_CSUM_DIFF => match ptr_arg_index {
            0 => Some(1),  // R1's size is R2
            2 => Some(3),  // R3's size is R4
            _ => None,
        },
        // Add other helpers with PTR_OR_NULL + SIZE_OR_ZERO pairs
        _ => None,
    }
}

// ============================================================================
// Argument Validation
// ============================================================================

/// Validates all arguments for a helper function based on its signature.
fn validate_helper_args(
    env: &mut VerifierEnv,
    state: &State,
    helper: u32,
    types: &TypeState,
    pc: usize,
) {
    let Some(sig) = get_helper_signature(helper) else {
        warn!("[Verifier] Unknown helper {} at pc {}, skipping arg validation", helper, pc);
        return;
    };

    // Get map info if first arg is a map (needed for key/value size validation)
    let map_info = if sig.args[0] == ConstMapPtr {
        get_map_info(types.get(Reg::R1), env)
    } else {
        None
    };

    // Validate each argument
    let arg_regs = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];
    
    for (i, (&arg_type, &reg)) in sig.args.iter().zip(arg_regs.iter()).enumerate() {
        info!("[Verifier] pc {}: validating arg R{} as {:?}", pc, i + 1, arg_type);
        if arg_type == DontCare {
            break; // No more arguments
        }

        let reg_type = types.get(reg);
        
        if !validate_single_arg(env, state, types, helper, pc, reg, arg_type, reg_type, &map_info, i) {
            // Validation failed, error already reported
            return;
        }
    }
}

/// Validates a single argument against its expected type.
/// Returns true if valid, false if invalid (error already reported).
fn validate_single_arg(
    env: &mut VerifierEnv,
    state: &State,
    types: &TypeState,
    helper: u32,
    pc: usize,
    reg: Reg,
    expected: BpfArgType,
    actual: RegType,
    map_info: &Option<MapInfo>,
    arg_index: usize,
) -> bool {
    match expected {
        DontCare => true,

        // ---- Map pointer ----
        ConstMapPtr => {
            if !matches!(actual, RegType::PtrToMapObject { .. }) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} expected PTR_TO_MAP, got {:?}", 
                       pc, arg_index + 1, actual);
                return false;
            } 
            // There are special requirements for bpf_map_lookup_elem
            else if helper == constants::BPF_MAP_LOOKUP_ELEM {
                match actual {
                    RegType::PtrToMapObject { map_idx } => {
                        let map_def = env.ctx.map_defs.get(map_idx);
                        if map_def.is_none() {
                            env.fail(VerificationError::InvalidArgType { pc, reg });
                            return false;
                        } else {
                            let map_def = map_def.unwrap();
                            if matches!(map_def.type_, 
                                constants::BPF_MAP_TYPE_STACK_TRACE | constants::BPF_MAP_TYPE_PROG_ARRAY
                                | constants::BPF_MAP_TYPE_SK_STORAGE) {
                                env.fail(VerificationError::InvalidArgType { pc, reg });
                                return false;
                            }
                        }
                    }
                    _ => return true
                }
            }
            true
        }

        // ---- Map key pointer ----
        PtrToMapKey => {
            let Some(target_info) = map_info else {
                return true;
            };
            
            if let RegType::PtrToMapValue { map_idx, .. } = actual {
                if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                    println!("Validating map value size: expected {}, got {}", 
                             target_info.value_size, map_def.value_size);
                    if map_def.value_size != target_info.value_size {
                        env.fail(VerificationError::InvalidArgType { pc, reg });
                        error!("[Verifier] pc {}: R{} map value size mismatch: expected {}, got {}", 
                               pc, arg_index + 1, target_info.value_size, map_def.key_size);
                        return false;
                    }
                } else {
                    env.fail(VerificationError::MapNotFound { pc, map_idx });
                    return false;
                }
            }
            
            validate_readable_mem(env, state, types, pc, reg, actual, Some(target_info.key_size))
        }

        // ---- Map value pointer ----
        PtrToMapValue => {
            let Some(target_info) = map_info else {
                return true;
            };
            
            if let RegType::PtrToMapValue { map_idx, .. } = actual {
                if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                    println!("Validating map value size: expected {}, got {}", 
                             target_info.value_size, map_def.value_size);
                    if map_def.value_size != target_info.value_size {
                        env.fail(VerificationError::InvalidArgType { pc, reg });
                        error!("[Verifier] pc {}: R{} map value size mismatch: expected {}, got {}", 
                               pc, arg_index + 1, target_info.value_size, map_def.value_size);
                        return false;
                    }
                } else {
                    env.fail(VerificationError::MapNotFound { pc, map_idx });
                    return false;
                }
            }
            
            validate_readable_mem(env, state, types, pc, reg, actual, Some(target_info.value_size))
        }

        PtrToMapValueOrNull => {
            let reg_type = types.get(reg);
            if reg_type.is_scalar() && is_zero(&state.dbm, reg) {
                return true;
            } else {
                if !matches!(reg_type, 
                    RegType::PtrToMapValue { .. } 
                    | RegType::PtrToMapValueOrNull { .. }
                    | RegType::PtrToStack { .. }
                    | RegType::PtrToPacket { .. }
                    | RegType::PtrToPacketMeta { .. }) {
                    env.fail(VerificationError::InvalidArgType { pc, reg });
                    error!("[Verifier] pc {}: R{} expected PTR_TO_MAP_VALUE or NULL, got {:?}", 
                           pc, arg_index + 1, actual);
                    return false;
                }
                true
            }
        }

        // ---- Uninitialized map value (output buffer) ----
        PtrToUninitMapValue => {
            let Some(info) = map_info else {
                return true;
            };
            validate_writable_mem(env, state, types, pc, reg, actual, Some(info.value_size))
        }

        // ---- Generic memory pointer ----
        PtrToMem => {
            if checked_by_mem_size_pairs(helper, reg) {
                return true;
            }
            // Some helpers reject packet pointers for specific args
            if matches!(actual, RegType::PtrToPacket { .. }) 
                && helper_rejects_packet_for_arg(helper, arg_index) 
            {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: helper {} does not accept packet pointer for R{}", 
                       pc, helper, arg_index + 1);
                return false;
            }
            validate_readable_mem(env, state, types, pc, reg, actual, None)
        }

        // ---- Uninitialized memory (output buffer) ----
        PtrToUninitMem => {
            validate_writable_mem(env, state, types, pc, reg, actual, None)
        }

        // ---- Size arguments ----
        ConstSize => {
            // Must be positive
            if !positive(&state.dbm, reg) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} (ConstSize) must be positive", 
                       pc, arg_index + 1);
                return false;
            }
            true
        }

        ConstSizeOrZero => {
            // Can be zero or positive
            if !nonneg(&state.dbm, reg) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} (ConstSizeOrZero) must be non-negative", 
                       pc, arg_index + 1);
                return false;
            }
            true
        }

        // ---- Context pointer ----
        PtrToCtx => {
            if !matches!(actual, RegType::PtrToCtx) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} expected PTR_TO_CTX, got {:?}", 
                       pc, arg_index + 1, actual);
                return false;
            }
            true
        }

        // ---- Context pointer or NULL ----
        PtrToCtxOrNull => {
            if state.types.get(reg).is_scalar() && is_zero(&state.dbm, reg) {
                return true;
            }
            if !matches!(actual, RegType::PtrToCtx) && !is_zero(&state.dbm, reg) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} expected PTR_TO_CTX or NULL, got {:?}", 
                       pc, arg_index + 1, actual);
                return false;
            }
            true
        }

        // ---- Any initialized value ----
        Anything => {
            // Just needs to be readable (not uninitialized)
            // The check_regs_readable at the start of transfer_call handles this
            true
        }

        // ---- Socket types ----
        PtrToSocket => {
            if !matches!(actual, RegType::PtrToSocket { .. } | RegType::PtrToSockCommon { .. } | RegType::PtrToStack { .. }) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} expected PTR_TO_SOCKET, got {:?}", 
                       pc, arg_index + 1, actual);
                return false;
            }
            true
        }

        PtrToSockCommon => {
            if !matches!(actual, RegType::PtrToSockCommon { .. } | RegType::PtrToSocket { .. } | RegType::PtrToTcpSock { .. }) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} expected PTR_TO_SOCK_COMMON, got {:?}", 
                       pc, arg_index + 1, actual);
                return false;
            }
            true
        }

        PtrToBTFIdSockCommon => {
            if !matches!(actual, 
                RegType::PtrToSockCommon { .. }
                | RegType::PtrToSocket { .. }
                | RegType::PtrToTcpSock { .. }) {
                    env.fail(VerificationError::InvalidArgType { pc, reg });
                    error!("[Verifier] pc {}: R{} expected PTR_TO_BTF_ID_SOCK_COMMON, got {:?}", 
                           pc, arg_index + 1, actual);
                    return false;
                }
            true
        }

        // ---- Stack pointer ----
        PtrToStack => {
            if !matches!(actual, RegType::PtrToStack { .. }) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} expected PTR_TO_STACK, got {:?}", 
                       pc, arg_index + 1, actual);
                return false;
            }
            true
        }

        PtrToStackOrNull => {
            if state.types.get(reg).is_scalar() && is_zero(&state.dbm, reg) {
                return true;
            }
            if !matches!(actual, RegType::PtrToStack { .. }) && !is_zero(&state.dbm, reg) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} expected PTR_TO_STACK or NULL, got {:?}", 
                       pc, arg_index + 1, actual);
                return false;
            }
            true
        }

        PtrToMemOrNull => {
            if state.types.get(reg).is_scalar() && is_zero(&state.dbm, reg) {
                return true;
            }
            if state.types.get(reg).is_nullable() {
                // Pointer is NULL - check that paired size arg is also 0
                if let Some(size_arg_idx) = get_nullable_ptr_size_pair(helper, arg_index) {
                    let size_reg = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5][size_arg_idx];
                    if !is_zero(&state.dbm, size_reg) {
                        env.fail(VerificationError::InvalidArgType { pc, reg: size_reg });
                        error!("[Verifier] pc {}: R{} must be 0 when R{} is NULL", 
                               pc, size_arg_idx + 1, arg_index + 1);
                        return false;
                    }
                }
                return validate_readable_mem(env, state, types, pc, reg, actual, None)
            }
            validate_readable_mem(env, state, types, pc, reg, actual, None)
        }

        PtrToLong => {
            if let RegType::PtrToStack { offset, frame_level } = actual {
                access::check_stack_access(
                    env, 
                    state, 
                    reg, 
                    offset, 
                    0, 
                    8, // PtrToLong is 8-byte access
                    pc, 
                    access::AccessKind::HelperOutput,
                    None,
                    frame_level
                );
                !env.failed()
            } else {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!("[Verifier] pc {}: R{} expected PTR_TO_LONG, got {:?}", 
                       pc, arg_index + 1, actual);
                false
            }
        }
    }
}

/// Validates that a register points to readable memory.
fn validate_readable_mem(
    env: &mut VerifierEnv,
    state: &State,
    _types: &TypeState,
    pc: usize,
    reg: Reg,
    reg_type: RegType,
    size: Option<u32>,
) -> bool {
    match reg_type {
        RegType::PtrToStack { offset: Some(off), .. } => {
            if let Some(sz) = size {
                access::check_stack_arg_readable(env, state, off, sz as i64, pc, AccessKind::Read);
            }
            true
        }
        RegType::PtrToStack { offset: None, .. } => {
            // Unknown stack offset - reject conservatively
            env.fail(VerificationError::UninitializedStackRead { pc, offset: 0 });
            false
        }
        // Delegate the checking for these to access.rs
        RegType::PtrToMapValue { map_idx, .. } => {
            if let Some(size) = size {
                access::check_load(env, state, reg, size as i64, 0);
                if env.failed() {
                    return false;
                }
                true
            } else {
                access::check_map_rw(env, map_idx, pc, false);
                false
            }
        }
        RegType::PtrToPacket { .. } => {
            if let Some(size) = size {
                access::check_load(env, state, reg, size as i64, 0);
                if env.failed() {
                    return false;
                }
                true
            } else {
                true
            }
        }
        RegType::PtrToCtx => {
            // Context can be read
            true
        }
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!("[Verifier] pc {}: {:?} not a valid memory pointer", pc, reg);
            false
        }
    }
}

/// Validates that a register points to writable memory.
fn validate_writable_mem(
    env: &mut VerifierEnv,
    _state: &State,
    _types: &TypeState,
    pc: usize,
    reg: Reg,
    reg_type: RegType,
    _size: Option<u32>,
) -> bool {
    match reg_type {
        RegType::PtrToStack { offset: Some(_), .. } => {
            // Stack is writable
            true
        }
        RegType::PtrToStack { offset: None, .. } => {
            // Unknown stack offset
            env.fail(VerificationError::UninitializedStackRead { pc, offset: 0 });
            false
        }
        RegType::PtrToMapValue { map_idx, .. } => {
            let writable = env.ctx.map_defs.get(map_idx)
                .map(|md| md.map_flags != constants::BPF_F_RDONLY_PROG)
                .unwrap_or(false);
            if writable {
                true
            } else {
                env.fail(VerificationError::MapStoreForbidden { pc, map_idx });
                false
            }
        }
        RegType::PtrToPacket { .. } => {
            // Packet pointers are NOT valid for uninit_mem arguments
            // (helper would write to packet, which is not allowed this way)
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!("[Verifier] pc {}: packet pointer not valid for output buffer", pc);
            false
        }
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!("[Verifier] pc {}: {:?} not a valid writable memory pointer", pc, reg);
            false
        }
    }
}

fn check_and_handle_spin_lock(
    env: &mut VerifierEnv,
    state: &mut State,
    helper: u32
) -> bool {
    let pc = state.pc;
    match state.types.get(Reg::R1) {
        RegType::PtrToMapValue { offset: _, map_idx, id } => {
            match env.ctx.map_defs.get(map_idx) {
                Some(map_def) => {
                    if let Some(val_type_id) = map_def.btf_val_type_id {
                        if helper == constants::BPF_SPIN_LOCK {
                            if state.has_active_lock() {
                                env.fail(VerificationError::LockAlreadyHeld { pc });
                                return false;
                            }
                            let special_fields = env.ctx.btf.find_special_fields(val_type_id);
                            let lock_offset_op = 
                                special_fields.iter().find(
                                    |f| f.kind == SpecialFieldKind::SpinLock)
                                    .map(|f| f.offset);
                            if lock_offset_op.is_none() {
                                env.fail(VerificationError::InvalidBtfType);
                                return false;
                            } else {
                                let lock_offset = lock_offset_op.unwrap();
                                state.acquire_lock(id, lock_offset);
                            }
                        } else {
                            if !state.has_active_lock() {
                                env.fail(VerificationError::LockNotHeld { pc });
                                return false;
                            } else {
                                let lock = state.get_active_lock().unwrap();
                                if lock.ptr_id != id {
                                    env.fail(VerificationError::LockNotHeld { pc });
                                    return false;
                                }
                            }
                            state.release_lock();
                        }
                    } else {
                        env.fail(VerificationError::InvalidBtfType);
                        return false;
                    }
                }
                _ => {
                    env.fail(VerificationError::MapNotFound { pc, map_idx });
                    return false;
                }
            }
        }
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return false;
        }
    }
    return true;
}

// ============================================================================
// Map Info Helpers
// ============================================================================

/// Information about a BPF map needed for validation.
#[derive(Debug, Clone, Copy)]
struct MapInfo {
    key_size: u32,
    value_size: u32,
}

fn get_map_info(map_type: RegType, env: &VerifierEnv) -> Option<MapInfo> {
    match map_type {
        RegType::PtrToMapObject { map_idx } => {
            env.ctx.map_defs.get(map_idx).map(|md| MapInfo {
                key_size: md.key_size,
                value_size: md.value_size,
            })
        }
        _ => None,
    }
}

// ============================================================================
// Transfer Functions
// ============================================================================

/// Transfer function for helper Call instructions.
pub(crate) fn transfer_call(
    env: &mut VerifierEnv,
    mut state: State,
    helper: u32,
) -> Vec<State> {
    let in_types = state.types.clone();
    let pc = state.pc;

    // ========================================================================
    // Check if the call is forbidden under an active lock
    // ========================================================================
    if state.has_active_lock() && !allowed_while_in_active_lock(helper) {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R0 });
        return vec![];
    }

    // ========================================================================
    // Validate pointer-size pairs
    // ========================================================================
    if !check_mem_size_pairs(env, &state, helper, pc) {
        return vec![];
    }

    // ========================================================================
    // Check argument registers are readable before the call
    // ========================================================================
    let arg_regs = get_arg_regs_from_signature(helper);
    if !check_regs_readable(env, &state, &arg_regs) {
        return vec![];
    }

    // ========================================================================
    // Validate helper arguments BEFORE executing
    // ========================================================================
    validate_helper_args(env, &state, helper, &in_types, pc);
    
    // ========================================================================
    // SPECIAL CASES
    // ========================================================================

    // bpf_tail_call
    // 
    // Semantics:
    //   - SUCCESS: Jump to target program, NEVER RETURNS (like exit)
    //   - FAILURE: Falls through to next instruction
    //
    // We only model the FAILURE path. Success means execution went elsewhere.
    if helper == constants::BPF_TAIL_CALL {
        if state.has_unreleased_refs() {
            error!("Entering tail calls but has unreleased references!");
            env.fail(VerificationError::UnreleasedReference {});
            return vec![];
        }
        // Update types (clobber caller-saved, R0 = scalar)
        update_call_types(env, &in_types, &mut state, helper);
        
        // Forget caller-saved in DBM
        for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            forget(&mut state.dbm, r);
        }
        
        // Return only the failure path (fall through)
        state.pc += 1;
        return vec![state];
    }

    // Special check for sk_release: R1 must have a reference
    if helper == constants::BPF_SK_RELEASE {
        if state.types.get(Reg::R1).get_ref_id().is_none() {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        }
    }

    // bpf_spin_lock and bpf_spin_unlock
    if helper == constants::BPF_SPIN_LOCK || helper == constants::BPF_SPIN_UNLOCK {
        if !check_and_handle_spin_lock(env, &mut state, helper) {
            return vec![];
        }
    }

    // bpf_d_path is restrictive
    if helper == constants::BPF_D_PATH {
        if !matches!(env.ctx.prog_kind, ProgramKind::Tracing | ProgramKind::Lsm) {
            env.fail(VerificationError::HelperNotAllowedForProgram { pc, helper, kind: env.ctx.prog_kind });
            return vec![];
        } else {
            if matches!(env.ctx.attach_kind, AttachKind::TraceRawTp) {
                env.fail(VerificationError::HelperNotAllowedForProgram { pc, helper, kind: env.ctx.prog_kind });
                return vec![];
            }
        }
    }
    
    // ========================================================================
    // Normal helper handling
    // ========================================================================

    // 1. Update types
    update_call_types(env, &in_types, &mut state, helper);
    
    // 2. Update DBM - forget caller-saved registers
    for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        forget(&mut state.dbm, r);
    }
    
    // 3. Apply return value bounds for specific helpers
    apply_return_bounds(&mut state, helper);
    
    // 4. Forget packet pointer DBM entries if they were invalidated
    if helper_invalidates_packets(helper) {
        for r in Reg::ALL {
            if r != Reg::R10 {
                match in_types.get(r) {
                    RegType::PtrToPacket { .. } | RegType::PtrToPacketEnd => {
                        forget(&mut state.dbm, r);
                    }
                    _ => {}
                }
            }
        }
    }
    
    // 5. Advance PC and return
    state.pc += 1;
    vec![state]
}

/// Apply return value bounds based on helper semantics.
fn apply_return_bounds(state: &mut State, helper: u32) {
    match helper {
        constants::BPF_REDIRECT => {
            // Returns TC_ACT_* (0-7)
            assume_ge_const(&mut state.dbm, Reg::R0, 0);
            assume_le_const(&mut state.dbm, Reg::R0, 7);
        }
        constants::BPF_FIB_LOOKUP => {
            // Returns BPF_FIB_LKUP_RET_* (0-8)
            assume_ge_const(&mut state.dbm, Reg::R0, 0);
            assume_le_const(&mut state.dbm, Reg::R0, 8);
        }
        constants::BPF_MAP_UPDATE_ELEM | 
        constants::BPF_MAP_DELETE_ELEM |
        constants::BPF_SKB_STORE_BYTES |
        constants::BPF_XDP_ADJUST_HEAD => {
            // Returns 0 on success, negative on error
            // Could add bounds but being conservative for now
        }
        constants::BPF_GET_PRANDOM_U32 | constants::BPF_GET_CGROUP_CLASS_ID => {
            // Returns a random u32
            assume_ge_const(&mut state.dbm, Reg::R0, 0);
            assume_le_const(&mut state.dbm, Reg::R0, 0xFFFF_FFFF);
            state.set_tnum(Reg::R0, Tnum::u32_unknown());
        }
        _ => {}
    }
}

/// Get argument registers based on helper signature.
fn get_arg_regs_from_signature(helper: u32) -> Vec<Reg> {
    let arg_regs = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];
    
    if let Some(sig) = get_helper_signature(helper) {
        arg_regs[..sig.arg_count()].to_vec()
    } else {
        // Unknown helper - conservatively check R1
        vec![Reg::R1]
    }
}

fn allowed_while_in_active_lock(helper: u32) -> bool {
    match helper {
        constants::BPF_GET_PRANDOM_U32 => false,
        _ => true,
    }
}

/// Transfer function for relative Call (BPF-to-BPF function call) instructions.
pub(crate) fn transfer_call_rel(
    env: &mut VerifierEnv,
    mut state: State,
    target: usize,
) -> Vec<State> {
    // Target cannot be a back edge
    if target <= state.pc {
        env.fail(VerificationError::BackEdge { pc: state.pc, target });
        return vec![];
    }

    // BPF enforces max call depth of 8
    info!("[Verifier] pc {}: current call depth = {}", state.pc, state.stack_frame_count());
    if state.stack_frame_count() >= 8 {
        env.fail(VerificationError::MaxCallDepthExceeded { pc: state.pc });
        return vec![];
    }

    // Push return address and jump to callee
    state.push_frame(state.pc + 1);

    // Update types
    update_call_rel_types(&mut state);
    state.pc = target;

    // Only the "enter callee" path — return path comes from callee's Exit
    vec![state]
}

// ============================================================================
// Bounds Checking Helper
// ============================================================================

/// Validates all pointer-size pairs for a helper call.
/// Returns true if all pairs are valid, false otherwise (error reported).
pub fn check_mem_size_pairs(
    env: &mut VerifierEnv,
    state: &State,
    helper: u32,
    pc: usize,
) -> bool {
    let pairs = get_mem_size_pairs(helper);
    
    for pair in pairs {
        if !check_single_mem_size_pair(env, state, pair, pc) {
            return false;
        }
    }
    
    true
}

/// Validates a single pointer-size pair.
fn check_single_mem_size_pair(
    env: &mut VerifierEnv,
    state: &State,
    pair: &MemSizePair,
    pc: usize,
) -> bool {
    let ptr_type = state.types.get(pair.ptr_reg);
    
    // Handle NULL pointer case
    if is_zero(&state.dbm, pair.ptr_reg) {
        if pair.allow_zero {
            // NULL ptr is OK, but size must also be 0
            if !is_zero(&state.dbm, pair.size_reg) {
                env.fail(VerificationError::InvalidArgType { pc, reg: pair.size_reg });
                error!("[Verifier] pc {}: {:?} must be 0 when {:?} is NULL",
                       pc, pair.size_reg, pair.ptr_reg);
                return false;
            }
            return true;
        } else {
            // NULL not allowed for this pair
            env.fail(VerificationError::InvalidArgType { pc, reg: pair.ptr_reg });
            error!("[Verifier] pc {}: {:?} cannot be NULL", pc, pair.ptr_reg);
            return false;
        }
    }
    
    // Get size bounds from DBM
    let (_, Some(max_size)) = get_bounds(&state.dbm, pair.size_reg) else {
        // Size is unbounded - reject
        env.fail(VerificationError::InvalidArgType { pc, reg: pair.size_reg });
        error!("[Verifier] pc {}: {:?} has unbounded size", pc, pair.size_reg);
        return false;
    };
    
    // Size must be non-negative
    if !nonneg(&state.dbm, pair.size_reg) {
        env.fail(VerificationError::InvalidArgType { pc, reg: pair.size_reg });
        error!("[Verifier] pc {}: {:?} must be non-negative", pc, pair.size_reg);
        return false;
    }
    
    // Check zero size
    if max_size == 0 {
        if pair.allow_zero {
            return true;
        } else {
            env.fail(VerificationError::InvalidArgType { pc, reg: pair.size_reg });
            error!("[Verifier] pc {}: {:?} cannot be 0", pc, pair.size_reg);
            return false;
        }
    }
    
    // Validate pointer can accommodate the access
    check_ptr_access_size(env, state, pair.ptr_reg, ptr_type, max_size as u32, pc)
}

fn checked_by_mem_size_pairs(
    helper: u32,
    reg: Reg
) -> bool {
    let pairs = get_mem_size_pairs(helper);
    
    for pair in pairs {
        if pair.ptr_reg == reg {
            return true;
        }
    }
    
    false
}

/// Checks that a pointer can safely access `size` bytes.
fn check_ptr_access_size(
    env: &mut VerifierEnv,
    state: &State,
    ptr_reg: Reg,
    ptr_type: RegType,
    size: u32,
    pc: usize,
) -> bool {
    match ptr_type {
        RegType::PtrToStack { offset: Some(off), .. } => {
            // Stack: check [off, off + size) is within stack bounds
            // Stack grows down, so valid range is [-512, 0)
            let end_offset = off + size as i64;
            if off < -512 || end_offset > 0 {
                env.fail(VerificationError::StackOutOfBounds { pc, off, size: size.into() });
                error!("[Verifier] pc {}: stack access [{}, {}) out of bounds",
                       pc, off, end_offset);
                return false;
            }
            // Also check stack slots are initialized for reads
            access::check_stack_arg_readable(env, state, off, size as i64, pc, AccessKind::HelperArg);
            !env.failed()
        }
        
        RegType::PtrToStack { offset: None, .. } => {
            env.fail(VerificationError::InvalidArgType { pc, reg: ptr_reg });
            error!("[Verifier] pc {}: {:?} has unknown stack offset", pc, ptr_reg);
            false
        }
        
        RegType::PtrToMapValue { map_idx, offset, id: _ } => {
            // Map value: check offset + size <= value_size
            let Some(map_def) = env.ctx.map_defs.get(map_idx) else {
                env.fail(VerificationError::MapNotFound { pc, map_idx });
                return false;
            };
            
            access::check_map_access(
                env,
                state,
                map_def.value_size as i64,
                offset,
                map_idx,
                ptr_reg,
                map_def,
                0,
                size as i64,
                pc,
            );
            !env.failed()
        }
        
        RegType::PtrToPacket { range, .. } => {
            // Packet: need to verify against packet bounds (data_end - data)
            // This requires range analysis between packet_data and packet_end
            // access::check_load(env, state, ptr_reg, size as i64, 0);
            access::check_packet_access(env, state, ptr_reg, 0, size as i64, range, pc, access::AccessKind::HelperArg);
            !env.failed()
        }
        
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg: ptr_reg });
            error!("[Verifier] pc {}: {:?} ({:?}) not a valid memory pointer",
                   pc, ptr_reg, ptr_type);
            false
        }
    }
}
