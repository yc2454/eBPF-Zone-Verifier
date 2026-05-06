// src/analysis/transfer/call/compat.rs
//
// Type compatibility tables and helper-map requirements.
// Based on Linux kernel's `compatible_reg_types` pattern.

use crate::analysis::machine::reg_types::RegType;
use crate::common::constants;

// ============================================================================
// Type Compatibility Predicates
// ============================================================================

/// Check if a RegType matches any predicate in the compatibility list.
pub fn is_compatible(actual: &RegType, compatible: &[fn(&RegType) -> bool]) -> bool {
    compatible.iter().any(|pred| pred(actual))
}

// --- Socket-related predicates ---

pub fn is_ptr_to_socket(t: &RegType) -> bool {
    matches!(t, RegType::PtrToSocket { .. })
}

pub fn is_ptr_to_sock_common(t: &RegType) -> bool {
    matches!(t, RegType::PtrToSockCommon { .. })
}

pub fn is_ptr_to_sock_common_or_null(t: &RegType) -> bool {
    matches!(t, RegType::PtrToSockCommonOrNull { .. })
}

pub fn is_ptr_to_socket_or_null(t: &RegType) -> bool {
    matches!(t, RegType::PtrToSocketOrNull { .. })
}

pub fn is_ptr_to_tcp_sock(t: &RegType) -> bool {
    matches!(t, RegType::PtrToTcpSock { .. })
}

/// True iff `t` is `PtrToBtfId{<sock-subtype>, ...}` — the kernel
/// `struct tcp_sock` / `tcp6_sock` / `tcp_timewait_sock` /
/// `tcp_request_sock` / `udp6_sock` / `unix_sock` produced by
/// `bpf_skc_to_*` helpers. The kernel's `bpf_sk_release` accepts any
/// PTR_TO_BTF_ID rooted at `struct sock_common` (subclass walk via
/// BTF). We approximate with a name allowlist: the closed set of
/// concrete kernel-struct names returned by the skc_to_* family.
pub fn is_ptr_to_btf_sock_subtype(t: &RegType) -> bool {
    matches!(
        t,
        RegType::PtrToBtfId {
            type_name: "tcp_sock"
                | "tcp6_sock"
                | "tcp_timewait_sock"
                | "tcp_request_sock"
                | "udp6_sock"
                | "unix_sock",
            ..
        }
    )
}

pub fn is_ptr_to_stack(t: &RegType) -> bool {
    matches!(t, RegType::PtrToStack { .. })
}

// --- Memory-related predicates ---

pub fn is_ptr_to_map_value(t: &RegType) -> bool {
    matches!(t, RegType::PtrToMapValue { .. })
}

pub fn is_ptr_to_map_value_or_null(t: &RegType) -> bool {
    matches!(t, RegType::PtrToMapValueOrNull { .. })
}

pub fn is_ptr_to_packet(t: &RegType) -> bool {
    matches!(t, RegType::PtrToPacket)
}

pub fn is_ptr_to_packet_meta(t: &RegType) -> bool {
    matches!(t, RegType::PtrToPacketMeta)
}

#[allow(dead_code)]
pub fn is_ptr_to_ctx(t: &RegType) -> bool {
    matches!(t, RegType::PtrToCtx)
}

#[allow(dead_code)]
pub fn is_ptr_to_map_object(t: &RegType) -> bool {
    matches!(t, RegType::PtrToMapObject { .. })
}

#[allow(dead_code)]
pub fn is_ptr_to_alloc_mem(t: &RegType) -> bool {
    matches!(t, RegType::PtrToAllocMem { .. })
}

#[allow(dead_code)]
pub fn is_ptr_to_btf_id(t: &RegType) -> bool {
    matches!(t, RegType::PtrToBtfId { .. })
}

/// Stricter PtrToBtfId predicate: only TRUSTED or RCU bands.
/// Mirrors kernel `ARG_PTR_TO_BTF_ID_SOCK_COMMON`'s requirement that
/// the pointer be `ptr_`, `trusted_ptr_`, or `rcu_ptr_` (verifier.c
/// rejects `untrusted_ptr_*`). Used by sock-class helper validators
/// (bpf_sk_storage_get/_delete) so a chained load like `skb->next`
/// — which our BTF field-walk types as PtrToBtfId{sk_buff, UNTRUSTED}
/// per kernel "old-style ptr_to_btf_id" — is rejected as the kernel
/// would, rather than accepted as a generic any-PtrToBtfId match.
pub fn is_ptr_to_btf_id_trusted_or_rcu(t: &RegType) -> bool {
    use crate::analysis::machine::reg_types::PtrFlags;
    matches!(
        t,
        RegType::PtrToBtfId { flags, .. }
            if flags.contains(PtrFlags::TRUSTED) || flags.contains(PtrFlags::RCU)
    )
}

// ============================================================================
// Type Compatibility Tables
// ============================================================================

/// Types compatible with PtrToSocket argument.
/// Phase 3 cluster B follow-on: `is_ptr_to_tcp_sock` accepts the
/// narrowed-by-`bpf_skc_to_tcp_sock` form so `bpf_sk_release(tcp)`
/// is allowed (kernel checks ref_id, not the static subclass —
/// PtrToTcpSock carries the same ref_id as the original socket).
/// Closes `verifier_ref_tracking::sk_release_btf_tcp_sock`.
pub static SOCKET_COMPAT: &[fn(&RegType) -> bool] = &[
    is_ptr_to_socket,
    is_ptr_to_sock_common,
    is_ptr_to_tcp_sock,
    is_ptr_to_btf_sock_subtype,
    is_ptr_to_stack,
];

/// Types compatible with PtrToSockCommon argument
pub static SOCK_COMMON_COMPAT: &[fn(&RegType) -> bool] = &[
    is_ptr_to_sock_common,
    is_ptr_to_socket,
    is_ptr_to_tcp_sock,
    is_ptr_to_btf_sock_subtype,
];

/// Types compatible with PtrToBTFIdSockCommon argument.
///
/// W6.4a-followon: includes `PtrToBtfId` (any BTF-typed pointer). The
/// kernel verifier's `ARG_PTR_TO_BTF_ID_SOCK_COMMON` accepts any
/// PTR_TO_BTF_ID whose type id is `struct sock` or a sock subclass
/// (`tcp_sock`, `udp_sock`, …). For struct_ops methods we lose the
/// exact type name (intern_btf_type_name returns "unknown"), so the
/// best we can do here is "any PtrToBtfId" — narrowing requires
/// resolving subclass relationships in BTF, which is W7 territory.
///
/// Also includes the OrNull variants: bpf_sk_storage_{get,delete}'s
/// R2 declares `ARG_PTR_TO_BTF_ID_SOCK_COMMON | PTR_MAYBE_NULL`, so
/// kernel accepts both null and non-null pointers (helper returns
/// NULL / no-op when arg is NULL). Tests like connect_force_port4
/// pass `ctx->sk` directly without an intervening null check.
pub static BTF_SOCK_COMMON_COMPAT: &[fn(&RegType) -> bool] = &[
    is_ptr_to_sock_common,
    is_ptr_to_sock_common_or_null,
    is_ptr_to_socket,
    is_ptr_to_socket_or_null,
    is_ptr_to_tcp_sock,
    // Strict trust gating on the generic PtrToBtfId fallthrough: kernel
    // rejects `untrusted_ptr_*` for ARG_PTR_TO_BTF_ID_SOCK_COMMON. The
    // bare `is_ptr_to_btf_id` would FA non-trusted chained loads like
    // `skb->next` passed to bpf_sk_storage_get (nested_trust_failure).
    is_ptr_to_btf_id_trusted_or_rcu,
    // cgroup/sock_create / cgroup/sock_release / cgroup/sockopt
    // contexts ARE a `struct bpf_sock *` — programs pass ctx directly
    // as the sk arg of bpf_sk_storage_{get,delete}. Kernel admits
    // PTR_TO_CTX for these per-prog-type registrations. udp_limit.c::
    // {sock,sock_release} drives this.
    is_ptr_to_ctx,
];

/// Types compatible with generic memory pointers (PtrToMem)
#[allow(dead_code)]
pub static MEM_COMPAT: &[fn(&RegType) -> bool] = &[
    is_ptr_to_stack,
    is_ptr_to_packet,
    is_ptr_to_map_value,
    is_ptr_to_ctx,
];

/// Types compatible with PtrToMapValue argument
#[allow(dead_code)]
pub static MAP_VALUE_COMPAT: &[fn(&RegType) -> bool] = &[
    is_ptr_to_map_value,
    is_ptr_to_stack,
    is_ptr_to_packet,
    is_ptr_to_packet_meta,
];

/// Types compatible with PtrToMapValueOrNull argument
pub static MAP_VALUE_OR_NULL_COMPAT: &[fn(&RegType) -> bool] = &[
    is_ptr_to_map_value,
    is_ptr_to_map_value_or_null,
    is_ptr_to_stack,
    is_ptr_to_packet,
    is_ptr_to_packet_meta,
];

// ============================================================================
// Helper-Map Requirements
// ============================================================================

/// Represents requirements for map types used with specific helpers.
#[derive(Debug, Clone, Copy)]
pub struct HelperMapRequirement {
    /// The helper function ID
    pub helper: u32,
    /// Required map type (if Some, the map MUST be this type)
    pub required_type: Option<u32>,
    /// Rejected map types (the map MUST NOT be any of these types)
    pub rejected_types: &'static [u32],
}

/// Table of helper-specific map type requirements.
/// This centralizes the logic that was scattered across the ConstMapPtr match arm.
pub static HELPER_MAP_REQUIREMENTS: &[HelperMapRequirement] = &[
    // bpf_tail_call requires PROG_ARRAY
    HelperMapRequirement {
        helper: constants::BPF_TAIL_CALL,
        required_type: Some(constants::BPF_MAP_TYPE_PROG_ARRAY),
        rejected_types: &[],
    },
    // bpf_perf_event_output requires PERF_EVENT_ARRAY
    HelperMapRequirement {
        helper: constants::BPF_PERF_EVENT_OUTPUT,
        required_type: Some(constants::BPF_MAP_TYPE_PERF_EVENT_ARRAY),
        rejected_types: &[],
    },
    // bpf_ringbuf_output/reserve require RINGBUF
    HelperMapRequirement {
        helper: constants::BPF_RINGBUF_OUTPUT,
        required_type: Some(constants::BPF_MAP_TYPE_RINGBUF),
        rejected_types: &[],
    },
    HelperMapRequirement {
        helper: constants::BPF_RINGBUF_RESERVE,
        required_type: Some(constants::BPF_MAP_TYPE_RINGBUF),
        rejected_types: &[],
    },
    // bpf_map_lookup_elem rejects certain map types
    HelperMapRequirement {
        helper: constants::BPF_MAP_LOOKUP_ELEM,
        required_type: None,
        rejected_types: &[
            constants::BPF_MAP_TYPE_STACK_TRACE,
            constants::BPF_MAP_TYPE_PROG_ARRAY,
            constants::BPF_MAP_TYPE_SK_STORAGE,
        ],
    },
];

/// Look up map requirements for a given helper.
pub fn get_helper_map_requirement(helper: u32) -> Option<&'static HelperMapRequirement> {
    HELPER_MAP_REQUIREMENTS.iter().find(|r| r.helper == helper)
}

/// Check if a map type is valid for a given helper.
/// Returns Ok(()) if valid, Err with message if invalid.
pub fn check_map_type_for_helper(helper: u32, map_type: u32) -> Result<(), &'static str> {
    if let Some(req) = get_helper_map_requirement(helper) {
        // Check required type
        if let Some(required) = req.required_type
            && map_type != required
        {
            return Err(match helper {
                constants::BPF_TAIL_CALL => "bpf_tail_call requires PROG_ARRAY map",
                constants::BPF_PERF_EVENT_OUTPUT => {
                    "bpf_perf_event_output requires PERF_EVENT_ARRAY map"
                }
                constants::BPF_RINGBUF_OUTPUT | constants::BPF_RINGBUF_RESERVE => {
                    "bpf_ringbuf_* requires RINGBUF map"
                }
                _ => "invalid map type for helper",
            });
        }

        // Check rejected types
        if req.rejected_types.contains(&map_type) {
            return Err("map type not allowed for this helper");
        }
    }
    Ok(())
}

// ============================================================================
// Nullable Type Helpers
// ============================================================================

use super::signatures::ArgKind;

/// Returns true if this argument type is a nullable variant (*OrNull).
pub fn is_nullable_arg_type(arg_type: ArgKind) -> bool {
    matches!(
        arg_type,
        ArgKind::PtrToCtxOrNull
            | ArgKind::PtrToMemOrNull
            | ArgKind::PtrToUninitMemOrNull
            | ArgKind::PtrToStackOrNull
            | ArgKind::PtrToMapValueOrNull
    )
}

/// Returns the base (non-nullable) type for a nullable argument type.
pub fn base_arg_type(arg_type: ArgKind) -> ArgKind {
    match arg_type {
        ArgKind::PtrToCtxOrNull => ArgKind::PtrToCtx,
        ArgKind::PtrToMemOrNull => ArgKind::PtrToMem,
        ArgKind::PtrToUninitMemOrNull => ArgKind::PtrToUninitMem,
        ArgKind::PtrToStackOrNull => ArgKind::PtrToStack,
        ArgKind::PtrToMapValueOrNull => ArgKind::PtrToMapValue,
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::machine::frame_stack::FrameLevel;

    #[test]
    fn test_socket_compat() {
        let socket = RegType::PtrToSocket { ref_id: None };
        let sock_common = RegType::PtrToSockCommon { ref_id: None };
        let stack = RegType::PtrToStack {
            frame_level: FrameLevel::MAIN,
        };
        let packet = RegType::PtrToPacket;

        assert!(is_compatible(&socket, SOCKET_COMPAT));
        assert!(is_compatible(&sock_common, SOCKET_COMPAT));
        assert!(is_compatible(&stack, SOCKET_COMPAT));
        assert!(!is_compatible(&packet, SOCKET_COMPAT));
    }

    #[test]
    fn test_helper_map_requirements() {
        // tail_call requires PROG_ARRAY
        assert!(
            check_map_type_for_helper(constants::BPF_TAIL_CALL, constants::BPF_MAP_TYPE_PROG_ARRAY)
                .is_ok()
        );
        assert!(
            check_map_type_for_helper(constants::BPF_TAIL_CALL, constants::BPF_MAP_TYPE_HASH)
                .is_err()
        );

        // lookup_elem rejects certain types
        assert!(
            check_map_type_for_helper(constants::BPF_MAP_LOOKUP_ELEM, constants::BPF_MAP_TYPE_HASH)
                .is_ok()
        );
        assert!(
            check_map_type_for_helper(
                constants::BPF_MAP_LOOKUP_ELEM,
                constants::BPF_MAP_TYPE_STACK_TRACE
            )
            .is_err()
        );
    }
}
