//! Map `SEC("…")` strings to BPF prog_type values.
//!
//! Mirrors libbpf's `section_defs[]` table, scoped to the SECs that
//! actually appear in `tools/testing/selftests/bpf/progs/verifier_*.c`
//! and the dynptr/iters/timer/cpumask/rbtree/list/refcount/rcu/arena
//! corpora we need for Phase 1, 4, and 5 translation.
//!
//! Unknown strings return `None` — caller decides whether to skip the
//! test or surface an error. Add entries as new corpora arrive.

use crate::common::constants;

#[derive(Debug, Clone, Copy)]
pub struct SecMatch {
    pub prog_type: u32,
    pub expected_attach_type: Option<u32>,
}

/// Look up a `SEC("…")` string. The libbpf `?` "optional" prefix should
/// already be stripped by the caller (see [`super::attrs::scrape`]).
pub fn lookup(sec: &str) -> Option<SecMatch> {
    // Take the part before the first '/' as the section "kind", which
    // matches how libbpf's prefix table works for SECs that carry an
    // attach-target after the slash (e.g. `tp/syscalls/...` → kind `tp`).
    let kind = sec.split('/').next().unwrap_or(sec);

    let prog_type = match kind {
        "socket" => constants::BPF_PROG_TYPE_SOCKET_FILTER,
        "kprobe" | "kretprobe" => constants::BPF_PROG_TYPE_KPROBE,

        // sched_cls and its modern aliases.
        "tc" | "classifier" | "tcx" | "netkit" => constants::BPF_PROG_TYPE_SCHED_CLS,

        "action" => constants::BPF_PROG_TYPE_SCHED_ACT,
        "tracepoint" | "tp" => constants::BPF_PROG_TYPE_TRACEPOINT,
        "raw_tracepoint" | "raw_tp" => constants::BPF_PROG_TYPE_RAW_TRACEPOINT,
        "tp_btf" | "fentry" | "fexit" | "fmod_ret" => constants::BPF_PROG_TYPE_TRACING,
        "xdp" => constants::BPF_PROG_TYPE_XDP,
        "perf_event" => constants::BPF_PROG_TYPE_PERF_EVENT,
        "cgroup_skb" => constants::BPF_PROG_TYPE_CGROUP_SKB,
        "cgroup_sock" => constants::BPF_PROG_TYPE_CGROUP_SOCK,
        "lwt_in" => constants::BPF_PROG_TYPE_LWT_IN,
        "lwt_out" => constants::BPF_PROG_TYPE_LWT_OUT,
        // Custom SEC names used by test_lwt_redirect.c. The C test
        // driver (prog_tests/lwt_redirect.c) calls
        // bpf_program__set_type(BPF_PROG_TYPE_LWT_{IN,OUT}) by SEC name
        // — see INGRESS_SEC / EGRESS_SEC #defines. The `_nomac` variants
        // map to the same prog types; the suffix distinguishes attach
        // configuration in the userspace side of the test.
        "redir_ingress" | "redir_ingress_nomac" => constants::BPF_PROG_TYPE_LWT_IN,
        "redir_egress" | "redir_egress_nomac" => constants::BPF_PROG_TYPE_LWT_OUT,
        "lwt_xmit" => constants::BPF_PROG_TYPE_LWT_XMIT,
        "lwt_seg6local" => constants::BPF_PROG_TYPE_LWT_SEG6LOCAL,
        "sockops" => constants::BPF_PROG_TYPE_SOCK_OPS,
        "sk_skb" => constants::BPF_PROG_TYPE_SK_SKB,
        "sk_msg" => constants::BPF_PROG_TYPE_SK_MSG,
        "sk_reuseport" => constants::BPF_PROG_TYPE_SK_REUSEPORT,
        "flow_dissector" => constants::BPF_PROG_TYPE_FLOW_DISSECTOR,
        "lsm" | "lsm.s" => constants::BPF_PROG_TYPE_LSM,
        // BPF_PROG_TYPE_SYSCALL (= 32) and iter prog types aren't in
        // common/constants.rs yet — Phase 6 territory. Add when needed.
        "iter" | "iter.s" => constants::BPF_PROG_TYPE_TRACING,

        _ => return None,
    };

    Some(SecMatch {
        prog_type,
        expected_attach_type: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_basic_sections() {
        assert_eq!(
            lookup("socket").unwrap().prog_type,
            constants::BPF_PROG_TYPE_SOCKET_FILTER
        );
        assert_eq!(
            lookup("xdp").unwrap().prog_type,
            constants::BPF_PROG_TYPE_XDP
        );
        assert_eq!(
            lookup("flow_dissector").unwrap().prog_type,
            constants::BPF_PROG_TYPE_FLOW_DISSECTOR
        );
    }

    #[test]
    fn collapses_modern_aliases_to_underlying_type() {
        // Phase 6 modernization plan calls these out: tcx/ingress, netkit/* etc.
        assert_eq!(
            lookup("tcx/ingress").unwrap().prog_type,
            constants::BPF_PROG_TYPE_SCHED_CLS
        );
        assert_eq!(
            lookup("tc").unwrap().prog_type,
            constants::BPF_PROG_TYPE_SCHED_CLS
        );
    }

    #[test]
    fn handles_attach_target_after_slash() {
        assert_eq!(
            lookup("tp/syscalls/sys_enter_nanosleep").unwrap().prog_type,
            constants::BPF_PROG_TYPE_TRACEPOINT
        );
        assert_eq!(
            lookup("tp_btf/kfree_skb").unwrap().prog_type,
            constants::BPF_PROG_TYPE_TRACING
        );
        assert_eq!(
            lookup("fentry/bpf_fentry_test1").unwrap().prog_type,
            constants::BPF_PROG_TYPE_TRACING
        );
    }

    #[test]
    fn unknown_returns_none() {
        assert!(lookup(".data.arr_foo").is_none());
    }
}
