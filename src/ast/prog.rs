// src/ast/prog.rs

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProgramKind {
    Unspec,
    SocketFilter,
    Kprobe,
    SchedCls,
    SchedAct,
    Tracepoint,
    Xdp,
    PerfEvent,
    CgroupSkb,
    CgroupSock,
    LwtIn,
    LwtOut,
    LwtXmit,
    SockOps,
    SkSkb,
    SkLookup,
    CgroupDevice,
    SkMsg,
    RawTracepoint,
    RawTracepointWritable,
    CgroupSockAddr,
    Lsm,
    Tracing,
    /// `SEC("syscall")` — BPF_PROG_TYPE_SYSCALL (kernel v5.11+).
    /// Distinct from generic Unknown so the W6.3 prog-type allowlist
    /// can permit cgroup / cpumask / task kfuncs in syscall programs
    /// (where they're allowed) but reject in raw_tp.
    Syscall,
    /// `SEC("struct_ops[.s]/<member>")` or bare `SEC("struct_ops")`
    /// — BPF_PROG_TYPE_STRUCT_OPS (kernel v5.6+, expanded by sched_ext
    /// in v6.12). Each program implements one member of an ops-struct
    /// (`tcp_congestion_ops.init`, `sched_ext_ops.dispatch`, …); R1..Rn
    /// entry types are derived from that member's BTF FUNC_PROTO by the
    /// W6.4 entry-state plumbing.
    StructOps,
    /// `SEC("netfilter")` — BPF_PROG_TYPE_NETFILTER. R0 at exit must be a
    /// known value in [0, 1] (NF_DROP / NF_ACCEPT).
    Netfilter,
    /// `SEC("flow_dissector")` — BPF_PROG_TYPE_FLOW_DISSECTOR. Receives
    /// `struct __sk_buff *` ctx but with a stricter allowlist than the
    /// generic SkBuff context (only `data`, `data_end`, `flow_keys`).
    FlowDissector,
    /// `SEC("sk_reuseport")` — BPF_PROG_TYPE_SK_REUSEPORT. Receives
    /// `struct sk_reuseport_md *` ctx directly (no BPF_PROG wrapper);
    /// ctx-access is BTF-driven via `field_at_offset` on the iter-style
    /// path in `validate_ctx_access`.
    SkReuseport,
    #[default]
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum ContextKind {
    XdpMd,
    SkBuff,
    SkLookup,
    SockOps,
    BpfSock,
    SkMsgMd,
    BpfSockAddr,
    PtRegs,
    IterTask,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttachKind {
    TraceRawTp,
    TraceIter,
    Unknown,
}

impl ProgramKind {
    pub fn from_section(s: &str) -> Self {
        let s = s.to_lowercase();
        let s = s.trim();

        // ---- Modern aliases (W6.2) ----
        //
        // Recognized natively rather than relying on incidental
        // `starts_with("tc")` matches or falling through to Unknown. Each
        // modern SEC routes to its underlying kernel prog_type (libbpf's
        // section_defs[] is the source of truth):
        //   `tcx/{ingress,egress}` / `netkit/{primary,peer}` → sched_cls
        //   `fentry[.s]/`, `fexit[.s]/`, `fmod_ret[.s]/`, `tp_btf/`,
        //     `iter[.s]/` → tracing
        //   `raw_tp[.w][/…]` → raw_tracepoint
        //   `lsm[.s]/` → lsm
        //   `uprobe[.s]/`, `uretprobe[.s]/` → kprobe
        //   `cgroup_skb/{ingress,egress}` (libbpf modern form, distinct
        //     from legacy `cgroup/skb`) → cgroup_skb
        //
        // SECs without a corresponding ProgramKind variant
        // (`syscall`, `flow_dissector`, `sk_reuseport`, `sk_lookup`,
        // `struct_ops/*`, `netfilter/*`) intentionally fall through to
        // Unknown — adding variants is W6.3/W6.4 territory.
        if s.starts_with("tcx/") || s.starts_with("netkit/") {
            return ProgramKind::SchedCls;
        }
        if s.starts_with("fentry/")
            || s.starts_with("fentry.s/")
            || s.starts_with("fexit/")
            || s.starts_with("fexit.s/")
            || s.starts_with("fmod_ret/")
            || s.starts_with("fmod_ret.s/")
            || s.starts_with("tp_btf/")
            // libbpf optional-load form: `?tp_btf/<func>`. Treat as
            // Tracing for kfunc-allowlist purposes (cf.
            // `verifier_global_ptr_args::trusted_task_arg_nullable`).
            // We don't strip `?` for the other tracing flavors because
            // `?fentry/` / `?fexit/` siblings in the corpus rely on
            // their current-Unknown kfunc rejection — see audit doc.
            || s.starts_with("?tp_btf/")
            || s.starts_with("iter/")
            || s.starts_with("iter.s/")
        {
            return ProgramKind::Tracing;
        }
        if s == "raw_tp"
            || s.starts_with("raw_tp/")
            || s.starts_with("raw_tp.w/")
            || s == "raw_tp.w"
        {
            return ProgramKind::RawTracepoint;
        }
        if s.starts_with("lsm/") || s.starts_with("lsm.s/") {
            return ProgramKind::Lsm;
        }
        if s.starts_with("uprobe/")
            || s.starts_with("uprobe.s/")
            || s.starts_with("uretprobe/")
            || s.starts_with("uretprobe.s/")
            // `uprobe.session` / `kprobe.session`: session-attach SEC has
            // no '/<func>' suffix in the test corpus (see
            // uprobe_multi_verifier.c). Match the bare flavor too so the
            // exit-time R0 ∈ [0, 1] rule in `expected_retval_rule` fires.
            || s == "uprobe.session"
            || s == "uretprobe.session"
            || s == "kprobe.session"
            || s == "kretprobe.session"
        {
            return ProgramKind::Kprobe;
        }
        if s.starts_with("cgroup_skb/") {
            return ProgramKind::CgroupSkb;
        }
        if s == "syscall" {
            return ProgramKind::Syscall;
        }
        if s == "netfilter" || s.starts_with("netfilter/") {
            return ProgramKind::Netfilter;
        }
        if s == "flow_dissector" || s.starts_with("flow_dissector/") {
            return ProgramKind::FlowDissector;
        }
        if s == "sk_reuseport" || s.starts_with("sk_reuseport/") {
            return ProgramKind::SkReuseport;
        }
        // struct_ops (W6.4). Forms in the wild:
        //   "struct_ops"             — bare, member named after func symbol
        //   "struct_ops/<member>"    — explicit member binding
        //   "struct_ops.s/<member>"  — sleepable variant
        //   "?struct_ops/<member>"   — optional (libbpf "weak") binding
        // The leading "?" is libbpf-internal optionality; strip before match.
        let trimmed = s.strip_prefix('?').unwrap_or(&s);
        if trimmed == "struct_ops"
            || trimmed.starts_with("struct_ops/")
            || trimmed.starts_with("struct_ops.s/")
        {
            return ProgramKind::StructOps;
        }

        // ---- Common tc section aliases used by Cilium/Suricata-style objects ----
        if matches!(
            s,
            "from-netdev"
                | "to-netdev"
                | "from-container"
                | "to-container"
                | "filter"
                | "bypass_filter"
                | "loadbalancer"
                | "lb"
                | "vlan_filter"
        ) {
            return ProgramKind::SchedCls;
        }
        if s.starts_with("xdp") {
            return ProgramKind::Xdp;
        }
        // Hotfix for OVS datapath benchmark: datapath.o utilizes bpf_tail_call
        // from ingress/egress (SchedCls) into sections prefixed with "tail-" and "downcall".
        // Since caller and callee must have the same program type, these target
        // sections execute under the SchedCls context (SkBuff). This is a fast-path
        // assumption and not a general mechanism for sound program kind inference.
        if s.starts_with("classifier")
            || s.starts_with("tc")
            || s.starts_with("sched_cls")
            || s.starts_with("action")
            || s.starts_with("ingress")
            || s.starts_with("egress")
            || s.starts_with("l2_")
            || s.starts_with("drop_")
            || s.starts_with("tail")
            || s.starts_with("downcall")
        {
            return ProgramKind::SchedCls;
        }
        if s.starts_with("socket") {
            return ProgramKind::SocketFilter;
        }
        if s.starts_with("sockops") {
            return ProgramKind::SockOps;
        }
        if s.starts_with("sk_msg") {
            return ProgramKind::SkMsg;
        }
        if s.starts_with("cgroup/bind")
            || s.starts_with("cgroup/connect")
            || s.starts_with("cgroup/sendmsg")
            || s.starts_with("cgroup/recvmsg")
            || s.starts_with("cgroup/getpeername")
            || s.starts_with("cgroup/getsockname")
        {
            return ProgramKind::CgroupSockAddr;
        }
        if s.starts_with("cgroup/skb") {
            return ProgramKind::CgroupSkb;
        }
        if s.starts_with("cgroup/sock") || s.starts_with("cgroup/post_bind") {
            return ProgramKind::CgroupSock;
        }
        if s.starts_with("kprobe") || s.starts_with("kretprobe") {
            return ProgramKind::Kprobe;
        }
        if s.starts_with("tracepoint") {
            return ProgramKind::Tracepoint;
        }
        if s.starts_with("raw_tracepoint") {
            return ProgramKind::RawTracepoint;
        }
        if s.starts_with("perf_event") {
            return ProgramKind::PerfEvent;
        }
        if s == "sk_lookup" || s.starts_with("sk_lookup/") {
            return ProgramKind::SkLookup;
        }
        // LWT attach types share __sk_buff context. `lwt_in`/`lwt_out`/
        // `lwt_xmit` map to the corresponding ProgramKind; `lwt_seg6local`
        // also uses __sk_buff so route it to LwtXmit (closest ctx-access
        // semantics — kernel verifies the same set of skb fields plus
        // the seg6local-specific helper allowlist, which is orthogonal).
        if s == "lwt_in" {
            return ProgramKind::LwtIn;
        }
        if s == "lwt_out" {
            return ProgramKind::LwtOut;
        }
        if s == "lwt_xmit" || s == "lwt_seg6local" {
            return ProgramKind::LwtXmit;
        }
        ProgramKind::Unknown
    }

    pub fn context_kind(&self) -> ContextKind {
        match self {
            ProgramKind::Xdp => ContextKind::XdpMd,
            ProgramKind::SchedCls
            | ProgramKind::SocketFilter
            | ProgramKind::SchedAct
            | ProgramKind::SkSkb
            | ProgramKind::CgroupSkb
            | ProgramKind::LwtIn
            | ProgramKind::LwtOut
            | ProgramKind::LwtXmit
            | ProgramKind::Lsm
            | ProgramKind::RawTracepoint
            | ProgramKind::FlowDissector => ContextKind::SkBuff,
            ProgramKind::SockOps => ContextKind::SockOps,
            ProgramKind::SkLookup => ContextKind::SkLookup,
            ProgramKind::SkMsg => ContextKind::SkMsgMd,
            ProgramKind::CgroupSockAddr => ContextKind::BpfSockAddr,
            ProgramKind::CgroupSock => ContextKind::BpfSock,
            _ => ContextKind::Unknown,
        }
    }

    pub fn requires_strict_return_code(&self) -> bool {
        matches!(
            self,
            ProgramKind::CgroupSkb | ProgramKind::CgroupSock | ProgramKind::CgroupSockAddr
        )
    }
}

/// Per-attach-type return-value rule (Cluster B).
///
/// Mirrors the kernel's `check_return_code` per-prog-type / per-expected-attach-type
/// table: at program exit, R0 must lie in `[lo, hi]`, and if `require_known` is
/// true, R0 must additionally be a single known value (smin == smax).
///
/// `subtype` is the SEC suffix after the first `/` lowercased — e.g. for
/// `SEC("cgroup/recvmsg4")` it is `"recvmsg4"`; for `SEC("lsm/file_mprotect")`
/// it is `"file_mprotect"`. For prog kinds whose retval rule does not depend
/// on attach subtype (e.g. netfilter), `subtype` is unused.
#[derive(Debug, Clone, Copy)]
pub struct RetvalRule {
    pub lo: i64,
    pub hi: i64,
    pub require_known: bool,
}

pub fn expected_retval_rule(prog_kind: ProgramKind, subtype: Option<&str>) -> Option<RetvalRule> {
    match prog_kind {
        ProgramKind::CgroupSockAddr => {
            let sub = subtype?;
            // recvmsg / getpeername / getsockname: must return exactly 1.
            if sub.starts_with("recvmsg")
                || sub.starts_with("getpeername")
                || sub.starts_with("getsockname")
            {
                return Some(RetvalRule { lo: 1, hi: 1, require_known: false });
            }
            // bind4 / bind6: [0, 3].
            if sub.starts_with("bind") {
                return Some(RetvalRule { lo: 0, hi: 3, require_known: false });
            }
            // sendmsg / connect: [0, 1] (default for cgroup/sock_addr hooks).
            Some(RetvalRule { lo: 0, hi: 1, require_known: false })
        }
        ProgramKind::Lsm => {
            let sub = subtype?;
            // bool retval hooks.
            if sub == "audit_rule_known" {
                return Some(RetvalRule { lo: 0, hi: 1, require_known: false });
            }
            // void retval hooks: no constraint.
            if sub == "file_free_security" || sub == "task_free" || sub == "inode_free_security" {
                return None;
            }
            // Default LSM hook: errno-or-zero. Only enforce on hooks we know
            // are checked upstream (avoid regressing PASS cases that we
            // currently accept but where the kernel's per-hook policy is
            // looser than [-4095, 0]).
            if sub == "file_mprotect" {
                return Some(RetvalRule { lo: -4095, hi: 0, require_known: false });
            }
            None
        }
        ProgramKind::Netfilter => {
            // NF_DROP=0, NF_ACCEPT=1; kernel additionally requires the value
            // to be a known constant (rejects "R0 is not a known value").
            Some(RetvalRule { lo: 0, hi: 1, require_known: true })
        }
        ProgramKind::Kprobe => {
            // SEC("kprobe.session") and SEC("uprobe.session"): the
            // kernel's session-attach hook expects R0 ∈ [0, 1] at exit
            // — 0 means "skip the matching kretprobe", 1 means "run
            // it". Plain `kprobe`/`uprobe` programs don't constrain R0.
            // Both share ProgramKind::Kprobe; the subtype derived from
            // the SEC string disambiguates.
            if matches!(subtype, Some("session")) {
                return Some(RetvalRule { lo: 0, hi: 1, require_known: false });
            }
            None
        }
        _ => None,
    }
}
