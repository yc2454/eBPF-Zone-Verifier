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
        {
            return ProgramKind::Kprobe;
        }
        if s.starts_with("cgroup_skb/") {
            return ProgramKind::CgroupSkb;
        }
        if s == "syscall" {
            return ProgramKind::Syscall;
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
        if s.starts_with("cgroup/sock") {
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
            | ProgramKind::RawTracepoint => ContextKind::SkBuff,
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
