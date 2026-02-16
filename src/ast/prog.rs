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
        if s == "xdp" || s.starts_with("xdp/") {
            return ProgramKind::Xdp;
        }
        if s == "classifier"
            || s == "tc"
            || s.starts_with("tc/")
            || s.starts_with("classifier/")
            || s == "sched_cls"
            || s == "action"
            || s.starts_with("action/")
        {
            return ProgramKind::SchedCls;
        }
        if s == "socket" || s.starts_with("socket/") {
            return ProgramKind::SocketFilter;
        }
        if s == "sockops" || s.starts_with("sockops/") {
            return ProgramKind::SockOps;
        }
        if s == "sk_msg" || s.starts_with("sk_msg/") {
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
        if s == "kprobe" || s.starts_with("kprobe/") || s.starts_with("kretprobe/") {
            return ProgramKind::Kprobe;
        }
        if s == "tracepoint" || s.starts_with("tracepoint/") {
            return ProgramKind::Tracepoint;
        }
        if s == "raw_tracepoint" || s.starts_with("raw_tracepoint/") {
            return ProgramKind::RawTracepoint;
        }
        if s == "perf_event" || s.starts_with("perf_event/") {
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
            ProgramKind::CgroupSock => ContextKind::SockOps,
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
