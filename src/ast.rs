// src/ast.rs
use std::fmt;

use crate::zone::domain::Reg;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operand {
    Reg(Reg),
    Imm(i64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Width {
    W32,
    W64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AluOp {
    Add,
    Sub,
    And,
    Or,
    Xor,
    Mov,
    Shl,
    Shr,
    Arsh,   // arithmetic right shift
    Mul,
    Mod,
    Div,
    Neg,
    // later: Div, Neg, etc.
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    UGe, ULe, UGt, ULt,
    Eq, Ne, SLt, SGt, SLe, SGe,
    Test, // special case for BPF_JSET
}

#[derive(Debug, Clone, Copy)]
pub enum EndianOp {
    ToBe, // to big-endian
    ToLe, // to little-endian
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemSize {
    U8,
    U16,
    U32,
    U64,
}

impl MemSize {
    pub fn bytes(&self) -> usize {
        match self {
            MemSize::U8  => 1,
            MemSize::U16 => 2,
            MemSize::U32 => 4,
            MemSize::U64 => 8,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PacketLoadMode {
    Abs, // Absolute: data[imm]
    Ind, // Indirect: data[src + imm]
}

#[derive(Debug, Clone, Copy)]
pub enum Instr {
    /// rX = arg0
    /// (Note: only used for entry point arg0 loading)
    MovArg0 { dst: Reg },

    /// dst = ALU(dst, src/imm)   (includes MOV as AluOp::Mov)
    /// Width matters for BPF (wX vs rX).
    Alu {
        width: Width,
        op: AluOp,
        dst: Reg,
        src: Operand,
    },

    /// Endian conversion on a register (BPF_END)
    Endian {
        dst: Reg,
        width: Width,
        op: EndianOp,
        size: u32,
    },

    /// if left (op) right goto target; else fallthrough
    If {
        width: Width,
        left: Reg,
        op: CmpOp,
        right: Operand,
        target: usize,
    },

    /// Unconditional jump to an absolute PC target.
    Jmp {
        target: usize,
    },

    /// dst = *(size *)(base + off)
    Load {
        size: MemSize,
        dst: Reg,
        base: Reg,
        off: i16,
    },

    /// *(size *)(base + off) = src
    Store {
        size: MemSize,
        base: Reg,
        off: i16,
        src: Operand,
    },

    /// 'lock *(size *)(base + off) += src'
    AtomicAdd {
        size: MemSize,
        base: Reg,
        off: i16,
        src: Reg,
    },

    /// Standard helper call (src_reg = 0) 
    Call {
        helper: u32,
    },

    // BPF-to-BPF Call (src_reg = 1)
    // Target is an absolute PC index, resolved during parsing
    CallRel { target: usize },

    PacketLoad {
        size: MemSize,
        mode: PacketLoadMode,
        offset_imm: i32,
        src: Option<Reg>, // Some(src) for IND, None for ABS
    },

    Exit,
}

/// BPF program type - determines context structure and available helpers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProgramKind {
    // Network - XDP context
    Xdp,
    
    // Network - __sk_buff context
    SchedCls,      // TC classifier (section: "classifier", "tc", "tc/ingress", etc.)
    SocketFilter,  // Socket filter (section: "socket")
    
    // Socket operations - specialized contexts
    SockOps,       // struct bpf_sock_ops (section: "sockops")
    SkMsg,         // struct sk_msg_md (section: "sk_msg")
    
    // Cgroup - various contexts
    CgroupSockAddr, // struct bpf_sock_addr (section: "cgroup/bind4", "cgroup/connect4", etc.)
    
    // Tracing - pt_regs context
    Kprobe,
    
    // Unknown or unsupported
    #[default]
    Unknown,
}

/// What matters for verification: the context structure
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContextKind {
    XdpMd,          // struct xdp_md
    SkBuff,         // struct __sk_buff
    SockOps,        // struct bpf_sock_ops
    SkMsgMd,        // struct sk_msg_md
    BpfSockAddr,    // struct bpf_sock_addr
    PtRegs,         // struct pt_regs (kprobe)
    Unknown,
}

impl ProgramKind {
    /// Parse from JSON/section string
    pub fn from_section(s: &str) -> Self {
        let s = s.to_lowercase();
        let s = s.trim();
        
        // XDP
        if s == "xdp" || s.starts_with("xdp/") {
            return ProgramKind::Xdp;
        }
        
        // TC classifier
        if s == "classifier" || s == "tc" 
            || s.starts_with("tc/") 
            || s.starts_with("classifier/")
            || s == "sched_cls" 
        {
            return ProgramKind::SchedCls;
        }
        
        // Socket filter
        if s == "socket" || s.starts_with("socket/") {
            return ProgramKind::SocketFilter;
        }
        
        // Sock ops
        if s == "sockops" || s.starts_with("sockops/") {
            return ProgramKind::SockOps;
        }
        
        // SK_MSG
        if s == "sk_msg" || s.starts_with("sk_msg/") {
            return ProgramKind::SkMsg;
        }
        
        // Cgroup sock addr
        if s.starts_with("cgroup/bind") 
            || s.starts_with("cgroup/connect")
            || s.starts_with("cgroup/sendmsg")
            || s.starts_with("cgroup/recvmsg")
            || s.starts_with("cgroup/getpeername")
            || s.starts_with("cgroup/getsockname")
        {
            return ProgramKind::CgroupSockAddr;
        }
        
        // Kprobe
        if s == "kprobe" || s.starts_with("kprobe/") || s.starts_with("kretprobe/") {
            return ProgramKind::Kprobe;
        }
        
        ProgramKind::Unknown
    }
    
    /// Get the context structure type for this program
    pub fn context_kind(&self) -> ContextKind {
        match self {
            ProgramKind::Xdp => ContextKind::XdpMd,
            ProgramKind::SchedCls | ProgramKind::SocketFilter => ContextKind::SkBuff,
            ProgramKind::SockOps => ContextKind::SockOps,
            ProgramKind::SkMsg => ContextKind::SkMsgMd,
            ProgramKind::CgroupSockAddr => ContextKind::BpfSockAddr,
            ProgramKind::Kprobe => ContextKind::PtRegs,
            ProgramKind::Unknown => ContextKind::Unknown,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Program {
    pub instrs: Vec<Instr>,
}

impl fmt::Display for Instr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Instr::*;
        match *self {
            MovArg0 { dst } =>
                write!(f, "{} = arg0", dst.name()),

            Alu { width, op, dst, src } => {
                let op_str = match op {
                    AluOp::Add  => "+",
                    AluOp::Sub  => "-",
                    AluOp::And  => "&",
                    AluOp::Or   => "|",
                    AluOp::Xor  => "^",
                    AluOp::Mov  => "=",
                    AluOp::Shl  => "<<",
                    AluOp::Shr  => ">>",
                    AluOp::Arsh => "s>>",
                    AluOp::Mul  => "*",
                    AluOp::Mod  => "%",
                    AluOp::Div  => "/",
                    AluOp::Neg  => "-",
                };

                let src_str = match src {
                    Operand::Reg(r) => r.name().to_string(),
                    Operand::Imm(i) => format!("{}", i),
                };

                // dst.name() is "r0", "r1", ...
                let base = dst.name();         // e.g. "r1"
                let idx  = &base[1..];         // e.g. "1"

                // LHS uses width: "w1" or "r1"
                let lhs = match width {
                    Width::W32 => format!("w{}", idx),
                    Width::W64 => format!("r{}", idx),
                };

                // MOV is special: just `w1 = r6` or `r3 = 5`
                if let AluOp::Mov = op {
                    return write!(f, "{} = {}", lhs, src_str);
                }

                // everything else: `w1 = r1 + 3`
                write!(f, "{} = {} {} {}", lhs, dst.name(), op_str, src_str)
            }

            Endian { dst, width: _, op, size } => {
                let kind_str = match (op, size) {
                    (EndianOp::ToBe, 16) => "be16",
                    (EndianOp::ToBe, 32) => "be32",
                    (EndianOp::ToBe, 64) => "be64",
                    (EndianOp::ToLe, 16) => "le16",
                    (EndianOp::ToLe, 32) => "le32",
                    (EndianOp::ToLe, 64) => "le64",
                    _ => "unknown",
                };
                write!(f, "{} = endian_{}", dst.name(), kind_str)
            },

            If { width, left, op, right, target } => {
                let op_str = match op {
                    CmpOp::UGe => ">=u",
                    CmpOp::ULe => "<=u",
                    CmpOp::UGt => ">u",
                    CmpOp::ULt => "<u",
                    CmpOp::Eq  => "==",
                    CmpOp::Ne  => "!=",
                    CmpOp::SLt => "<",
                    CmpOp::SGt => ">",
                    CmpOp::SLe => "<=",
                    CmpOp::SGe => ">=",
                    CmpOp::Test => "&",
                };
                let right_str = match right {
                    Operand::Reg(r) => r.name().to_string(),
                    Operand::Imm(i) => format!("{}", i),
                };
                let width_str = match width {
                    Width::W32 => "w",
                    Width::W64 => "r",
                };
                write!(f, "if {} {} {} {} goto {}", left.name(), op_str, right_str, width_str, target)
            },

            Jmp { target } =>
                write!(f, "goto {}", target),

            Load { size, dst, base, off } => {
                let size_str = match size {
                    MemSize::U8  => "u8",
                    MemSize::U16 => "u16",
                    MemSize::U32 => "u32",
                    MemSize::U64 => "u64",
                };
                write!(f, "{} = *({} *)({} + {})", dst.name(), size_str, base.name(), off)
            },

            Store { size, base, off, src } => {
                let size_str = match size {
                    MemSize::U8  => "u8",
                    MemSize::U16 => "u16",
                    MemSize::U32 => "u32",
                    MemSize::U64 => "u64",
                };
                let src_str = match src {
                    Operand::Reg(r) => r.name().to_string(),
                    Operand::Imm(i) => format!("{}", i),
                };
                write!(f, "*({} *)({} + {}) = {}", size_str, base.name(), off, src_str)
            },

            AtomicAdd { size, base, off, src } => {
                let size_str = match size {
                    MemSize::U8  => "u8",
                    MemSize::U16 => "u16",
                    MemSize::U32 => "u32",
                    MemSize::U64 => "u64",
                };
                write!(f, "lock *({} *)({} + {}) += {}", size_str, base.name(), off, src.name())
            },

            Call { helper } =>
                write!(f, "call {}", helper),

            CallRel { target } =>
                write!(f, "call {}", target),

            PacketLoad { size, mode, offset_imm, src } => {
                write!(f, "ld_abs or ld_ind")
            }

            Exit =>
                write!(f, "exit"),
        }
    }
}
