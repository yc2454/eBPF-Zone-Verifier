// convert_tests.c
// Converts kernel BPF verifier test cases to JSON format.
//
// Usage: gcc convert_tests.c -o convert && ./convert < array_access.c > array_access.json
//
// The test file is included via stdin redirection to avoid hardcoding paths.
// We use a wrapper approach: this file sets up all definitions, then includes
// the test cases.

#include <stdio.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>

// ============================================================================
// BPF definitions from linux/bpf.h and linux/bpf_common.h
// ============================================================================

typedef uint8_t  __u8;
typedef uint16_t __u16;
typedef uint32_t __u32;
typedef uint64_t __u64;
typedef int16_t  __s16;
typedef int32_t  __s32;
typedef int64_t  __s64;

// Instruction classes
#define BPF_LD          0x00
#define BPF_LDX         0x01
#define BPF_ST          0x02
#define BPF_STX         0x03
#define BPF_ALU         0x04
#define BPF_JMP         0x05
#define BPF_JMP32       0x06
#define BPF_ALU64       0x07

// ld/ldx fields
#define BPF_DW          0x18
#define BPF_W           0x00
#define BPF_H           0x08
#define BPF_B           0x10

#define BPF_IMM         0x00
#define BPF_ABS         0x20
#define BPF_IND         0x40
#define BPF_MEM         0x60
#define BPF_ATOMIC      0xc0

// alu/jmp fields
#define BPF_ADD         0x00
#define BPF_SUB         0x10
#define BPF_MUL         0x20
#define BPF_DIV         0x30
#define BPF_OR          0x40
#define BPF_AND         0x50
#define BPF_LSH         0x60
#define BPF_RSH         0x70
#define BPF_NEG         0x80
#define BPF_MOD         0x90
#define BPF_XOR         0xa0
#define BPF_MOV         0xb0
#define BPF_ARSH        0xc0
#define BPF_END         0xd0

#define BPF_JA          0x00
#define BPF_JEQ         0x10
#define BPF_JGT         0x20
#define BPF_JGE         0x30
#define BPF_JSET        0x40
#define BPF_JNE         0x50
#define BPF_JLT         0xa0
#define BPF_JLE         0xb0
#define BPF_JSGT        0x60
#define BPF_JSGE        0x70
#define BPF_JSLT        0xc0
#define BPF_JSLE        0xd0

#define BPF_CALL        0x80
#define BPF_EXIT        0x90

#define BPF_K           0x00
#define BPF_X           0x08

#define BPF_FETCH       0x01

#define BPF_OP(code)    ((code) & 0xf0)
#define BPF_SIZE(code)  ((code) & 0x18)

// BPF instruction structure
struct bpf_insn {
    __u8    code;
    __u8    dst_reg:4;
    __u8    src_reg:4;
    __s16   off;
    __s32   imm;
};

// Pseudo map FD
#define BPF_PSEUDO_MAP_FD       1
#define BPF_PSEUDO_MAP_VALUE    2

// Endian conversion
#define BPF_TO_LE       0x00
#define BPF_TO_BE       0x08

// Limits
#include <limits.h>
#ifndef UINT_MAX
#define UINT_MAX        0xffffffffU
#endif
#ifndef INT_MAX
#define INT_MAX         0x7fffffff
#endif

// Errno values (for retval tests)
#include <errno.h>
#ifndef ENOENT
#define ENOENT          2
#endif
#ifndef EINVAL
#define EINVAL          22
#endif
#ifndef ENOTSUPP
#define ENOTSUPP        524
#endif

// ============================================================================
// BPF instruction macros (from bpf_insn.h)
// ============================================================================

#define BPF_ALU64_REG(OP, DST, SRC) \
    ((struct bpf_insn) { \
        .code  = BPF_ALU64 | BPF_OP(OP) | BPF_X, \
        .dst_reg = DST, .src_reg = SRC, .off = 0, .imm = 0 })

#define BPF_ALU32_REG(OP, DST, SRC) \
    ((struct bpf_insn) { \
        .code  = BPF_ALU | BPF_OP(OP) | BPF_X, \
        .dst_reg = DST, .src_reg = SRC, .off = 0, .imm = 0 })

#define BPF_ALU64_IMM(OP, DST, IMM) \
    ((struct bpf_insn) { \
        .code  = BPF_ALU64 | BPF_OP(OP) | BPF_K, \
        .dst_reg = DST, .src_reg = 0, .off = 0, .imm = IMM })

#define BPF_ALU32_IMM(OP, DST, IMM) \
    ((struct bpf_insn) { \
        .code  = BPF_ALU | BPF_OP(OP) | BPF_K, \
        .dst_reg = DST, .src_reg = 0, .off = 0, .imm = IMM })

#define BPF_MOV64_REG(DST, SRC) \
    ((struct bpf_insn) { \
        .code  = BPF_ALU64 | BPF_MOV | BPF_X, \
        .dst_reg = DST, .src_reg = SRC, .off = 0, .imm = 0 })

#define BPF_MOV32_REG(DST, SRC) \
    ((struct bpf_insn) { \
        .code  = BPF_ALU | BPF_MOV | BPF_X, \
        .dst_reg = DST, .src_reg = SRC, .off = 0, .imm = 0 })

#define BPF_MOV64_IMM(DST, IMM) \
    ((struct bpf_insn) { \
        .code  = BPF_ALU64 | BPF_MOV | BPF_K, \
        .dst_reg = DST, .src_reg = 0, .off = 0, .imm = IMM })

#define BPF_MOV32_IMM(DST, IMM) \
    ((struct bpf_insn) { \
        .code  = BPF_ALU | BPF_MOV | BPF_K, \
        .dst_reg = DST, .src_reg = 0, .off = 0, .imm = IMM })

#define BPF_LD_IMM64_RAW(DST, SRC, IMM) \
    ((struct bpf_insn) { \
        .code  = BPF_LD | BPF_DW | BPF_IMM, \
        .dst_reg = DST, .src_reg = SRC, .off = 0, \
        .imm   = (__u32) (IMM) }), \
    ((struct bpf_insn) { \
        .code  = 0, .dst_reg = 0, .src_reg = 0, .off = 0, \
        .imm   = ((__u64) (IMM)) >> 32 })

#define BPF_LD_IMM64(DST, IMM) \
    BPF_LD_IMM64_RAW(DST, 0, IMM)

#define BPF_LD_MAP_FD(DST, MAP_FD) \
    BPF_LD_IMM64_RAW(DST, BPF_PSEUDO_MAP_FD, MAP_FD)

#define BPF_LD_ABS(SIZE, IMM) \
    ((struct bpf_insn) { \
        .code  = BPF_LD | BPF_SIZE(SIZE) | BPF_ABS, \
        .dst_reg = 0, .src_reg = 0, .off = 0, .imm = IMM })

#define BPF_LD_IND(SIZE, SRC, IMM) \
    ((struct bpf_insn) { \
        .code  = BPF_LD | BPF_SIZE(SIZE) | BPF_IND, \
        .dst_reg = 0, .src_reg = SRC, .off = 0, .imm = IMM })

#define BPF_LDX_MEM(SIZE, DST, SRC, OFF) \
    ((struct bpf_insn) { \
        .code  = BPF_LDX | BPF_SIZE(SIZE) | BPF_MEM, \
        .dst_reg = DST, .src_reg = SRC, .off = OFF, .imm = 0 })

#define BPF_STX_MEM(SIZE, DST, SRC, OFF) \
    ((struct bpf_insn) { \
        .code  = BPF_STX | BPF_SIZE(SIZE) | BPF_MEM, \
        .dst_reg = DST, .src_reg = SRC, .off = OFF, .imm = 0 })

#define BPF_ST_MEM(SIZE, DST, OFF, IMM) \
    ((struct bpf_insn) { \
        .code  = BPF_ST | BPF_SIZE(SIZE) | BPF_MEM, \
        .dst_reg = DST, .src_reg = 0, .off = OFF, .imm = IMM })

#define BPF_ATOMIC_OP(SIZE, OP, DST, SRC, OFF) \
    ((struct bpf_insn) { \
        .code  = BPF_STX | BPF_SIZE(SIZE) | BPF_ATOMIC, \
        .dst_reg = DST, .src_reg = SRC, .off = OFF, .imm = OP })

#define BPF_STX_XADD(SIZE, DST, SRC, OFF) \
    BPF_ATOMIC_OP(SIZE, BPF_ADD, DST, SRC, OFF)

#define BPF_JMP_REG(OP, DST, SRC, OFF) \
    ((struct bpf_insn) { \
        .code  = BPF_JMP | BPF_OP(OP) | BPF_X, \
        .dst_reg = DST, .src_reg = SRC, .off = OFF, .imm = 0 })

#define BPF_JMP32_REG(OP, DST, SRC, OFF) \
    ((struct bpf_insn) { \
        .code  = BPF_JMP32 | BPF_OP(OP) | BPF_X, \
        .dst_reg = DST, .src_reg = SRC, .off = OFF, .imm = 0 })

#define BPF_JMP_IMM(OP, DST, IMM, OFF) \
    ((struct bpf_insn) { \
        .code  = BPF_JMP | BPF_OP(OP) | BPF_K, \
        .dst_reg = DST, .src_reg = 0, .off = OFF, .imm = IMM })

#define BPF_JMP32_IMM(OP, DST, IMM, OFF) \
    ((struct bpf_insn) { \
        .code  = BPF_JMP32 | BPF_OP(OP) | BPF_K, \
        .dst_reg = DST, .src_reg = 0, .off = OFF, .imm = IMM })

#define BPF_JMP_A(OFF) \
    ((struct bpf_insn) { \
        .code  = BPF_JMP | BPF_JA, \
        .dst_reg = 0, .src_reg = 0, .off = OFF, .imm = 0 })

#define BPF_CALL_REL(TGT) \
    ((struct bpf_insn) { \
        .code  = BPF_JMP | BPF_CALL, \
        .dst_reg = 0, .src_reg = 1, .off = 0, .imm = TGT })

#define BPF_RAW_INSN(CODE, DST, SRC, OFF, IMM) \
    ((struct bpf_insn) { \
        .code  = CODE, .dst_reg = DST, .src_reg = SRC, .off = OFF, .imm = IMM })

#define BPF_EXIT_INSN() \
    ((struct bpf_insn) { \
        .code  = BPF_JMP | BPF_EXIT, \
        .dst_reg = 0, .src_reg = 0, .off = 0, .imm = 0 })

#define BPF_ENDIAN(TYPE, DST, LEN) \
    ((struct bpf_insn) { \
        .code  = BPF_ALU | BPF_END | BPF_SRC(TYPE), \
        .dst_reg = DST, .src_reg = 0, .off = 0, .imm = LEN })

#define BPF_SRC(code)   ((code) & 0x08)

// ============================================================================
// Test-specific macros (from test_verifier.c)
// ============================================================================

// Direct packet access setup: R2 = skb->data, R3 = skb->data_end
#define BPF_DIRECT_PKT_R2 \
    BPF_LDX_MEM(BPF_W, BPF_REG_2, BPF_REG_1, offsetof(struct __sk_buff, data)), \
    BPF_LDX_MEM(BPF_W, BPF_REG_3, BPF_REG_1, offsetof(struct __sk_buff, data_end))

// Random number generation with zero extension
#define BPF_RAND_UEXT_R7 \
    BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32), \
    BPF_MOV64_REG(BPF_REG_7, BPF_REG_0)

// Random number generation with sign extension  
#define BPF_RAND_SEXT_R7 \
    BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, BPF_FUNC_get_prandom_u32), \
    BPF_ALU64_IMM(BPF_LSH, BPF_REG_0, 32), \
    BPF_ALU64_IMM(BPF_ARSH, BPF_REG_0, 32), \
    BPF_MOV64_REG(BPF_REG_7, BPF_REG_0)

// Helper call macro
#define BPF_EMIT_CALL(FUNC) \
    BPF_RAW_INSN(BPF_JMP | BPF_CALL, 0, 0, 0, FUNC)

// __sk_buff structure offsets (simplified)
struct __sk_buff {
    __u32 len;
    __u32 pkt_type;
    __u32 mark;
    __u32 queue_mapping;
    __u32 protocol;
    __u32 vlan_present;
    __u32 vlan_tci;
    __u32 vlan_proto;
    __u32 priority;
    __u32 ingress_ifindex;
    __u32 ifindex;
    __u32 tc_index;
    __u32 cb[5];
    __u32 hash;
    __u32 tc_classid;
    __u32 data;           // offset 76
    __u32 data_end;       // offset 80
    __u32 napi_id;
    __u32 family;
    __u32 remote_ip4;
    __u32 local_ip4;
    __u32 remote_ip6[4];
    __u32 local_ip6[4];
    __u32 remote_port;
    __u32 local_port;
    __u32 data_meta;
    // ... more fields
};

// ============================================================================
// Register names
// ============================================================================

#define BPF_REG_0   0
#define BPF_REG_1   1
#define BPF_REG_2   2
#define BPF_REG_3   3
#define BPF_REG_4   4
#define BPF_REG_5   5
#define BPF_REG_6   6
#define BPF_REG_7   7
#define BPF_REG_8   8
#define BPF_REG_9   9
#define BPF_REG_10  10
#define BPF_REG_FP  BPF_REG_10

// ============================================================================
// BPF helper function IDs (common ones)
// ============================================================================

#define BPF_FUNC_unspec                 0
#define BPF_FUNC_map_lookup_elem        1
#define BPF_FUNC_map_update_elem        2
#define BPF_FUNC_map_delete_elem        3
#define BPF_FUNC_probe_read             4
#define BPF_FUNC_ktime_get_ns           5
#define BPF_FUNC_trace_printk           6
#define BPF_FUNC_get_prandom_u32        7
#define BPF_FUNC_get_smp_processor_id   8
#define BPF_FUNC_skb_store_bytes        9
#define BPF_FUNC_l3_csum_replace        10
#define BPF_FUNC_l4_csum_replace        11
#define BPF_FUNC_tail_call              12
#define BPF_FUNC_clone_redirect         13
#define BPF_FUNC_get_current_pid_tgid   14
#define BPF_FUNC_get_current_uid_gid    15
#define BPF_FUNC_get_current_comm       16
#define BPF_FUNC_get_cgroup_classid     17
#define BPF_FUNC_skb_vlan_push          18
#define BPF_FUNC_skb_vlan_pop           19
#define BPF_FUNC_skb_get_tunnel_key     20
#define BPF_FUNC_skb_set_tunnel_key     21
#define BPF_FUNC_perf_event_read        22
#define BPF_FUNC_redirect               23
#define BPF_FUNC_get_route_realm        24
#define BPF_FUNC_perf_event_output      25
#define BPF_FUNC_skb_load_bytes         26
#define BPF_FUNC_get_stackid            27
#define BPF_FUNC_csum_diff              28
#define BPF_FUNC_skb_get_tunnel_opt     29
#define BPF_FUNC_skb_set_tunnel_opt     30
#define BPF_FUNC_skb_change_proto       31
#define BPF_FUNC_skb_change_type        32
#define BPF_FUNC_skb_under_cgroup       33
#define BPF_FUNC_get_hash_recalc        34
#define BPF_FUNC_get_current_task       35
#define BPF_FUNC_probe_write_user       36
#define BPF_FUNC_current_task_under_cgroup 37
#define BPF_FUNC_skb_change_tail        38
#define BPF_FUNC_skb_pull_data          39
#define BPF_FUNC_csum_update            40
#define BPF_FUNC_set_hash_invalid       41
#define BPF_FUNC_get_numa_node_id       42
#define BPF_FUNC_skb_change_head        43
#define BPF_FUNC_xdp_adjust_head        44
#define BPF_FUNC_probe_read_str         45
#define BPF_FUNC_get_socket_cookie      46
#define BPF_FUNC_get_socket_uid         47
#define BPF_FUNC_set_hash               48
#define BPF_FUNC_setsockopt             49
#define BPF_FUNC_skb_adjust_room        50
#define BPF_FUNC_redirect_map           51
#define BPF_FUNC_sk_redirect_map        52
#define BPF_FUNC_sock_map_update        53
#define BPF_FUNC_xdp_adjust_meta        54
#define BPF_FUNC_perf_event_read_value  55
#define BPF_FUNC_perf_prog_read_value   56
#define BPF_FUNC_getsockopt             57
#define BPF_FUNC_override_return        58
#define BPF_FUNC_sock_ops_cb_flags_set  59
#define BPF_FUNC_msg_redirect_map       60
#define BPF_FUNC_msg_apply_bytes        61
#define BPF_FUNC_msg_cork_bytes         62
#define BPF_FUNC_msg_pull_data          63
#define BPF_FUNC_bind                   64
#define BPF_FUNC_xdp_adjust_tail        65
#define BPF_FUNC_skb_get_xfrm_state     66
#define BPF_FUNC_get_stack              67
#define BPF_FUNC_skb_load_bytes_relative 68
#define BPF_FUNC_fib_lookup             69
#define BPF_FUNC_sock_hash_update       70
#define BPF_FUNC_msg_redirect_hash      71
#define BPF_FUNC_sk_redirect_hash       72
#define BPF_FUNC_lwt_push_encap         73
#define BPF_FUNC_lwt_seg6_store_bytes   74
#define BPF_FUNC_lwt_seg6_adjust_srh    75
#define BPF_FUNC_lwt_seg6_action        76
#define BPF_FUNC_rc_repeat              77
#define BPF_FUNC_rc_keydown             78
#define BPF_FUNC_skb_cgroup_id          79
#define BPF_FUNC_get_current_cgroup_id  80
#define BPF_FUNC_get_local_storage      81
#define BPF_FUNC_sk_select_reuseport    82
#define BPF_FUNC_skb_ancestor_cgroup_id 83
#define BPF_FUNC_sk_lookup_tcp          84
#define BPF_FUNC_sk_lookup_udp          85
#define BPF_FUNC_sk_release             86
#define BPF_FUNC_map_push_elem          87
#define BPF_FUNC_map_pop_elem           88
#define BPF_FUNC_map_peek_elem          89
#define BPF_FUNC_msg_push_data          90
#define BPF_FUNC_msg_pop_data           91
#define BPF_FUNC_rc_pointer_rel         92
#define BPF_FUNC_ringbuf_output         130
#define BPF_FUNC_ringbuf_reserve        131
#define BPF_FUNC_ringbuf_submit         132
#define BPF_FUNC_ringbuf_discard        133
#define BPF_FUNC_ringbuf_query          134
#define BPF_FUNC_get_netns_cookie       97
#define BPF_FUNC_get_current_ancestor_cgroup_id 98
#define BPF_FUNC_check_mtu              99
#define BPF_FUNC_for_each_map_elem      164
#define BPF_FUNC_snprintf               165

// ============================================================================
// Program types
// ============================================================================

enum bpf_prog_type {
    BPF_PROG_TYPE_UNSPEC,
    BPF_PROG_TYPE_SOCKET_FILTER,
    BPF_PROG_TYPE_KPROBE,
    BPF_PROG_TYPE_SCHED_CLS,
    BPF_PROG_TYPE_SCHED_ACT,
    BPF_PROG_TYPE_TRACEPOINT,
    BPF_PROG_TYPE_XDP,
    BPF_PROG_TYPE_PERF_EVENT,
    BPF_PROG_TYPE_CGROUP_SKB,
    BPF_PROG_TYPE_CGROUP_SOCK,
    BPF_PROG_TYPE_LWT_IN,
    BPF_PROG_TYPE_LWT_OUT,
    BPF_PROG_TYPE_LWT_XMIT,
    BPF_PROG_TYPE_SOCK_OPS,
    BPF_PROG_TYPE_SK_SKB,
    BPF_PROG_TYPE_CGROUP_DEVICE,
    BPF_PROG_TYPE_SK_MSG,
    BPF_PROG_TYPE_RAW_TRACEPOINT,
    BPF_PROG_TYPE_CGROUP_SOCK_ADDR,
    BPF_PROG_TYPE_LWT_SEG6LOCAL,
    BPF_PROG_TYPE_LIRC_MODE2,
    BPF_PROG_TYPE_SK_REUSEPORT,
    BPF_PROG_TYPE_FLOW_DISSECTOR,
    BPF_PROG_TYPE_CGROUP_SYSCTL,
    BPF_PROG_TYPE_RAW_TRACEPOINT_WRITABLE,
    BPF_PROG_TYPE_CGROUP_SOCKOPT,
    BPF_PROG_TYPE_TRACING,
    BPF_PROG_TYPE_STRUCT_OPS,
    BPF_PROG_TYPE_EXT,
    BPF_PROG_TYPE_LSM,
    BPF_PROG_TYPE_SK_LOOKUP,
    BPF_PROG_TYPE_SYSCALL,
};

// Attach types
enum bpf_attach_type {
    BPF_CGROUP_INET_INGRESS,
    BPF_CGROUP_INET_EGRESS,
    BPF_CGROUP_INET_SOCK_CREATE,
    BPF_CGROUP_SOCK_OPS,
    BPF_SK_SKB_STREAM_PARSER,
    BPF_SK_SKB_STREAM_VERDICT,
    BPF_CGROUP_DEVICE,
    BPF_SK_MSG_VERDICT,
    BPF_CGROUP_INET4_BIND,
    BPF_CGROUP_INET6_BIND,
    BPF_CGROUP_INET4_CONNECT,
    BPF_CGROUP_INET6_CONNECT,
    BPF_CGROUP_INET4_POST_BIND,
    BPF_CGROUP_INET6_POST_BIND,
    BPF_CGROUP_UDP4_SENDMSG,
    BPF_CGROUP_UDP6_SENDMSG,
    BPF_LIRC_MODE2,
    BPF_FLOW_DISSECTOR,
    BPF_CGROUP_SYSCTL,
    BPF_CGROUP_UDP4_RECVMSG,
    BPF_CGROUP_UDP6_RECVMSG,
    BPF_CGROUP_GETSOCKOPT,
    BPF_CGROUP_SETSOCKOPT,
    BPF_TRACE_RAW_TP,
    BPF_TRACE_FENTRY,
    BPF_TRACE_FEXIT,
    BPF_MODIFY_RETURN,
    BPF_LSM_MAC,
    BPF_TRACE_ITER,
    BPF_CGROUP_INET4_GETPEERNAME,
    BPF_CGROUP_INET6_GETPEERNAME,
    BPF_CGROUP_INET4_GETSOCKNAME,
    BPF_CGROUP_INET6_GETSOCKNAME,
    BPF_XDP_DEVMAP,
    BPF_CGROUP_INET_SOCK_RELEASE,
    BPF_XDP_CPUMAP,
    BPF_SK_LOOKUP,
    BPF_XDP,
    BPF_SK_SKB_VERDICT,
    BPF_SK_REUSEPORT_SELECT,
    BPF_SK_REUSEPORT_SELECT_OR_MIGRATE,
    BPF_PERF_EVENT,
    BPF_TRACE_KPROBE_MULTI,
    BPF_LSM_CGROUP,
    __MAX_BPF_ATTACH_TYPE
};

// ============================================================================
// Test framework definitions
// ============================================================================

#define MAX_INSNS       4096
#define MAX_FIXUPS      8
#define MAX_ENTRIES     11

#define F_NEEDS_EFFICIENT_UNALIGNED_ACCESS  (1 << 0)
#define F_LOAD_WITH_STRICT_ALIGNMENT        (1 << 1)

// Result codes
enum {
    UNDEF,
    ACCEPT,
    REJECT,
    VERBOSE_ACCEPT,
};

// Struct referenced by offsetof() in tests
struct test_val {
    unsigned int index;
    int foo[MAX_ENTRIES];
};

struct other_val {
    long long foo;
    long long bar;
};

// Kfunc pair (not used in basic tests but needed for struct definition)
struct kfunc_btf_id_pair {
    const char *kfunc;
    int insn_idx;
};

// The test case structure
#define MAX_TEST_RUNS 8

struct test_result {
    uint32_t retval;
    union {
        __u8 data[64];
        __u64 data64[8];
    };
};

struct bpf_test {
    const char *descr;
    struct bpf_insn insns[MAX_INSNS];
    struct bpf_insn *fill_insns;
    int fixup_map_hash_8b[MAX_FIXUPS];
    int fixup_map_hash_48b[MAX_FIXUPS];
    int fixup_map_hash_16b[MAX_FIXUPS];
    int fixup_map_array_48b[MAX_FIXUPS];
    int fixup_map_sockmap[MAX_FIXUPS];
    int fixup_map_sockhash[MAX_FIXUPS];
    int fixup_map_xskmap[MAX_FIXUPS];
    int fixup_map_stacktrace[MAX_FIXUPS];
    int fixup_prog1[MAX_FIXUPS];
    int fixup_prog2[MAX_FIXUPS];
    int fixup_map_in_map[MAX_FIXUPS];
    int fixup_cgroup_storage[MAX_FIXUPS];
    int fixup_percpu_cgroup_storage[MAX_FIXUPS];
    int fixup_map_spin_lock[MAX_FIXUPS];
    int fixup_map_array_ro[MAX_FIXUPS];
    int fixup_map_array_wo[MAX_FIXUPS];
    int fixup_map_array_small[MAX_FIXUPS];
    int fixup_sk_storage_map[MAX_FIXUPS];
    int fixup_map_event_output[MAX_FIXUPS];
    int fixup_map_reuseport_array[MAX_FIXUPS];
    int fixup_map_ringbuf[MAX_FIXUPS];
    struct kfunc_btf_id_pair fixup_kfunc_btf_id[MAX_FIXUPS];
    const char *errstr;
    const char *errstr_unpriv;
    uint32_t insn_processed;
    int prog_len;
    int result;
    int result_unpriv;
    enum bpf_prog_type prog_type;
    enum bpf_attach_type expected_attach_type;
    uint8_t flags;
    void (*fill_helper)(struct bpf_test *self);
    int runs;
    struct test_result retvals[MAX_TEST_RUNS];
    uint32_t retval;
    uint32_t retval_unpriv;
};

// ============================================================================
// Test cases - included from the test file
// ============================================================================

// The test file is specified via -D TEST_FILE="filename" at compile time
// or defaults to testcases.h
#ifndef TEST_FILE
#define TEST_FILE "testcases.h"
#endif

// The test file should define tests as: { "name", .insns = {...}, ... },
static struct bpf_test tests[] = {
#include TEST_FILE
};

// ============================================================================
// JSON output helpers
// ============================================================================

void print_json_string(const char *s) {
    if (!s) {
        printf("null");
        return;
    }
    printf("\"");
    for (; *s; s++) {
        switch (*s) {
            case '"':  printf("\\\""); break;
            case '\\': printf("\\\\"); break;
            case '\n': printf("\\n"); break;
            case '\r': printf("\\r"); break;
            case '\t': printf("\\t"); break;
            default:
                if ((unsigned char)*s < 32) {
                    printf("\\u%04x", (unsigned char)*s);
                } else {
                    putchar(*s);
                }
        }
    }
    printf("\"");
}

int has_fixup(int *arr) {
    for (int i = 0; i < MAX_FIXUPS; i++) {
        if (arr[i]) return 1;
    }
    return 0;
}

void print_fixup(const char *name, int *arr, int *first) {
    if (!has_fixup(arr)) return;
    
    if (!*first) printf(",");
    *first = 0;
    printf("\n    \"%s\": [", name);
    int first_elem = 1;
    for (int i = 0; i < MAX_FIXUPS && arr[i]; i++) {
        if (!first_elem) printf(", ");
        first_elem = 0;
        printf("%d", arr[i]);
    }
    printf("]");
}

const char *result_str(int r) {
    switch (r) {
        case ACCEPT: return "ACCEPT";
        case REJECT: return "REJECT";
        case VERBOSE_ACCEPT: return "VERBOSE_ACCEPT";
        default: return "UNDEF";
    }
}

// Count instructions, handling LDDW (2-insn sequences)
int count_insns(struct bpf_insn *insns) {
    for (int i = 0; i < MAX_INSNS; i++) {
        if (insns[i].code == 0) {
            // Check if this is LDDW continuation
            if (i > 0 && (insns[i-1].code == (BPF_LD | BPF_DW | BPF_IMM))) {
                continue;  // This is the second part of LDDW
            }
            return i;
        }
    }
    return MAX_INSNS;
}

// ============================================================================
// Main
// ============================================================================

int main() {
    int n = sizeof(tests) / sizeof(tests[0]);
    
    printf("[\n");
    for (int i = 0; i < n; i++) {
        struct bpf_test *t = &tests[i];
        
        // Skip tests that use fill_helper (dynamically generated)
        if (t->fill_helper || t->fill_insns) {
            fprintf(stderr, "Skipping test '%s': uses fill_helper\n", t->descr);
            continue;
        }
        
        int insn_cnt = count_insns(t->insns);
        
        printf("  {\n");
        printf("    \"name\": ");
        print_json_string(t->descr);
        
        int first = 0;  // After name, we've printed something
        
        printf(",\n    \"result\": \"%s\"", result_str(t->result));
        
        if (t->result_unpriv && t->result_unpriv != UNDEF) {
            printf(",\n    \"result_unpriv\": \"%s\"", result_str(t->result_unpriv));
        }
        
        if (t->errstr) {
            printf(",\n    \"errstr\": ");
            print_json_string(t->errstr);
        }
        
        if (t->errstr_unpriv) {
            printf(",\n    \"errstr_unpriv\": ");
            print_json_string(t->errstr_unpriv);
        }
        
        if (t->prog_type) {
            printf(",\n    \"prog_type\": %d", t->prog_type);
        }
        
        if (t->expected_attach_type) {
            printf(",\n    \"expected_attach_type\": %d", t->expected_attach_type);
        }
        
        if (t->flags) {
            printf(",\n    \"flags\": %d", t->flags);
        }
        
        // Print fixups
        first = 1;
        int printed_fixup_header = 0;
        
        #define PRINT_FIXUP(name) \
            if (has_fixup(t->name)) { \
                if (!printed_fixup_header) { \
                    printf(",\n    \"fixups\": {"); \
                    printed_fixup_header = 1; \
                } \
                print_fixup(#name, t->name, &first); \
            }
        
        PRINT_FIXUP(fixup_map_hash_8b);
        PRINT_FIXUP(fixup_map_hash_48b);
        PRINT_FIXUP(fixup_map_hash_16b);
        PRINT_FIXUP(fixup_map_array_48b);
        PRINT_FIXUP(fixup_map_sockmap);
        PRINT_FIXUP(fixup_map_sockhash);
        PRINT_FIXUP(fixup_map_xskmap);
        PRINT_FIXUP(fixup_map_stacktrace);
        PRINT_FIXUP(fixup_prog1);
        PRINT_FIXUP(fixup_prog2);
        PRINT_FIXUP(fixup_map_in_map);
        PRINT_FIXUP(fixup_cgroup_storage);
        PRINT_FIXUP(fixup_percpu_cgroup_storage);
        PRINT_FIXUP(fixup_map_spin_lock);
        PRINT_FIXUP(fixup_map_array_ro);
        PRINT_FIXUP(fixup_map_array_wo);
        PRINT_FIXUP(fixup_map_array_small);
        PRINT_FIXUP(fixup_sk_storage_map);
        PRINT_FIXUP(fixup_map_event_output);
        PRINT_FIXUP(fixup_map_reuseport_array);
        PRINT_FIXUP(fixup_map_ringbuf);
        
        if (printed_fixup_header) {
            printf("\n    }");
        }
        
        // Print instructions
        printf(",\n    \"insns\": [");
        for (int j = 0; j < insn_cnt; j++) {
            struct bpf_insn *in = &t->insns[j];
            if (j > 0) printf(",");
            printf("\n      {\"code\": %d, \"dst\": %d, \"src\": %d, \"off\": %d, \"imm\": %d}",
                   in->code, in->dst_reg, in->src_reg, in->off, in->imm);
        }
        printf("\n    ]");
        
        printf("\n  }");
        
        // Comma between tests (but not after the last one)
        if (i < n - 1) printf(",");
        printf("\n");
    }
    printf("]\n");
    
    return 0;
}