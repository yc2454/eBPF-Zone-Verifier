// src/analysis/transfer/call/helper_protos.rs
//
// Helper-function proto table (`get_helper_proto`) and small per-helper
// utility predicates (`is_fastcall_helper`, etc.).

use crate::common::constants;
use crate::parsing::btf::SpecialFieldKind;
use super::kfunc_protos::get_kfunc_proto;
use super::signatures::{ArgKind::*, CallFlags, CallProto, RetKind, SideEffect};
use super::signatures::pairs;

pub fn get_helper_proto(helper: u32) -> Option<CallProto> {
    Some(match helper {
        // ---- Map operations ----
        constants::BPF_MAP_LOOKUP_ELEM => CallProto::with_args([
            ConstMapPtr, // R1: map
            PtrToMapKey, // R2: key
            DontCare,
            DontCare,
            DontCare,
        ]),

        // bpf_map_lookup_percpu_elem(map, key, cpu) — same shape as
        // map_lookup_elem with an extra cpu scalar arg. Returns a
        // pointer to the per-cpu copy of the value, or NULL.
        // R0 typing handled by `update_call_types` (PtrToMapValueOrNull
        // keyed off R1's map).
        constants::BPF_MAP_LOOKUP_PERCPU_ELEM => CallProto::with_args([
            ConstMapPtr, // R1: map
            PtrToMapKey, // R2: key
            Anything,    // R3: cpu
            DontCare,
            DontCare,
        ]),

        constants::BPF_MAP_UPDATE_ELEM => CallProto::with_args([
            ConstMapPtr,   // R1: map
            PtrToMapKey,   // R2: key
            PtrToMapValue, // R3: value
            Anything,      // R4: flags
            DontCare,
        ]),

        constants::BPF_MAP_DELETE_ELEM => CallProto::with_args([
            ConstMapPtr, // R1: map
            PtrToMapKey, // R2: key
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_GET_LOCAL_STORAGE => CallProto::with_args([
            ConstMapPtr, // R1: map
            Anything,    // R2: index
            DontCare,
            DontCare,
            DontCare,
        ]),

        // ---- Memory helpers ----
        constants::BPF_GET_STACK => CallProto::with_args([
            PtrToCtx,
            PtrToUninitMem,
            ConstSizeOrZero,
            Anything,
            DontCare,
        ])
        .mem_size_pairs(&pairs::GET_STACK),

        // ---- Tail call ----
        constants::BPF_TAIL_CALL => CallProto::with_args([
            PtrToCtx,    // R1: ctx
            ConstMapPtr, // R2: prog_array_map
            Anything,    // R3: index
            DontCare,
            DontCare,
        ]),

        // ---- Socket/context helpers ----
        constants::BPF_GET_SOCKET_COOKIE => CallProto::with_args([
            // Kernel registers 4 per-prog-type protos for this helper
            // (skb-ctx / sock / sock_addr-ctx / sock_common-btf-id).
            // We use PtrToCtx for the validator entry point; the
            // sock-shaped variants are admitted via a per-helper
            // relaxation in `validate_ptr_to_ctx` (keyed on
            // `ctx.helper == BPF_GET_SOCKET_COOKIE`) so that ctx-offset
            // validation still fires for skb-ctx programs.
            PtrToCtx, // R1: ctx / sock / btf_id sock_common
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_GET_NETNS_COOKIE => CallProto::with_args([
            PtrToCtxOrNull, // R1: ctx (nullable — kernel accepts NULL)
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_CSUM_UPDATE => CallProto::with_args([
            PtrToCtx, // R1: skb
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_CSUM_DIFF => CallProto::with_args([
            PtrToMemOrNull,  // R1: from
            ConstSizeOrZero, // R2: from_size
            PtrToMemOrNull,  // R3: to
            ConstSizeOrZero, // R4: to_size
            Anything,        // R5: seed
        ])
        .mem_size_pairs(&pairs::CSUM_DIFF),

        constants::BPF_SKB_ECN_SET_CE => CallProto::with_args([
            PtrToCtxOrNull, // R1: skb (can be NULL)
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_GET_HASH_RECALC => CallProto::with_args([
            PtrToCtx, // R1: ctx
            DontCare, DontCare, DontCare, DontCare,
        ]),

        // ---- SKB data access ----
        constants::BPF_SKB_LOAD_BYTES => CallProto::with_args([
            PtrToCtx,       // R1: skb
            Anything,       // R2: offset
            PtrToUninitMem, // R3: to (destination buffer)
            ConstSize,      // R4: len
            DontCare,
        ])
        .mem_size_pairs(&pairs::SKB_LOAD_BYTES),

        constants::BPF_SKB_VLAN_PUSH => CallProto::with_args([
            PtrToCtx, // R1: skb
            Anything, // R2: vlan_proto
            Anything, // R3: vlan_tci
            DontCare, DontCare,
        ]),

        constants::BPF_SKB_GET_TUNNEL_KEY => CallProto::with_args([
            PtrToCtx,       // R1: skb
            PtrToUninitMem, // R2: key (buffer to store key)
            ConstSize,      // R3: size
            Anything,       // R4: flags
            DontCare,
        ])
        .mem_size_pairs(&pairs::SKB_GET_TUNNEL_KEY),

        constants::BPF_SKB_SET_TUNNEL_KEY => CallProto::with_args([
            PtrToCtx,  // R1: skb
            PtrToMem,  // R2: key
            ConstSize, // R3: size
            Anything,  // R4: flags
            DontCare,
        ])
        .mem_size_pairs(&pairs::SKB_SET_TUNNEL_KEY),

        constants::BPF_SKB_VLAN_POP => CallProto::with_args([
            PtrToCtx, // R1: skb
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_SKB_STORE_BYTES => CallProto::with_args([
            PtrToCtx,  // R1: skb
            Anything,  // R2: offset
            PtrToMem,  // R3: from (source buffer)
            ConstSize, // R4: len
            DontCare,
        ])
        .mem_size_pairs(&pairs::SKB_STORE_BYTES),

        // ---- Redirect ----
        constants::BPF_REDIRECT => CallProto::with_args([
            Anything, // R1: ifindex
            Anything, // R2: flags
            DontCare, DontCare, DontCare,
        ]),

        // ---- XDP helpers ----
        constants::BPF_XDP_ADJUST_HEAD
        | constants::BPF_XDP_ADJUST_TAIL
        | constants::BPF_XDP_ADJUST_META => CallProto::with_args([
            PtrToCtx, // R1: xdp_md
            Anything, // R2: delta
            DontCare, DontCare, DontCare,
        ]),

        // ---- Tail modification ----
        constants::BPF_SKB_CHANGE_TAIL => CallProto::with_args([
            PtrToCtx, // R1: skb
            Anything, // R2: len
            Anything, // R3: flags
            DontCare, DontCare,
        ]),

        // ---- Socket lookup ----
        constants::BPF_SKC_LOOKUP_TCP => CallProto::with_args([
            PtrToCtx, // R1: ctx
            PtrToMem, // R2: tuple
            Anything, // R3: tuple_size
            DontCare, DontCare,
        ])
        .ret(RetKind::PtrToSockCommon)
        .flags(CallFlags::ACQUIRE.union(CallFlags::RET_NULL))
        .mem_size_pairs(&pairs::SK_LOOKUP_TCP),

        constants::BPF_SK_LOOKUP_TCP => CallProto::with_args([
            PtrToCtx,  // R1: ctx
            PtrToMem,  // R2: tuple
            ConstSize, // R3: tuple_size
            Anything,  // R4: netns
            Anything,  // R5: flags
        ])
        .ret(RetKind::PtrToSocket)
        .flags(CallFlags::ACQUIRE.union(CallFlags::RET_NULL))
        .mem_size_pairs(&pairs::SK_LOOKUP_TCP),

        constants::BPF_SK_LOOKUP_UDP => CallProto::with_args([
            PtrToCtx,  // R1: ctx
            PtrToMem,  // R2: tuple
            ConstSize, // R3: tuple_size
            Anything,  // R4: netns
            Anything,  // R5: flags
        ])
        .ret(RetKind::PtrToSocket)
        .flags(CallFlags::ACQUIRE.union(CallFlags::RET_NULL))
        .mem_size_pairs(&pairs::SK_LOOKUP_UDP),

        constants::BPF_SK_RELEASE => CallProto::with_args([
            PtrToSocket, // R1: socket
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        constants::BPF_SKC_TO_UDP6_SOCK => CallProto::with_args([
            PtrToSocket, // R1: socket
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_SK_FULLSOCK => CallProto::with_args([
            PtrToSockCommon, // R1: sock_common
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_TCP_SOCK => {
            CallProto::with_args([PtrToSockCommon, DontCare, DontCare, DontCare, DontCare])
        }

        // ---- Socket storage helpers ----
        constants::BPF_SK_STORAGE_GET => CallProto::with_args([
            ConstMapPtr,
            PtrToBTFIdSockCommon,
            PtrToMapValueOrNull,
            Anything,
            DontCare,
        ]),

        constants::BPF_GET_SOCKOPT => {
            // R1 is `bpf_socket` (kernel UAPI). The kernel verifier accepts
            // it as PtrToCtx in cgroup_sock_addr/sock_ops contexts AND as
            // a trusted PtrToBtfId{sock} in struct_ops contexts (where the
            // BPF_PROG-wrapped struct_ops method has unpacked the sock arg
            // out of the ctx array). Modeling as `Anything` matches the
            // multi-shape acceptance and lets struct_ops methods like
            // bpf_dctcp_init pass; the size pair on (R4, R5) still gates
            // the actual write region.
            CallProto::with_args([Anything, Anything, Anything, PtrToUninitMem, ConstSize])
                .mem_size_pairs(&pairs::GET_SOCKOPT)
        }

        // ---- FIB lookup ----
        constants::BPF_FIB_LOOKUP => CallProto::with_args([
            PtrToCtx, // R1: ctx
            PtrToMem, // R2: params (bpf_fib_lookup struct)
            Anything, // R3: plen
            Anything, // R4: flags
            DontCare,
        ]),

        constants::BPF_PROBE_READ
        | constants::BPF_PROBE_READ_STR
        | constants::BPF_PROBE_READ_USER => CallProto::with_args([
            PtrToUninitMem,  // R1: dst
            ConstSizeOrZero, // R2: size
            Anything,        // R3: unsafe_ptr (user address)
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::PROBE_READ),

        constants::BPF_PROBE_READ_KERNEL => CallProto::with_args([
            PtrToUninitMem,  // R1: dst (output buffer)
            ConstSizeOrZero, // R2: size
            Anything,        // R3: unsafe_ptr (kernel address, not validated)
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::PROBE_READ),

        constants::BPF_PERF_EVENT_READ_VALUE => CallProto::with_args([
            ConstMapPtr,     // R1: map
            Anything,        // R2: flags
            PtrToUninitMem,  // R3: buf
            ConstSizeOrZero, // R4: buf_size
            DontCare,
        ])
        .mem_size_pairs(&pairs::PERF_EVENT_READ_VALUE),

        constants::BPF_PERF_PROG_READ_VALUE => CallProto::with_args([
            PtrToCtx,        // R1: ctx
            PtrToUninitMem,  // R2: buf
            ConstSizeOrZero, // R3: buf_size
            DontCare,        // R4: flags (not verified here)
            DontCare,
        ])
        .mem_size_pairs(&pairs::PERF_PROG_READ_VALUE),

        // ---- Spin lock ----
        // void bpf_spin_lock(struct bpf_spin_lock *lock)
        // void bpf_spin_unlock(struct bpf_spin_lock *lock)
        // R1 must be a PtrToMapValue aimed at a `bpf_spin_lock` field
        // recorded in the map's value-type BTF. The shape check rides
        // `MapValueSpecial { SpinLock }`; the lock-state mutation
        // (`active_lock` acquire / release) is driven by the
        // `SPIN_LOCK_{ACQUIRE,RELEASE}` flags in the pre-call hook.
        constants::BPF_SPIN_LOCK => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::SpinLock },
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::SPIN_LOCK_ACQUIRE),

        constants::BPF_SPIN_UNLOCK => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::SpinLock },
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::SPIN_LOCK_RELEASE),

        // ---- RCU read-side critical section ----
        // void bpf_rcu_read_lock(void)
        // void bpf_rcu_read_unlock(void)
        constants::BPF_RCU_READ_LOCK => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::RCU_READ_LOCK),

        constants::BPF_RCU_READ_UNLOCK => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::RCU_READ_UNLOCK),

        // ---- Timers ----
        // long bpf_timer_init(struct bpf_timer *timer, struct bpf_map *map, u64 flags)
        constants::BPF_TIMER_INIT => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::Timer }, // R1: &timer field
            ConstMapPtr,                                       // R2: map the cb will operate on
            Anything,                                          // R3: flags
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // long bpf_timer_set_callback(struct bpf_timer *timer,
        //                             void *callback_fn)
        // Routed through is_callback_helper → transfer_callback_helper for
        // the cb-frame fork; this proto just covers the arg validation
        // (timer field + PtrToCallback) and post-call R0 typing for the
        // skip successor (the cb-frame branch updates R0 separately).
        constants::BPF_TIMER_SET_CALLBACK => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::Timer }, // R1: &timer field
            PtrToCallback,                                     // R2: callback subprog
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // long bpf_timer_start(struct bpf_timer *timer, u64 nsecs, u64 flags)
        constants::BPF_TIMER_START => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::Timer }, // R1: &timer field
            Anything,                                          // R2: nsecs
            Anything,                                          // R3: flags
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // long bpf_timer_cancel(struct bpf_timer *timer)
        constants::BPF_TIMER_CANCEL => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::Timer }, // R1: &timer field
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- Ringbuf helpers ----
        constants::BPF_RINGBUF_OUTPUT => CallProto::with_args([
            ConstMapPtr,     // R1: ringbuf map
            PtrToMem,        // R2: data to copy (must be initialized)
            ConstSizeOrZero, // R3: size
            Anything,        // R4: flags
            DontCare,
        ]),

        constants::BPF_RINGBUF_RESERVE => CallProto::with_args([
            ConstMapPtr,
            ConstAllocSizeOrZero,
            Anything,
            DontCare,
            DontCare,
        ]),

        constants::BPF_RINGBUF_SUBMIT => {
            CallProto::with_args([PtrToAllocMem, Anything, DontCare, DontCare, DontCare])
        }

        // bpf_user_ringbuf_drain(map, callback, ctx, flags)
        // Drains a user-space-written ringbuf, invoking `callback`
        // for each sample. Routed through `is_callback_helper` →
        // `transfer_callback_helper` so the callback subprog gets a
        // pushed frame on the enter-callback successor; the callback
        // signature is `(struct bpf_dynptr *dynptr, void *ctx) -> long`,
        // but per the existing callback convention we leave R1/R2 as
        // NotInit in the callee frame — programs that dereference
        // `ctx` (R2) without typing reject, which is the right outcome
        // for the lone existing test (`unsafe_ringbuf_drain`).
        constants::BPF_USER_RINGBUF_DRAIN => CallProto::with_args([
            ConstMapPtrOfType(crate::common::constants::BPF_MAP_TYPE_USER_RINGBUF),
            PtrToCallback,
            Anything,
            Anything,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- Information helpers ----
        constants::BPF_KTIME_GET_NS => {
            CallProto::with_args([DontCare, DontCare, DontCare, DontCare, DontCare])
        }
        constants::BPF_KTIME_GET_COARSE_NS => {
            CallProto::with_args([DontCare, DontCare, DontCare, DontCare, DontCare])
        }

        // ---- Process info helpers ----

        // bpf_get_current_pid_tgid() -> u64 (no args). Real kernel
        // helper (BPF_FUNC id 14) that was previously unregistered, so
        // validate_helper_args skipped it. Registering it is the
        // faithful model (no pointer args to validate, scalar return)
        // and is the prerequisite for the unknown-helper-REJECT
        // backstop: test_get_stack_rawtp (a real bundle-producer) calls
        // this helper, so without a proto the backstop would
        // false-reject it.
        constants::BPF_GET_CURRENT_PID_TGID => {
            CallProto::with_args([DontCare, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_GET_TASK_STACK => CallProto::with_args([
            PtrToBtfId,
            PtrToUninitMem,
            ConstSizeOrZero,
            Anything,
            DontCare,
        ])
        .mem_size_pairs(&pairs::GET_TASK_STACK),

        // bpf_get_branch_snapshot(void *entries, u32 size, u64 flags) -> long
        // Writes ≤ size bytes; R0 ∈ [-MAX_ERRNO, R2_max]. The size-arg
        // bound on R0 is what unblocks `total_entries / 24 ≤ ENTRY_CNT`
        // for static reasoning over `entries[i]` arrays — without it,
        // total_entries is unbounded and the `i < total_entries` exit
        // branch can't refine i's bound.
        constants::BPF_GET_BRANCH_SNAPSHOT => CallProto::with_args([
            PtrToUninitMem,
            ConstSize,
            Anything,
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::GET_BRANCH_SNAPSHOT)
        .ret(RetKind::Scalar),

        // ---- Sockmap operations ----
        constants::BPF_SOCK_MAP_UPDATE => CallProto::with_args([
            PtrToCtx,    // R1: bpf_sock_ops context (SockOps only)
            ConstMapPtr, // R2: sockmap
            PtrToMapKey, // R3: key
            Anything,    // R4: flags
            DontCare,
        ]),

        // ---- Miscellaneous ----
        constants::BPF_GET_PRANDOM_U32 => {
            CallProto::with_args([DontCare, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_TRACE_PRINTK => CallProto::with_args([
            PtrToMem,  // R1: fmt string
            ConstSize, // R2: fmt_size (MUST BE > 0)
            Anything,  // R3: arg1
            Anything,  // R4: arg2
            Anything,  // R5: arg3
        ]),

        constants::BPF_STRTOUL => {
            CallProto::with_args([PtrToMem, ConstSize, Anything, PtrToLong, DontCare])
        }

        constants::BPF_STRTOL => {
            CallProto::with_args([PtrToMem, ConstSize, Anything, PtrToLong, DontCare])
        }

        constants::BPF_CHECK_MTU => CallProto::with_args([
            PtrToCtx,       // R1: ctx (skb / xdp_md)
            Anything,       // R2: ifindex
            PtrToUninitMem, // R3: u32 *mtu_len — writable; rdonly-map gated
            Anything,       // R4: len_diff
            Anything,       // R5: flags
        ]),

        constants::BPF_COPY_FROM_USER => CallProto::with_args([
            PtrToUninitMem, // R1: dst — writable; rdonly-map gated
            ConstSize,      // R2: size
            Anything,       // R3: user_ptr
            DontCare,
            DontCare,
        ])
        .flags(CallFlags::MIGHT_SLEEP),

        // bpf_copy_from_user_task(void *dst, u32 size, const void __user
        // *src, struct task_struct *task, u64 flags) — sleepable variant
        // that reads from another task's address space. Required as a
        // *helper* proto (helper id 191) so the MIGHT_SLEEP gate fires
        // when called inside an RCU read region — closes
        // rcu_read_lock::inproper_sleepable_helper. R4 uses bare
        // `PtrToBtfId` (any BTF id) rather than `PtrToBtfIdNamed{"task_struct"}`
        // because kernel selftests pass `task_struct___local`-typed
        // subprog args via `__arg_trusted` (libbpf rewrites the FUNC
        // proto to a local struct alias for CO-RE compatibility);
        // strict-name matching breaks `verifier_global_ptr_args::flavor_ptr_*`.
        constants::BPF_COPY_FROM_USER_TASK => CallProto::with_args([
            PtrToUninitMem, // R1: dst
            ConstSize,      // R2: size
            Anything,       // R3: user_ptr
            PtrToBtfId,     // R4: task (any BTF id; libbpf alias-tolerant)
            Anything,       // R5: flags
        ])
        .mem_size_pairs(&pairs::COPY_FROM_USER_STR)
        .flags(CallFlags::MIGHT_SLEEP),

        constants::BPF_GET_CGROUP_CLASS_ID => {
            CallProto::with_args([PtrToCtx, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_GET_CURRENT_COMM => CallProto::with_args([
            PtrToUninitMem, // R1: buf (output buffer for comm string)
            ConstSize,      // R2: size_of_buf
            DontCare,
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::GET_CURRENT_COMM),

        constants::BPF_PERF_EVENT_OUTPUT => CallProto::with_args([
            PtrToCtx,    // R1: ctx
            ConstMapPtr, // R2: map
            Anything,    // R3: flags
            PtrToMem,    // R4: data
            ConstSize,   // R5: size
        ])
        .mem_size_pairs(&pairs::PERF_EVENT_OUTPUT),

        constants::BPF_L3_CSUM_REPLACE => CallProto::with_args([
            PtrToCtx, // R1: skb
            Anything, // R2: offset
            Anything, // R3: from
            Anything, // R4: to
            Anything, // R5: flags
        ]),

        constants::BPF_L4_CSUM_REPLACE => CallProto::with_args([
            PtrToCtx, // R1: skb
            Anything, // R2: offset
            Anything, // R3: from
            Anything, // R4: to
            Anything, // R5: flags
        ]),

        // ---- storage_get/_delete (sk + task + inode) ----
        // R0 typing for *_storage_get is handled by the legacy
        // `update_call_types` arm in transfer/types.rs, which keys
        // PtrToMapValueOrNull off R1 (the map) — same pattern as
        // bpf_get_local_storage. The arg-side proto is identical across
        // the three families; only R2's expected ptr family differs
        // (sock_common vs btf_id task vs btf_id inode).
        constants::BPF_SK_STORAGE_DELETE => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToBTFIdSockCommon,   // R2: sk
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        constants::BPF_TASK_STORAGE_GET => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToTask,              // R2: task
            PtrToMapValueOrNull,    // R3: value (may be NULL)
            Anything,               // R4: flags
            DontCare,
        ]),

        constants::BPF_TASK_STORAGE_DELETE => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToTask,              // R2: task
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        constants::BPF_INODE_STORAGE_GET => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToBtfId,             // R2: inode
            PtrToMapValueOrNull,    // R3: value
            Anything,               // R4: flags
            DontCare,
        ]),

        constants::BPF_INODE_STORAGE_DELETE => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToBtfId,             // R2: inode
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // bpf_cgrp_storage_get(map, cgroup, value, flags)
        // R0 typing handled by `update_call_types` (PtrToMapValueOrNull
        // keyed off R1's map). Arg-side: R2 must be a `cgroup` PtrToBtfId
        // — the typical bug (cgrp_ls_negative.c::on_enter) is passing a
        // task_struct cast as cgroup; PtrToBtfIdNamed catches the type
        // mismatch.
        constants::BPF_CGRP_STORAGE_GET => CallProto::with_args([
            ConstMapPtr,                                  // R1: map
            PtrToBtfIdNamed { type_name: "cgroup" },      // R2: cgroup
            PtrToMapValueOrNull,                          // R3: value
            Anything,                                     // R4: flags
            DontCare,
        ]),

        constants::BPF_CGRP_STORAGE_DELETE => CallProto::with_args([
            ConstMapPtr,                                  // R1: map
            PtrToBtfIdNamed { type_name: "cgroup" },      // R2: cgroup
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- bpf_get_current_task_btf ----
        // Returns the kernel's current-task pointer, typed as PTR_TO_BTF_ID
        // (task_struct *) with PTR_TRUSTED. Modeled here as PtrToTask (no
        // ACQUIRE — the kernel guarantees the returned pointer is live for
        // the duration of the program). Zero arguments.
        constants::BPF_GET_CURRENT_TASK_BTF => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToTask),

        // ---- bpf_d_path ----
        // (path: struct path *, buf: writable, sz: const) -> s64
        constants::BPF_D_PATH => CallProto::with_args([
            PtrToBtfId,     // R1: struct path *
            PtrToUninitMem, // R2: buf
            ConstSize,      // R3: sz
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::D_PATH)
        .ret(RetKind::Scalar),

        // ---- bpf_snprintf ----
        // (buf, sz, fmt, data, data_len) -> s32
        // Lite scope: fmt and data are accepted as PtrToMem; the kernel
        // additionally validates fmt against const-rodata + matches data
        // entries against fmt specifiers (not modeled).
        constants::BPF_SNPRINTF => CallProto::with_args([
            PtrToUninitMemOrNull, // R1: buf (NULL OK with size=0; "compute length only")
            ConstSizeOrZero,      // R2: sz
            PtrToConstStr,        // R3: fmt — must be const string in rodata map
            PtrToMemOrNull,  // R4: data (u64 array; may be NULL if data_len=0)
            ConstSizeOrZero, // R5: data_len
        ])
        .mem_size_pairs(&pairs::SNPRINTF)
        .ret(RetKind::Scalar),

        // ---- bpf_strncmp ----
        // (s1: PtrToMem, s1_sz: ConstSize, s2: PtrToConstStr) -> s32
        // Kernel rejects writable / non-NUL-terminated comparands via
        // ARG_PTR_TO_CONST_STR (validate_ptr_to_const_str enforces
        // BPF_F_RDONLY_PROG + NUL-within-rodata-bounds). Closes
        // strncmp_bad_writable_target and strncmp_bad_not_null_term_target.
        constants::BPF_STRNCMP => CallProto::with_args([
            PtrToMem,       // R1: s1
            ConstSize,      // R2: s1_sz
            PtrToConstStr,  // R3: s2 (rodata, NUL-terminated)
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::STRNCMP)
        .ret(RetKind::Scalar),

        // ---- Dynptr helpers ----
        //
        // These are real helpers (numeric BPF_FUNC_* ids in v6.15 uapi),
        // not kfuncs — clang emits CALL insns with the helper id, not
        // PSEUDO_KFUNC_CALL. Their prototypes happen to live in the
        // name-keyed table next to the related kfuncs (slice/from_skb/
        // from_xdp); delegate by name so we don't duplicate them. Without
        // these arms the entire dynptr modeling (init/release/leak
        // detection) is unreachable on numeric-helper calls.
        constants::BPF_DYNPTR_FROM_MEM => return get_kfunc_proto("bpf_dynptr_from_mem"),
        constants::BPF_RINGBUF_RESERVE_DYNPTR => {
            return get_kfunc_proto("bpf_ringbuf_reserve_dynptr");
        }
        constants::BPF_RINGBUF_SUBMIT_DYNPTR => {
            return get_kfunc_proto("bpf_ringbuf_submit_dynptr");
        }
        constants::BPF_RINGBUF_DISCARD_DYNPTR => {
            return get_kfunc_proto("bpf_ringbuf_discard_dynptr");
        }
        constants::BPF_DYNPTR_READ => return get_kfunc_proto("bpf_dynptr_read"),
        constants::BPF_DYNPTR_WRITE => return get_kfunc_proto("bpf_dynptr_write"),
        constants::BPF_DYNPTR_DATA => return get_kfunc_proto("bpf_dynptr_data"),

        _ => return None,
    })
}

pub(crate) fn is_fastcall_helper(helper: u32) -> bool {
    matches!(
        helper,
        constants::BPF_KTIME_GET_NS
            | constants::BPF_GET_SMP_PROCESSOR_ID
            | constants::BPF_GET_CURRENT_PID_TGID
            | constants::BPF_GET_CURRENT_UID_GID
            | constants::BPF_GET_CURRENT_COMM
            | constants::BPF_GET_CURRENT_TASK
            | constants::BPF_GET_NUMA_NODE_ID
            | constants::BPF_GET_CURRENT_CGROUP_ID
            | constants::BPF_JIFFIES64
            | constants::BPF_KTIME_GET_BOOT_NS
            | constants::BPF_KTIME_GET_COARSE_NS
    )
}

/// Returns true if the helper rejects packet pointers for the given argument index.
pub(crate) fn helper_rejects_packet_for_arg(helper: u32, arg_index: usize) -> bool {
    match helper {
        // bpf_skb_store_bytes: R3 (from buffer) cannot be packet pointer
        // because the helper modifies packet data, causing pointer invalidation
        constants::BPF_SKB_STORE_BYTES => arg_index == 2,

        // Add other helpers with similar restrictions here
        _ => false,
    }
}

/// For helpers with PTR_OR_NULL args, returns the index of the paired size argument.
pub(crate) fn get_nullable_ptr_size_pair(helper: u32, ptr_arg_index: usize) -> Option<usize> {
    match helper {
        // bpf_csum_diff: R1=from (PTR_OR_NULL) paired with R2=from_size,
        //                R3=to (PTR_OR_NULL) paired with R4=to_size
        constants::BPF_CSUM_DIFF => match ptr_arg_index {
            0 => Some(1), // R1's size is R2
            2 => Some(3), // R3's size is R4
            _ => None,
        },
        // bpf_snprintf: R1=buf (UNINIT_MEM_OR_NULL) paired with R2=size,
        //               R4=data (MEM_OR_NULL) paired with R5=data_len.
        constants::BPF_SNPRINTF => match ptr_arg_index {
            0 => Some(1),
            3 => Some(4),
            _ => None,
        },
        // Add other helpers with PTR_OR_NULL + SIZE_OR_ZERO pairs
        _ => None,
    }
}
