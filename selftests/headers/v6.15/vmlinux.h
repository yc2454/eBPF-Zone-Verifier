/* Wrapper around the bcc-published vmlinux.h (kernel 6.14 BTF) plus
 * forward declarations for kfuncs added in v6.15 that are missing from
 * the base file. As we hit more 6.15-only symbols during translation,
 * append them at the bottom. */
#ifndef __ZOVIA_VMLINUX_H
#define __ZOVIA_VMLINUX_H

#include "vmlinux_v614_base.h"

/* ===== v6.15 additions ===== */

extern int bpf_dynptr_copy(struct bpf_dynptr *dst, __u32 dst_off,
                           struct bpf_dynptr *src, __u32 src_off,
                           __u32 size) __weak __ksym;

/* ===== W6.4b sched_ext additions =====
 * The task_struct.scx field and struct sched_ext_entity live in
 * vmlinux_v614_base.h since they need to be visible inside task_struct.
 * The remaining sched_ext surface (struct sched_ext_ops, opaque iter/info
 * fwd decls, and the SCX_* enum constants the corpus + scx/common.bpf.h
 * reference) lives here. Values are plausible but only their nonzeroness
 * and uniqueness matter for our verifier's purposes — we do not model
 * sched_ext semantics beyond struct_ops dispatch.
 */

/* opaque iter (only fwd-decl used) */
struct bpf_iter_scx_dsq;
struct scx_event_stats;

/* sched_ext callback arg structs. BPF_PROG macro expansion forces these
 * to be complete (it dereferences the pointer args to extract from ctx[]),
 * so each gets a minimal body. The corpus only reads
 * `scx_init_task_args.fork`; everything else is opaque payload. */
struct scx_exit_info {
	s64  kind;
	s64  exit_code;
	const char *reason;
	const char *msg;
	char *dump;
	u64  __opaque[4];
};

struct scx_init_task_args {
	bool fork;
	u64  __opaque[4];
};

struct scx_exit_task_args {
	bool cancelled;
	u64  __opaque[4];
};

struct scx_cpu_acquire_args {
	u64  __opaque[4];
};

struct scx_cpu_release_args {
	int  reason;
	struct task_struct *task;
	u64  __opaque[4];
};

struct scx_cgroup_init_args {
	u32  weight;
	u64  __opaque[4];
};

/* SCX enum constants. Split into named enums matching kernel sched/ext.h
 * because compat.bpf.h calls bpf_core_enum_value_exists(enum scx_enq_flags,
 * ...) which requires the enum to be a real named type. SCX_DSQ_FLAG_BUILTIN
 * must be nonzero for the sanity _Static_assert in scx/common.bpf.h. */
enum scx_dsq_id_flags {
	SCX_DSQ_FLAG_BUILTIN		= 1ULL << 63,
	SCX_DSQ_FLAG_LOCAL_ON		= 1ULL << 62,
	SCX_DSQ_INVALID			= SCX_DSQ_FLAG_BUILTIN | 0,
	SCX_DSQ_GLOBAL			= SCX_DSQ_FLAG_BUILTIN | 1,
	SCX_DSQ_LOCAL			= SCX_DSQ_FLAG_BUILTIN | 2,
	SCX_DSQ_LOCAL_ON		= SCX_DSQ_FLAG_BUILTIN | SCX_DSQ_FLAG_LOCAL_ON,
	SCX_DSQ_LOCAL_CPU_MASK		= 0xffffffffULL,
};

enum scx_ops_flags {
	SCX_OPS_KEEP_BUILTIN_IDLE	= 1ULL << 0,
	SCX_OPS_ENQ_LAST		= 1ULL << 1,
	SCX_OPS_ENQ_EXITING		= 1ULL << 2,
	SCX_OPS_SWITCH_PARTIAL		= 1ULL << 3,
	SCX_OPS_ENQ_DFL_NO_DISPATCH	= 1ULL << 4,
};

enum scx_enq_flags {
	SCX_ENQ_WAKEUP			= 1ULL << 0,
	SCX_ENQ_HEAD			= 1ULL << 1,
	SCX_ENQ_PREEMPT			= 1ULL << 32,
	SCX_ENQ_REENQ			= 1ULL << 40,
	SCX_ENQ_LAST			= 1ULL << 41,
	SCX_ENQ_CPU_SELECTED		= 1ULL << 48,
};

enum scx_pick_idle_cpu_flags {
	SCX_PICK_IDLE_CORE		= 1ULL << 0,
	SCX_PICK_IDLE_IN_NODE		= 1ULL << 1,
};

enum scx_kick_flags {
	SCX_KICK_IDLE			= 1ULL << 0,
	SCX_KICK_PREEMPT		= 1ULL << 1,
	SCX_KICK_WAIT			= 1ULL << 2,
};

enum scx_exit_code {
	SCX_ECODE_RSN_HOTPLUG		= 1ULL << 32,
	SCX_ECODE_ACT_RESTART		= 1ULL << 48,
};

#define SCX_SLICE_DFL			(20ULL * 1000000ULL)	/* 20ms */

/* sched_ext_ops — kernel-canonical layout. Field ordering doesn't affect
 * us (struct_ops binding goes through BTF, not C-level offsets). */
struct sched_ext_ops {
	s32  (*select_cpu)(struct task_struct *p, s32 prev_cpu, u64 wake_flags);
	void (*enqueue)(struct task_struct *p, u64 enq_flags);
	void (*dequeue)(struct task_struct *p, u64 deq_flags);
	void (*dispatch)(s32 cpu, struct task_struct *prev);
	void (*tick)(struct task_struct *p);
	void (*runnable)(struct task_struct *p, u64 enq_flags);
	void (*running)(struct task_struct *p);
	void (*stopping)(struct task_struct *p, bool runnable);
	void (*quiescent)(struct task_struct *p, u64 deq_flags);
	bool (*yield)(struct task_struct *from, struct task_struct *to);
	bool (*core_sched_before)(struct task_struct *a, struct task_struct *b);
	void (*set_weight)(struct task_struct *p, u32 weight);
	void (*set_cpumask)(struct task_struct *p, const struct cpumask *cpumask);
	void (*update_idle)(s32 cpu, bool idle);
	void (*cpu_acquire)(s32 cpu, struct scx_cpu_acquire_args *args);
	void (*cpu_release)(s32 cpu, struct scx_cpu_release_args *args);
	void (*cpu_online)(s32 cpu);
	void (*cpu_offline)(s32 cpu);
	s32  (*init_task)(struct task_struct *p, struct scx_init_task_args *args);
	void (*exit_task)(struct task_struct *p, struct scx_exit_task_args *args);
	void (*enable)(struct task_struct *p);
	void (*disable)(struct task_struct *p);
	s32  (*cgroup_init)(struct cgroup *cgrp, struct scx_cgroup_init_args *args);
	void (*cgroup_exit)(struct cgroup *cgrp);
	s32  (*cgroup_prep_move)(struct task_struct *p, struct cgroup *from, struct cgroup *to);
	void (*cgroup_move)(struct task_struct *p, struct cgroup *from, struct cgroup *to);
	void (*cgroup_cancel_move)(struct task_struct *p, struct cgroup *from, struct cgroup *to);
	void (*cgroup_set_weight)(struct cgroup *cgrp, u32 weight);
	s32  (*init)(void);
	void (*exit)(struct scx_exit_info *ei);
	u32  dispatch_max_batch;
	u64  flags;
	u32  timeout_ms;
	u32  exit_dump_len;
	u64  hotplug_seq;
	char name[128];
};

/* ===== end sched_ext additions ===== */

#endif /* __ZOVIA_VMLINUX_H */
