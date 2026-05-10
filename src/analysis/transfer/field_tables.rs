// src/analysis/transfer/field_tables.rs
//
// Static field-trust lookup tables for BTF struct field loads.
// These are pure data — no logic, no state.

/// Allowlist of `(struct_name, field_name)` pairs whose loaded pointer
/// is marked PTR_TRUSTED by the kernel verifier. Returns true when the
/// field load should yield a trusted pointer.
pub fn trusted_field_load(struct_name: &str, field_name: &str) -> bool {
    // Universal `bpf_iter__*` pointer fields. The kernel emits
    // bpf_iter ctx structs as `struct bpf_iter__X { struct
    // bpf_iter_meta *meta; <iter-payload-pointers...>; }`. The
    // payload pointers are marked PTR_TRUSTED while the iter is
    // alive — same lifetime band as the ctx itself. Programs read
    // them via `ctx->task`, `ctx->sk_common`, `ctx->file`, etc.,
    // then deref BTF fields. Allowlisting all iter-prefix structs'
    // pointer fields covers the per-iter-subtype fan-out without
    // enumerating each one.
    if struct_name.starts_with("bpf_iter__") {
        return true;
    }
    matches!(
        (struct_name, field_name),
        // task_struct.cpus_ptr — `cpumask_t *` carrying the task's
        // current CPU mask. Kernel marks PTR_TRUSTED on load (the
        // task's PCB is alive while the program holds a trusted
        // task pointer); KF_RCU consumers like
        // `bpf_cpumask_test_cpu` accept.
        ("task_struct", "cpus_ptr")
        // task_struct.group_leader — kernel's
        // `task_struct_btf_ids_trusted_set` lists this as a
        // permanently-trusted pointer (the leader of the thread
        // group; lifetime tied to the task itself). Drives
        // task_kfunc_success.c::task_kfunc_acquire_trusted_walked.
        // task_struct.{parent, real_parent} are NOT here — they are
        // `__rcu` fields gated by `rcu_field_load` below: yield RCU
        // inside CS, ScalarValue (untrusted) outside.
        | ("task_struct", "group_leader")
        // sk_buff.sk — `struct sock *`. Trusted while the skb is
        // trusted. Drives `nested_trust_success::test_skb_field`'s
        // `bpf_sk_storage_get(&map, skb->sk, …)` accepting path.
        | ("sk_buff", "sk")
        // LSM hook chains — fields kernel marks PTR_TRUSTED on load
        // from a trusted-rooted access (each entry corresponds to a
        // specific FR in local_storage.c). Adding more entries should
        // always cross-check against the matching `__failure` siblings
        // — see the cpumask reader/mutator split for the kind of FA
        // risk loose typing exposes.
        | ("linux_binprm", "file")  // bprm->file (exec)
        | ("file", "f_inode")        // bprm->file->f_inode (exec)
        | ("dentry", "d_inode")      // dentry->d_inode (inode_rename, unlink_hook)
        | ("socket", "sk")           // sock->sk (socket_bind, socket_post_create)
        | ("task_struct", "bpf_storage")  // task->bpf_storage (unlink_hook)
        | ("sock", "sk_bpf_storage")      // sk->sk_bpf_storage (socket_bind)
        | ("bpf_local_storage", "smap")   // local_storage->smap (unlink_hook, socket_bind)
        // Iter / direct-typed-ctx hooks. The BPF program holds a
        // typed ctx pointer directly; the kernel marks the embedded
        // sock pointer trusted while the iter is alive.
        // `bpf_iter__sockmap.sk` (verifier_sockmap_mutate::test_trace_iter):
        // `__bpf_md_ptr(struct sock *, sk)` at offset 0; pointee
        // resolves via the anonymous-union descent in `field_at_offset`.
        | ("bpf_iter__sockmap", "sk")
        // `sk_reuseport_md.sk` (verifier_sockmap_mutate::test_sk_reuseport):
        // `__bpf_md_ptr(struct bpf_sock *, sk)` — kernel marks bpf_sock
        // pointer trusted on load; SOCKMAP/SOCKHASH map-update accepts.
        | ("sk_reuseport_md", "sk")
        // `bpf_iter__bpf_map.map` (verifier_arena::iter_maps1):
        // `__bpf_md_ptr(struct bpf_map *, map)` — the iter ctx's
        // current map. Kernel marks it trusted while the iter is alive;
        // `bpf_arena_alloc_pages(map, ...)` accepts the loaded
        // `PtrToBtfId{bpf_map, TRUSTED}` as its `__map`-suffixed arg
        // (kernel `verifier.c` ~L13227 KF_ARG_PTR_TO_MAP).
        | ("bpf_iter__bpf_map", "map")
        // cgroup.kn → kernfs_node. Used by cgroup_id() helper
        // (`cgrp->kn->id`) — appears in cgroup_hierarchical_stats and
        // cgrp_kfunc_success::test_cgrp_from_id.
        | ("cgroup", "kn")
        // sock.<descent-to-sk_cgrp_data.cgroup>. The kernel admits
        // `sk->sk_cgrp_data.cgroup` from any trusted sock pointer.
        // `field_at_offset` descends through the embedded
        // `sock_cgroup_data` struct so the leaf field name is
        // `cgroup` (offset 664 in tcp_sock via the inet_conn chain).
        // Closes the cgrp_ls_attach_cgroup helper-arg path.
        | ("sock", "cgroup")
        // vm_area_struct.vm_file → `struct file *`. Trusted while the
        // vma is trusted (bpf_find_vma's callback receives a TRUSTED
        // vm_area_struct *). Programs typically chain to
        // `vma->vm_file->f_path.dentry->d_shortname.string` for
        // probe_read_kernel_str; downstream loads on the resulting
        // PtrToBtfId{file} are admitted via the lax PtrToBtfId access
        // policy. Closes find_vma::handle_{getpid,pe}.
        | ("vm_area_struct", "vm_file")
        // vm_area_struct.vm_mm → `struct mm_struct *`. Trusted while
        // the vma is trusted; programs commonly chain to
        // `vma->vm_mm->start_stack` etc. Drives lsm::test_int_hook's
        // file_mprotect handler.
        | ("vm_area_struct", "vm_mm")
        // request_sock.sk → struct sock *. Trusted while the request_sock
        // is trusted; tp_btf hooks like tcp_retransmit_synack pass req
        // and chain `req->sk` into bpf_sk_storage_get.
        | ("request_sock", "sk")
    )
}

/// Allowlist of `(struct_name, field_name)` pairs whose loaded pointer
/// is `__rcu`-tagged in the kernel: the load yields a typed pointer
/// only inside an RCU CS (PtrToBtfId{..., RCU}); outside the CS, the
/// kernel calls it "old style ptr_to_btf_id" and the result carries
/// no trust flag — downstream kfunc/helper arg validators that
/// require TRUSTED/RCU reject. We model "no trust outside CS" by
/// leaving dst as ScalarValue (the typed-pointer fallthrough).
///
/// Drives the rcu_read_lock.c success cases (real_parent walks under
/// bpf_rcu_read_lock) and the matching __failure tests
/// (verifier_vfs_reject::get_task_exe_file_kfunc_untrusted,
/// rcu_read_lock cluster's no_lock / cross_rcu_region /
/// nested_rcu_region / task_untrusted_rcuptr).
pub fn rcu_field_load(struct_name: &str, field_name: &str) -> bool {
    matches!(
        (struct_name, field_name),
        ("task_struct", "real_parent")
        | ("task_struct", "parent")
        // task_struct.cgroups → css_set, css_set.dfl_cgrp → cgroup
        // are kernel `__rcu` fields. In non-sleepable tracing programs
        // the kernel holds an implicit RCU CS at entry (mirrored by
        // `auto_rcu` in analysis::mod.rs), so the load yields RCU and
        // downstream `bpf_cgrp_storage_get` accepts. In sleepable
        // programs (`fentry.s/...`) the program must enter an explicit
        // `bpf_rcu_read_lock` first; outside the CS the load lands
        // UNTRUSTED and the storage helper rejects (kernel: "task->
        // cgroups is untrusted in sleepable prog outside of RCU CS").
        // Closes cgrp_ls_sleepable::no_rcu_lock.
        | ("task_struct", "cgroups")
        | ("css_set", "dfl_cgrp")
    )
}

/// Static allowlist of `(struct, field) → "percpu" | "user"` for kernel
/// fields whose BTF TYPE_TAG annotation lives in vmlinux BTF (which we
/// don't ship). Direct deref of these is rejected by `memory/access.rs`'s
/// PERCPU/USER check; programs must go through `bpf_per_cpu_ptr` /
/// `bpf_copy_from_user`. Without this, the BTF field-walk produces an
/// untagged pointer and the kernel-rejection mechanism doesn't fire.
///
/// Mirror kernel sources only — adding speculative entries would FA
/// `__failure` tests that exercise the matching deref path.
pub(super) fn percpu_or_user_field(struct_name: &str, field_name: &str) -> Option<&'static str> {
    match (struct_name, field_name) {
        // struct cgroup { ... struct cgroup_rstat_cpu __percpu *rstat_cpu; }
        // — drives btf_type_tag_percpu::test_percpu_load (`__failure`).
        ("cgroup", "rstat_cpu") => Some("percpu"),
        _ => None,
    }
}
