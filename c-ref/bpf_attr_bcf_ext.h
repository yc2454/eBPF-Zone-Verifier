/* SPDX-License-Identifier: GPL-2.0 WITH Linux-syscall-note */
/*
 * Proposed bpf_attr extension for userspace BCF.
 *
 * This header is documentation, not a real UAPI patch. Step 3.4 will splice
 * these two fields into `union bpf_attr`'s anonymous struct for
 * BPF_PROG_LOAD inside `include/uapi/linux/bpf.h`, alongside
 * `keyring_id`. Tools-uapi gets the same patch.
 *
 *
 * Wire shape (additions to the existing BPF_PROG_LOAD anonymous struct):
 *
 *   __aligned_u64 bcf_bundle;       // userptr to bcf_bundle_header
 *   __u32         bcf_bundle_size;  // bytes; 0 disables BCF
 *
 * Both fields are optional. A program load with `bcf_bundle_size == 0`
 * behaves identically to today's BPF_PROG_LOAD — BCF refinement is opt-in,
 * never required for correctness. When set, the kernel parses the buffer
 * as a `struct bcf_bundle_header` (see c-ref/bcf_bundle.h), and at each
 * verifier refinement site looks up entries by canonical hash.
 *
 *
 * Comparison vs. BCF set1 patch 0003:
 *
 * BCF's original 5-field extension supported suspend/resume via an anon-fd:
 *
 *   __aligned_u64 bcf_buf;          // shared cond/proof buffer
 *   __u32         bcf_buf_size;
 *   __u32         bcf_buf_true_size;
 *   __u32         bcf_fd;           // anon-fd owning preserved verifier_env
 *   __u32         bcf_flags;        // PROOF_PROVIDED / PATH_UNREACHABLE
 *
 * We deliberately cut all four protocol-state fields. The bundle is a
 * one-shot input: the kernel reads it once during BPF_PROG_LOAD and never
 * surfaces an anon-fd back to userspace. Net delta vs. BCF: -3 fields,
 * suspend/resume machinery gone.
 *
 *
 * Validation invariants the kernel must enforce:
 *
 *   - `!!attr->bcf_bundle == !!attr->bcf_bundle_size`  (both set or both 0)
 *   - `bcf_bundle_size >= sizeof(struct bcf_bundle_header)`
 *   - `header.magic == BCF_BUNDLE_MAGIC`
 *   - `header.total_size <= bcf_bundle_size`
 *   - every entry's `(goal_off, goal_size)` and `(proof_off, proof_size)`
 *     stay within `[sizeof(header) + entry_cnt*sizeof(entry), total_size)`
 *
 * Error path: -EINVAL on any violation; the load fails before symbolic
 * execution begins (no partial-bundle semantics).
 */

#ifndef _UAPI__LINUX_BPF_ATTR_BCF_EXT_H__
#define _UAPI__LINUX_BPF_ATTR_BCF_EXT_H__

/* This file intentionally contains no struct definitions — the fields land
 * inside `union bpf_attr` itself. See c-ref/bcf_bundle.h for the payload
 * format pointed at by `bcf_bundle`.
 */

#endif /* _UAPI__LINUX_BPF_ATTR_BCF_EXT_H__ */
