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

#endif /* __ZOVIA_VMLINUX_H */
