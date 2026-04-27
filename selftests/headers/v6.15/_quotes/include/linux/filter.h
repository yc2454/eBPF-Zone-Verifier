/* Minimal in-tree stub for `linux/filter.h` — the upstream selftests
 * reach for it via `#include "../../../include/linux/filter.h"` (a
 * path that is meaningful inside the kernel tree but not here). The
 * stub is loaded via `-iquote selftests/headers/v6.15/_quotes/q1/q2/q3`
 * which lets clang resolve the relative path against this directory.
 *
 * Only the macros the selftest corpus actually uses are defined. Real
 * filter.h is much larger; if a new corpus file fails to compile
 * because something here is missing, add the minimal definition.
 */
#ifndef __ZOVIA_STUB_LINUX_FILTER_H__
#define __ZOVIA_STUB_LINUX_FILTER_H__

#include <linux/bpf.h>

#ifndef MAX_BPF_STACK
#define MAX_BPF_STACK 512
#endif

#ifndef BPF_RAW_INSN
#define BPF_RAW_INSN(CODE, DST, SRC, OFF, IMM)               \
    ((struct bpf_insn) {                                     \
        .code  = (CODE),                                     \
        .dst_reg = (DST),                                    \
        .src_reg = (SRC),                                    \
        .off   = (OFF),                                      \
        .imm   = (IMM) })
#endif

#ifndef BPF_ATOMIC_OP
#define BPF_ATOMIC_OP(SIZE, OP, DST, SRC, OFF)               \
    BPF_RAW_INSN(BPF_STX | (SIZE) | BPF_ATOMIC, DST, SRC, OFF, OP)
#endif

#endif /* __ZOVIA_STUB_LINUX_FILTER_H__ */
