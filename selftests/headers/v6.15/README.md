# Vendored headers for v6.15 selftests

These headers exist so `clang -target bpf` can compile the upstream
sources in `selftests/progs/` without requiring a system libbpf,
kernel UAPI, or libc install. The selftest pipeline runs on any OS
with a recent clang (macOS, Linux, …).

## Contents

### Selftests-specific (Linux v6.15 verbatim)

| File | Source |
|---|---|
| `bpf_misc.h` | `tools/testing/selftests/bpf/progs/bpf_misc.h` |
| `bpf_kfuncs.h` | `tools/testing/selftests/bpf/bpf_kfuncs.h` |
| `bpf_experimental.h` | `tools/testing/selftests/bpf/bpf_experimental.h` |
| `bpf_compiler.h` | `tools/testing/selftests/bpf/progs/bpf_compiler.h` |

### libbpf (Linux v6.15 verbatim)

| File | Source |
|---|---|
| `bpf/bpf_helpers.h` | `tools/lib/bpf/bpf_helpers.h` |
| `bpf/bpf_tracing.h` | `tools/lib/bpf/bpf_tracing.h` |
| `bpf/bpf_helper_defs.h` | libbpf v1.5.0 release artifact (generated) |

### Kernel UAPI (Linux v6.15 verbatim)

| File | Source |
|---|---|
| `linux/bpf.h` | `tools/include/uapi/linux/bpf.h` |
| `linux/bpf_common.h` | `tools/include/uapi/linux/bpf_common.h` |
| `linux/types.h` | `tools/include/uapi/linux/types.h` |
| `asm-generic/int-ll64.h` | `include/uapi/asm-generic/int-ll64.h` |
| `asm/bitsperlong.h` | `include/uapi/asm-generic/bitsperlong.h` |

### vmlinux.h (BTF type dump)

`vmlinux_v614_base.h` is a 3.4 MB pre-generated dump from kernel 6.14
(via [iovisor/bcc](https://github.com/iovisor/bcc/blob/master/libbpf-tools/x86/vmlinux_614.h)).
`vmlinux.h` is a thin wrapper that includes the base then adds forward
declarations for kfuncs introduced in v6.15 (e.g. `bpf_dynptr_copy`).
Append to `vmlinux.h`'s "v6.15 additions" section as new symbols
surface during translation; keep `vmlinux_v614_base.h` byte-identical
to its bcc source.

### Stubs (`_stubs/`)

Minimal headers that satisfy `#include`s of standard / libc files
when compiling `-target bpf`. The host system's `<string.h>`,
`<errno.h>`, etc. don't apply because `-target bpf` isn't a recognized
arch in libc headers. These stubs cover only the symbols the corpus
actually consumes — extend as needed.

| Stub | Provides |
|---|---|
| `_stubs/string.h` | `memcpy`/`memset` decls (real implementations are clang builtins or BPF helpers) |
| `_stubs/stdbool.h` | `bool`, `true`, `false` |
| `_stubs/limits.h` | `INT_MAX`, `LONG_MAX`, … |
| `_stubs/time.h` | `time_t` |
| `_stubs/errno.h` | shim → `linux/errno.h` |
| `_stubs/linux/errno.h` | common errno constants (`EINVAL`, `ENOMEM`, …) |
| `_stubs/linux/if_ether.h` | `ETH_HLEN`, `ETH_P_IP`, `struct ethhdr` |

`-nostdinc` blocks system include search; `-isystem <clang-resource-dir>/include`
adds back compiler-intrinsic headers (`stddef.h`, `stdarg.h`, `stdint.h`).

## Updating

Refresh in lockstep with `selftests/SOURCE_TAG`. Don't edit vendored
files locally — keep them byte-identical to upstream so the diff trail
is obvious. Stubs and the `vmlinux.h` wrapper are ours; modify those
freely.

## Currently working end-to-end

| Source | `selftest-file` defines |
|---|---|
| `verifier_gotol.c`  | `CAN_USE_GOTOL` |
| `verifier_ldsx.c`   | `__TARGET_ARCH_x86` |
| `verifier_movsx.c`  | `__TARGET_ARCH_x86` |
| `dynptr_success.c`  | (compiles; no per-prog annotations — all skipped) |
| `dynptr_fail.c`     | (partial — see runner output) |
| `iters.c`           | (partial — wallclock-bounded) |

## Deferred

`verifier_may_goto_1.c`, `verifier_load_acquire.c`, `verifier_store_release.c`
all `#include "../../../include/linux/filter.h"` — a literal relative
path that resolves outside our project tree. Clang can't be told to
redirect literal include paths, so making these work requires either
mirroring upstream's `tools/testing/selftests/bpf/` depth or vendoring
the file at the resolved location.
