# selftests/

Layout mirrors modern `tools/testing/selftests/` in the kernel tree.
Most subdirs come from the `bpf/` selftest suite; `sched_ext/` is a sibling
suite vendored because its `.bpf.c` programs are the only kernel-side
exercise of `scx_bpf_*` kfuncs and `SEC("struct_ops.s/sched_ext_ops/...")`.

```
selftests/
├── legacy/                    (from bpf/) pre-6.2 + hand-authored old-style backports
│   ├── verifier/                pre-6.2 upstream tests (old struct bpf_test format)
│   └── verifier_backport/       hand-authored old-style translations of post-6.2 tests
├── progs/                     (from bpf/progs/) verifier_*.c + struct_ops .c — reference
├── sched_ext/                 (from sched_ext/) verbatim *.bpf.c — sibling selftest suite (W6.4)
├── test_kmods/                (from bpf/test_kmods/) companion headers (bpf_testmod.h, …)
├── prog_tests/                placeholder (empty)
├── map_tests/                 placeholder (empty)
└── SOURCE_TAG                 kernel tag that vendored sources were pulled from
```

The pipeline today (`convert.sh` → JSON → `selftest-suite`) consumes only
`legacy/verifier/` and `legacy/verifier_backport/`. The other directories
reserve shape for future work; see each dir's README for specifics.
