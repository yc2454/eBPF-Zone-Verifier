# selftests/

Layout mirrors modern `tools/testing/selftests/bpf/` in the kernel tree.

```
selftests/
├── legacy/
│   ├── verifier/              pre-6.2 upstream tests (old struct bpf_test format)
│   └── verifier_backport/     hand-authored old-style translations of post-6.2 tests
├── progs/                     verbatim copies of kernel progs/verifier_*.c (reference)
├── prog_tests/                placeholder (empty)
├── map_tests/                 placeholder (empty)
└── SOURCE_TAG                 kernel tag that progs/ was pulled from
```

The pipeline today (`convert.sh` → JSON → `selftest-suite`) consumes only
`legacy/verifier/` and `legacy/verifier_backport/`. The other directories
reserve shape for future work; see each dir's README for specifics.
