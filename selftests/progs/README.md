# progs/

Verbatim copies of `tools/testing/selftests/bpf/progs/verifier_*.c` from a
pinned kernel tag (see `../SOURCE_TAG`). These files use the modern
test-loader format (BPF C with inline asm + `__success`/`__failure`
annotations) and are **not** consumed by `convert.sh` today — they serve as
the source of truth against which hand-authored backports in
`../legacy/verifier_backport/` are reviewed.

Adding a new-format parser to `convert_tests.c` is a separate workstream;
until then, treat these as reference material only.
