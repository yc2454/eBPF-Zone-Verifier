#!/usr/bin/env bash
# Apply BCF set1..set5 patches as git commits. Resumable: skips any patch
# whose subject is already in `git log`. On conflict, halts so you can
# resolve + `git am --continue`, then re-run this script.
#
# Used during the userspace-BCF Phase 3.4 kernel bootstrap on the Cloudlab
# box. See docs/userspace-bcf/3.4-bootstrap.md for the full procedure.
#
# Expected to live on the Cloudlab box at
# /users/yc1795/BCF/scripts/apply_all_patches.sh — KERNEL_DIR and
# PATCH_DIRS below are pinned to that layout. Adjust if BCF lives elsewhere.

set -uo pipefail

KERNEL_DIR=/users/yc1795/BCF/build/bpf-next
PATCH_DIRS=(
    /users/yc1795/BCF/patches-kernel/set1:verifier_and_initial_checker_support
    /users/yc1795/BCF/patches-kernel/set2:add_core_proof_rules
    /users/yc1795/BCF/patches-kernel/set3:add_boolean_proof_rules
    /users/yc1795/BCF/patches-kernel/set4:add_bv_proof_rules
    /users/yc1795/BCF/patches-kernel/set5:bpftool_libbpf_support
)

cd "$KERNEL_DIR"

# Bail if a previous `git am` is mid-flight
if [[ -d .git/rebase-apply ]]; then
    echo "ERROR: a git am is in progress."
    echo "Resolve the conflict (edit files, git add, git am --continue),"
    echo "then re-run this script."
    exit 1
fi

applied=0
skipped=0
for dir in "${PATCH_DIRS[@]}"; do
    [[ -d "$dir" ]] || { echo "Missing dir: $dir"; exit 1; }
    for p in "$dir"/*.patch; do
        name=$(basename "$p")
        [[ "$name" == 0000-* ]] && continue

        # Explicit skip list: patches we intentionally don't apply.
        # 0016 is the resume half of BCF's suspend/resume — our deltas replace it.
        case "$name" in
            "0016-bpf-Resume-verifier-env-and-check-proof.patch")
                echo "--- skipping (intentional, bundle replaces this): $name"
                skipped=$((skipped+1))
                continue
                ;;
        esac

        # Extract Subject line (after the [PATCH ...] tag) and check git log.
        # Uses process substitution rather than a pipe to avoid pipefail+SIGPIPE
        # when grep -q closes the pipe early (a real footgun under `set -o pipefail`).
        subj=$(grep -m1 '^Subject:' "$p" | sed -E 's/^Subject: \[PATCH[^]]*\] //' | tr -d '\r')
        if [[ -n "$subj" ]] && grep -qxF "$subj" <(git log --pretty=%s); then
            skipped=$((skipped+1))
            continue
        fi

        echo "=== Applying: $name ==="
        if ! git am --reject --keep-cr "$p"; then
            # If the only rejects are .clang-format (cosmetic), auto-accept and continue.
            # bpf-next's .clang-format has drifted from BCF's authoring base and the
            # entries are purely formatter hints — no kernel behavior depends on them.
            rejects=$(find . -name "*.rej" 2>/dev/null)
            if [[ "$rejects" == "./.clang-format.rej" ]]; then
                echo "    (auto-skipping .clang-format reject)"
                rm .clang-format.rej
                git add -A
                git am --continue >/dev/null
                applied=$((applied+1))
                continue
            fi
            echo ""
            echo "----------------------------------------------------------"
            echo "FAILED on: $name"
            echo "Rejects:"
            echo "$rejects"
            echo ""
            echo "Fix manually then:  git add <files>; git am --continue"
            echo "Then re-run this script."
            echo "----------------------------------------------------------"
            exit 1
        fi
        applied=$((applied+1))
    done
done

echo ""
echo "=========================================="
echo "All patches applied. $applied new, $skipped already applied."
echo "Now tag the baseline:"
echo "    git tag bcf-applied"
echo "=========================================="
