#!/usr/bin/env bash
# check-prover-glue.sh -- the Lean-emitted prover glue is exactly what its Lean
# source emits now.
#
# Three modules write Rust when they elaborate (`#eval ….run`, paths relative
# to the working directory):
#   Compiler/MinidreggV1NativeGlue.lean      -> prover/generated/semantic_artifact_v1.rs
#   Compiler/EvmStage0NativeDeployment.lean  -> prover/generated/evm_stage0_add_aux.rs
#   Compiler/ArithmeticNativeDeployment.lean -> prover/src/semantic_artifact_arithmetic.rs
# They re-emit only when lake rebuilds them, so a codec-version move upstream
# left the committed copies stale until some unrelated build rewrote them as
# "drift". This gate re-elaborates the three modules in a TEMPORARY working
# directory (the tree is never written) and compares byte-for-byte with the
# tracked copies. Exit 1 on any difference or on an emitter that wrote nothing.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
export PATH=$HOME/.elan/bin:$PATH
modules=(Compiler/MinidreggV1NativeGlue Compiler/EvmStage0NativeDeployment Compiler/ArithmeticNativeDeployment)
files=(prover/generated/semantic_artifact_v1.rs prover/generated/evm_stage0_add_aux.rs prover/src/semantic_artifact_arithmetic.rs)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/prover-glue.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/prover/generated" "$tmp/prover/src" "$tmp/before"
# The tracked copies as they stand BEFORE anything is built: a lake build of an
# emitter rewrites them in place, which would make a later comparison vacuous.
for file in "${files[@]}"; do
  mkdir -p "$tmp/before/$(dirname "$file")"
  cp "$root/$file" "$tmp/before/$file"
done
# Build the emitters' dependencies (not the emitters' own outputs into the tree:
# lake may rebuild them here, which is what the build does anyway).
lake build "${modules[@]//\//.}" >/dev/null
for module in "${modules[@]}"; do
  (cd "$tmp" && lake -d "$root" env lean "$root/$module.lean" >/dev/null)
done
status=0
for file in "${files[@]}"; do
  if [ ! -s "$tmp/$file" ]; then
    echo "FAIL: $file was not emitted"; status=1; continue
  fi
  if ! cmp -s "$tmp/$file" "$tmp/before/$file"; then
    echo "DRIFT: $file differs from what its Lean source emits"
    diff "$tmp/before/$file" "$tmp/$file" | cut -c1-200 | head -8
    status=1
  fi
done
[ "$status" = 0 ] && echo "OK: prover glue (${#files[@]} files) matches its Lean source"
exit "$status"
