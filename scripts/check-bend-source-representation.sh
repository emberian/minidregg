#!/usr/bin/env bash
set -euo pipefail
task_source_root="${BEND_REPRESENTATION_SOURCE_ROOT:-$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)}"
cd "$task_source_root"
export LEAN_NUM_THREADS=2
export LEAN_PATH="$PWD/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
for task_package in "$task_source_root"/.lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$task_package/.lake/build/lib/lean"
done
task_lean="${BEND_REPRESENTATION_LEAN:-lean}"
task_version="$("$task_lean" --version)"
case "$task_version" in *"version 4.30.0"*) ;; *) printf 'REFUSED: Lean4.30.0 required, got %s\n' "$task_version"; exit 2 ;; esac
for task_module in BendSourceRepresentation BendSourceTypedRepresentation BendSourceByteCodec; do
  "$task_lean" -j 2 "Compiler/$task_module.lean" -o ".lake/build/lib/lean/Compiler/$task_module.olean"
done
printf 'BEND SOURCE REPRESENTATION SCOPED CHECK PASS\n'
