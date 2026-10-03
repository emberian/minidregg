#!/usr/bin/env bash
set -euo pipefail
cd /home/hbox/workbox/codex-bend-logic-20261003/src
export LEAN_NUM_THREADS=2
task_outputs=/tank/dregg-build/codex-bend-natural-20261003/olean
mkdir -p "$task_outputs/Compiler"
export LEAN_PATH="$task_outputs:$PWD/.lake/build/lib/lean"
for task_package in /home/hbox/workbox/codex-unified-integration-20261003/src/.lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$task_package/.lake/build/lib/lean"
done
task_lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
# Qualified dependencies only; four new owned modules, no full lake.
for task_module in BendNaturalExpression BendNaturalSource BendNaturalCircuit BendNaturalMethod; do
  "$task_lean" -j 2 "Compiler/$task_module.lean" -o "$task_outputs/Compiler/$task_module.olean"
done
printf 'BEND-NATURAL EXPRESSION SOURCE/CIRCUIT/METHOD SCOPED CHECK PASS\n'
