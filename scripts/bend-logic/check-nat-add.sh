#!/usr/bin/env bash
set -euo pipefail
cd /home/hbox/workbox/codex-bend-logic-20261003/src
export LEAN_NUM_THREADS=2
export LEAN_PATH="$PWD/.lake/build/lib/lean"
for task_package in /home/hbox/workbox/codex-unified-integration-20261003/src/.lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$task_package/.lake/build/lib/lean"
done
task_lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
# Run after NatOperation/NatTyped qualified; never rebuild missing dependencies.
"$task_lean" -j 2 Compiler/BendLogicNatAdd.lean -o .lake/build/lib/lean/Compiler/BendLogicNatAdd.olean
sha256sum Compiler/BendLogicNatAdd.lean
printf 'BEND-NAT-ADD SCOPED CHECK PASS\n'
