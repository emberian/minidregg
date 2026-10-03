#!/usr/bin/env bash
set -euo pipefail
cd /home/hbox/workbox/codex-bend-logic-20261003/src
export LEAN_NUM_THREADS=2
export LEAN_PATH="$PWD/.lake/build/lib/lean"
for task_package in /home/hbox/workbox/codex-unified-integration-20261003/src/.lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$task_package/.lake/build/lib/lean"
done
task_lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
"$task_lean" -j 2 Compiler/BendLogicSerialize.lean -o .lake/build/lib/lean/Compiler/BendLogicSerialize.olean
"$task_lean" -j 2 Compiler/BendLogicMux.lean -o .lake/build/lib/lean/Compiler/BendLogicMux.olean
"$task_lean" -j 2 Compiler/BendLogicMuxEntry.lean -o .lake/build/lib/lean/Compiler/BendLogicMuxEntry.olean
"$task_lean" -j 2 Compiler/BendLogicSignedSemantics.lean -o .lake/build/lib/lean/Compiler/BendLogicSignedSemantics.olean
"$task_lean" -j 2 --run Host/BendLogicMuxEmit.lean > ../mux-artifact.json
python3 -c 'import json; json.load(open("../mux-artifact.json"))'
sha256sum Compiler/BendLogicMuxEntry.lean Compiler/BendLogicSerialize.lean Compiler/BendLogicMux.lean Compiler/BendLogicSignedSemantics.lean Host/BendLogicMuxEmit.lean ../mux-artifact.json
printf 'BEND-MUX SCOPED CHECK PASS\n'
