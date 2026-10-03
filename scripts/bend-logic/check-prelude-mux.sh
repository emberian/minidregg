#!/usr/bin/env bash
set -euo pipefail
cd /home/hbox/workbox/codex-bend-logic-20261003/src
export LEAN_NUM_THREADS=2
export LEAN_PATH="$PWD/.lake/build/lib/lean"
for task_package in /home/hbox/workbox/codex-unified-integration-20261003/src/.lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$task_package/.lake/build/lib/lean"
done
task_lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
# Run only after representation owner's choose module is qualified in this overlay.
"$task_lean" -j 2 Compiler/BendLogicPreludeMux.lean -o .lake/build/lib/lean/Compiler/BendLogicPreludeMux.olean
"$task_lean" -j 2 --run Host/BendLogicPreludeMuxEmit.lean > ../prelude-mux-artifact.json
python3 -c 'import json; json.load(open("../prelude-mux-artifact.json"))'
sha256sum Compiler/BendLogicPreludeMux.lean Host/BendLogicPreludeMuxEmit.lean ../BoolChooseSource.bend ../BoolChooseSource.bendtt ../prelude-mux-artifact.json
printf 'BEND-PRELUDE-MUX SCOPED CHECK PASS\n'
