#!/usr/bin/env bash
set -euo pipefail
# Captain invokes this only with the active shared compiler seat.
cd /home/hbox/workbox/codex-bend-logic-20261003/src
task_lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
task_common=/home/hbox/workbox/codex-unified-integration-20261003/src
: "${BEND_SOURCE_OLEANS:?Set to the captain-checked BendTTSource/BendLiveMachine olean root}"
mkdir -p .lake/build/lib/lean/Compiler .lake/build/lib/lean/Host
# Lean resolves a module root once; own Compiler output must overlay its imports.
python3 - "$task_common/.lake/build/lib/lean" "$BEND_SOURCE_OLEANS" "$PWD/.lake/build/lib/lean" <<'PY_OVERLAY'
from pathlib import Path
import sys
out=Path(sys.argv[3])
for root in map(Path,sys.argv[1:3]):
  for src in root.rglob('*'):
    if not src.is_file(): continue
    dest=out/src.relative_to(root)
    dest.parent.mkdir(parents=True,exist_ok=True)
    if not dest.exists() and not dest.is_symlink(): dest.symlink_to(src)
PY_OVERLAY
task_paths="$PWD/.lake/build/lib/lean:$BEND_SOURCE_OLEANS:$task_common/.lake/build/lib/lean"
for task_package in "$task_common"/.lake/packages/*; do
  task_paths="$task_paths:$task_package/.lake/build/lib/lean"
done
export LEAN_PATH="$task_paths"
export LEAN_NUM_THREADS=2
"$task_lean" -j 2 Compiler/BendLogicCase.lean -o .lake/build/lib/lean/Compiler/BendLogicCase.olean
"$task_lean" -j 2 Compiler/BendLogicBFVPlain.lean -o .lake/build/lib/lean/Compiler/BendLogicBFVPlain.olean
"$task_lean" -j 2 Compiler/BendLogicSpecialization.lean -o .lake/build/lib/lean/Compiler/BendLogicSpecialization.olean
"$task_lean" -j 2 Compiler/BendLogicTrace.lean -o .lake/build/lib/lean/Compiler/BendLogicTrace.olean
"$task_lean" -j 2 --run Host/BendLogicEmit.lean > ../artifact.json
python3 -c 'import json; json.load(open("../artifact.json"))'
sha256sum Compiler/BendLogicBFVPlain.lean Compiler/BendLogicCase.lean Compiler/BendLogicSpecialization.lean Compiler/BendLogicTrace.lean Host/BendLogicEmit.lean ../artifact.json
printf 'BEND-LOGIC SCOPED CHECK PASS\n'
