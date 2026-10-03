#!/usr/bin/env bash
set -euo pipefail
# Captain invokes with a shared compiler seat; no full native build.
cd /home/hbox/workbox/codex-bend-world-20261003/src
task_lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
task_common=/home/hbox/workbox/codex-unified-integration-20261003/src
: "${BEND_SOURCE_OLEANS:?Set to captain-checked Bend source olean root}"
mkdir -p .lake/build/lib/lean/Compiler .lake/build/lib/lean/Kernel
python3 - "$task_common/.lake/build/lib/lean" "$BEND_SOURCE_OLEANS" "$task_common/../scoped-olean" "$PWD/.lake/build/lib/lean" <<'PY_OVERLAY'
from pathlib import Path
import sys
out=Path(sys.argv[4])
for root in map(Path,sys.argv[1:4]):
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
for task_module in Compiler/BendInvocation Compiler/BendMethodAttribution Kernel/BendOpaqueResultReceiver Kernel/BendReturnRelease; do
  "$task_lean" -j 2 "$task_module.lean" -o ".lake/build/lib/lean/$task_module.olean"
  printf 'BEND-RETURN SCOPED PASS %s\n' "$task_module"
done
printf 'BEND-RETURN SCOPED CHECK PASS\n'
