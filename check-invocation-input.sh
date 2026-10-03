#!/usr/bin/env bash
set -euo pipefail
task_source=/home/hbox/workbox/codex-bend-world-20261003/src
task_output=/tank/dregg-build/codex-bend-native-core-next-20261003/olean
cd "$task_source"
mkdir -p "$task_output"
task_lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
task_common=/home/hbox/workbox/codex-unified-integration-20261003/src
BEND_SOURCE_OLEANS=/tank/dregg-build/codex-private-lifecycle-20261003/olean
python3 - "$task_output" "$task_source/.lake/build/lib/lean" "$BEND_SOURCE_OLEANS" "$task_common/../scoped-olean" "$task_common/.lake/build/lib/lean" /home/hbox/workbox/codex-bend-logic-20261003/src/.lake/build/lib/lean <<'PY_OVERLAY'
from pathlib import Path
import sys
out=Path(sys.argv[1])
for root in map(Path,sys.argv[2:]):
 for source in root.rglob('*.olean'):
  target=out/source.relative_to(root)
  target.parent.mkdir(parents=True,exist_ok=True)
  if not target.exists() and not target.is_symlink(): target.symlink_to(source)
PY_OVERLAY
export LEAN_PATH="$task_output"
for task_package in "$task_common"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$task_package/.lake/build/lib/lean"; done
export LEAN_NUM_THREADS=2
for task_module in Kernel/BendInvocationInput; do
 [[ ! -L "$task_output/$task_module.olean" ]] || rm "$task_output/$task_module.olean"
 "$task_lean" -j 2 "$task_module.lean" -o "$task_output/$task_module.olean"
 printf 'BEND-INVOCATION-INPUT SCOPED PASS %s\n' "$task_module"
done
printf 'BEND-INVOCATION-INPUT SCOPED CHECK PASS\n'
