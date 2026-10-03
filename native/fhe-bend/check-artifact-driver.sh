#!/usr/bin/env bash
set -euo pipefail
task_source=/home/hbox/workbox/codex-homomorphic-bend-20261003/src
task_output=/home/hbox/workbox/codex-homomorphic-bend-20261003/artifact-driver-olean
task_common=/home/hbox/workbox/codex-unified-integration-20261003/src
mkdir -p "$task_output"
python3 - "$task_output" /tank/dregg-build/codex-bend-binding-20261003/olean /home/hbox/workbox/codex-homomorphic-bend-20261003/driver-olean /home/hbox/workbox/codex-bend-scalar-20261003/olean "$task_source/.lake/build/lib/lean" <<'OVERLAY'
import sys
from pathlib import Path
out=Path(sys.argv[1])
owned={'Host/BendFheArtifact.olean','Host/BendFheArtifactCheck.olean','Host/BendSessionDriver.olean','Host/BendSessionCursor.olean','Host/BendSessionDriverJson.olean'}
for root in map(Path,sys.argv[2:]):
 for source in root.rglob('*.olean'):
  relative=source.relative_to(root)
  if str(relative) in owned: continue
  target=out/relative
  target.parent.mkdir(parents=True,exist_ok=True)
  if not target.exists() and not target.is_symlink(): target.symlink_to(source)
OVERLAY
export LEAN_PATH="$task_output"
for task_package in "$task_common"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$task_package/.lake/build/lib/lean"; done
export LEAN_NUM_THREADS=2
cd "$task_source"
task_lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
for task_module in Host/BendFheArtifact Host/BendFheArtifactCheck Host/BendSessionDriver Host/BendSessionCursor Host/BendSessionDriverJson; do
 mkdir -p "$task_output/$(dirname "$task_module")"
 "$task_lean" -j 2 "$task_module.lean" -o "$task_output/$task_module.olean"
 printf 'BEND-FHE ARTIFACT/DRIVER PASS %s\n' "$task_module"
done
"$task_lean" -j 2 --run Host/BendFheArtifactCheck.lean /home/hbox/workbox/codex-bend-logic-20261003/natural-expression-artifact.json /home/hbox/workbox/codex-authored-workshop-20261003/tooling/bend.ts /home/hbox/workbox/codex-authored-workshop-20261003/tooling/safe.ts "$task_common/vendor/bend/bendtt.lean" /home/hbox/workbox/codex-homomorphic-bend-20261003/compiler-closure-v1.bin /home/hbox/workbox/codex-authored-workshop-20261003/tooling/base.bend /home/hbox/workbox/codex-homomorphic-bend-20261003/natural-native-artifact.bin
printf 'BEND-FHE ARTIFACT/DRIVER COHORT CHECK PASS\n'
