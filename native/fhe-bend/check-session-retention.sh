#!/usr/bin/env bash
set -euo pipefail
task_source=/home/hbox/workbox/codex-homomorphic-bend-20261003/src
task_output=/home/hbox/workbox/codex-homomorphic-bend-20261003/artifact-driver-olean
task_common=/home/hbox/workbox/codex-unified-integration-20261003/src
export LEAN_PATH="$task_output"
for task_package in "$task_common"/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$task_package/.lake/build/lib/lean"; done
export LEAN_NUM_THREADS=2
cd "$task_source"
task_lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
"$task_lean" -j 2 Host/BendSessionDriverJson.lean -o "$task_output/Host/BendSessionDriverJson.olean"
printf 'BEND SESSION JSON RETENTION CONSUMER PASS\n'
"$task_lean" -j 2 Host/BendSessionRetentionCheck.lean -o "$task_output/Host/BendSessionRetentionCheck.olean"
"$task_lean" -j 2 --run Host/BendSessionRetentionCheck.lean "$1"
printf 'BEND SESSION RETENTION COHORT CHECK PASS\n'
