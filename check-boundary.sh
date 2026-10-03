#!/usr/bin/env bash
set -euo pipefail
backend=/home/hbox/workbox/codex-private-backend-20261003
warm=/tank/dregg-build/claude-hostnext-r1/main-build/src
custody=/tank/dregg-build/codex-private-lifecycle-20261003/olean
cd "$backend/src"
mkdir -p "$backend/olean/Compiler"
export LEAN_PATH="$backend/olean:$custody:$warm/.lake/build/lib/lean"
for lib in "$warm"/.lake/packages/*/.lake/build/lib/lean; do export LEAN_PATH="$LEAN_PATH:$lib"; done
export LEAN_NUM_THREADS=2
lean=/home/hbox/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
"$lean" -o "$backend/olean/Compiler/PrivateBackendBoundary.olean" Compiler/PrivateBackendBoundary.lean
"$lean" -o "$backend/olean/Compiler/PrivateAllocationReceipt.olean" Compiler/PrivateAllocationReceipt.lean
printf 'PRIVATE-BACKEND LEAN PASS source boundary\n'
"$lean" --run Compiler/PrivateBackendBoundaryFixture.lean > "$backend/evidence/native-wire-fixtures.jsonl"
printf 'PRIVATE-BACKEND LEAN PASS native fixture\n'
