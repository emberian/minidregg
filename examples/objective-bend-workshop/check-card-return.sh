#!/usr/bin/env bash
set -euo pipefail
# Run through the project's bounded build lease. LEAN_PATH must point at exact
# already-qualified dependencies; this script never rebuilds their closure.
if [[ $# != 3 ]]; then
  printf 'usage: check-card-return.sh OWN_OLEAN_DIR complete.bendtt alternate.bendtt\n' >&2
  exit 2
fi
: "${LEAN_PATH:?Provide exact qualified warm imports}"
task_olean=$1
task_complete=$2
task_alternate=$3
[[ "$task_olean" = /* ]] || { printf 'OWN_OLEAN_DIR must be absolute\n' >&2; exit 2; }
task_repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
task_lean=${LEAN_BIN:-lean}
mkdir -p "$task_olean/Compiler"
export LEAN_PATH="$task_olean:$LEAN_PATH"
export LEAN_NUM_THREADS=2
cd "$task_repo"
"$task_lean" -j2 Compiler/WorkshopCardReturn.lean -o "$task_olean/Compiler/WorkshopCardReturn.olean"
"$task_lean" -j2 --run examples/objective-bend-workshop/RunCardReturn.lean "$task_complete" "$task_alternate"
printf 'WORKSHOP CARD RETURN CHECK PASS\n'
