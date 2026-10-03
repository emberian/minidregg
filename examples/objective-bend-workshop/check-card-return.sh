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
[[ ! -L "$task_olean/Compiler/WorkshopCardReturn.olean" ]] || { printf 'own output is a foreign symlink\n' >&2; exit 2; }
# Lean resolves namespace directories from one root. Build a local overlay of
# read-only warm files so our own Compiler output does not hide sibling imports.
python3 - "$task_olean" <<'PY'
from pathlib import Path
import os,sys
out=Path(sys.argv[1])
for entry in os.environ['LEAN_PATH'].split(':'):
    root=Path(entry)
    if not root.is_dir(): raise SystemExit('missing qualified warm root: '+entry)
    for source in root.rglob('*'):
        if not source.is_file(): continue
        relative=source.relative_to(root)
        if str(relative).startswith('Compiler/WorkshopCardReturn.'): continue
        dest=out/relative
        dest.parent.mkdir(parents=True,exist_ok=True)
        if not dest.exists() and not dest.is_symlink(): dest.symlink_to(source)
PY
export LEAN_PATH="$task_olean:$LEAN_PATH"
export LEAN_NUM_THREADS=2
cd "$task_repo"
"$task_lean" -j2 Compiler/WorkshopCardReturn.lean -o "$task_olean/Compiler/WorkshopCardReturn.olean"
"$task_lean" -j2 --run examples/objective-bend-workshop/RunCardReturn.lean "$task_complete" "$task_alternate"
printf 'WORKSHOP CARD RETURN CHECK PASS\n'
