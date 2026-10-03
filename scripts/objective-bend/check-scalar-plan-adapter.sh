#!/usr/bin/env bash
set -euo pipefail
# Run only under an allocated compiler seat. Dependencies must be qualified
# separately; this script checks one new module and does not invoke Lake builds.
: "${SCALAR_LEAN_BINARY:?Set exact Lean 4.30 compiler executable}"
: "${SCALAR_LEAN_PATH:?Set scoped qualified dependency olean search path}"
: "${SCALAR_OLEAN_DIRECTORY:?Set own writable output directory}"
scalar_threads="${SCALAR_LEAN_THREADS:-2}"
case "$scalar_threads" in 1|2) ;; *) printf "Use one or two allocated threads\n" >&2; exit 2 ;; esac
scalar_repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
mkdir -p "$SCALAR_OLEAN_DIRECTORY/Compiler"
# Lean selects the first package namespace root; populate own read-only
# dependency overlay instead of assuming search-path fallback.
python3 - "$SCALAR_OLEAN_DIRECTORY" "$SCALAR_LEAN_PATH" <<'PY_OVERLAY'
from pathlib import Path
import sys
out=Path(sys.argv[1])
for root in map(Path,sys.argv[2].split(':')):
  for source in root.rglob('*'):
    if not source.is_file(): continue
    destination=out/source.relative_to(root)
    destination.parent.mkdir(parents=True,exist_ok=True)
    if not destination.exists() and not destination.is_symlink():
      destination.symlink_to(source)
PY_OVERLAY
export LEAN_PATH="$SCALAR_OLEAN_DIRECTORY:$SCALAR_LEAN_PATH"
export LEAN_NUM_THREADS="$scalar_threads"
cd "$scalar_repo"
"$SCALAR_LEAN_BINARY" -j "$scalar_threads" Compiler/BendScalarPlanAdapter.lean \
  -o "$SCALAR_OLEAN_DIRECTORY/Compiler/BendScalarPlanAdapter.olean"
printf "BEND-SCALAR SCOPED CHECK PASS\n"
