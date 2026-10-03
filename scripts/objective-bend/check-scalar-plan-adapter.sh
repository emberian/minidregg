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
export LEAN_PATH="$SCALAR_OLEAN_DIRECTORY:$SCALAR_LEAN_PATH"
export LEAN_NUM_THREADS="$scalar_threads"
cd "$scalar_repo"
"$SCALAR_LEAN_BINARY" -j "$scalar_threads" Compiler/BendScalarPlanAdapter.lean \
  -o "$SCALAR_OLEAN_DIRECTORY/Compiler/BendScalarPlanAdapter.olean"
printf "BEND-SCALAR SCOPED CHECK PASS\n"
