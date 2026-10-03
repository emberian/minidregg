#!/usr/bin/env bash
set -euo pipefail
# Scoped portable warm-only checks. Caller owns the named build/auxiliary seat.
# BEND_LOGIC_SOURCE_ROOT is the checkout root; BEND_LOGIC_OUTPUT_ROOT is owned
# pre-populated overlay containing qualified dependencies. No dependency builds.
: "${BEND_LOGIC_SOURCE_ROOT:?Set source checkout root}"
: "${BEND_LOGIC_OUTPUT_ROOT:?Set owned qualified dependency overlay}"
: "${BEND_LOGIC_LEAN:?Set pinned Lean 4.30 binary}"
cd "$BEND_LOGIC_SOURCE_ROOT"
export LEAN_NUM_THREADS=2
export LEAN_PATH="$BEND_LOGIC_OUTPUT_ROOT${BEND_LOGIC_PACKAGE_PATHS:+:$BEND_LOGIC_PACKAGE_PATHS}"
case "${1:-}" in
  prelude-case)
    "$BEND_LOGIC_LEAN" -j 2 Compiler/BendLogicPreludeCase.lean -o "$BEND_LOGIC_OUTPUT_ROOT/Compiler/BendLogicPreludeCase.olean"
    "$BEND_LOGIC_LEAN" -j 2 --run Host/BendLogicPreludeEmit.lean > "$BEND_LOGIC_OUTPUT_ROOT/prelude-artifact.json"
    python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$BEND_LOGIC_OUTPUT_ROOT/prelude-artifact.json"
    ;;
  prelude-mux)
    "$BEND_LOGIC_LEAN" -j 2 Compiler/BendLogicPreludeMux.lean -o "$BEND_LOGIC_OUTPUT_ROOT/Compiler/BendLogicPreludeMux.olean"
    "$BEND_LOGIC_LEAN" -j 2 --run Host/BendLogicPreludeMuxEmit.lean > "$BEND_LOGIC_OUTPUT_ROOT/prelude-mux-artifact.json"
    python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$BEND_LOGIC_OUTPUT_ROOT/prelude-mux-artifact.json"
    ;;
  nat-add)
    "$BEND_LOGIC_LEAN" -j 2 Compiler/BendLogicNatAdd.lean -o "$BEND_LOGIC_OUTPUT_ROOT/Compiler/BendLogicNatAdd.olean"
    ;;
  *) echo 'Expected prelude-case, prelude-mux or nat-add' >&2; exit 2 ;;
esac
printf 'BEND-LOGIC PORTABLE SCOPED CHECK PASS\n'
