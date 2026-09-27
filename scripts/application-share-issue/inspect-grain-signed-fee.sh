#!/bin/sh
# Source-owned read-only fee extraction from the exact retained event-22 Plan.
set -eu
if [ "$#" -ne 1 ]; then
  echo "usage: $0 PLAN.bin" >&2
  exit 2
fi
MINI_LEAN_ROOT=${MINI_LEAN_ROOT:?set source-qualified event-22 Mini Lean root}
FEE_SOURCE=${FEE_SOURCE:?set exact inspect-grain-signed-fee.lean source}
PLAN=$1
for absolute in "$MINI_LEAN_ROOT" "$FEE_SOURCE" "$PLAN"; do
  case "$absolute" in
    /*) ;;
    *) echo "Lean root, source and Plan must be absolute paths" >&2; exit 2 ;;
  esac
done
FEE_SOURCE_SHA=57102608ad0bf6afd470cd8cc74332edacf10c0cce0013cee74f7383cc1bfd88
[ "$(sha256sum "$FEE_SOURCE" | cut -d ' ' -f 1)" = "$FEE_SOURCE_SHA" ] || {
  echo "source-owned grain fee inspector changed" >&2; exit 2;
}
[ -f "$PLAN" ] || { echo "missing retained Plan" >&2; exit 2; }
SEAT=${MINI_LEAN_SEAT:-/tmp/minidregg-overnight-20260926/lean-seat-2}
case "$SEAT" in
  /*) ;;
  *) echo "Lean seat must be absolute" >&2; exit 2 ;;
esac
mkdir "$SEAT" || { echo "Lean seat unavailable" >&2; exit 75; }
cleanup() { rmdir "$SEAT" 2>/dev/null || :; }
trap cleanup EXIT
trap 'exit 143' HUP INT TERM
cd "$MINI_LEAN_ROOT"
LEAN_NUM_THREADS=2 lake env lean --run "$FEE_SOURCE" "$PLAN"
