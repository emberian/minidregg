#!/bin/sh
# Private read-only Lean inspection of the exact share-issue plan retained by
# custody. This launcher does not parse or reprice the birth in shell.
set -eu
if [ "$#" -ne 1 ]; then
  echo "usage: $0 PLAN.bin" >&2
  exit 2
fi
MINI_LEAN_ROOT=${MINI_LEAN_ROOT:?set source-qualified Mini Lean build root}
FEE_SOURCE=${FEE_SOURCE:?set exact inspect-signed-fee.lean source}
PLAN=$1
for absolute in "$MINI_LEAN_ROOT" "$FEE_SOURCE" "$PLAN"; do
  case "$absolute" in
    /*) ;;
    *) echo "Lean root, source and plan must be absolute paths" >&2; exit 2 ;;
  esac
done
FEE_SOURCE_SHA=bc2acd4bfeb698c5ebc939eb0694c4c634f437dc6f9a9f3066774ec978f403cc
[ "$(sha256sum "$FEE_SOURCE" | cut -d ' ' -f 1)" = "$FEE_SOURCE_SHA" ] || {
  echo "source-owned fee inspector changed" >&2; exit 2;
}
[ -f "$PLAN" ] || { echo "missing retained plan" >&2; exit 2; }
SEAT=${MINI_LEAN_SEAT:-/tmp/minidregg-overnight-20260926/lean-seat-2}
case "$SEAT" in
  /*) ;;
  *) echo "Lean seat must be an absolute path" >&2; exit 2 ;;
esac
mkdir "$SEAT" || { echo "Lean seat unavailable" >&2; exit 75; }
trap 'rmdir "$SEAT"' EXIT HUP INT TERM
cd "$MINI_LEAN_ROOT"
LEAN_NUM_THREADS=2 lake env lean --run "$FEE_SOURCE" "$PLAN"
