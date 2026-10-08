#!/usr/bin/env bash
# One bounded replay, for locating a phase that prevents full acceptance.
set -euo pipefail
[[ $# == 3 ]] || { echo 'usage: diagnose-totality.sh RUNNER STORES.json ROW' >&2; exit 2; }
src=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
evidence=$(mktemp -d "$src/.lake/kp-diag.XXXXXX")
printf 'EVIDENCE %s\n' "$evidence"
jq --arg row "$3" '[.[] | select(.row == $row)]' "$2" >"$evidence/store.json"
if systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 \
    "$1" --row "$3" "$evidence/store.json" >"$evidence/replay.out" 2>"$evidence/replay.err"; then
  rc=0
else
  rc=$?
fi
cat "$evidence/replay.out"
cat "$evidence/replay.err" >&2
exit "$rc"
