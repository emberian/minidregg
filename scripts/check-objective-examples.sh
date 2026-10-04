#!/usr/bin/env bash
# Objective Bend reference examples: typed, asserted, regenerated from source.
#
# Each row is examples/objective-bend-world/reference/<Name>.lean, which embeds
# <Name>.typed.json (the typed core packet the CURRENT front end produces for the
# preview-cohort.json row <Name>) and pins the observation as a theorem. A row fails when
#   1. the committed packet differs from what the Lean front end (capture -> parser ->
#      elaborator) now produces (refresh with --refresh), or
#   2. the driver does not elaborate (its `native_decide` theorem or `#assert_compiled`
#      pin fails), or
#   3. the summary the driver prints differs from the cohort row's expectation.
# A final row runs the whole preview cohort (tests/objective-bend-source/check-preview.ts),
# which covers the sources that have no driver of their own; --no-cohort skips it.
#
# usage:  scripts/check-objective-examples.sh [--refresh] [--no-cohort]
# env:    LAKE_ROOT  a built tree providing .lake/build/lib/lean and `lake env` (default: this repo)
#         BUN        bun binary (default: bun)
#         WORK       new directory for outputs (default: a fresh mktemp -d)
# Every module the examples import (the front end, Host.ObjectiveBendPreview,
# Theory.AssertCompiled) is in the default build; LAKE_ROOT is only read.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
refresh=0 cohort=1
for arg in "$@"; do case "$arg" in
  --refresh) refresh=1 ;; --no-cohort) cohort=0 ;;
  *) echo "usage: $0 [--refresh] [--no-cohort]" >&2; exit 2 ;; esac; done
lake_root=${LAKE_ROOT:-$repo}
bun=${BUN:-bun}
work=${WORK:-$(mktemp -d "${TMPDIR:-/tmp}/objective-examples.XXXXXX")}
[ -z "$(ls -A "$work" 2>/dev/null)" ] || { echo "WORK must be empty or new: $work" >&2; exit 2; }
mkdir -p "$work"
export LEAN_NUM_THREADS=2

examples=(GenericExtensionReuse EvenOddTen TwiceReview LazySharedField)

root_olean="$lake_root/.lake/build/lib/lean"
lean_path=$(cd "$lake_root" && lake env printenv LEAN_PATH)
lean=$(cd "$lake_root" && lake env which lean)
[ -f "$root_olean/Host/ObjectiveBendFrontEnd.olean" ] || { echo "no built front end under $root_olean" >&2; exit 2; }

status=0
results="$work/results.txt"
: > "$results"
row() { echo "$1" | tee -a "$results"; }

# 1. Typed packets from the current front end (also writes <Name>.expected.json from the cohort).
mode=check; [ "$refresh" = 1 ] && mode=refresh
if (cd "$repo" && "$bun" scripts/objective-examples.ts "$mode" "$work/gen" "$lean" "$lean_path" "${examples[@]}") 2> "$work/gen.err"; then
  row "PASS packets ($mode): ${examples[*]}"
else
  row "FAIL packets ($mode): $(tr '\n' ' ' < "$work/gen.err")"; status=1
fi

# 2 and 3. One row per example.
for name in "${examples[@]}"; do
  driver="$repo/examples/objective-bend-world/reference/$name.lean"
  out="$work/$name.driver.out"
  if ! LEAN_PATH="$lean_path" "$lean" -j 2 "$driver" > "$out" 2> "$work/$name.driver.err"; then
    row "FAIL $name: driver did not elaborate (see $work/$name.driver.err, $out)"; status=1; continue
  fi
  if python3 - "$out" "$work/gen/$name.expected.json" <<'PY'
import json,sys
printed=[json.loads(l) for l in open(sys.argv[1]) if l.startswith("{")]
expected=json.load(open(sys.argv[2]))
sys.exit(0 if printed==[expected] else 1)
PY
  then row "PASS $name"
  else row "FAIL $name: printed summary differs from the cohort expectation ($out vs $work/gen/$name.expected.json)"; status=1; fi
done

# Optional: the whole cohort.
if [ "$cohort" = 1 ]; then
  if (cd "$repo" && "$bun" tests/objective-bend-source/check-preview.ts tests/objective-bend-source/preview-cohort.json "$work/cohort" "$lean" "$lean_path") > "$work/cohort.out" 2> "$work/cohort.err"; then
    row "PASS cohort: $(cat "$work/cohort.out" | head -c 300)"
  else row "FAIL cohort (see $work/cohort.err)"; status=1; fi
fi

echo "results: $results"
exit $status
