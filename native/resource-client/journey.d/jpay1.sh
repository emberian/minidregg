#!/usr/bin/env bash
# J-PAY-1 (PAY.md §6 row P1): the pay watcher on its fixtures, no network, no keys.
#
# For every vector in native/pay-watcher/fixtures/<vector>/ it runs the watcher binary in
# fixture mode against the vector's two endpoints and checks the binary's exit code, the
# observation count, and the SET of event reasons against the vector's expect.json. Then:
#   happy-64byte  every observation's signature is 128 hex digits (the 64 raw bytes)
#   restart       two runs on the same answers and receipts give byte-identical files
# One row per vector on stdout.
#
# Journey hook contract (native/resource-client/journey.sh header): exit 0 = PASS; the LAST
# stdout line is the deciding artifact's absolute path (a file holding the rows and the
# verdict); the last stderr line is the verdict, `J-PAY-1 PASS n/n` or
# `J-PAY-1 FAIL <first failing vector>: <why>`.
#
# The binary is PAY_WATCHER_BIN, else native/pay-watcher/target/release/pay-watcher. A missing
# binary FAILS; absence is never a pass. Requires jq, cmp.

set -u
umask 077
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../../.." && pwd)
CRATE=$REPO/native/pay-watcher
FIX=$CRATE/fixtures
BIN=${PAY_WATCHER_BIN:-$CRATE/target/release/pay-watcher}
if [ -n "${JOURNEY_STEP_DIR:-}" ]; then
  D=$JOURNEY_STEP_DIR/jpay1
  mkdir -p "$D"
else
  D=$(mktemp -d "${TMPDIR:-/tmp}/jpay1.XXXXXX")
fi
RESULT=$D/jpay1-result.txt
: >"$RESULT"

finish() { # finish EXIT VERDICT
  echo "$2" | tee -a "$RESULT"
  echo "$2" >&2
  echo "$RESULT"
  exit "$1"
}
row() { printf '%-24s %-4s %s\n' "$1" "$2" "$3" | tee -a "$RESULT"; }

for tool in jq cmp; do
  command -v "$tool" >/dev/null 2>&1 || finish 1 "J-PAY-1 FAIL setup: $tool is required"
done
[ -x "$BIN" ] || finish 1 "J-PAY-1 FAIL setup: pay-watcher binary missing at $BIN"
[ -d "$FIX" ] || finish 1 "J-PAY-1 FAIL setup: fixtures missing at $FIX"

watch() { # watch VECTOR OUTDIR -> exit code
  mkdir -p "$2"
  env -u PAY_RPC_ENDPOINTS "$BIN" --config "$FIX/$1/config.json" --out "$2" \
    --rpc-fixture "$FIX/$1/endpoints/a" --rpc-fixture "$FIX/$1/endpoints/b" \
    >"$2/stdout" 2>"$2/stderr"
}

total=0
passed=0
first_fail=
fail_row() { # fail_row NAME WHY
  row "$1" FAIL "$2"
  [ -n "$first_fail" ] || first_fail="$1: $2"
}

for dir in "$FIX"/*/; do
  v=$(basename "$dir")
  [ -f "$dir/expect.json" ] || continue
  total=$((total + 1))
  out=$D/$v
  watch "$v" "$out"
  rc=$?
  want_rc=$(jq -r .exit "$dir/expect.json")
  want_n=$(jq -r .observations "$dir/expect.json")
  want_r=$(jq -r '.reasons | sort | join(",")' "$dir/expect.json")
  if [ ! -f "$out/observations.json" ] || [ ! -f "$out/events.json" ]; then
    fail_row "$v" "no output (exit $rc): $(tail -1 "$out/stderr")"
    continue
  fi
  got_n=$(jq '.observations | length' "$out/observations.json")
  got_r=$(jq -r '[.[].reason] | unique | join(",")' "$out/events.json")
  if [ "$rc" = "$want_rc" ] && [ "$got_n" = "$want_n" ] && [ "$got_r" = "$want_r" ]; then
    passed=$((passed + 1))
    row "$v" PASS "exit=$rc observations=$got_n reasons=${got_r:-none}"
  else
    fail_row "$v" "exit=$rc/$want_rc observations=$got_n/$want_n reasons=${got_r:-none}/${want_r:-none}"
  fi
done

total=$((total + 1))
bad=$(jq '[.observations[] | select((.signature | test("^[0-9a-f]{128}$")) | not)] | length' \
  "$D/happy/observations.json" 2>/dev/null)
if [ "$bad" = 0 ] && [ "$(jq '.observations | length' "$D/happy/observations.json")" -gt 0 ]; then
  passed=$((passed + 1))
  row happy-64byte PASS "every signature is 64 raw bytes (128 hex)"
else
  fail_row happy-64byte "signature not 64 raw bytes in happy/observations.json"
fi

total=$((total + 1))
watch happy "$D/restart"
if cmp -s "$D/happy/observations.json" "$D/restart/observations.json" \
  && cmp -s "$D/happy/events.json" "$D/restart/events.json"; then
  passed=$((passed + 1))
  row restart PASS "second run byte-identical ($(wc -c <"$D/restart/observations.json") bytes)"
else
  fail_row restart "second run on the same fixture differs"
fi

if [ "$passed" = "$total" ]; then
  finish 0 "J-PAY-1 PASS $passed/$total"
fi
finish 1 "J-PAY-1 FAIL $first_fail"
