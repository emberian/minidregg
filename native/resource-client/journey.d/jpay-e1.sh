#!/usr/bin/env bash
# J-PAY-E1 (PAY.md §11.9 row P1b): the pay watcher's enrollment index, on fixtures, no network,
# no keys. For every native/pay-watcher/fixtures/enrol-*/ vector (a private COPY: the watcher
# writes its enrollment cursor beside the config) it runs the binary against the vector's two
# endpoints and checks the exit code, the observation count, the SET of event reasons, and the
# per-observation memo verdict ("memo" = memo bytes emitted, "none" = memo and memoError null,
# else the memoError) against expect.json. Then:
#   memo-hex        every emitted memo is lowercase hex that decodes to the fixture's 400-byte
#                   `enrol:v1:` text; memo XOR memoError; ordinary rows carry neither
#   cursor-phase1   300 dust transfers settle; the cursor file names the newest
#   cursor-phase2   the next run lists from that cursor only and emits the late enrollment
#   restart         two runs of enrol-happy give byte-identical observations, events and cursor
#
# Journey hook contract (native/resource-client/journey.sh header): exit 0 = PASS; the LAST
# stdout line is the deciding artifact's absolute path; the last stderr line is the verdict,
# `J-PAY-E1 PASS n/n` or `J-PAY-E1 FAIL <first failing row>: <why>`.
#
# The binary is PAY_WATCHER_BIN, else native/pay-watcher/target/release/pay-watcher. A missing
# binary FAILS. Requires jq, cmp, xxd.

set -u
umask 077
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../../.." && pwd)
CRATE=$REPO/native/pay-watcher
FIX=$CRATE/fixtures
BIN=${PAY_WATCHER_BIN:-$CRATE/target/release/pay-watcher}
if [ -n "${JOURNEY_STEP_DIR:-}" ]; then
  D=$JOURNEY_STEP_DIR/jpay-e1
  mkdir -p "$D"
else
  D=$(mktemp -d "${TMPDIR:-/tmp}/jpay-e1.XXXXXX")
fi
RESULT=$D/jpay-e1-result.txt
: >"$RESULT"

finish() { # finish EXIT VERDICT
  echo "$2" | tee -a "$RESULT"
  echo "$2" >&2
  echo "$RESULT"
  exit "$1"
}
row() { printf '%-24s %-4s %s\n' "$1" "$2" "$3" | tee -a "$RESULT"; }

for tool in jq cmp xxd; do
  command -v "$tool" >/dev/null 2>&1 || finish 1 "J-PAY-E1 FAIL setup: $tool is required"
done
[ -x "$BIN" ] || finish 1 "J-PAY-E1 FAIL setup: pay-watcher binary missing at $BIN"
[ -d "$FIX/enrol-happy" ] || finish 1 "J-PAY-E1 FAIL setup: enrollment fixtures missing at $FIX"

watch() { # watch VECTOR_DIR OUTDIR -> exit code (runs on the directory it is given)
  mkdir -p "$2"
  env -u PAY_RPC_ENDPOINTS "$BIN" --config "$1/config.json" --out "$2" \
    --rpc-fixture "$1/endpoints/a" --rpc-fixture "$1/endpoints/b" \
    >"$2/stdout" 2>"$2/stderr"
}

total=0
passed=0
first_fail=
fail_row() { # fail_row NAME WHY
  row "$1" FAIL "$2"
  [ -n "$first_fail" ] || first_fail="$1: $2"
}
pass_row() { passed=$((passed + 1)); row "$1" PASS "$2"; }

check_vector() { # check_vector NAME VECTOR_DIR OUTDIR
  local v=$1 dir=$2 out=$3 rc want_rc want_n want_r want_m got_n got_r got_m
  total=$((total + 1))
  watch "$dir" "$out"
  rc=$?
  want_rc=$(jq -r .exit "$dir/expect.json")
  want_n=$(jq -r .observations "$dir/expect.json")
  want_r=$(jq -r '.reasons | sort | join(",")' "$dir/expect.json")
  want_m=$(jq -r '.memos | join(",")' "$dir/expect.json")
  if [ ! -f "$out/observations.json" ] || [ ! -f "$out/events.json" ]; then
    fail_row "$v" "no output (exit $rc): $(tail -1 "$out/stderr")"
    return
  fi
  got_n=$(jq '.observations | length' "$out/observations.json")
  got_r=$(jq -r '[.[].reason] | unique | join(",")' "$out/events.json")
  got_m=$(jq -r '[.observations[] | if .memo != null then "memo" elif .memoError == null then "none"
    else .memoError end] | join(",")' "$out/observations.json")
  if [ "$rc" = "$want_rc" ] && [ "$got_n" = "$want_n" ] && [ "$got_r" = "$want_r" ] \
    && [ "$got_m" = "$want_m" ]; then
    pass_row "$v" "exit=$rc observations=$got_n reasons=${got_r:-none} memos=${got_m:-none}"
  else
    fail_row "$v" "exit=$rc/$want_rc observations=$got_n/$want_n reasons=${got_r:-none}/${want_r:-none} memos=${got_m:-none}/${want_m:-none}"
  fi
}

for dir in "$FIX"/enrol-*/; do
  v=$(basename "$dir")
  [ -f "$dir/expect.json" ] || continue
  rm -rf "$D/$v.in"
  cp -R "$dir" "$D/$v.in"
  check_vector "$v" "$D/$v.in" "$D/$v"
done

# memo-hex: the memo field is the chain's bytes, hex; it decodes to the text the fixture carries.
total=$((total + 1))
bad=$(jq '[.observations[] | select(
    (.memo != null and .memoError != null)
    or (.index != 0 and (.memo != null or .memoError != null))
    or (.memo != null and (.memo | test("^([0-9a-f]{2})+$") | not)))] | length' \
  "$D/enrol-happy/observations.json" 2>/dev/null)
first_memo=$(jq -r '[.observations[] | select(.memo != null)][0].memo' "$D/enrol-happy/observations.json" 2>/dev/null)
text=$(printf '%s' "$first_memo" | xxd -r -p)
if [ "$bad" = 0 ] && [ "${#text}" = 400 ] && [ "${text#enrol:v1:}" != "$text" ]; then
  pass_row memo-hex "memo is lowercase hex of the 400-byte enrol:v1: text; ordinary rows carry none"
else
  fail_row memo-hex "enrol-happy memo fields off-contract (bad=${bad:-?} len=${#text})"
fi

# The cursor: two runs over one cursor file, in a private copy.
rm -rf "$D/enrol-cursor.in"
cp -R "$FIX/enrol-cursor" "$D/enrol-cursor.in"
check_vector cursor-phase1 "$D/enrol-cursor.in/phase1" "$D/cursor-phase1"
want_c=$(jq -S -c .cursorAfter "$FIX/enrol-cursor/phase1/expect.json")
got_c=$(jq -S -c .cursors "$D/enrol-cursor.in/cursor.json" 2>/dev/null)
total=$((total + 1))
floors=$(jq '[.[] | select(.reason == "belowJournalFloor")] | length' "$D/cursor-phase1/events.json" 2>/dev/null)
if [ "$got_c" = "$want_c" ] && [ "$floors" = 300 ]; then
  pass_row cursor-file "300 dust recorded once; cursor.json names the newest ($(wc -c <"$D/enrol-cursor.in/cursor.json") bytes)"
else
  fail_row cursor-file "cursor after phase 1: ${got_c:-absent} want $want_c (dust events ${floors:-?})"
fi
check_vector cursor-phase2 "$D/enrol-cursor.in/phase2" "$D/cursor-phase2"

total=$((total + 1))
rm -rf "$D/restart.in"
cp -R "$FIX/enrol-happy" "$D/restart.in"
watch "$D/restart.in" "$D/restart"
if cmp -s "$D/enrol-happy/observations.json" "$D/restart/observations.json" \
  && cmp -s "$D/enrol-happy/events.json" "$D/restart/events.json" \
  && cmp -s "$D/enrol-happy.in/enrol-cursor.json" "$D/restart.in/enrol-cursor.json"; then
  pass_row restart "second run byte-identical ($(wc -c <"$D/restart/observations.json") bytes)"
else
  fail_row restart "second run of enrol-happy differs"
fi

if [ "$passed" = "$total" ]; then
  finish 0 "J-PAY-E1 PASS $passed/$total"
fi
finish 1 "J-PAY-E1 FAIL $first_fail"
