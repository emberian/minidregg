#!/usr/bin/env bash
# K-CLOCK (MUD.md item 3): the deployment's one clock, on the journey's Store.
#
# Journey hook contract (journey.sh header): executed with MINI, SPONSOR_WS,
# NEWCOMER_WS, JOURNEY_WORLD and JOURNEY_STEP_DIR exported, against the live
# journey service. Exit 0 = PASS. The verdict line `K-CLOCK PASS n/n` is the
# last stderr line and the line before the last stdout line; the last stdout
# line is the deciding artifact (rows.tsv).
#
# The ticker is the real one (`mini clock --action tick`, the v1 time source);
# the law is an ordinary resource law over `clock/now`, judged by the Host.
#
# Rows: the genesis clock is 0; a resource whose law is `not (le clock/now 99)`
# ("writable from t=100") is created; a write before any tick is refused by the
# law at admission; the sponsor ticks 100 and the view reads now=100; the same write is
# admitted; a tick at 50 and a tick at 100 are refused clockNotAdvancing; the
# newcomer (no factory control capability) is refused; a wall-clock tick is
# confirmed and the view reads the asserted time.
set -uo pipefail
umask 077
for name in MINI SPONSOR_WS NEWCOMER_WS JOURNEY_WORLD JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jclock: $name is required" >&2; exit 2; fi
done
D=$JOURNEY_STEP_DIR/jclock
[ ! -e "$D" ] || { echo "jclock: refusing to reuse $D" >&2; exit 2; }
mkdir -p "$D"
ROWS=$D/rows.tsv
printf 'verdict\tstep\texpected\tobserved\n' >"$ROWS"
PASS=0 TOTAL=0
CONTROL=$(jq -r .factoryControllerCapability "$JOURNEY_WORLD/genesis.json")

run() {  # run NAME CMD... : stdout/stderr/rc retained under $D
  local name=$1; shift
  "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"
}
rc() { cat "$D/$1.rc"; }
row() {  # row NAME EXPECTED OBSERVED OK(0/1)
  TOTAL=$((TOTAL + 1))
  local v=FAIL; [ "$4" = 0 ] && { v=PASS; PASS=$((PASS + 1)); }
  printf '%s\t%s\t%s\t%s\n' "$v" "$1" "$2" "$3" >>"$ROWS"
  printf '%s\t%s\t%s\n' "$v" "$1" "$3" >&2
}
# reason NAME: the Host's refusal detail of a clock outcome, decoded from hex.
reason() { jq -r '.detail // empty' "$D/$1.out" 2>/dev/null | xxd -r -p 2>/dev/null | sed 's/.*Reject\.//'; }
# refusal NAME: the attempt's retained Host outcome as "phase: detail" (hex-decoded).
refusal() {
  local o=$SPONSOR_WS/attempts/clock-$1/outcome.json
  [ -f "$o" ] || return 0
  printf '%s: %s' "$(jq -r '.phase // empty' "$o" | xxd -r -p)" "$(jq -r '.detail // empty' "$o" | xxd -r -p)"
}
view() { run "$1" "$MINI" clock --action view --workspace "$SPONSOR_WS"; }
now_of() { jq -r .now "$D/$1.out" 2>/dev/null; }
tick() {  # tick NAME WS [--now N]
  local name=$1 ws=$2; shift 2
  run "$name" "$MINI" clock --action tick --workspace "$ws" --control "$CONTROL" "$@"
}
REQ=$D/requests; mkdir -p "$REQ"
printf '%s\n' '{"type":"not","predicate":{"type":"le","slot":"clock/now","value":"99"}}' >"$REQ/from-100.json"
write_req() {  # write_req VALUE : create field 5 of `timed`
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"timed","payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"5"},"value":"%s"}]}}]}\n' "$1"
}
attempt_write() {  # attempt_write ID VALUE -> rc 0 iff admitted and installed
  write_req "$2" >"$REQ/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$REQ/$1.json" --proposal-id "clock-$1" || true
  [ "$(rc "$1-propose")" = 0 ] || return 1
  run "$1-submit" "$MINI" workspace --action submit --dir "$SPONSOR_WS" \
    --intent "$SPONSOR_WS/proposals/clock-$1/intent.json" --attempt "$SPONSOR_WS/attempts/clock-$1"
  [ "$(rc "$1-submit")" = 0 ] && jq -e '.type == "confirmed"' "$SPONSOR_WS/attempts/clock-$1/outcome.json" >/dev/null 2>&1
}
started=$(date +%s)

view v0
row "genesis clock" "now 0 slot 0" "rc=$(rc v0) now=$(now_of v0) slot=$(jq -r .slot "$D/v0.out" 2>/dev/null)" \
  "$([ "$(rc v0)" = 0 ] && [ "$(now_of v0)" = 0 ] && [ "$(jq -r .slot "$D/v0.out")" = 0 ]; echo $?)"

run create "$MINI" workspace --action create --dir "$SPONSOR_WS" --name timed --storage declared --predicate "$REQ/from-100.json"
row "create resource under law not(le clock/now 99)" "created" "rc=$(rc create)" "$([ "$(rc create)" = 0 ]; echo $?)"

attempt_write w-early 1; r=$?; why=$(refusal w-early)
row "create field 5 at clock 0" "refused at admission (the Host names no reason; row 5 is the same create after the tick)" \
  "admitted=$([ $r = 0 ] && echo yes || echo no) outcome=[$why]" \
  "$([ $r != 0 ] && [ "$why" = "admission: request refused" ]; echo $?)"

tick t100 "$SPONSOR_WS" --now 100
view v1
row "sponsor ticks now=100" "confirmed; view now=100 day=0" "rc=$(rc t100) $(jq -r .type "$D/t100.out" 2>/dev/null) now=$(now_of v1) day=$(jq -r .day "$D/v1.out" 2>/dev/null)" \
  "$([ "$(rc t100)" = 0 ] && [ "$(now_of v1)" = 100 ] && [ "$(jq -r .day "$D/v1.out")" = 0 ]; echo $?)"

attempt_write w-after 2; r=$?
row "same create at clock 100" "admitted (confirmed)" "admitted=$([ $r = 0 ] && echo yes || echo no) $(refusal w-after | cut -c1-120)" "$([ $r = 0 ]; echo $?)"

tick t50 "$SPONSOR_WS" --now 50
row "tick behind: now=50" "refused clockNotAdvancing" "rc=$(rc t50) $(reason t50)" \
  "$([ "$(rc t50)" != 0 ] && [ "$(reason t50)" = clockNotAdvancing ]; echo $?)"
tick t100b "$SPONSOR_WS" --now 100
row "tick at the current time: now=100" "refused clockNotAdvancing" "rc=$(rc t100b) $(reason t100b)" \
  "$([ "$(rc t100b)" != 0 ] && [ "$(reason t100b)" = clockNotAdvancing ]; echo $?)"

tick tnew "$NEWCOMER_WS" --now 150
row "newcomer (no factory control) ticks now=150" "refused capabilityRejected" "rc=$(rc tnew) $(reason tnew)" \
  "$([ "$(rc tnew)" != 0 ] && [ "$(reason tnew)" = capabilityRejected ]; echo $?)"

view v2
row "clock after refusals" "now=100" "now=$(now_of v2)" "$([ "$(now_of v2)" = 100 ]; echo $?)"

wall=$(date +%s)
tick twall "$SPONSOR_WS"
view v3
asserted=$(jq -r .asserted.now "$D/twall.out" 2>/dev/null)
row "wall-clock tick (the v1 ticker)" "confirmed; view now = asserted ≈ date +%s" \
  "rc=$(rc twall) asserted=$asserted view=$(now_of v3) wall=$wall day=$(jq -r .day "$D/v3.out" 2>/dev/null)" \
  "$([ "$(rc twall)" = 0 ] && [ "$(now_of v3)" = "$asserted" ] && [ "$asserted" -ge "$wall" ] && [ "$asserted" -le $((wall + 60)) ]; echo $?)"

verdict="K-CLOCK $([ $PASS = $TOTAL ] && echo PASS || echo FAIL) $PASS/$TOTAL ($(( $(date +%s) - started )) s)"
echo "$verdict"
echo "$verdict" >&2
echo "$ROWS"
[ $PASS = $TOTAL ]
