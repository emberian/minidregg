#!/usr/bin/env bash
# C14 TAIL-BOUND (COMPUTE.md §5.2, §6): a node cannot run more than L heights
# past its last certified head.
#
# Journey hook contract (journey.sh header): executed with MINI, HOST, STORE,
# VERIFIER and JOURNEY_STEP_DIR exported. Exit 0 = PASS. The verdict line
# `C14 TAIL PASS n/n` is the last stderr line and the line before the last
# stdout line; the last stdout line is the deciding artifact (rows.tsv).
#
# The journey's own Store runs the default L (256); this hook needs a small L,
# so it bootstraps a FRESH private Store with MINI_TAIL_BOUND=8 through the one
# genesis template (newparticipant-acceptance.sh -> genesis.sh), runs its own
# service on its own socket, and stops it (by its recorded pid) at the end.
#
# Rows: the genesis system cell is certified 0 under L; a resource is created;
# the operator certifies (mini checkpoint); the writes up to the bound are
# admitted; the next write is refused by the Host naming `tail-bound`; the
# operator certifies again and the refused write is admitted; the service is
# restarted and the bound holds from the certified height loaded from the
# Store (the write past it is refused again); the operator audit re-admits
# every record from genesis, certify records and the tail law included.
set -uo pipefail
umask 077
for name in MINI HOST STORE VERIFIER JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jtail: $name is required" >&2; exit 2; fi
done
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
L=${JTAIL_BOUND:-8}
D=$JOURNEY_STEP_DIR/jtail
[ ! -e "$D" ] || { echo "jtail: refusing to reuse $D" >&2; exit 2; }
mkdir -p "$D"
ROWS=$D/rows.tsv
printf 'verdict\tstep\texpected\tobserved\n' >"$ROWS"
PASS=0 TOTAL=0
started=$(date +%s)

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
W=$D/world
SERVER=
stop_server() {
  local pid
  pid=$(cat "$W/public/server.pid" 2>/dev/null) || return 0
  [ -n "$pid" ] || return 0
  kill "$pid" 2>/dev/null
  for _ in $(seq 1 100); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  rm -f "$W/public/mini.sock"
}
finish() {
  stop_server
  local verdict
  verdict="C14 TAIL $([ $PASS = $TOTAL ] && [ $TOTAL -gt 0 ] && echo PASS || echo FAIL) $PASS/$TOTAL ($(( $(date +%s) - started )) s)"
  echo "$verdict"; echo "$verdict" >&2; echo "$ROWS"
  [ $PASS = $TOTAL ] && [ $TOTAL -gt 0 ]
}

MINI_TAIL_BOUND=$L run boot sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$W"
row "fresh Store with tailBound=$L (genesis source via genesis.sh)" "bootstrapped" \
  "rc=$(rc boot) tailBound=$(jq -r .tailBound "$W/genesis.json" 2>/dev/null)" \
  "$([ "$(rc boot)" = 0 ] && [ "$(jq -r .tailBound "$W/genesis.json")" = "$L" ]; echo $?)"
[ "$(rc boot)" = 0 ] || { finish; exit 1; }
WS=$W/sponsor
CONFIG=$W/deployment/pinned-config.json
CONTROL=$(jq -r .factoryControllerCapability "$W/genesis.json")

view() { run "$1" "$MINI" checkpoint --action view --workspace "$WS"; }
v() { jq -r ".$2" "$D/$1.out" 2>/dev/null; }
certify() { run "$1" "$MINI" checkpoint --action certify --workspace "$WS" --control "$CONTROL"; }
REQ=$D/requests; mkdir -p "$REQ"
printf '%s\n' '{"type":"all","predicates":[]}' >"$REQ/open.json"
echo 100 >"$D/field"   # the field counter lives in a file: fill runs in a subshell
attempt_write() {  # attempt_write ID -> rc 0 iff admitted; creates the next fresh field
  local FIELD; FIELD=$(( $(cat "$D/field") + 1 )); echo "$FIELD" >"$D/field"
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"tb","payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"%s"},"value":"%s"}]}}]}\n' "$FIELD" "$FIELD" >"$REQ/$1.json"
  run "$1-propose" "$MINI" workspace --action propose --dir "$WS" --request "$REQ/$1.json" --proposal-id "tail-$1"
  [ "$(rc "$1-propose")" = 0 ] || return 1
  run "$1-submit" "$MINI" workspace --action submit --dir "$WS" \
    --intent "$WS/proposals/tail-$1/intent.json" --attempt "$WS/attempts/tail-$1"
  [ "$(rc "$1-submit")" = 0 ] && jq -e '.type == "confirmed"' "$WS/attempts/tail-$1/outcome.json" >/dev/null 2>&1
}
reason_of() { jq -r '.reason // empty' "$WS/attempts/tail-$1/outcome.json" 2>/dev/null; }
explain_of() { grep -m1 '^refused:' "$D/$1-submit.err" 2>/dev/null | cut -c1-160; }
fill() {  # fill PREFIX COUNT -> number admitted
  local i ok=0
  for i in $(seq 1 "$2"); do attempt_write "$1-$i" && ok=$((ok + 1)); done
  echo $ok
}

view v0
row "genesis system cell" "certified 0, tailBound $L" \
  "rc=$(rc v0) certified=$(v v0 certifiedHeight) tailBound=$(v v0 tailBound) head=$(v v0 head)" \
  "$([ "$(rc v0)" = 0 ] && [ "$(v v0 certifiedHeight)" = 0 ] && [ "$(v v0 tailBound)" = "$L" ]; echo $?)"

run create "$MINI" workspace --action create --dir "$WS" --name tb --storage declared --predicate "$REQ/open.json"
row "create resource tb (open law)" "created" "rc=$(rc create)" "$([ "$(rc create)" = 0 ]; echo $?)"

view v1; h1=$(v v1 head)
certify c1
view v2
row "operator certifies head $h1 (mini checkpoint)" "confirmed; certified=$h1, tail 1, remaining $((L - 1))" \
  "rc=$(rc c1) $(jq -r .type "$D/c1.out" 2>/dev/null) certified=$(v v2 certifiedHeight) tail=$(v v2 tail) remaining=$(v v2 remaining)" \
  "$([ "$(rc c1)" = 0 ] && [ "$(v v2 certifiedHeight)" = "$h1" ] && [ "$(v v2 tail)" = 1 ] && [ "$(v v2 remaining)" = $((L - 1)) ]; echo $?)"

n=$(fill a $((L - 1)))
view v3
row "the $((L - 1)) writes up to the bound (heights $((h1 + 2))..$((h1 + L)))" "all admitted; tail $L, remaining 0" \
  "admitted=$n tail=$(v v3 tail) remaining=$(v v3 remaining) head=$(v v3 head)" \
  "$([ "$n" = $((L - 1)) ] && [ "$(v v3 tail)" = "$L" ] && [ "$(v v3 remaining)" = 0 ]; echo $?)"

attempt_write over1; r=$?
row "the next write (height $((h1 + L + 1)) = certified + L + 1)" "refused tail-bound, named with its heights" \
  "admitted=$([ $r = 0 ] && echo yes || echo no) reason=$(reason_of over1) [$(explain_of over1)]" \
  "$([ $r != 0 ] && [ "$(reason_of over1)" = tail-bound ] && [[ "$(explain_of over1)" == *"head $((h1 + L + 1)) certified $h1 bound $L"* ]]; echo $?)"

view v4
row "head after the refusal" "unchanged ($((h1 + L)))" "head=$(v v4 head)" "$([ "$(v v4 head)" = $((h1 + L)) ]; echo $?)"

certify c2
view v5
row "operator certifies at the full tail" "confirmed (a certify is the one record the bound exempts); certified=$((h1 + L))" \
  "rc=$(rc c2) certified=$(v v5 certifiedHeight) remaining=$(v v5 remaining)" \
  "$([ "$(rc c2)" = 0 ] && [ "$(v v5 certifiedHeight)" = $((h1 + L)) ] && [ "$(v v5 remaining)" = $((L - 1)) ]; echo $?)"

attempt_write resume1; r=$?
row "writes resume after the checkpoint" "admitted" "admitted=$([ $r = 0 ] && echo yes || echo no) $(reason_of resume1)" "$([ $r = 0 ]; echo $?)"

# Restart: the bound must hold from the certified height the Store holds.
view v6; rem=$(v v6 remaining); cert6=$(v v6 certifiedHeight)
stop_server
nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$W/public/mini.sock" \
  >"$W/public/serve-2.log" 2>&1 </dev/null &
echo $! >"$W/public/server.pid"
for _ in $(seq 1 1200); do [ -S "$W/public/mini.sock" ] && break; sleep 0.1; done
view v7
row "restart: the service reopens the Store" "certified loaded = $cert6, remaining $rem" \
  "rc=$(rc v7) certified=$(v v7 certifiedHeight) remaining=$(v v7 remaining)" \
  "$([ "$(rc v7)" = 0 ] && [ "$(v v7 certifiedHeight)" = "$cert6" ] && [ "$(v v7 remaining)" = "$rem" ]; echo $?)"
n=$(fill b "$rem")
attempt_write over2; r=$?
row "after restart: $rem writes admitted, the next refused" "admitted=$rem, then tail-bound" \
  "admitted=$n next=$([ $r = 0 ] && echo admitted || echo refused) reason=$(reason_of over2)" \
  "$([ "$n" = "$rem" ] && [ $r != 0 ] && [ "$(reason_of over2)" = tail-bound ]; echo $?)"

run audit "$HOST" "$CONFIG" audit
row "operator audit (genesis re-admission, tail law included)" "every record re-admitted" \
  "rc=$(rc audit) $(tail -1 "$D/audit.out" 2>/dev/null | cut -c1-120)" \
  "$([ "$(rc audit)" = 0 ]; echo $?)"

finish
