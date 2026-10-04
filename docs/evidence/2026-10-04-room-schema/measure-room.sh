#!/bin/bash
# measure-room.sh BIN_HOST BIN_MINI BIN_STORE BIN_VERIFIER WORLD FIELDS ROSTER_BASE OUT [PERF]
# One fresh scratch world (own Store, own socket under WORLD), one room-shaped
# declared cell `lab` born with FIELDS, the founder rows written at ROSTER_BASE,
# then ONE signed read of `lab` under MINI_TRACE (and perf on the Host if PERF=1).
set -euo pipefail
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 W=$5 FIELDS=$6 BASE=$7 OUT=$8 PERF=${9:-0}
HERE=$(dirname "$(readlink -f "$0")")
SRC=$HERE/src/native/resource-client
mkdir -p "$OUT"
SOCK=$W.sock
t0=$(date +%s.%N)
sh "$SRC/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$W" "$SOCK" >"$OUT/bootstrap.out" 2>"$OUT/bootstrap.err"
t1=$(date +%s.%N)
echo "bootstrap $(echo "$t1 - $t0" | bc) s" >>"$OUT/timings.txt"
WS=$W/sponsor
printf "%s\n" "{\"type\":\"all\",\"predicates\":[]}" >"$OUT/permit-all.json"
/usr/bin/time -f "create %e s %M KB" -a -o "$OUT/timings.txt" \
  "$MINI" workspace --action create --dir "$WS" --name lab --storage declared \
    --predicate "$OUT/permit-all.json" --fields "$FIELDS" >"$OUT/create.out" 2>"$OUT/create.err"
S=$(jq -r .subject "$W/sponsor/workspace.json" 2>/dev/null || echo 7)
f0=$BASE f1=$((BASE+1)) f2=$((BASE+2))
printf "%s\n" "{\"type\":\"minidregg-workspace-proposal-v1\",\"action\":\"invoke\",\"targets\":[{\"name\":\"lab\",\"payload\":{\"type\":\"scalar\",\"actions\":[{\"type\":\"create\",\"key\":{\"type\":\"object\",\"field\":\"$f0\"},\"value\":\"7\"},{\"type\":\"create\",\"key\":{\"type\":\"object\",\"field\":\"$f1\"},\"value\":\"7\"},{\"type\":\"create\",\"key\":{\"type\":\"object\",\"field\":\"$f2\"},\"value\":\"12345\"}]}}]}" >"$OUT/roster.json"
/usr/bin/time -f "propose %e s" -a -o "$OUT/timings.txt" \
  "$MINI" workspace --action propose --dir "$WS" --request "$OUT/roster.json" --proposal-id roster >"$OUT/propose.out" 2>"$OUT/propose.err"
/usr/bin/time -f "submit %e s" -a -o "$OUT/timings.txt" \
  "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/roster/intent.json" --attempt "$WS/attempts/roster" >"$OUT/submit.out" 2>"$OUT/submit.err"
HPID=$(pgrep -P "$(cat "$W/public/server.pid")" | head -1 || true)
echo "server $(cat "$W/public/server.pid") host-child ${HPID:-none}" >>"$OUT/timings.txt"
if [ "$PERF" = 1 ] && [ -n "$HPID" ]; then
  sudo -n perf record -F 999 -g -p "$HPID" -o "$OUT/perf.data" >"$OUT/perf-record.log" 2>&1 &
  PPID_PERF=$!
  sleep 1
fi
MINI_TRACE=$OUT/read.trace /usr/bin/time -f "read %e s %M KB" -a -o "$OUT/timings.txt" \
  "$MINI" workspace --action read --dir "$WS" --name lab >"$OUT/read.out" 2>"$OUT/read.err"
if [ "$PERF" = 1 ] && [ -n "${PPID_PERF:-}" ]; then
  sleep 0.5; sudo -n kill -INT "$PPID_PERF" 2>/dev/null || true
  wait "$PPID_PERF" 2>/dev/null || true
fi
echo "read.out bytes $(wc -c <"$OUT/read.out")" >>"$OUT/timings.txt"
jq -c "{decl:(.cell.declaration|if type==\"array\" then length else . end), from:.cell.declaredFrom, entries:(.cell.entries|length), items:(.opening.items|length), hiding:.hiding}" "$OUT/read.out" >>"$OUT/timings.txt" 2>/dev/null || true
cat "$OUT/timings.txt"
