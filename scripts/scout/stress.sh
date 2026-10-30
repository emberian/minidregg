#!/usr/bin/env bash
# scripts/scout/stress.sh -- off-script stress of one J0-J4 world on a candidate (hbox).
#   stress.sh MANIFEST SRC_TREE RUN [PHASES]      PHASES default "A B C D"
# A: N concurrent writers on one field (no lost update); B: aging (sequential write+read, p50 per block,
# operator certify every 100); C: oversized/hostile inputs (refused by name, host answers on);
# D: kill -9 the Host mid-write-loop, restart, exact retry of the in-flight attempt.
# Output: RUN/stress.tsv  PHASE<TAB>KEY<TAB>VALUE. Every process started has a pid file under RUN.
set -uo pipefail
MANIFEST=$1 SRC=$2 RUN=$3 PHASES=${4-A B C D}
N=${STRESS_N:-8} B_ITERS=${STRESS_B_ITERS:-300}
OUT=$RUN/stress.tsv; mkdir -p "$RUN"; : >"$OUT"
emit() { printf '%s\t%s\t%s\n' "$1" "$2" "$3" | tee -a "$OUT" >&2; }
if [ ! -d "$RUN/jr/world" ]; then
  JOURNEY_STEPS="J0 J1 J2 J3 J4" bash "$SRC/native/resource-client/journey.sh" "$MANIFEST" "$RUN/jr" >"$RUN/journey.out" 2>"$RUN/journey.err" \
    || { emit setup FAIL "J0-J4: $(tail -1 "$RUN/journey.err")"; exit 1; }
fi
W=$RUN/jr/world; MINI=$(jq -r .mini "$MANIFEST"); HOST=$(jq -r .host "$MANIFEST")
CONFIG=$W/deployment/pinned-config.json; NWS=$W/newcomer-workspace; SWS=$W/sponsor
SOCKET=/run/user/$(id -u)/scout-st-$(basename "$RUN")/h.sock; mkdir -p -m 700 "$(dirname "$SOCKET")"
for ws in "$NWS" "$SWS"; do   # the journey's own socket directory is gone: point both workspaces at ours
  jq --arg s "$SOCKET" '.socket = $s' "$ws/workspace.json" >"$RUN/ws.new" && cat "$RUN/ws.new" >"$ws/workspace.json"; done   # in place: the custody check wants the file private and unmoved
CONTROL=$(jq -r .factoryControllerCapability "$W/genesis.json")
serve() {
  mkdir -p "$(dirname "$SOCKET")"; rm -f "$SOCKET"
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" >"$RUN/serve.log" 2>&1 </dev/null &
  echo $! >"$RUN/serve.pid"
  for _ in $(seq 1 100); do [ -S "$SOCKET" ] && return 0; sleep 0.3; done; return 1
}
stop_serve() { [ -f "$RUN/serve.pid" ] && kill "$(cat "$RUN/serve.pid")" 2>/dev/null; sleep 1; }
serve || { emit setup FAIL "serve did not come up"; exit 1; }
cur() { "$MINI" workspace --action read --dir "$NWS" --name shared 2>/dev/null | jq -r '[.cell.entries[]? | select(.key.field=="2") | .value][0] // "absent"'; }
wreq() { printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"shared","payload":{"type":"scalar","actions":[{"type":"write","key":{"type":"object","field":"2"},"expected":"%s","value":"%s"}]}}]}\n' "$1" "$2"; }
# one write: tag expected value -> prints rc and outcome type
write1() {  # write1 TAG EXPECTED VALUE
  local t=$1 d=$RUN/req; mkdir -p "$d"
  wreq "$2" "$3" >"$d/$t.json"
  "$MINI" workspace --action propose --dir "$NWS" --request "$d/$t.json" --proposal-id "$t" >"$d/$t.p.out" 2>"$d/$t.p.err" || { echo "propose-refused"; return 1; }
  "$MINI" workspace --action submit --dir "$NWS" --intent "$NWS/proposals/$t/intent.json" --attempt "$NWS/attempts/$t" >"$d/$t.s.out" 2>"$d/$t.s.err" || { echo "submit-refused: $(grep -m1 '^refused' "$d/$t.s.err" | cut -c1-120)"; return 1; }
  echo confirmed
}
certify() { "$MINI" checkpoint --action certify --workspace "$SWS" --control "$CONTROL" --min-tail 1 >/dev/null 2>&1; }
ms() { echo $(( $(date +%s%N) / 1000000 )); }

for P in $PHASES; do case $P in
A) certify; v0=$(cur); emit A start "field2=$v0 writers=$N"
   pids=(); for i in $(seq 1 $N); do ( write1 "a$i" "$v0" "$((v0 + 100 + i))" >"$RUN/a$i.res" ) & pids+=($!); done; wait "${pids[@]}"
   ok=$(cat "$RUN"/a*.res | grep -c '^confirmed'); v1=$(cur)
   emit A confirmed "$ok of $N"; emit A refusals "$(cat "$RUN"/a*.res | grep -v '^confirmed' | sort | uniq -c | tr '\n' ';')"
   emit A final "field2=$v1"
   # no lost update: with the same expected value, at most one writer may win
   [ "$ok" -le 1 ] && emit A verdict PASS || emit A verdict "FAIL: $ok writers all won on the same expected value"
   ;;
B) v=$(cur); blk=0; : >"$RUN/b.tsv"
   for i in $(seq 1 $B_ITERS); do
     t0=$(ms); r=$(write1 "b$i" "$v" "$((v + 1))"); t1=$(ms); cur >/dev/null; t2=$(ms)
     [ "$r" = confirmed ] && v=$((v + 1)) || emit B refused "iter $i: $r"
     printf '%s\t%s\t%s\n' "$i" "$((t1 - t0))" "$((t2 - t1))" >>"$RUN/b.tsv"
     [ $((i % 100)) = 0 ] && certify
   done
   for s in $(seq 1 50 $B_ITERS); do
     awk -F'\t' -v a=$s -v b=$((s + 49)) '$1>=a && $1<=b {w[++n]=$2; r[n]=$3} END {if(n){asort(w);asort(r);printf "iters %d-%d write p50 %d ms max %d; read p50 %d ms max %d\n", a, b, w[int((n+1)/2)], w[n], r[int((n+1)/2)], r[n]}}' "$RUN/b.tsv" | { read -r l; emit B block "$l"; }
   done ;;
C) v=$(cur)
   big=$(head -c 200000 /dev/zero | tr '\0' '9')
   r=$(write1 c-big "$v" "$big"); emit C huge-value-200k-digits "$r"
   emit C host-alive-after "$(cur)"
   python3 - "$RUN/req/c-many.json" "$v" <<'PY'
import json,sys
acts=[{"type":"write","key":{"type":"object","field":"2"},"expected":sys.argv[2],"value":str(i)} for i in range(5000)]
json.dump({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"shared","payload":{"type":"scalar","actions":acts}}]},open(sys.argv[1],"w"))
PY
   "$MINI" workspace --action propose --dir "$NWS" --request "$RUN/req/c-many.json" --proposal-id c-many >"$RUN/req/c-many.p.out" 2>"$RUN/req/c-many.p.err"; emit C actions-5000-propose "rc=$? $(grep -m1 -E '^(mini|refused)' "$RUN/req/c-many.p.err" | cut -c1-140)"
   emit C host-alive-after "$(cur)"
   printf '{"type":"garbage"' >"$RUN/req/c-bad.json"
   "$MINI" workspace --action propose --dir "$NWS" --request "$RUN/req/c-bad.json" --proposal-id c-bad >/dev/null 2>"$RUN/req/c-bad.err"; emit C malformed-json "rc=$? $(head -c 140 "$RUN/req/c-bad.err" | tr '\n' ' ')"
   # a hostile raw client: 50 silent connections, then an honest read
   python3 - "$SOCKET" <<'PY'
import socket,sys
s=[]
for _ in range(200):
    c=socket.socket(socket.AF_UNIX); c.connect(sys.argv[1]); s.append(c)
print("opened",len(s))
import time; time.sleep(3)
PY
   emit C honest-read-after-200-silent "$(cur)" ;;
D) v=$(cur); emit D start "field2=$v"
   v2=$((v + 1000))
   ( write1 d-inflight "$v" "$v2" >"$RUN/d.res" ) & wp=$!
   sleep 0.15; kill -9 "$(cat "$RUN/serve.pid")" 2>/dev/null; wait $wp 2>/dev/null
   emit D inflight-result "$(cat "$RUN/d.res")"
   sleep 1; serve; emit D restarted "field2=$(cur)"
   # exact retry of the in-flight attempt: either replays the confirmed outcome or lands it once
   "$MINI" workspace --action submit --dir "$NWS" --intent "$NWS/proposals/d-inflight/intent.json" --attempt "$NWS/attempts/d-inflight" >"$RUN/d.retry.out" 2>"$RUN/d.retry.err"; emit D retry "rc=$? $(jq -r '.confirmation // .type // empty' "$RUN/d.retry.out" 2>/dev/null) $(grep -m1 '^refused' "$RUN/d.retry.err" | cut -c1-140)"
   v3=$(cur); emit D after-retry "field2=$v3"
   { [ "$v3" = "$v" ] || [ "$v3" = "$v2" ]; } && emit D verdict "PASS (value is the old or the new, never anything else)" || emit D verdict "FAIL: value $v3 is neither $v nor $v2" ;;
esac; done
stop_serve
