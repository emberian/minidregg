#!/usr/bin/env bash
# journey.d/jbirthwin.sh — K-BIRTH-WINDOW rows, on the journey's fresh Store.
#
# A birth is authored at the current height H0; its root grants name
# notBefore = H0. Any admission between authoring and admission moves the
# height. The kernel admits the birth while height <= H0 + birthSlack and
# refuses it `birthStale` past that (operator log; the submitter sees the
# uniform `undisclosed`). A refused birth's name can be created again.
#
# A second workspace (the newcomer) writes one field every KBW_WRITE_PERIOD
# seconds into its own resource `kbw-pad` for the whole step: the same race as
# the clock ticker. Rows:
#   births-under-writer   KBW_BIRTHS sponsor births, each by `workspace create`  -> all installed
#   stale-birth           a birth stopped (SIGSTOP) after authoring, held past
#                         birthSlack admissions, then continued                -> refused, operator log birthStale
#   same-name-again       `workspace create` of the stale birth's name again   -> installed (custody released)
#   cold-audit            service stopped: `audit` re-admits every record      -> exit 0
# Every count and every operator-log reason is recorded in the rows file.
# Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
N=${KBW_BIRTHS:-20}
PERIOD=${KBW_WRITE_PERIOD:-5}
SLACK=${KBW_SLACK:-64}
mkdir -p "$D/req" "$D/births"
rows=$D/kbw-rows.tsv
: >"$rows"
bad=0
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"

oplog() { cat "$W"/public/serve*.log 2>/dev/null; }
count_reason() { oplog | grep -c "submission refused (operator log).*$1" ; }
row() { # NAME EXPECT GOT DETAIL
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$rows"
  [ "$2" = "$3" ] || bad=$((bad + 1))
}
create() { # WS NAME LOG
  "$MINI" workspace --action create --dir "$1" --name "$2" --storage declared \
    --predicate "$D/req/permit-all.json" >"$3.out" 2>"$3.err"
}
installed() { [ -f "$1/attempts/create-$2/outcome.json" ] \
  && jq -e '.type == "confirmed" and (.confirmation == "installed" or .confirmation == "replayed")' \
       "$1/attempts/create-$2/outcome.json" >/dev/null 2>&1; }

# The concurrent writer's resource: the sponsor births `kbw-pad` and delegates
# observe+mutate on it to the newcomer (the J3/J4 path).
must() { "$@" >>"$D/setup.out" 2>>"$D/setup.err" || { echo "setup failed: $* :: $(tail -1 "$D/setup.err")" >&2; exit 1; }; }
must create "$SPONSOR_WS" kbw-pad "$D/pad"
jq -n --arg r "$NEWCOMER_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"kbw-pad",
  recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$D/req/delegate.json"
must "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/delegate.json" --proposal-id kbw-grant
must "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/kbw-grant/intent.json" \
  --attempt "$SPONSOR_WS/attempts/kbw-grant"
must "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id kbw-grant \
  --attempt "$SPONSOR_WS/attempts/kbw-grant"
must "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name kbw-pad \
  --from-ref "$SPONSOR_WS/proposals/kbw-grant/recipient-reference.json"
WRITES=$D/writes.count; echo 0 >"$WRITES"
write_once() { # ID -> 0 when the write was installed
  local id=$1 i=${1##*-}
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"kbw-pad","payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"%s"},"value":"1"}]}}]}\n' \
    "$i" >"$D/req/$id.json"
  "$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$D/req/$id.json" --proposal-id "$id" \
      >"$D/$id.out" 2>"$D/$id.err" \
    && "$MINI" workspace --action submit --dir "$NEWCOMER_WS" \
      --intent "$NEWCOMER_WS/proposals/$id/intent.json" --attempt "$NEWCOMER_WS/attempts/$id" \
      >>"$D/$id.out" 2>>"$D/$id.err" \
    && echo $(( $(cat "$WRITES") + 1 )) >"$WRITES"
}
writer() { # PREFIX FIELD_BASE PERIOD [INSTALLED_TARGET]: until killed, or until that many installed
  local prefix=$1 base=$2 period=$3 target=${4:-0} i=0 done=0
  while :; do
    i=$((i + 1))
    write_once "$prefix-$((base + i))" && done=$((done + 1))
    [ "$target" -gt 0 ] && [ "$done" -ge "$target" ] && return 0
    [ "$i" -gt $((target * 3 + 1000)) ] && return 1
    sleep "$period"
  done
}

# Row 1: KBW_BIRTHS births under a writer.
writer kbw-w 1000 "$PERIOD" &
WRITER=$!
admitted=0; refused_admission=0; refused_authoring=0; other=0
for i in $(seq 1 "$N"); do
  name=kbw-b$i
  create "$SPONSOR_WS" "$name" "$D/births/$name"
  if installed "$SPONSOR_WS" "$name"; then admitted=$((admitted + 1))
  elif grep -q "birth authoring refused" "$D/births/$name.err"; then refused_authoring=$((refused_authoring + 1))
  elif grep -q "refused" "$D/births/$name.err" "$D/births/$name.out" 2>/dev/null; then refused_admission=$((refused_admission + 1))
  else other=$((other + 1)); fi
done
kill "$WRITER" 2>/dev/null; wait "$WRITER" 2>/dev/null
gt=$(count_reason grantTemplate); st=$(count_reason birthStale); fu=$(count_reason birthFuture)
row births-under-writer "installed=$N" "installed=$admitted" \
  "refused at admission=$refused_admission refused at authoring=$refused_authoring other=$other writes=$(cat "$WRITES") oplog grantTemplate=$gt birthStale=$st birthFuture=$fu"

# Row 2: a birth held past the slack.
name=kbw-stale
before_stale=$(count_reason birthStale); before_gt=$(count_reason grantTemplate)
"$MINI" workspace --action create --dir "$SPONSOR_WS" --name "$name" --storage declared \
  --predicate "$D/req/permit-all.json" >"$D/stale1.out" 2>"$D/stale1.err" &
CREATE=$!
gen=$SPONSOR_WS/sources/create-$name.authoring/g0001
held=no; held_writes=0
for _ in $(seq 1 3000); do
  if [ -f "$gen/reply.frame" ] && [ "$(head -c1 "$gen/reply.frame" | xxd -p)" != ff ]; then
    kill -STOP "$CREATE" 2>/dev/null && held=yes; break
  fi
  kill -0 "$CREATE" 2>/dev/null || break
  sleep 0.01
done
if [ "$held" = yes ] && [ ! -f "$SPONSOR_WS/attempts/create-$name/outcome.json" ]; then
  w0=$(cat "$WRITES")
  writer kbw-s 5000 0 "$((SLACK + 1))" >/dev/null 2>&1
  held_writes=$(( $(cat "$WRITES") - w0 ))
  kill -CONT "$CREATE"
fi
wait "$CREATE"; rc=$?
after_stale=$(count_reason birthStale); after_gt=$(count_reason grantTemplate)
if [ "$held" != yes ]; then got=not-held
elif installed "$SPONSOR_WS" "$name"; then got=installed
elif [ "$((after_stale - before_stale))" -ge 1 ]; then got=birthStale
elif [ "$((after_gt - before_gt))" -ge 1 ]; then got=grantTemplate
else got="rc=$rc"; fi
row stale-birth birthStale "$got" "held through ${held_writes:-0} installed writes (slack $SLACK); client: $(grep -h refused "$D/stale1.err" "$D/stale1.out" | tail -1 | cut -c1-120)"

# Row 3: the same name again.
create "$SPONSOR_WS" "$name" "$D/stale2"
if installed "$SPONSOR_WS" "$name"; then got=installed; else got="not-installed"; fi
retired=$(ls -d "$SPONSOR_WS/attempts/create-$name".released-* 2>/dev/null | wc -l)
row same-name-again installed "$got" "released attempts retained: $retired; $(tail -1 "$D/stale2.err" | cut -c1-120)"

# Row 4: cold audit. Stop our service, re-admit every record of the closed
# Store from genesis, then start the service again on the same socket.
pid=$(cat "$W/public/server.pid")
kids=$(pgrep -P "$pid" | tr '\n' ' ')
kill -TERM "$pid"
for _ in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
for k in $kids; do for _ in $(seq 1 100); do kill -0 "$k" 2>/dev/null || break; sleep 0.1; done; done
"$HOST" "$CONFIG" audit >"$D/audit.out" 2>"$D/audit.err"; arc=$?
row cold-audit "exit=0" "exit=$arc" "$(cat "$D/audit.out" "$D/audit.err" | tail -1 | cut -c1-160)"
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-kbw.log" 2>&1 </dev/null &
echo "$!" >"$W/public/server.pid"
for _ in $(seq 1 600); do [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-kbw.log" 2>/dev/null && break; sleep 0.1; done

cat "$rows" >&2
echo "KBW: $bad rows off; births $admitted/$N installed under a writer" >&2
echo "$rows"
[ "$bad" = 0 ]
