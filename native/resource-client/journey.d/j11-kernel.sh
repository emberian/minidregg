#!/usr/bin/env bash
# journey.d/j11-kernel.sh — per-author streams in a room (K-STREAM, PLACE §2.3/§4.4),
# the kernel rows of J11, on the journey's fresh Store after J5 (three keys:
# A the sponsor, B the newcomer, C the third key).
#
# A opens the room `commons`. C, not yet a member, tries to read A's stream:
# refused. A invites B and C (`"room": true`, child `under commons`, verbs
# observe+append). A births each member's stream `--in commons` owned by that
# member under the per-author law (every write is by its author). Then:
#   round 1: A1 B1 C1 are ALL planned (each from one read of its own stream)
#            before any is submitted, then submitted in that order;
#   round 2: A2 B2 C2 likewise.  Six appends, six plans: zero re-plans.
#   same stream: two appends to A's stream planned from ONE read; the second
#            is refused by name (staleTarget).
#   C crafts an append into B's stream with its room grant: refused by the law.
#   B tails all three streams; the Host is stopped and started; B tails again:
#   identical bytes. `audit` before and after the restart: equal.
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS NEWCOMER_WS
# NEWCOMER_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. Exit 0 = every row as
# expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
AW=$SPONSOR_WS
BW=$NEWCOMER_WS
CW=$W/third-workspace
mkdir -p "$D/req"
rows=$D/stream-rows.tsv
: >"$rows"
bad=0
plans=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45

run() { # NAME cmd...
  local name=$1; shift
  "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"
}
host_refused() {
  [ "$(cat "$D/$1.rc")" != 0 ] && grep -q "encoded refusal: $REFUSAL_TAG" "$D/$1.err"
}
refusal_text() {
  grep -o 'encoded refusal: [0-9a-f]*' "$D/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' ' | cut -c1-200
}
row() { # NAME EXPECT(ok|read|refused) [NEEDLE: a refusal must name it]
  local name=$1 expect=$2 needle=${3:-} got detail
  if [ "$(cat "$D/$name.rc")" = 0 ]; then got=$expect; [ "$expect" = refused ] && got=ACCEPTED
  elif host_refused "$name"; then got=refused
  else got="client-error"
  fi
  detail=$([ "$got" = refused ] && refusal_text "$name" || tail -1 "$D/$name.err" | cut -c1-160)
  if [ "$got" = refused ] && [ -n "$needle" ] && ! printf '%s' "$detail" | grep -q -- "$needle"; then
    got="refused-not-$needle"
  fi
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$name" "$expect" "$got" "$detail" >>"$rows"
  [ "$got" = "$expect" ] || bad=$((bad + 1))
}
ok() { # NAME
  [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -1 "$D/$1.err")" >&2; exit 1; }
}
subject_of() { jq -r .subject "$1/workspace.json"; }
A=$(subject_of "$AW"); B=$(subject_of "$BW"); C=$(subject_of "$CW")

law() { # SUBJECT FILE: every write (mutate=2, append=7) is by SUBJECT
  jq -n --arg s "$1" '{type:"any",predicates:[
    {type:"not",predicate:{type:"memberOf",slot:"request/verb",values:["2","7"]}},
    {type:"eq",slot:"request/subject",value:$s}]}' >"$2"
}
plan() { # WS PROPOSAL STREAM TOPIC TEXT: plan one append (reads the stream once)
  jq -n --arg n "$3" --arg t "$4" --arg x "$5" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",
      targets:[{name:$n,payload:{type:"append",topic:$t,text:$x}}]}' >"$D/req/$2.json"
  run "plan-$2" "$MINI" workspace --action propose --dir "$1" --request "$D/req/$2.json" --proposal-id "$2"
  plans=$((plans + 1))
}
submit() { # WS PROPOSAL
  run "$2" "$MINI" workspace --action submit --dir "$1" \
    --intent "$1/proposals/$2/intent.json" --attempt "$1/attempts/$2"
}

printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"

# The room; A's own stream in it.
run create-commons "$MINI" workspace --action create --dir "$AW" --name commons --storage declared \
  --predicate "$D/req/permit-all.json"; ok create-commons
commons=$(jq -r .target "$AW/refs/commons.json")
law "$A" "$D/req/law-a.json"
run create-sa "$MINI" workspace --action create --dir "$AW" --name sa --storage stream \
  --predicate "$D/req/law-a.json" --in commons; ok create-sa
sa=$(jq -r .target "$AW/refs/sa.json")

# C is not yet a member: its read of A's stream is refused.
acap=$(jq -r .observeCapability "$AW/refs/commons.json")
run c-import-sa-early "$MINI" workspace --action import --dir "$CW" --name sa-early --kind object \
  --target "$sa" --observe-capability "$acap"; ok c-import-sa-early
run outsider-tail "$MINI" workspace --action tail --dir "$CW" --name sa-early --from 1 --count 16
row outsider-tail refused

# Invites: room delegations to B and C (observe + append under commons).
invite() { # WHO SUBJECT
  jq -n --arg r "$2" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"commons",
    recipient:$r,verbs:["observe","append"],maxCost:"50000",room:true}' >"$D/req/sinvite-$1.json"
  run "sinvite-$1-propose" "$MINI" workspace --action propose --dir "$AW" --request "$D/req/sinvite-$1.json" \
    --proposal-id "sinvite-$1"; ok "sinvite-$1-propose"
  run "sinvite-$1-submit" "$MINI" workspace --action submit --dir "$AW" \
    --intent "$AW/proposals/sinvite-$1/intent.json" --attempt "$AW/attempts/sinvite-$1"; ok "sinvite-$1-submit"
  run "sinvite-$1-publish" "$MINI" workspace --action publish-delegation --dir "$AW" --proposal-id "sinvite-$1" \
    --attempt "$AW/attempts/sinvite-$1"; ok "sinvite-$1-publish"
}
invite b "$B"
invite c "$C"
run b-import-commons "$MINI" workspace --action import --dir "$BW" --name commons \
  --from-ref "$AW/proposals/sinvite-b/recipient-reference.json"; ok b-import-commons
run c-import-commons "$MINI" workspace --action import --dir "$CW" --name commons \
  --from-ref "$AW/proposals/sinvite-c/recipient-reference.json"; ok c-import-commons
bcap=$(jq -r .observeCapability "$BW/refs/commons.json")
ccap=$(jq -r .observeCapability "$CW/refs/commons.json")

# The founder births B's and C's own streams in the room (the room template:
# owner = the member, law = the member's author law; A pays). B and C hold
# the owner grants; A holds nothing on them.
law "$B" "$D/req/law-b.json"
law "$C" "$D/req/law-c.json"
run create-sb "$MINI" workspace --action create --dir "$AW" --name sb --storage stream \
  --predicate "$D/req/law-b.json" --in commons --owner "$B"; ok create-sb
run create-sc "$MINI" workspace --action create --dir "$AW" --name sc --storage stream \
  --predicate "$D/req/law-c.json" --in commons --owner "$C"; ok create-sc
sb=$(jq -r .target "$AW/refs/sb.json")
sc=$(jq -r .target "$AW/refs/sc.json")
own() { # WS NAME FROM-REF: the member imports its own stream with its owner grant
  run "import-own-$2" "$MINI" workspace --action import --dir "$1" --name "$2" --kind object \
    --target "$(jq -r .target "$3")" --observe-capability "$(jq -r .observeCapability "$3")" \
    --operation-capability "$(jq -r .operationCapability "$3")"; ok "import-own-$2"
}
own "$BW" sb "$AW/refs/sb.json"
own "$CW" sc "$AW/refs/sc.json"

# K=3, interleaved, every plan of a round made before any submit of it.
for round in 1 2; do
  plan "$AW" "a$round" sa general "hello from A, round $round"
  plan "$BW" "b$round" sb general "hello from B, round $round"
  plan "$CW" "c$round" sc general "hello from C, round $round"
  for who in a b c; do
    case $who in a) ws=$AW;; b) ws=$BW;; c) ws=$CW;; esac
    ok "plan-$who$round"
    submit "$ws" "$who$round"; row "$who$round" ok
  done
done
admitted=0
for p in a1 b1 c1 a2 b2 c2; do [ "$(cat "$D/$p.rc")" = 0 ] && admitted=$((admitted + 1)); done
replans=$((plans - 6))
printf 'contention-k3\texpect=6/6,replans=0\tgot=%s/6,replans=%s\tplans=%s submits=6 (A1 B1 C1 A2 B2 C2, each round planned before submitted)\n' \
  "$admitted" "$replans" "$plans" >>"$rows"
[ "$admitted" = 6 ] && [ "$replans" = 0 ] || bad=$((bad + 1))

# Two appends to ONE stream planned from the same read: the second refuses by name.
plan "$AW" same-1 sa general "first of two from one read"
plan "$AW" same-2 sa general "second of two from one read"
ok plan-same-1; ok plan-same-2
submit "$AW" same-1; row same-1 ok
submit "$AW" same-2; row same-2 refused staleTarget

# C crafts an append into B's stream with its room grant (observe+append under
# commons, which covers sb). Control first: the SAME grant admits C's append to
# its own stream sc, so the grant is sufficient and the only thing that differs
# is sb's author law. A submit-time refusal is the uniform public outcome
# (`NativeHost.public_refusal_uniform`), read from the retained outcome.
run c-import-sc-room "$MINI" workspace --action import --dir "$CW" --name sc-room --kind object \
  --target "$sc" --observe-capability "$ccap" --operation-capability "$ccap"; ok c-import-sc-room
plan "$CW" c-own-via-room sc-room general "C in its own stream with the room grant"
ok plan-c-own-via-room
submit "$CW" c-own-via-room; row c-own-via-room ok
run c-import-sb "$MINI" workspace --action import --dir "$CW" --name sb-forged --kind object \
  --target "$sb" --observe-capability "$ccap" --operation-capability "$ccap"; ok c-import-sb
plan "$CW" c-into-b sb-forged general "C speaking in B's stream"
ok plan-c-into-b
submit "$CW" c-into-b
outcome=$CW/attempts/c-into-b/outcome.json
if [ "$(cat "$D/c-into-b.rc")" != 0 ] && [ "$(jq -r .type "$outcome" 2>/dev/null)" = refused ]; then
  got=refused; detail="phase=$(jq -r .phase "$outcome" | xxd -r -p) detail=$(jq -r .detail "$outcome" | xxd -r -p)"
# On final (P-LAW) the Host evaluates the target's law when it prepares the
# submission and refuses there with the failing clause: law-denied, naming
# sb's author clause.
elif host_refused c-into-b && grep -q "law-denied" "$D/c-into-b.err"; then
  got=refused; detail=$(grep -o "law-denied: [^;]*" "$D/c-into-b.err" | head -1)
else got="ACCEPTED-or-error"; detail=$(tail -1 "$D/c-into-b.err"); fi
printf 'c-into-b\texpect=refused\tgot=%s\t%s (same grant admitted c-own-via-room: the author law of sb refuses)\n' \
  "$got" "$detail" >>"$rows"
[ "$got" = refused ] || bad=$((bad + 1))

# B tails all three streams (its room grant covers them).
for s in sa sb sc; do
  case $s in sa) t=$sa;; sb) t=$sb;; sc) t=$sc;; esac
  run "b-import-$s" "$MINI" workspace --action import --dir "$BW" --name "$s-view" --kind object \
    --target "$t" --observe-capability "$bcap"; ok "b-import-$s"
  run "tail-$s-before" "$MINI" workspace --action tail --dir "$BW" --name "$s-view" --from 1 --count 16
  row "tail-$s-before" read
done
run tail-window "$MINI" workspace --action tail --dir "$BW" --name sa-view --from 2 --count 1
win=$(jq -c '[.entries[].sequence]' "$D/tail-window.out" 2>/dev/null)
printf 'tail-window\texpect=["2"]\tgot=%s\tfrom=2 count=1 of sa; nextSeq=%s\n' "$win" \
  "$(jq -r .nextSeq "$D/tail-window.out" 2>/dev/null)" >>"$rows"
[ "$win" = '["2"]' ] || bad=$((bad + 1))
jq -s '[.[] | .entries[] | {height: (.height|tonumber), author, sequence, topic}] | sort_by(.height)' \
  "$D/tail-sa-before.out" "$D/tail-sb-before.out" "$D/tail-sc-before.out" >"$D/timeline.json" 2>/dev/null \
  || echo '[]' >"$D/timeline.json"

# Stop and start the Host (the journey's server); audit on either side.
pidfile=$W/public/server.pid
restart() {
  local pid; pid=$(cat "$pidfile")
  kill -TERM "$pid"
  for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$pid" 2>/dev/null && { echo "server $pid alive after TERM" >&2; exit 1; }
  "$MINI" audit --host "$HOST" --config "$CONFIG" >"$D/audit-$1.out" 2>"$D/audit-$1.err"
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$W/public/serve-k11-$1.log" 2>&1 </dev/null &
  echo $! >"$pidfile"
  for i in $(seq 1 6000); do
    [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-k11-$1.log" 2>/dev/null && break; sleep 0.1
  done
}
restart r1
for s in sa sb sc; do
  run "tail-$s-after" "$MINI" workspace --action tail --dir "$BW" --name "$s-view" --from 1 --count 16
  row "tail-$s-after" read
  if cmp -s "$D/tail-$s-before.out" "$D/tail-$s-after.out"; then same=identical; else same=DIFFERENT; fi
  printf 'tail-%s-restart\texpect=identical\tgot=%s\t%s entries\n' "$s" "$same" \
    "$(jq '.entries|length' "$D/tail-$s-after.out" 2>/dev/null)" >>"$rows"
  [ "$same" = identical ] || bad=$((bad + 1))
done
restart r2
if [ -s "$D/audit-r1.out" ] && cmp -s "$D/audit-r1.out" "$D/audit-r2.out"; then same=equal; else same=DIFFERENT; fi
printf 'audit-restart\texpect=equal\tgot=%s\t%s\n' "$same" "$(head -c 120 "$D/audit-r1.out" | tr '\n' ' ')" >>"$rows"
[ "$same" = equal ] || bad=$((bad + 1))

cat "$rows" >&2
echo "timeline (B's merge by height): $(jq -c '.' "$D/timeline.json")" >&2
[ "$bad" = 0 ] || { echo "$bad stream rows differ from expectation (see $rows)" >&2; exit 1; }
echo "all stream rows as expected: K=3 six appends, $plans plans, zero re-plans; same-stream second refused; outsider and forged writes refused; tail identical across restart" >&2
echo "$rows"
