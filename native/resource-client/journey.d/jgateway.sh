#!/usr/bin/env bash
# journey.d/jgateway.sh — JGATE: the gateway's content target refuses every other subject's signed
# direct call (cv 01a1177f-1ba6; restores the live check deleted with
# scripts/fn-e1e2/probe_gateway_direct_submit).
#
# The fn consumer gateway is a Mini principal whose content resource carries the subject-locked
# law `request/subject == GATEWAY` (Kernel/FnGatewayPolicy.subjectLocked; checkCurrent requires
# exactly that law before a consumer command is prepared; non_gateway_subject_refused is the
# Lean statement). What this row shows is that the DEPLOYED Host refuses the call, not that the
# model says so:
#
#   A (the sponsor) is the gateway. A creates the content resource `gw` under the open law and
#   delegates observe+mutate on it to B (an ordinary subject), so B's grant is valid and covers
#   the target. A installs the gateway law. Then:
#     - A appends an atom: admitted (the law admits the gateway; control);
#     - B's direct append through its own workspace is refused at the served gate (law-denied);
#     - a call B signed under the open law is refused at authentication after the law;
#     - B's own draft, planned for the current state past the served gates (operator-local
#       `minidregg-host plan-ungated`), signed with B's key and sent raw, is refused by the
#       RECEIVER by the law (DeclaredResourceController.Reject.policyRejected in the operator log;
#       the public reply names nothing);
#     - the Host's read of the target is the same before and after the refused calls.
#
# PLANT (JGATE_PLANT=widen): the installed law also admits B. The row first asserts that the Host
# reports the widened law (the plant APPLIED; a no-op plant fails here, not green), then B's
# append is admitted, so the refusal row goes red. Run it by hand; the journey runs it unplanted.
#
# Hook contract (journey.sh header): MINI SPONSOR_WS NEWCOMER_WS SPONSOR_SUBJECT NEWCOMER_SUBJECT
# JOURNEY_STEP_DIR exported; NEWCOMER_WS is initialized by J4. Exit 0 = every row matched; last stdout line = rows.tsv.
set -uo pipefail
umask 077
for name in MINI HOST CONFIG SOCKET JOURNEY_WORLD SPONSOR_WS NEWCOMER_WS SPONSOR_SUBJECT NEWCOMER_SUBJECT JOURNEY_STEP_DIR; do
  if [ -z "${!name:-}" ]; then echo "jgateway: $name is required" >&2; exit 2; fi
done
PLANT=${JGATE_PLANT:-}
case "$PLANT" in ""|widen) ;; *) echo "jgateway: JGATE_PLANT must be empty or widen" >&2; exit 2;; esac
D=$JOURNEY_STEP_DIR/jgateway
[ ! -e "$D" ] || { echo "jgateway: refusing to reuse $D" >&2; exit 2; }
mkdir -p "$D/req"
ROWS=$D/rows.tsv
printf 'verdict\trow\texpected\tobserved\n' >"$ROWS"
PASS=0 TOTAL=0
WS_A=$SPONSOR_WS WS_B=$NEWCOMER_WS A=$SPONSOR_SUBJECT B=$NEWCOMER_SUBJECT
[ "$A" != "$B" ] || { echo "jgateway: the gateway and the ordinary subject must differ" >&2; exit 2; }

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
rc() { cat "$D/$1.rc"; }
row() {  # row NAME EXPECTED OBSERVED OK(0 = pass)
  TOTAL=$((TOTAL + 1))
  local v=FAIL; [ "$4" = 0 ] && { v=PASS; PASS=$((PASS + 1)); }
  printf '%s\t%s\t%s\t%s\n' "$v" "$1" "$2" "$3" >>"$ROWS"
  printf '%s\t%s\t%s\n' "$v" "$1" "$3" >&2
}
hex() { printf '%s' "$1" | od -An -tx1 | tr -d ' \n'; }
turn() {  # turn WS ID REQUEST -> 0 iff confirmed
  run "$2-propose" "$MINI" workspace --action propose --dir "$1" --request "$3" --proposal-id "jgw-$2"
  [ "$(rc "$2-propose")" = 0 ] || return 1
  run "$2-submit" "$MINI" workspace --action submit --dir "$1" \
    --intent "$1/proposals/jgw-$2/intent.json" --attempt "$1/attempts/jgw-$2"
  [ "$(rc "$2-submit")" = 0 ] && jq -e '.type == "confirmed"' "$1/attempts/jgw-$2/outcome.json" >/dev/null 2>&1
}
refusal() {  # refusal WS ID -> the Host's named refusal for that attempt
  local a=$1/attempts/jgw-$2
  if [ -f "$a/outcome.json" ] && jq -e '.type == "refused"' "$a/outcome.json" >/dev/null 2>&1; then
    printf '%s: %s' "$(jq -r '.phase // empty' "$a/outcome.json" | xxd -r -p)" "$(jq -r '.detail // empty' "$a/outcome.json" | xxd -r -p)"
  elif [ -s "$D/$2-submit.err" ]; then tail -1 "$D/$2-submit.err"
  else printf 'propose: %s' "$(tail -1 "$D/$2-propose.err" 2>/dev/null)"; fi
}
append() {  # append ATOM TEXT -> request file
  jq -n --arg atom "$1" --arg p "$(hex "$2")" '{type:"minidregg-workspace-proposal-v1",action:"invoke",
    targets:[{name:"gw",payload:{type:"content",actions:[{type:"createAtom",atom:$atom,kind:{type:"text"},payload:$p}]}}]}' \
    >"$D/req/append-$1.json"
  echo "$D/req/append-$1.json"
}
target_view() {  # target_view WS NAME -> the Host's read of gw, canonical JSON
  run "read-$2" "$MINI" workspace --action read --dir "$1" --name gw
  jq -S '.cell' "$D/read-$2.out" 2>/dev/null
}
started=$(date +%s)
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
RAW="python3 $HERE/lib/hostraw.py"
OPLOG=$(ls -t "$JOURNEY_WORLD"/public/serve*.log 2>/dev/null | head -1)
[ -f "$OPLOG" ] || { echo "jgateway: no operator log under $JOURNEY_WORLD/public" >&2; exit 1; }

# ---- the gateway's content target, and an ordinary subject's valid grant on it
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/open-law.json"
run create "$MINI" workspace --action create --dir "$WS_A" --name gw --storage content --predicate "$D/req/open-law.json"
row "A (the gateway, subject $A) creates the content target gw" created "rc=$(rc create) $(tail -1 "$D/create.err" | cut -c1-160)" "$(rc create)"
jq -n --arg r "$B" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"gw",
  recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$D/req/grant.json"
turn "$WS_A" grant "$D/req/grant.json"; g=$?
run grant-publish "$MINI" workspace --action publish-delegation --dir "$WS_A" --proposal-id jgw-grant \
  --attempt "$WS_A/attempts/jgw-grant"
run import "$MINI" workspace --action import --dir "$WS_B" --name gw \
  --from-ref "$WS_A/proposals/jgw-grant/recipient-reference.json"
row "A delegates observe+mutate on gw to B (subject $B); B imports the grant" "granted, imported" \
  "grant=$g publish=$(rc grant-publish) import=$(rc import)" \
  "$([ "$g" = 0 ] && [ "$(rc grant-publish)" = 0 ] && [ "$(rc import)" = 0 ]; echo $?)"
turn "$WS_B" b-open "$(append 7501 "B writes while the law is open")"; r=$?
row "control: B's grant covers gw (B appends under the open law)" admitted \
  "$([ $r = 0 ] && echo admitted || echo "refused [$(refusal "$WS_B" b-open | cut -c1-200)]")" "$r"

# B signs one more direct append while the law is still open and does NOT submit it. Its call
# (call.bin) is sent raw after the law: a signature binds the state it was signed on. Its intent
# (B's own draft) is what row (ii) below re-plans for the current state.
turn_prepare() {
  run "$2-propose" "$MINI" workspace --action propose --dir "$1" --request "$3" --proposal-id "jgw-$2"
  [ "$(rc "$2-propose")" = 0 ] || return 1
  run "$2-prepare" "$MINI" workspace --action submit --dir "$1" --intent "$1/proposals/jgw-$2/intent.json"     --attempt "$1/attempts/jgw-$2" --prepare-only true
  [ "$(rc "$2-prepare")" = 0 ] && [ -s "$1/attempts/jgw-$2/call.bin" ] && [ ! -e "$1/attempts/jgw-$2/outcome.bin" ]
}
turn_prepare "$WS_B" b-signed "$(append 7504 "signed before the law, sent after it")"; r=$?
row "B signs a direct append on gw under the open law and holds it (prepared, not submitted)" "call.bin, no outcome"   "$([ $r = 0 ] && echo "call.bin $(stat -c %s "$WS_B/attempts/jgw-b-signed/call.bin")B" || echo "prepare failed [$(tail -1 "$D/b-signed-prepare.err" 2>/dev/null | cut -c1-160)]")" "$r"

# ---- the gateway law
if [ "$PLANT" = widen ]; then
  jq -n --arg a "$A" --arg b "$B" '{type:"any",predicates:[{type:"eq",slot:"request/subject",value:$a},
    {type:"eq",slot:"request/subject",value:$b}]}' >"$D/req/gateway-law.json"
else
  jq -n --arg a "$A" '{type:"eq",slot:"request/subject",value:$a}' >"$D/req/gateway-law.json"
fi
jq -n '{type:"minidregg-workspace-proposal-v1",action:"install-policy",name:"gw",predicate:input}' \
  "$D/req/gateway-law.json" >"$D/req/install.json"
turn "$WS_A" law "$D/req/install.json"; r=$?
row "A installs the gateway law on gw$([ "$PLANT" = widen ] && echo " (PLANT: widened to admit B)")" installed \
  "$(jq -r '.type + " " + (.confirmation // "")' "$WS_A/attempts/jgw-law/outcome.json" 2>/dev/null)" "$r"
# What the Host now reports as gw's law (Lean view over A's own signed read). This is the check
# that the plant, when asked for, is what is installed.
run inspect-law "$MINI" workspace --action inspect --view law --name gw --dir "$WS_A" --json true
cp "$D/inspect-law.out" "$D/installed-law.json" 2>/dev/null
LAW=$(jq -r '.law // empty' "$D/inspect-law.out" 2>/dev/null)
if [ "$PLANT" = widen ]; then
  row "PLANT APPLIED: the Host reports gw's law admitting subject $B as well as $A" "subject == $A and subject == $B"     "inspect rc=$(rc inspect-law); law [$LAW]"     "$([ "$(rc inspect-law)" = 0 ] && [[ "$LAW" == *"subject == $A"* && "$LAW" == *"subject == $B"* ]]; echo $?)"
else
  row "the Host reports gw's law as exactly subject == $A" "subject == $A"     "inspect rc=$(rc inspect-law); law [$LAW]"     "$([ "$(rc inspect-law)" = 0 ] && [ "$LAW" = "subject == $A" ]; echo $?)"
fi

# ---- the gateway writes; the ordinary subject's direct call is refused
turn "$WS_A" a-law "$(append 7502 "the gateway writes under its own law")"; r=$?
row "control: the gateway (A) appends under the gateway law" admitted \
  "$([ $r = 0 ] && echo admitted || echo "refused [$(refusal "$WS_A" a-law | cut -c1-200)]")" "$r"
before=$(target_view "$WS_A" before)
turn "$WS_B" b-direct "$(append 7503 "a direct call that must not land")"; r=$?
why=$(refusal "$WS_B" b-direct)
row "B's signed direct append on gw (valid grant, covered target) is refused by the gateway law" \
  "refused: law-denied, naming request/subject" \
  "$([ $r = 0 ] && echo admitted || echo "[$(printf '%s' "$why" | cut -c1-240)]")" \
  "$([ $r != 0 ] && [[ "$why" == *law-denied* || "$why" == *lawDenied* ]] && [[ "$why" == *request/subject* || "$why" == *subject* ]]; echo $?)"
# (i) The call B signed under the open law, sent now as raw bytes: its signature binds the state it
# was signed on, so it cannot land under the new law (refused at authentication, wrongMessage).
sendraw() {  # sendraw NAME CALL.bin -> D/NAME.reasons.tsv (operator-log entries for this request)
  local m; m=$(stat -c %s "$OPLOG")
  $RAW call "$SOCKET" "$CONFIG" "$HOST" 2 "$2" "$D/$1-reply.bin" >"$D/$1-reply.ms" 2>"$D/$1-reply.err"
  $RAW refusals "$OPLOG" "$m" >"$D/$1.reasons.tsv" 2>/dev/null
}
sendraw held "$WS_B/attempts/jgw-b-signed/call.bin"
n=$(wc -l <"$D/held.reasons.tsv"); reason=$(cut -f3 "$D/held.reasons.tsv" | head -1)
row "a call B signed under the open law does not land after the gateway law (its signature binds the old state)"   "one refusal entry, authoritySignature wrongMessage" "$n: $(printf '%s' "$reason" | cut -c1-200)"   "$([ "$n" = 1 ] && [[ "$reason" == *wrongMessage* ]]; echo $?)"

# (ii) The RECEIVER on a call signed for the CURRENT state. Every shipped client path plans through
# the Host's served gates, which refuse B (above), so the test plans B's own draft without them
# (`minidregg-host plan-ungated`, operator-local), B signs each slot with its own key, the Host
# assembles it, and the raw call goes to the live receiver. The draft is B's held intent; the
# planner re-reads each target's expected root from the current cell.
run plan "$HOST" "$CONFIG" plan-ungated "$WS_B/attempts/jgw-b-signed/intent.bin" "$D/plan.bin"
run plan-view "$HOST" "$CONFIG" inspect plan "$D/plan.bin" "$D/plan.json"
signed=1
if [ "$(rc plan)" = 0 ] && [ "$(rc plan-view)" = 0 ]; then
  (printf '302e020100300506032b657004220420' | xxd -r -p; cat "$JOURNEY_WORLD/newcomer.key") >"$D/b.der"
  openssl pkey -inform DER -in "$D/b.der" -out "$D/b.pem" 2>"$D/b-pem.err"
  rm -f "$D/b.der"
  : >"$D/sigs.txt"
  for i in $(seq 0 $(($(jq '.slots | length' "$D/plan.json") - 1))); do
    jq -r --argjson i "$i" '.slots[$i].header' "$D/plan.json" | xxd -r -p >"$D/slot-$i.bin"
    openssl pkeyutl -sign -inkey "$D/b.pem" -rawin -in "$D/slot-$i.bin" -out "$D/slot-$i.sig" 2>>"$D/sign.err" || break
    xxd -p -c 64 "$D/slot-$i.sig" >>"$D/sigs.txt"
  done
  rm -f "$D/b.pem"
  jq -R . "$D/sigs.txt" | jq -s . >"$D/sigs.json"
  run sigs "$HOST" "$CONFIG" signatures "$D/sigs.json" "$D/sigs.bin"
  run assemble "$HOST" "$CONFIG" assemble "$D/plan.bin" "$D/sigs.bin" "$D/ungated-call.bin"
  [ "$(rc sigs)" = 0 ] && [ "$(rc assemble)" = 0 ] && signed=0
fi
row "B's direct append is planned past the served gates and signed by B for the current state"   "a signed call (plan, sign, assemble)"   "plan=$(rc plan) [$(tail -1 "$D/plan.err" | cut -c1-120)] assemble=$(rc assemble 2>/dev/null || echo -)" "$signed"
sendraw ungated "$D/ungated-call.bin"
n=$(wc -l <"$D/ungated.reasons.tsv"); reason=$(cut -f3 "$D/ungated.reasons.tsv" | head -1)
row "the RECEIVER refuses B's current, correctly signed direct call by the gateway law"   "one refusal entry, the receiver's policy refusal Reject.policyRejected (not a signature or stale-root refusal)"   "$n: $(printf '%s' "$reason" | cut -c1-260)"   "$([ "$signed" = 0 ] && [ "$n" = 1 ] && [[ "$reason" == *DeclaredResourceController.Reject.policyRejected ]] && [[ "$reason" != *Signature* ]]; echo $?)"
after=$(target_view "$WS_A" after)
row "the refused call changed nothing: the Host's read of gw before = after" unchanged \
  "$([ -n "$before" ] && [ "$before" = "$after" ] && echo unchanged || echo "changed or unread (before $(printf '%s' "$before" | sha256sum | cut -c1-12), after $(printf '%s' "$after" | sha256sum | cut -c1-12))")" \
  "$([ -n "$before" ] && [ "$before" = "$after" ]; echo $?)"

echo "$ROWS"
echo "JGATE $PASS/$TOTAL$([ -n "$PLANT" ] && echo " PLANT=$PLANT") ($(( $(date +%s) - started )) s)" >&2
[ "$PASS" = "$TOTAL" ]
