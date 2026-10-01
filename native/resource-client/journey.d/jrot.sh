#!/usr/bin/env bash
# JROT (K-PREROTATE, DEOS #19): key pre-rotation on the journey's live Store.
#
# A friend enrolls with a committed next key kept on "other media"; writes; a
# thief holding a copy of the friend's daily key tries to rotate the subject to
# its own key (refused: notPrecommitted) and to the committed next key signing
# with the daily key (refused: noPossession); the friend rotates with the next
# key (admitted); the thief's next write with the old daily key is refused; the
# friend's grant and resource still work under the new key; a second rotation
# works; a subject enrolled --no-prerotation cannot rotate (notPrerotated), as no
# subject could before; the service restarts and the friend still signs; the
# operator audit re-admits every record (rotations included) through
# NativeHostReplay.
#
# Hook contract: journey.sh exports MINI HOST CONFIG SOCKET SPONSOR_WS
# JOURNEY_WORLD JOURNEY_STEP_DIR. Last stdout line = artifact; last stderr line = detail.
set -u
umask 077
D=$JOURNEY_STEP_DIR/jrot
mkdir -p -m 700 "$D" "$D/offline" "$D/req"
T=$D/jrot.tsv; : >"$T"
W=$JOURNEY_WORLD
N=0; BAD=0

run() {  # run NAME CMD... : records out/err/rc
  local name=$1; shift
  { printf '%q ' "$@"; echo; } >"$D/$name.cmd"
  timeout 600 "$@" >"$D/$name.out" 2>"$D/$name.err"
  echo $? >"$D/$name.rc"
  return "$(cat "$D/$name.rc")"
}
row() {  # row CHECK EXPECTED OBSERVED OK(0/1)
  N=$((N + 1))
  if [ "$4" = 1 ]; then printf 'PASS\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"
  else printf 'FAIL\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"; BAD=$((BAD + 1)); fi
}
die() { echo "$T"; echo "JROT: $*" >&2; exit 1; }
installed() { jq -e '.type == "confirmed" and .confirmation == "installed"' "$1" >/dev/null 2>&1; }
# The Host's named refusal from a client refusal ending (exit 3).
refusal() { grep -m1 '^refused: ' "$D/$1.err" 2>/dev/null | cut -c1-240; }
field_value() { jq -r --arg f "$2" '[.cell.entries[]? | select(.key.field == $f) | .value][0] // "absent"' "$1"; }
scalar() {  # scalar NAME FIELD VALUE
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"%s","payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"%s"},"value":"%s"}]}}]}\n' "$1" "$2" "$3"
}
write() {  # write WS ID FIELD : propose + submit a create of FIELD=1 on `rot`
  scalar rot "$3" 1 >"$D/req/$2.json"
  run "$2-propose" "$MINI" workspace --action propose --dir "$1" --request "$D/req/$2.json" --proposal-id "$2" \
    && run "$2-submit" "$MINI" workspace --action submit --dir "$1" \
      --intent "$1/proposals/$2/intent.json" --attempt "$1/attempts/$2"
}
status_of() { run "$1" "$MINI" key-status --workspace "$2" && cat "$D/$1.out"; }

# ---------------------------------------------------------------- the friend
"$MINI" keygen --secret "$D/friend.key" --public "$D/friend.pub" --next-to "$D/offline/friend.next" \
  >"$D/keygen.out" 2>"$D/keygen.err" || die "friend keygen failed: $(tail -1 "$D/keygen.err")"
[ -f "$D/friend.key.next.pub" ] && [ -f "$D/offline/friend.next" ] || die "keygen made no next key"
grep -q "Keep the next key OFF this machine" "$D/keygen.err"
row "keygen makes the daily key and a next key on other media, with the notice" "next key + notice" \
  "$(ls "$D/offline")" "$([ $? = 0 ] && echo 1 || echo 0)"

A=$D/enroll-friend
run eplan "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
  --name rot-friend --new-key "$D/friend.key" --dir "$A" || die "friend enroll plan: $(tail -1 "$D/eplan.err")"
run eseal "$MINI" enroll --action seal --dir "$A" || die "friend seal: $(tail -1 "$D/eseal.err")"
run esubmit "$MINI" enroll --action submit --dir "$A" || die "friend submit: $(tail -1 "$D/esubmit.err")"
digest=$(jq -r '.key.nextKeyDigest' "$A/command.json")
row "enrollment commits to the next key's digest" "decimal digest in the enrolled record" "$digest" \
  "$(echo "$digest" | grep -Eq '^[0-9]+$' && echo 1 || echo 0)"
FRIEND=$(jq -r .subject "$A/enrollment.json")
FW=$D/friend-ws
run finit "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --enrollment "$A/enrollment.json" --dir "$FW" || die "friend init: $(tail -1 "$D/finit.err")"

# The sponsor's resource and the friend's grant.
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
run create "$MINI" workspace --action create --dir "$SPONSOR_WS" --name rot --storage declared \
  --predicate "$D/req/permit-all.json" || die "create rot: $(tail -1 "$D/create.err")"
jq -n --arg r "$FRIEND" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"rot",
  recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$D/req/delegate.json"
run dprop "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/delegate.json" \
  --proposal-id rot-grant || die "delegate propose: $(tail -1 "$D/dprop.err")"
run dsub "$MINI" workspace --action submit --dir "$SPONSOR_WS" \
  --intent "$SPONSOR_WS/proposals/rot-grant/intent.json" --attempt "$SPONSOR_WS/attempts/rot-grant" \
  || die "delegate submit: $(tail -1 "$D/dsub.err")"
run dpub "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id rot-grant \
  --attempt "$SPONSOR_WS/attempts/rot-grant" || die "publish: $(tail -1 "$D/dpub.err")"
REF=$SPONSOR_WS/proposals/rot-grant/recipient-reference.json
run fimport "$MINI" workspace --action import --dir "$FW" --name rot --from-ref "$REF" || die "friend import"
write "$FW" w-before 2
row "the friend writes under the daily key" "installed" "rc=$(cat "$D/w-before-submit.rc")" \
  "$(installed "$FW/attempts/w-before/outcome.json" && echo 1 || echo 0)"
status_of st0 "$FW" >/dev/null
row "key-status: epoch 1, pre-rotated, the next key matches the commitment" \
  "1 true true" "$(jq -r '"\(.keyEpoch) \(.prerotated) \(.nextKeyMatchesCommitment)"' "$D/st0.out")" \
  "$(jq -e '.keyEpoch == "1" and .prerotated and .isCurrent and .nextKeyMatchesCommitment' "$D/st0.out" >/dev/null && echo 1 || echo 0)"

# ---------------------------------------------------------------- the thief
cp "$D/friend.key" "$D/stolen.key"
AW=$D/thief-ws
run tinit "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --key "$D/stolen.key" --subject "$FRIEND" --dir "$AW" || die "thief init: $(tail -1 "$D/tinit.err")"
run timport "$MINI" workspace --action import --dir "$AW" --name rot --from-ref "$REF" || die "thief import"
"$MINI" keygen --secret "$D/thief.key" --public "$D/thief.pub" --no-prerotation >/dev/null 2>&1 || die "thief keygen"
run trot1 "$MINI" rotate-key --workspace "$AW" --next-key "$D/thief.key"
row "the thief (daily key) rotates to its own key: refused by name" "exit 3, notPrecommitted" \
  "rc=$(cat "$D/trot1.rc") $(refusal trot1)" \
  "$([ "$(cat "$D/trot1.rc")" = 3 ] && grep -q notPrecommitted "$D/trot1.err" && echo 1 || echo 0)"
run trot2 "$MINI" rotate-key --workspace "$AW" --next-key "$D/stolen.key" --to-public-key "$D/friend.key.next.pub"
row "the thief names the committed next key but signs with the daily key: refused by name" \
  "exit 3, noPossession" "rc=$(cat "$D/trot2.rc") $(refusal trot2)" \
  "$([ "$(cat "$D/trot2.rc")" = 3 ] && grep -q noPossession "$D/trot2.err" && echo 1 || echo 0)"
status_of st1 "$FW" >/dev/null
row "after both thief attempts the subject is still at epoch 1 under the daily key" "1 true" \
  "$(jq -r '"\(.keyEpoch) \(.isCurrent)"' "$D/st1.out")" \
  "$(jq -e '.keyEpoch == "1" and .isCurrent' "$D/st1.out" >/dev/null && echo 1 || echo 0)"

# ---------------------------------------------------------------- the friend rotates
old_next=$(sha256sum "$D/offline/friend.next" | cut -d' ' -f1)
run frot1 "$MINI" rotate-key --workspace "$FW" --next-key "$D/offline/friend.next"
row "the friend rotates with the committed next key" "admitted, epoch 2" \
  "rc=$(cat "$D/frot1.rc") epoch=$(jq -r .keyEpoch "$D/frot1.out" 2>/dev/null)" \
  "$([ "$(cat "$D/frot1.rc")" = 0 ] && [ "$(jq -r .keyEpoch "$D/frot1.out")" = 2 ] && echo 1 || echo 0)"
[ "$(sha256sum "$D/offline/friend.next" | cut -d' ' -f1)" != "$old_next" ]
row "the next-key file now holds the key after next" "replaced" "rotated" "$([ $? = 0 ] && echo 1 || echo 0)"

write "$AW" w-thief 9
row "the old daily key's next write is refused" "not installed" \
  "rc=$(cat "$D/w-thief-submit.rc" 2>/dev/null || cat "$D/w-thief-propose.rc") $(refusal w-thief-submit 2>/dev/null || true)$(refusal w-thief-propose 2>/dev/null || true)" \
  "$(installed "$AW/attempts/w-thief/outcome.json" && echo 0 || echo 1)"
THIEF_REASON="$(refusal w-thief-submit 2>/dev/null)$(refusal w-thief-propose 2>/dev/null)"
run tstat "$MINI" key-status --workspace "$AW"
row "the old key is not current; the subject is at epoch 2" "isCurrent false, epoch 2" \
  "$(jq -r '"isCurrent \(.isCurrent) epoch \(.keyEpoch)"' "$D/tstat.out" 2>/dev/null)" \
  "$(jq -e '(.isCurrent | not) and .keyEpoch == "2"' "$D/tstat.out" >/dev/null && echo 1 || echo 0)"

write "$FW" w-after 3
run fread1 "$MINI" workspace --action read --dir "$FW" --name rot
row "the grant survives: the friend writes and reads under the new key" "field 3 = 1, field 2 = 1" \
  "f2=$(field_value "$D/fread1.out" 2) f3=$(field_value "$D/fread1.out" 3)" \
  "$(installed "$FW/attempts/w-after/outcome.json" && [ "$(field_value "$D/fread1.out" 3)" = 1 ] && [ "$(field_value "$D/fread1.out" 2)" = 1 ] && echo 1 || echo 0)"
[ "$(field_value "$D/fread1.out" 9)" = absent ]
row "nothing the thief tried is in the resource" "field 9 absent" "f9=$(field_value "$D/fread1.out" 9)" \
  "$([ $? = 0 ] && echo 1 || echo 0)"

run frot2 "$MINI" rotate-key --workspace "$FW" --next-key "$D/offline/friend.next"
write "$FW" w-second 4
row "a second rotation works and the friend still writes" "epoch 3, installed" \
  "rc=$(cat "$D/frot2.rc") epoch=$(jq -r .keyEpoch "$D/frot2.out" 2>/dev/null)" \
  "$([ "$(cat "$D/frot2.rc")" = 0 ] && [ "$(jq -r .keyEpoch "$D/frot2.out")" = 3 ] && installed "$FW/attempts/w-second/outcome.json" && echo 1 || echo 0)"

# ---------------------------------------------------------------- no pre-rotation
"$MINI" keygen --secret "$D/plain.key" --public "$D/plain.pub" --no-prerotation >"$D/pkeygen.out" 2>"$D/pkeygen.err" \
  || die "plain keygen"
P=$D/enroll-plain
run pplan0 "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
  --name rot-plain --new-key "$D/plain.key" --dir "$P"
row "enrollment without a next key and without --no-prerotation is refused" "exit !=0, names --no-prerotation" \
  "rc=$(cat "$D/pplan0.rc")" \
  "$([ "$(cat "$D/pplan0.rc")" != 0 ] && grep -q -- "--no-prerotation" "$D/pplan0.err" && echo 1 || echo 0)"
rm -rf "$P"
run pplan "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
  --name rot-plain-2 --new-key "$D/plain.key" --no-prerotation --dir "$P" || die "plain plan: $(tail -1 "$D/pplan.err")"
run pseal "$MINI" enroll --action seal --dir "$P" || die "plain seal"
run psub "$MINI" enroll --action submit --dir "$P" || die "plain submit: $(tail -1 "$D/psub.err")"
PW=$D/plain-ws
run pinit "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --enrollment "$P/enrollment.json" --dir "$PW" || die "plain init"
run pstat "$MINI" key-status --workspace "$PW"
"$MINI" keygen --secret "$D/plain-next.key" --public "$D/plain-next.pub" --no-prerotation >/dev/null 2>&1
run prot "$MINI" rotate-key --workspace "$PW" --next-key "$D/plain-next.key"
row "a subject enrolled --no-prerotation cannot rotate, as before (refused by name)" \
  "prerotated false; exit 3, notPrerotated" \
  "prerotated=$(jq -r .prerotated "$D/pstat.out") rc=$(cat "$D/prot.rc") $(refusal prot)" \
  "$(jq -e '.prerotated | not' "$D/pstat.out" >/dev/null && [ "$(cat "$D/prot.rc")" = 3 ] && grep -q notPrerotated "$D/prot.err" && echo 1 || echo 0)"

# ---------------------------------------------------------------- restart
pidf=$W/public/server.pid
pid=$(cat "$pidf")
case "$(ps -o args= -p "$pid" 2>/dev/null)" in *" serve "*"--socket $SOCKET"*) ;; *) die "server $pid is not the journey service";; esac
kids=$(pgrep -P "$pid" | tr '\n' ' ')
kill -TERM "$pid"
for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
kill -0 "$pid" 2>/dev/null && die "server alive 30 s after TERM"
for k in $kids; do for i in $(seq 1 100); do kill -0 "$k" 2>/dev/null || break; sleep 0.1; done; done
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-JROT.log" 2>&1 </dev/null &
echo $! >"$pidf"
for i in $(seq 1 6000); do
  [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-JROT.log" 2>/dev/null && break; sleep 0.1
done
write "$FW" w-restart 5
run fread2 "$MINI" workspace --action read --dir "$FW" --name rot
status_of st2 "$FW" >/dev/null
row "after restart the friend signs at epoch 3 and reads every write" "epoch 3; f2..f5 = 1" \
  "epoch=$(jq -r .keyEpoch "$D/st2.out") f5=$(field_value "$D/fread2.out" 5)" \
  "$(jq -e '.keyEpoch == "3" and .isCurrent' "$D/st2.out" >/dev/null && installed "$FW/attempts/w-restart/outcome.json" && [ "$(field_value "$D/fread2.out" 4)" = 1 ] && [ "$(field_value "$D/fread2.out" 5)" = 1 ] && echo 1 || echo 0)"
"$HOST" "$CONFIG" audit >"$D/audit.out" 2>"$D/audit.err"; arc=$?
row "operator audit re-admits every record, rotations included" "exit 0" \
  "exit=$arc $(tail -1 "$D/audit.out")" "$([ "$arc" = 0 ] && echo 1 || echo 0)"

echo "$T"
if [ "$BAD" = 0 ]; then
  echo "JROT: $N/$N checks; friend subject $FRIEND rotated 1->2->3; thief refused (${THIEF_REASON:-?}); plain subject notPrerotated; audit: $(tail -1 "$D/audit.out")" >&2
  exit 0
fi
echo "JROT: $BAD of $N checks failed (see $T)" >&2
exit 1
