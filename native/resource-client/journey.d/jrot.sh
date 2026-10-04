#!/usr/bin/env bash
# JROT (K-PREROTATE, DEOS #19): key pre-rotation on the journey's live Store.
#
# A friend enrolls with a committed next key kept on "other media"; writes; a
# thief holding a copy of the friend's daily key tries to rotate the subject to
# its own key (refused: notPrecommitted) and to the committed next key signing
# with the daily key (refused: unauthenticated, before the gate runs); the friend rotates with the next
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
write_on() {  # write_on WS ID REF FIELD : propose + submit a create of FIELD=1 through reference REF
  scalar "$3" "$4" 1 >"$D/req/$2.json"
  run "$2-propose" "$MINI" workspace --action propose --dir "$1" --request "$D/req/$2.json" --proposal-id "$2" \
    && run "$2-submit" "$MINI" workspace --action submit --dir "$1" \
      --intent "$1/proposals/$2/intent.json" --attempt "$1/attempts/$2"
}
renounce() {  # renounce WS ID REF : propose + submit a renounce of the grant REF names (K-RENOUNCE)
  jq -n --arg n "$3" '{type:"minidregg-workspace-proposal-v1",action:"renounce",name:$n}' >"$D/req/$2.json"
  run "$2-propose" "$MINI" workspace --action propose --dir "$1" --request "$D/req/$2.json" --proposal-id "$2" \
    && run "$2-submit" "$MINI" workspace --action submit --dir "$1" \
      --intent "$1/proposals/$2/intent.json" --attempt "$1/attempts/$2"
}

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
# Include the denied attempts' fields (8 and 9) too: those must fail because
# the grant is revoked or the key is stale, not because a field is undeclared.
run create "$MINI" workspace --action create --dir "$SPONSOR_WS" --name rot --storage declared \
  --predicate "$D/req/permit-all.json" --fields 2,3,4,5,6,7,8,9 \
  || die "create rot: $(tail -1 "$D/create.err")"
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
# A second grant on the same resource, issued under the friend's FIRST key: the
# one the friend renounces after rotating (K-RENOUNCE x K-PREROTATE).
jq -n --arg r "$FRIEND" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"rot",
  recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$D/req/delegate-rn.json"
run rnprop "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/delegate-rn.json" \
  --proposal-id rn-grant || die "second grant propose: $(tail -1 "$D/rnprop.err")"
run rnsub "$MINI" workspace --action submit --dir "$SPONSOR_WS" \
  --intent "$SPONSOR_WS/proposals/rn-grant/intent.json" --attempt "$SPONSOR_WS/attempts/rn-grant" \
  || die "second grant submit: $(tail -1 "$D/rnsub.err")"
run rnpub "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id rn-grant \
  --attempt "$SPONSOR_WS/attempts/rn-grant" || die "second grant publish: $(tail -1 "$D/rnpub.err")"
RNREF=$SPONSOR_WS/proposals/rn-grant/recipient-reference.json
run frnimport "$MINI" workspace --action import --dir "$FW" --name rn --from-ref "$RNREF" || die "friend import rn"
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
# FIX-IDENTITY: a client holding no next key refuses a pre-rotated subject.
run tinit0 "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --key "$D/stolen.key" --subject "$FRIEND" --dir "$D/thief-ws0"
row "init of a pre-rotated subject by a client holding no next key: refused by name" "exit != 0, YOUR next key" \
  "rc=$(cat "$D/tinit0.rc") $(grep -m1 -o 'YOUR next key' "$D/tinit0.err")" \
  "$([ "$(cat "$D/tinit0.rc")" != 0 ] && grep -q 'YOUR next key' "$D/tinit0.err" && [ ! -e "$D/thief-ws0/workspace.json" ] && echo 1 || echo 0)"
run tinit1 "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --key "$D/stolen.key" --subject "$FRIEND" --no-prerotation --dir "$D/thief-ws1"
row "the same with --no-prerotation: refused by name (a key you do not hold could replace yours)" "exit != 0, holds none" \
  "rc=$(cat "$D/tinit1.rc") $(grep -m1 -o 'holds none' "$D/tinit1.err")" \
  "$([ "$(cat "$D/tinit1.rc")" != 0 ] && grep -q 'holds none' "$D/tinit1.err" && [ ! -e "$D/thief-ws1/workspace.json" ] && echo 1 || echo 0)"
# The thief is not bound by an honest client: it names the friend's committed
# next PUBLIC key (public), so its client passes and the Host is what refuses it.
run tinit "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --key "$D/stolen.key" --subject "$FRIEND" --next-pub "$D/friend.key.next.pub" --dir "$AW" \
  || die "thief init: $(tail -1 "$D/tinit.err")"
thief_follow() {  # the thief re-points its client at the friend's current commitment
  jq --arg n "$(xxd -p -c 64 "$D/friend.key.next.pub")" '.nextPublicKey = $n' "$AW/workspace.json" >"$AW/workspace.json.t" \
    && mv "$AW/workspace.json.t" "$AW/workspace.json"
}
run timport "$MINI" workspace --action import --dir "$AW" --name rot --from-ref "$REF" || die "thief import"
run trnimport "$MINI" workspace --action import --dir "$AW" --name rn --from-ref "$RNREF" || die "thief import rn"
"$MINI" keygen --secret "$D/thief.key" --public "$D/thief.pub" --no-prerotation >/dev/null 2>&1 || die "thief keygen"
run trot1 "$MINI" rotate-key --workspace "$AW" --next-key "$D/thief.key"
row "the thief (daily key) rotates to its own key: refused by name" "exit 3, notPrecommitted" \
  "rc=$(cat "$D/trot1.rc") $(refusal trot1)" \
  "$([ "$(cat "$D/trot1.rc")" = 3 ] && grep -q notPrecommitted "$D/trot1.err" && echo 1 || echo 0)"
# The client refuses NEXT == its own daily key file, so the thief signs with a
# copy of the stolen daily key. The generic Receiver verifies the one possession
# claim (the named key over the possession frame) BEFORE the gate runs
# (Kernel.Receiving, 66967962): the refusal is `unauthenticated <claim>`.
# The Host refused trot1 at its plan (op 140): nothing was signed or submitted, so
# the client records that attempt refused, and the next request is a new attempt.
row "a rotation the Host refuses at its plan is recorded refused by the client (no ingress, not wedged)" \
  "custody phase refused, no ingress.bin" \
  "$(jq -r .phase "$AW/attempts/rotate-default/custody.json" 2>/dev/null) ingress=$([ -e "$AW/attempts/rotate-default/ingress.bin" ] && echo yes || echo no)" \
  "$([ "$(jq -r .phase "$AW/attempts/rotate-default/custody.json" 2>/dev/null)" = refused ] && [ ! -e "$AW/attempts/rotate-default/ingress.bin" ] && echo 1 || echo 0)"
cp "$D/stolen.key" "$D/stolen-as-next.key"
run trot2 "$MINI" rotate-key --workspace "$AW" --next-key "$D/stolen-as-next.key" --to-public-key "$D/friend.key.next.pub" \
  --new-attempt possession
row "the thief names the committed next key but signs with the daily key: refused unauthenticated, before the gate" \
  "exit 3, unauthenticated" "rc=$(cat "$D/trot2.rc") $(refusal trot2)" \
  "$([ "$(cat "$D/trot2.rc")" = 3 ] && grep -q unauthenticated "$D/trot2.err" && echo 1 || echo 0)"
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

# An honest client of the OLD key refuses to build on a subject whose commitment
# is no longer its next key (FIX-IDENTITY: every load re-checks).
cp -a "$AW" "$D/thief-ws-honest"
run thonest "$MINI" workspace --action read --dir "$D/thief-ws-honest" --name rot
row "after the rotation, the old key's own client refuses to load the workspace by name" "exit != 0, NOT yours" \
  "rc=$(cat "$D/thonest.rc") $(grep -m1 -o 'NOT yours' "$D/thonest.err")" \
  "$([ "$(cat "$D/thonest.rc")" != 0 ] && grep -q 'NOT yours' "$D/thonest.err" && echo 1 || echo 0)"
thief_follow
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

# A completed rotation attempt replays its own result; a new succession names a new attempt.
run frot2 "$MINI" rotate-key --workspace "$FW" --next-key "$D/offline/friend.next" --new-attempt second
write "$FW" w-second 4
row "a second rotation works and the friend still writes" "epoch 3, installed" \
  "rc=$(cat "$D/frot2.rc") epoch=$(jq -r .keyEpoch "$D/frot2.out" 2>/dev/null)" \
  "$([ "$(cat "$D/frot2.rc")" = 0 ] && [ "$(jq -r .keyEpoch "$D/frot2.out")" = 3 ] && installed "$FW/attempts/w-second/outcome.json" && echo 1 || echo 0)"

# ---------------------------------------------------------------- renounce after rotation
# The grant rn was issued while the friend's first key was current. After two
# rotations only the CURRENT key may give it up: the old key's renounce is
# refused and changes nothing; the new key's is admitted and revokes exactly rn.
thief_follow
renounce "$AW" rn-thief rn
rc_thief=$(cat "$D/rn-thief-submit.rc" 2>/dev/null || cat "$D/rn-thief-propose.rc")
row "the OLD key (stolen, two rotations ago) renounces the friend's grant: refused" "exit != 0, not confirmed" \
  "rc=$rc_thief $(refusal rn-thief-submit)$(refusal rn-thief-propose)" \
  "$([ "$rc_thief" != 0 ] && ! installed "$AW/attempts/rn-thief/outcome.json" && echo 1 || echo 0)"
write_on "$FW" w-rn-1 rn 7
row "the old key's renounce changed nothing: the friend still writes through rn" "installed" \
  "rc=$(cat "$D/w-rn-1-submit.rc" 2>/dev/null)" \
  "$(installed "$FW/attempts/w-rn-1/outcome.json" && echo 1 || echo 0)"
renounce "$FW" rn-friend rn
row "the friend, signing with the CURRENT key (epoch 3), renounces rn: admitted" "confirmed" \
  "rc=$(cat "$D/rn-friend-submit.rc" 2>/dev/null) $(jq -r '.type // empty' "$FW/attempts/rn-friend/outcome.json" 2>/dev/null)" \
  "$(jq -e '.type == "confirmed"' "$FW/attempts/rn-friend/outcome.json" >/dev/null 2>&1 && echo 1 || echo 0)"
write_on "$FW" w-rn-2 rn 8
row "a write through the renounced grant is refused, naming the revocation" "exit != 0, revoked" \
  "$(refusal w-rn-2-propose)$(refusal w-rn-2-submit)" \
  "$(! installed "$FW/attempts/w-rn-2/outcome.json" 2>/dev/null && cat "$D/w-rn-2-propose.err" "$D/w-rn-2-submit.err" 2>/dev/null | grep -qi revoked && echo 1 || echo 0)"
write "$FW" w-after-rn 6
row "the renounce took exactly rn: the friend's other grant (rot) still writes" "installed" \
  "rc=$(cat "$D/w-after-rn-submit.rc" 2>/dev/null)" \
  "$(installed "$FW/attempts/w-after-rn/outcome.json" && echo 1 || echo 0)"

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
  --enrollment "$P/enrollment.json" --no-prerotation --dir "$PW" || die "plain init"
run pstat "$MINI" key-status --workspace "$PW"
"$MINI" keygen --secret "$D/plain-next.key" --public "$D/plain-next.pub" --no-prerotation >/dev/null 2>&1
run prot "$MINI" rotate-key --workspace "$PW" --next-key "$D/plain-next.key"
row "a subject enrolled --no-prerotation cannot rotate, as before (refused by name)" \
  "prerotated false; exit 3, notPrerotated" \
  "prerotated=$(jq -r .prerotated "$D/pstat.out") rc=$(cat "$D/prot.rc") $(refusal prot)" \
  "$(jq -e '.prerotated | not' "$D/pstat.out" >/dev/null && [ "$(cat "$D/prot.rc")" = 3 ] && grep -q notPrerotated "$D/prot.err" && echo 1 || echo 0)"

# ---------------------------------------------------------------- FIX-IDENTITY: a sponsor's next key
# The sponsor commits a next key IT holds (and co-signs with it, so the kernel's
# possession rule is met: it cannot tell whose key a key is). The friend's own
# client refuses the subject by name; the friend never builds on it.
"$MINI" keygen --secret "$D/victim.key" --public "$D/victim.pub" >/dev/null 2>"$D/vkeygen.err" || die "victim keygen"
"$MINI" keygen --secret "$D/evil.key" --public "$D/evil.pub" --no-prerotation >/dev/null 2>&1 || die "evil keygen"
run vbad "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
  --name rot-victim0 --new-key "$D/victim.key" --next-public-key "$D/evil.pub" --dir "$D/enroll-victim0"
row "a sponsor's plan naming a next key that did not co-sign: refused by name" "exit != 0, co-signature does not verify" \
  "rc=$(cat "$D/vbad.rc") $(grep -m1 -o 'co-signature does not verify' "$D/vbad.err")" \
  "$([ "$(cat "$D/vbad.rc")" != 0 ] && grep -q 'co-signature does not verify' "$D/vbad.err" && echo 1 || echo 0)"
run vcos "$MINI" enroll --action cosign --public-key "$D/victim.pub" --next-key "$D/evil.key" --output "$D/evil.cosign" \
  || die "evil cosign: $(tail -1 "$D/vcos.err")"
V=$D/enroll-victim
run vplan "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
  --name rot-victim --new-key "$D/victim.key" --next-public-key "$D/evil.pub" --next-cosign "$D/evil.cosign" --dir "$V" \
  && run vseal "$MINI" enroll --action seal --dir "$V" && run vsub "$MINI" enroll --action submit --dir "$V"
row "the sponsor's own next key, co-signed by itself, is admitted (the kernel cannot know whose key it is)" "installed" \
  "rc=$(cat "$D/vsub.rc" 2>/dev/null)" "$([ "$(cat "$D/vsub.rc" 2>/dev/null)" = 0 ] && echo 1 || echo 0)"
run vinit "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --enrollment "$V/enrollment.json" --dir "$D/victim-ws"
row "the friend's init refuses a subject whose committed next key is not his, by name" "exit != 0, NOT yours, no workspace" \
  "rc=$(cat "$D/vinit.rc") $(grep -m1 -o 'NOT yours' "$D/vinit.err")" \
  "$([ "$(cat "$D/vinit.rc")" != 0 ] && grep -q 'NOT yours' "$D/vinit.err" && [ ! -e "$D/victim-ws/workspace.json" ] && echo 1 || echo 0)"
# The honest path: the friend's next key co-signed at keygen, the plan carries it.
"$MINI" keygen --secret "$D/honest.key" --public "$D/honest.pub" >/dev/null 2>"$D/hkeygen.err" || die "honest keygen"
H=$D/enroll-honest
run hplan "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
  --name rot-honest --new-key "$D/honest.key" --dir "$H" \
  && run hseal "$MINI" enroll --action seal --dir "$H" && run hsub "$MINI" enroll --action submit --dir "$H" \
  && run hinit "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --enrollment "$H/enrollment.json" --dir "$D/honest-ws"
row "an enrollment co-signed by the friend's own next key: admitted, and the friend's init accepts it" "installed, init 0" \
  "submit=$(cat "$D/hsub.rc" 2>/dev/null) init=$(cat "$D/hinit.rc" 2>/dev/null) cosign=$(jq -r .nextCosign "$H/request.json" | cut -c1-16)" \
  "$([ "$(cat "$D/hinit.rc" 2>/dev/null)" = 0 ] && jq -e '.prerotation == true' "$D/honest-ws/workspace.json" >/dev/null && echo 1 || echo 0)"

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
