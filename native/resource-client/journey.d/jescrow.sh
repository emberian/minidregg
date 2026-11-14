#!/usr/bin/env bash
# JESC (R8, PRIVATE-CELL.md "Key loss"): the escrow loop, ending at the Host's decision.
#
#   enc-public       the sponsor's hybrid (X25519 + ML-KEM-768) public key, twice the same
#   enc-key-id       its 32-byte id
#   keygen escrow    a friend's key written with --escrow-to-sponsor: the .escrow file beside the public key
#   escrow-recover   the wrong subject and the wrong sponsor key are refused (client-side: nothing is
#                    sent, nothing is written); the right ones write a key byte-identical to the
#                    friend's and print its public half; a second recovery over it is refused
#   the Host         the friend (enrolled from the ORIGINAL key by the sponsor) holds an observe grant;
#                    a workspace opened with the RECOVERED key and the friend's subject reads the
#                    resource: the Host answers the signed read as the friend (admitted), and the value
#                    the sponsor wrote comes back. A key that is not the friend's is refused by the
#                    Host (J5's stranger rows), so the read is the proof the recovered key signs as them.
#
# The escrow is bound to a label the sponsor and friend agree on (the friend's request label here:
# the subject is assigned only after the key exists). Hook contract: journey.sh (executed). Needs
# MINI HOST CONFIG SOCKET SPONSOR_WS JOURNEY_STEP_DIR JOURNEY_WORLD. Last stdout line: the row table.
set -u
umask 077
HERE=$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
. "$HERE/lib/rows.sh"
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}" "${JOURNEY_WORLD:?}"
rows_init JESC
K=$D/keys; mkdir -m 700 "$K" "$D/req"
LABEL=escrow-friend-$(od -An -N4 -tx1 /dev/urandom | tr -d ' \n')
RES=esc$(od -An -N4 -tx1 /dev/urandom | tr -d ' \n')
hex() { od -An -tx1 -v "$1" | tr -d ' \n'; }
is_hex() { case "$1" in ""|*[!0-9a-f]*) return 1 ;; *) return 0 ;; esac; }
field_value() { jq -r --arg f "$2" '[.cell.entries[]? | select(.key.field == $f) | .value][0] // "absent"' "$1"; }
SP_KEY=$(jq -r .key "$SPONSOR_WS/workspace.json")

run encpub1 "$MINI" enc-public --secret "$SP_KEY"; SPUB=$(tr -d '\n' <"$OUT")
run encpub2 "$MINI" enc-public --secret "$SP_KEY"
row "enc-public: the sponsor's hybrid public key, the same on a second call" "lowercase hex, equal twice" \
  "rc $RC, ${#SPUB} hex chars, equal=$([ "$SPUB" = "$(tr -d '\n' <"$OUT")" ] && echo yes || echo no)" \
  "$(is_hex "$SPUB" && [ "${#SPUB}" -ge 64 ] && [ "$SPUB" = "$(tr -d '\n' <"$OUT")" ] && echo 1 || echo 0)"
run keyid "$MINI" enc-key-id --secret "$SP_KEY"; KID=$(tr -d '\n' <"$OUT")
row "enc-key-id: its 32-byte id" "64 lowercase hex chars" "rc $RC, '$KID'" \
  "$([ "$RC" = 0 ] && is_hex "$KID" && [ "${#KID}" = 64 ] && echo 1 || echo 0)"

run keygen "$MINI" keygen --secret "$K/friend.key" --public "$K/friend.pub" --escrow-to-sponsor "$SPUB" --escrow-subject "$LABEL"
row "keygen --escrow-to-sponsor: the escrow sits beside the public key" "rc 0, friend.pub.escrow non-empty, 32-byte public key" \
  "rc $RC, escrow $(wc -c <"$K/friend.pub.escrow" 2>/dev/null || echo none) bytes, public $(wc -c <"$K/friend.pub" 2>/dev/null || echo none) bytes" \
  "$([ "$RC" = 0 ] && [ -s "$K/friend.pub.escrow" ] && [ "$(wc -c <"$K/friend.pub")" = 32 ] && echo 1 || echo 0)"
run half "$MINI" keygen --secret "$K/half.key" --public "$K/half.pub" --escrow-to-sponsor "$SPUB"
row "client: --escrow-to-sponsor without --escrow-subject is refused and writes no key" "rc != 0, no half.key" \
  "rc $RC, $(first_line | cut -c1-120)" "$([ "$RC" != 0 ] && [ ! -e "$K/half.key" ] && echo 1 || echo 0)"

run wrongsubj "$MINI" escrow-recover --escrow "$K/friend.pub.escrow" --sponsor-secret "$SP_KEY" --subject not-$LABEL --secret "$K/r-subj.key"
row "client: escrow-recover for another subject is refused and writes no key" "rc != 0, no key written" \
  "rc $RC, $(head -1 "$ERR" | cut -c1-120)" "$([ "$RC" != 0 ] && [ ! -e "$K/r-subj.key" ] && [ -s "$ERR" ] && echo 1 || echo 0)"
run wrongsponsor "$MINI" escrow-recover --escrow "$K/friend.pub.escrow" --sponsor-secret "$K/friend.key" --subject "$LABEL" --secret "$K/r-sponsor.key"
row "client: escrow-recover with a key that is not the sponsor's is refused and writes no key" "rc != 0, no key written" \
  "rc $RC, $(head -1 "$ERR" | cut -c1-120)" "$([ "$RC" != 0 ] && [ ! -e "$K/r-sponsor.key" ] && [ -s "$ERR" ] && echo 1 || echo 0)"
run recover "$MINI" escrow-recover --escrow "$K/friend.pub.escrow" --sponsor-secret "$SP_KEY" --subject "$LABEL" --secret "$K/recovered.key"
row "escrow-recover: the sponsor's recovery prints the friend's public key and writes the friend's key" "stdout = friend.pub hex; recovered.key identical to friend.key" \
  "rc $RC, printed $(tr -d '\n' <"$OUT" | cut -c1-16)…, key identical=$(cmp -s "$K/friend.key" "$K/recovered.key" && echo yes || echo no)" \
  "$([ "$RC" = 0 ] && is_hex "$(tr -d '\n' <"$OUT")" && [ "$(tr -d '\n' <"$OUT")" = "$(hex "$K/friend.pub")" ] && cmp -s "$K/friend.key" "$K/recovered.key" && echo 1 || echo 0)"
run again "$MINI" escrow-recover --escrow "$K/friend.pub.escrow" --sponsor-secret "$SP_KEY" --subject "$LABEL" --secret "$K/recovered.key"
row "client: a second recovery over the written key is refused" "rc != 0, refusing to replace" \
  "rc $RC, $(head -1 "$ERR" | cut -c1-100)" "$([ "$RC" != 0 ] && grep -q 'refusing to replace' "$ERR" && echo 1 || echo 0)"

# ---- the Host: the sponsor enrols the friend from the ORIGINAL key and grants an observe; the RECOVERED
# key then reads as the friend.
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
scalar() { printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"%s","payload":{"type":"scalar","actions":[{"type":"%s","key":{"type":"object","field":"%s"},"value":"%s"}]}}]}\n' "$1" "$2" "$3" "$4"; }
A=$D/enroll
b=$(confirmed_count "$SPONSOR_WS")
run plan "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory --name "$LABEL" --new-key "$K/friend.key" --dir "$A"
run seal "$MINI" enroll --action seal --dir "$A"
run submit "$MINI" enroll --action submit --dir "$A"
FS=$(jq -r '.subject // empty' "$OUT" 2>/dev/null)
row "enroll: the Host admits the friend's ORIGINAL key under the sponsor's factory grant" "outcome confirmed, a subject" \
  "rc $RC, type $(jq -r '.type // "none"' "$A/submit.json" 2>/dev/null), subject '${FS:-none}'" \
  "$([ "$RC" = 0 ] && [ -n "$FS" ] && jq -e '.type == "confirmed"' "$A/submit.json" >/dev/null 2>&1 && echo 1 || echo 0)"

b=$(confirmed_count "$SPONSOR_WS")
run create "$MINI" workspace --action create --dir "$SPONSOR_WS" --name "$RES" --storage declared --predicate "$D/req/permit-all.json" --fields 2
want_admitted "create: the sponsor's resource $RES is admitted" "$b" "$SPONSOR_WS"
b=$(confirmed_count "$SPONSOR_WS")
scalar "$RES" create 2 7 >"$D/req/write.json"
run wpropose "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/write.json" --proposal-id "w-$RES"
run wsubmit "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/w-$RES/intent.json" --attempt "$SPONSOR_WS/attempts/w-$RES"
want_admitted "write: field 2 := 7 is admitted" "$b" "$SPONSOR_WS"
b=$(confirmed_count "$SPONSOR_WS")
jq -n --arg r "${FS:-0}" --arg n "$RES" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:$n,recipient:$r,verbs:["observe"],perRequestBytes:"50000"}' >"$D/req/delegate.json"
run dpropose "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/delegate.json" --proposal-id "g-$RES"
run dsubmit "$MINI" workspace --action submit --dir "$SPONSOR_WS" --intent "$SPONSOR_WS/proposals/g-$RES/intent.json" --attempt "$SPONSOR_WS/attempts/g-$RES"
want_admitted "delegate: the observe grant to the friend's subject is admitted" "$b" "$SPONSOR_WS"
run dpublish "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id "g-$RES" --attempt "$SPONSOR_WS/attempts/g-$RES"

FW=$D/friend-ws
run finit "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" --key "$K/recovered.key" --subject "${FS:-0}" --next-pub "$K/friend.key.next.pub" --dir "$FW"
run fimport "$MINI" workspace --action import --dir "$FW" --name "$RES" --from-ref "$SPONSOR_WS/proposals/g-$RES/recipient-reference.json"
run fread "$MINI" workspace --action read --dir "$FW" --name "$RES"
row "Host: a workspace opened with the RECOVERED key reads as the friend" "signed read answered; field 2 = 7 (what the sponsor wrote)" \
  "rc $RC, field 2 = $(field_value "$OUT" 2 2>/dev/null || echo none), $(head -1 "$ERR" | cut -c1-100)" \
  "$([ "$RC" = 0 ] && [ "$(field_value "$OUT" 2)" = 7 ] && echo 1 || echo 0)"
rows_finish
