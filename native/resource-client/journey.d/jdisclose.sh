#!/usr/bin/env bash
# JDISCLOSE (lane FIX-DISCLOSE): refusal disclosure, the install guard and eight client defects, on the journey's live Store.
#
# A. A law refusal is narrowed to the requester's field grant: a guest whose grant
#    names field 1 is told no clause over field 2 and never its value; its refusal
#    frame is byte-identical whatever field 2 holds; the owner keeps clause and value.
# B. An observation request authenticates before any target is read: a key that was
#    never enrolled, naming an enrolled subject, gets the same frame, at the same op,
#    for a present and an absent target.
# C. The install guard asks the installer's own question: a law no request by the
#    installer passes is not proposed without --i-lock-myself-out; sealed keeps
#    --allow-unsatisfiable; a law its installer can never change warns.
# D. Eight client defects in the room and document verbs, one row each (d1 … d8).
#
# Hook contract: journey.sh exports MINI HOST CONFIG SOCKET SPONSOR_WS SHELL_BIN
# JOURNEY_WORLD JOURNEY_STEP_DIR. Last stdout line = artifact; last stderr line = detail.
set -u
. "$(dirname "${BASH_SOURCE[0]}")/../journey-private.sh"
umask 077
D=$JOURNEY_STEP_DIR/jdisclose
H=$D/h; WS=$D/w
mkdir -p -m 700 "$D" "$H" "$WS" "$H/sponsor" "$D/raw"
T=$D/jdisclose.tsv; : >"$T"
SH=${SHELL_BIN:-$MINI}
N=0; BAD=0
LAST=$D/last.out; LASTERR=$D/last.err
row() {  # row CHECK EXPECTED OBSERVED OK(0/1)
  N=$((N + 1))
  if [ "$4" = 1 ]; then printf 'PASS\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"
  else printf 'FAIL\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"; BAD=$((BAD + 1)); fi
}
die() { echo "$T"; echo "JDISCLOSE: $*" >&2; exit 1; }
ws_of() { if [ "$1" = sponsor ]; then echo "$SPONSOR_WS"; else echo "$WS/$1"; fi; }
Q=0
q() {  # q WHO LINE : one shell line; RC. Every line's output is retained as raw/NNN-WHO.{line,out,err}.
  local wait
  for _ in 1 2 3; do
    MINI_KEYCACHE_PASSPHRASE="cache-pass-$1" timeout 600 "$SH" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
      --workspace "$(ws_of "$1")" --home "$H/$1" --line "$2" >"$LAST" 2>"$LASTERR"
    RC=$?
    # The Host's per-subject request rate (a468ccad0: 300 signed reads per 60 s) refuses a
    # read with no record and names the wait; the member's cure is to retry after it.
    wait=$(grep -m1 -o 'rate-limited: this subject has used its request rate for now; retry in [0-9]* s' "$LASTERR" | grep -o '[0-9]* s$' | cut -d' ' -f1)
    [ -n "$wait" ] || break
    cp "$LASTERR" "$D/raw/rate-limited-$(printf '%03d' "$((Q + 1))")-$1.err"; sleep "$((wait + 1))"
  done
  Q=$((Q + 1)); local tag; tag=$(printf '%03d-%s' "$Q" "$1")
  printf '%s\n' "$2" >"$D/raw/$tag.line"; cp "$LAST" "$D/raw/$tag.out"; cp "$LASTERR" "$D/raw/$tag.err"
  return "$RC"  # `q ... || die` sees the shell's exit (a usage or error line is 2 or 1), never the assignment's 0
}
refused() { grep -m1 '^refused: \|^error: ' "$LASTERR" | sed 's/; encoded refusal.*//' | cut -c1-200; }
enc() { grep -o 'encoded refusal: [0-9a-f]*' "$LASTERR" | head -1 | cut -d' ' -f3; }
printf '{"type":"all","predicates":[]}\n' >"$D/permit-all.json"
enroll() {  # enroll WHO FUND
  local f=$1 subject
  mkdir -p -m 700 "$H/$f"
  q "$f" "keygen mini.key" || die "keygen $f"
  install_private 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/jd-$f.key"
  # The record commits to the newcomer's NEXT key and that key co-signs (FIX-IDENTITY): `keygen` printed both
  # beside the key; the shell's `enroll plan` takes them as hex (or --no-prerotation), never a file of the home.
  q sponsor "enroll plan jd-$f jd-$f.key $(xxd -p -c 256 "$H/$f/keys/mini.key.next.pub") $(xxd -p -c 256 "$H/$f/keys/mini.key.next.cosign")" || die "enroll plan $f: $(refused)"
  q sponsor "enroll seal jd-$f" || die "enroll seal $f"
  q sponsor "enroll submit jd-$f" || die "enroll submit $f: $(refused)"
  subject=$(jq -r '.subject // empty' "$LAST")
  [ -n "$subject" ] || die "enroll submit $f printed no subject (raw/$(printf '%03d' "$Q")-sponsor.out): $(head -c 160 "$LAST") $(refused)"
  rm -f "$H/sponsor/keys/jd-$f.key"
  "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "jd-$f" --holder "$subject" --funding "$2" \
    --account-predicate "$D/permit-all.json" --factory-ref factory >"$LAST" 2>"$LASTERR" || die "provision $f"
  install_private 0600 "$SPONSOR_WS/provisions/jd-$f/birth-context.json" "$H/$f/provision/birth-context.json"
  q "$f" "init mini.key $subject" || die "init $f"
  echo "$subject" >"$H/$f/subject"
}
subj() { cat "$H/$1/subject"; }
share() {  # share FROM TO ID REFNAME : submit, publish, export, import
  q "$1" "submit $3" || die "submit $3: $(refused)"; q "$1" "publish $3"; q "$1" "export $3"
  local ref; ref=$(cat "$LAST"); q "$2" "import $4 $ref" || die "import $4 by $2"
}

enroll alice 5000; enroll bob 2000; enroll carl 500; enroll eve 500
A=$(subj alice); BOB=$(subj bob); CARL=$(subj carl); EVE=$(subj eve)

# ------------------------------------------------ A. the narrowed law leaf
# The leaf lives on a declared cell born with fields 1,2, not on a room: ROOM-SCHEMA
# v2 (6a173263b) dropped the pre-declared roster slots 2..1000 a v1 room carried, so
# a room cell no longer declares any field for a law's clause to read (the original
# `room new vault` + `create 2` red: undeclaredField 2 at prepare). The guests' field
# grants are delegate proposals narrowed to field 1 (K-FIELDS) -- the same delegate a
# `room invite --fields` compiles to; the shell `delegate` verb has no --fields yet.
# K-FIELD-CLOSURE (2ab6ef007) births a declared cell holding its declaration and NO
# field: field 1 is created here (= 0) so the guests' `write 1 1 0` (value 1, expected
# 0) passes its guard and reaches the law. Without it every write, the owner's
# included, is refused `guard-rejected 0` (the Host names it so; the committed repr is guardRejected 0) at prepare: the expected-0 guard over an
# absent field, which says nothing about the law or the grant.
q alice "create vault declared open 1,2" || die "create vault"
q alice "invoke v-c1 vault create 1 0"; q alice "submit v-c1" || die "field 1: $(refused)"
q alice "invoke v-c2 vault create 2 4242"; q alice "submit v-c2" || die "field 2"
q alice "law v-law vault \"any [ not (verb == write), field 2 <= 3 ]\""; q alice "submit v-law" || die "vault law"
mkdir -p -m 700 "$H/alice/requests"
grant() {  # grant ID SUBJECT VERBS-JSON [CELL [FIELDS-JSON]] : one delegate by alice, by default on vault narrowed to field 1
  printf '{"type":"minidregg-workspace-proposal-v1","action":"delegate","name":"%s","recipient":"%s","verbs":[%s],"maxCost":"50000","fields":[%s]}\n' \
    "${4:-vault}" "$2" "$3" "${5:-\"1\"}" >"$H/alice/requests/jd-$1.json"
  q alice "propose $1 @jd-$1.json" || die "propose $1: $(refused)"
}
grant v-bob "$BOB" '"observe"'; share alice bob v-bob vault
grant v-carl "$CARL" '"observe","mutate"'; share alice carl v-carl vault
q bob "invoke v-wb vault write 1 1 0"; q bob "submit v-wb"; R=$(refused)
row narrow-observe-only "law-denied naming no clause, no 4242" "$R" \
  "$([[ $R == *"outside your grant"* && $R != *4242* ]] && echo 1 || echo 0)"
q carl "invoke v-w1 vault write 1 1 0"; q carl "submit v-w1"; R1=$(refused); E1=$(enc)
row narrow-mutate "law-denied naming no clause, no 4242" "$R1" \
  "$([[ $R1 == *"outside your grant"* && $R1 != *4242* ]] && echo 1 || echo 0)"
q carl "why"; W=$(tr '\n' ' ' <"$LAST"); q carl "can vault"; C=$(tr '\n' ' ' <"$LAST")
q carl "inspect law vault"; L=$(tr '\n' ' ' <"$LAST")
row narrow-views "why/can/inspect law: no 4242; field 2 outside your grant" "$(printf %s "$L" | grep -o 'field 2 = [^)]*)' | head -1)" \
  "$([[ $W$C$L != *4242* && $L == *"outside your grant"* ]] && echo 1 || echo 0)"
# A whole-word match: 4242 as a value, not four digits inside a root, id or hex string.
HITS=$(grep -rlw 4242 "$WS/carl" "$H/carl" "$WS/bob" "$H/bob" 2>/dev/null | wc -l)
row narrow-homes "no file of bob's or carl's holds 4242" "$HITS files" "$([ "$HITS" = 0 ] && echo 1 || echo 0)"
# (After narrow-homes: these drafts name 4242 themselves, in carl's own home.)
# A guard is a read: a narrowed guest must not learn field 2 by guessing it in a write's
# `expected` (or by `create`'s absent guard). The right guess (4242) and a wrong one (5)
# give carl one refusal frame, and neither names 4242.
q carl "invoke v-g1 vault write 2 1 4242"; q carl "submit v-g1"; RG1=$(refused); G1=$(enc)
q carl "invoke v-g2 vault write 2 1 5"; q carl "submit v-g2"; RG2=$(refused); G2=$(enc)
row narrow-guess-frame-identical "carl's write expecting field 2 = 4242 and = 5: one frame and line, no 4242" "$(printf %s "$G1|$RG1" | sha256sum | cut -c1-12) $(printf %s "$G2|$RG2" | sha256sum | cut -c1-12) ${RG1:0:100} / ${RG2:0:100}" \
  "$([ -n "$RG1" ] && [ "$G1|$RG1" = "$G2|$RG2" ] && [[ $RG1 != *4242* ]] && echo 1 || echo 0)"
q alice "law v-open vault open"; q alice "submit v-open"
q alice "invoke v-c9 vault write 2 9 4242"; q alice "submit v-c9" || die "field 2 := 9"
q alice "law v-law2 vault \"any [ not (verb == write), field 2 <= 3 ]\""; q alice "submit v-law2"
q carl "invoke v-w2 vault write 1 1 0"; q carl "submit v-w2"; E2=$(enc)
row narrow-frame-identical "carl's refusal frame equal for field 2 = 4242 and 9" "$(printf %s "$E1" | sha256sum | cut -c1-12) $(printf %s "$E2" | sha256sum | cut -c1-12)" \
  "$([ -n "$E1" ] && [ "$E1" = "$E2" ] && echo 1 || echo 0)"
q alice "invoke v-wa vault write 1 1 0"; q alice "submit v-wa"; R=$(refused)
row narrow-owner "the owner is told the clause and the value" "$R" "$([[ $R == *"field 2 <= 3 (value 9)"* ]] && echo 1 || echo 0)"
# Law 10: every refusal a requester can see names its clause, in words. A write whose expected
# value is wrong is refused by the cell's controller at prepare (operation-rejected); the line and
# `why` carry the clause path (`guard-rejected N`), never the constructor's source spelling.
q alice "invoke v-wg vault write 1 1 7"; q alice "submit v-wg"; RC=$(refused); q alice "why"; WC=$(tr '\n' ' ' <"$LAST")
row refusal-names-clause "operation-rejected line and why name guard-rejected; law-denied names its clause; no raw constructor" \
  "${RC:0:140} | ${WC:0:140} | ${R:0:80}" \
  "$([[ $RC == *"operation-rejected"* && $RC == *"guard-rejected"* && $RC != *guardRejected* && $RC != *"Reject."* \
      && $WC == *"clause: "*"guard-rejected"* && $R == *"field 2 <= 3"* ]] && echo 1 || echo 0)"

# ------------------------------------------------ B. authentication before any target is read
mkdir -p -m 700 "$H/mallory"; q mallory "keygen mini.key" || die "mallory keygen"
VAULT=$(jq -r .target "$WS/alice/refs/vault.json"); BOBCAP=$(jq -r .observeCapability "$WS/bob/refs/vault.json")
probe() {  # probe LABEL TARGET CAP I
  printf '{"grants":[{"capability":"%s","kind":"object","target":"%s"}],"nonce":"8%035d","purpose":{"kind":"object","target":"%s","type":"query","view":"resource"},"subject":"%s"}\n' \
    "$3" "$2" "$4" "$2" "$A" >"$D/raw/$1-$4.json"
  # Thin consent (177826a36) reads no Store, so the client does not pre-refuse a key that is not
  # the subject's (3dd5a7b17's local custody check): the frame reaches the Host, as a hostile
  # client's would, and the Host's own authentication is what is measured.
  MINI_THIN_CONSENT=1 timeout 600 "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" --intent "$D/raw/$1-$4.json" \
    --key "$H/mallory/keys/mini.key" --view resource --dir "$D/raw/$1-$4" >"$LAST" 2>"$LASTERR"
  cp "$LASTERR" "$D/raw/$1-$4.err"
  # The op is read from the attempt itself: a refusal at challenge leaves no challenge.bin
  # (the Host issued none), whatever words the client prints around the refusal line.
  local at=at-challenge; [ -e "$D/raw/$1-$4/challenge.bin" ] && at=after-challenge
  printf '%s|%s|%s\n' "$(enc)" "$at" "$(grep -m1 'refused' "$LASTERR" | sed 's/; encoded refusal.*//' | cut -c1-200)"
}
for i in 1 2 3; do
  P=$(probe present "$VAULT" "$BOBCAP" $i); X=$(probe absent 999999999999 1234567890123 $i)
  row "unenrolled-$i" "present and absent: one frame and line, refused at challenge, bad-signature" "$(printf %s "$P" | sha256sum | cut -c1-12) $(printf %s "$X" | sha256sum | cut -c1-12) ${P#*|}" \
    "$([ -n "${P%%|*}" ] && [ "$P" = "$X" ] && [[ $P == *"|at-challenge|"*bad-signature* ]] && echo 1 || echo 0)"
done

# ------------------------------------------------ C. self-lockout
q alice "create pin declared open" || die "create pin"
q alice "law check \"subject == 12345\""; LC=$(tr '\n' ' ' <"$LAST")
row lockout-check "law check names the lockout and its certificate" "$(printf %s "$LC" | cut -c1-120)" \
  "$([[ $LC == *"LOCKS YOU OUT"* && $LC == *"subject == $A"* ]] && echo 1 || echo 0)"
q alice "law pin1 pin \"subject == 12345\""; R=$(refused)
row lockout-refused "not proposed without --i-lock-myself-out" "rc=$RC $R" "$([ "$RC" != 0 ] && [[ $R == *law-locks-you-out* ]] && echo 1 || echo 0)"
q alice "law pin1 pin \"subject == 12345\" --i-lock-myself-out"; P1=$RC; q alice "submit pin1"
row lockout-flag "proposed and installed with --i-lock-myself-out" "rc=$P1/$RC" "$([ "$P1" = 0 ] && [ "$RC" = 0 ] && echo 1 || echo 0)"
q alice "create sealme declared open"
q alice "law s1 sealme sealed --allow-unsatisfiable"; P1=$RC; q alice "submit s1"
row lockout-sealed "sealed needs only --allow-unsatisfiable, as before" "rc=$P1/$RC" "$([ "$P1" = 0 ] && [ "$RC" = 0 ] && echo 1 || echo 0)"
q alice "create pin2 declared open"
q alice "law p2 pin2 \"any [ not (verb == install), subject == 12345 ]\""; W=$(grep -c 'can never be changed by you' "$LASTERR")
row lockout-relaw-warns "a law its installer can never change: proposed, with a warning" "rc=$RC warnings=$W" "$([ "$RC" = 0 ] && [ "$W" -ge 1 ] && echo 1 || echo 0)"

# ------------------------------------------------ D. client rows
q alice "room new lab --template workroom" || die "template room"
q alice "can --all"; row d1-can-all "can --all with a template room exits 0 and judges lab/..." "rc=$RC lab/ lines $(grep -c '^lab/' "$LAST")" \
  "$([ "$RC" = 0 ] && [ "$(grep -c '^lab/' "$LAST")" -ge 1 ] && echo 1 || echo 0)"
q alice "room ls lab"; row d4-room-ls "room ls on a room made by room new" "rc=$RC $(head -1 "$LAST" | cut -c1-80)" "$([ "$RC" = 0 ] && echo 1 || echo 0)"
row d5-inspect-law "inspect law: a field outside the grant is not 'absent now'" "$(printf %s "$L" | grep -o 'field 2 = [^)]*)' | head -1)" \
  "$([[ $L == *"outside your grant"* && $L != *"absent now"* ]] && echo 1 || echo 0)"
q alice "help forget"; row d6-help-forget "help forget names the caveat" "$(grep -c 'until the room is rotated' "$LAST")" \
  "$([ "$(grep -c 'until the room is rotated' "$LAST")" -ge 1 ] && echo 1 || echo 0)"
# A pending delegation and its staleness (rows d8). Since 8b35fd17c a delegation
# signs its parent by id, not the whole authority root: an unrelated authority write no longer
# stales a pending one (the M8 contention), so st-carl, authored before st-eve landed, is
# admitted. What still moves under a pending delegation is its parent: carl authors a
# re-delegation under his grant on a fresh cell, alice revokes that grant, carl submits. The
# kernel refuses that by its own name, `revoked`, ahead of the descent check; the hint law is
# that a refusal names its cure, so this one must not carry descent's "propose it again"
# (re-proposing under a revoked grant cannot succeed).
q alice "room invite st-carl lab $CARL --verbs observe"; q alice "room invite st-eve lab $EVE --verbs observe"; q alice "submit st-eve"
q alice "submit st-carl"; R=$(refused)
row d8-sibling-not-stale "a delegation authored before an unrelated authority write is still admitted" "rc=$RC $R" "$([ "$RC" = 0 ] && echo 1 || echo 0)"
q alice "create stale declared open 1" || die "create stale"
grant h-carl "$CARL" '"observe","delegate"' stale '"1"'; share alice carl h-carl stale
mkdir -p -m 700 "$H/carl/requests"
printf '{"type":"minidregg-workspace-proposal-v1","action":"delegate","name":"stale","recipient":"%s","verbs":["observe"],"maxCost":"50000","fields":["1"]}\n' \
  "$EVE" >"$H/carl/requests/jd-st-eve.json"
q carl "propose st-eve @jd-st-eve.json" || die "carl propose st-eve: $(refused)"
q alice "revoke rv-carl stale $CARL" || die "revoke rv-carl: $(refused)"; q alice "submit rv-carl" || die "submit rv-carl: $(refused)"
q carl "submit st-eve"; R=$(refused)
row d8-revoked-names-cause "a delegation whose parent was revoked is refused by name, without a wrong cure" "rc=$RC ${R:0:120}" \
  "$([ "$RC" != 0 ] && [[ $R == "refused: revoked:"* ]] && ! grep -q 'Propose it again' "$LASTERR" && echo 1 || echo 0)"
q alice "chat new porch" || die "chat new porch"; q alice "chat invite porch $BOB bob"; INV=$(grep '^chat join porch ' "$LAST" | tail -1); q bob "$INV" || die "bob join porch"
q alice "room kick k-bob porch $BOB"; q alice "submit k-bob" || die "kick bob"
q alice "tail --in porch"; HD=$(head -1 "$LAST")
row d7-tail-members "tail counts current members only" "$HD" "$([[ $HD == *"1 members: me"* && $HD == *"no longer members: bob"* ]] && echo 1 || echo 0)"
# A private room's first invite carries the member's own signed v3 recipient declaration
# (1333 bytes; roomkey.rs invitation_record): bob pins alice's founder key, handed to him
# directly, and prints it; a bare key id names only an already-stored record.
q alice "chat new hush --private" || die "hush"
HUSH=$(jq -r .target "$WS/alice/refs/hush.json"); HUSHK=$(jq -r .private.keys "$WS/alice/refs/hush.json")
KE_B=$(MINI_KEYCACHE_PASSPHRASE=cache-pass-bob "$MINI" key-status --workspace "$WS/bob" | jq -r .keyEpoch)
MINI_KEYCACHE_PASSPHRASE=cache-pass-bob "$MINI" workspace --action room-key --op recipient-record --dir "$WS/bob" \
  --room-id "$HUSH" --keys-cell "$HUSHK" --key-epoch "$KE_B" --founder-key "$(xxd -p -c 256 "$H/alice/keys/mini.key.pub")" \
  >"$D/raw/decl-hush-bob.json" 2>"$D/raw/decl-hush-bob.err" || die "bob recipient-record: $(tail -1 "$D/raw/decl-hush-bob.err")"
install_private 0600 "$D/raw/decl-hush-bob.json" "$H/alice/requests/decl-hush-bob.json"
# bob's key IS a file on this box (every journey member is provisioned here) and his own signed
# record says so (d4e881b37); a private invite to a hosted member is made with --i-know.
q alice "chat invite hush $BOB bob --enc @decl-hush-bob.json --i-know" || die "invite bob to hush: $(refused)"
INV=$(grep '^chat join hush ' "$LAST" | tail -1); q bob "$INV" || die "bob join hush"
# Fresh private text goes through protected-document custody (e32866fe6 / 4564a8faf: a room-key
# envelope is no longer written for new text): `doc protect` enrolls the empty document's audience.
q alice "doc new secrets --in hush" || die "secrets"; q alice "doc protect secrets" || die "protect secrets: $(refused)"
q alice "doc append da1 secrets PRIVATE-DOC-LINE-7731"; q alice "submit da1" || die "da1: $(refused)"
q alice "doc show secrets"; S=$(cat "$LAST")
row d2-doc-show "a sealed doc reads back opened, no envelope bytes" "$(grep -c PRIVATE-DOC-LINE-7731 "$LAST") opened, $(grep -c 'DREGG/PRIVATE-CELL' "$LAST") envelopes" \
  "$([[ $S == *PRIVATE-DOC-LINE-7731* && $S != *DREGG/PRIVATE-CELL* ]] && echo 1 || echo 0)"
T1=$(jq -r .target "$WS/alice/refs/secrets.json"); O1=$(jq -r .observeCapability "$WS/alice/refs/secrets.json"); P1=$(jq -r .operationCapability "$WS/alice/refs/secrets.json")
q alice "import secrets-alias object $T1 $O1 $P1"; q alice "doc append al1 secrets-alias ALIAS-LINE-7731"; q alice "submit al1"
SCAN=$(python3 - "$JOURNEY_WORLD/store/forward-link.sqlite3" <<'PY'
import sqlite3,sys
c=sqlite3.connect("file:"+sys.argv[1]+"?mode=ro",uri=True)
blob=b"".join(r[0] for r in c.execute("select record from durable_log order by height"))
print(blob.count(b"ALIAS-LINE-7731"), blob.count(b"PRIVATE-DOC-LINE-7731"))
PY
)
row d3-alias-sealed "an append through a second name is sealed (store plaintext 0 0)" "rc=$RC store $SCAN" "$([ "$RC" = 0 ] && [ "$SCAN" = "0 0" ] && echo 1 || echo 0)"
HC=$(jq -r .observeCapability "$WS/bob/refs/hush.json")
q bob "import secrets-b object $T1 $HC $HC"; q bob "doc append bb1 secrets-b BOB-PLAIN-7731"; R=$(refused)
row d3-unmarked-refused "a workspace without the mark refuses plaintext into a sealed cell" "rc=$RC $R" "$([ "$RC" != 0 ] && [[ $R == *"holds sealed lines"* ]] && echo 1 || echo 0)"

echo "$T"
[ "$BAD" = 0 ] || { echo "JDISCLOSE: $BAD of $N rows failed" >&2; exit 1; }
echo "JDISCLOSE: $N rows ok ($T)" >&2
