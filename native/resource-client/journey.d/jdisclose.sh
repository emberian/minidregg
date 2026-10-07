#!/usr/bin/env bash
# JDISCLOSE (lane FIX-DISCLOSE, AUDIT-ROOMS findings 3, 6, 8, 10) on the journey's live Store.
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
# D. The eight client defects of AUDIT-ROOMS finding 10, one row each.
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
q() {  # q WHO LINE : one shell line; RC
  MINI_KEYCACHE_PASSPHRASE="cache-pass-$1" timeout 600 "$SH" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$(ws_of "$1")" --home "$H/$1" --line "$2" >"$LAST" 2>"$LASTERR"
  RC=$?
}
refused() { grep -m1 '^refused: \|^error: ' "$LASTERR" | sed 's/; encoded refusal.*//' | cut -c1-200; }
enc() { grep -o 'encoded refusal: [0-9a-f]*' "$LASTERR" | head -1 | cut -d' ' -f3; }
printf '{"type":"all","predicates":[]}\n' >"$D/permit-all.json"
enroll() {  # enroll WHO FUND
  local f=$1 subject
  mkdir -p -m 700 "$H/$f"
  q "$f" "keygen mini.key" || die "keygen $f"
  install_private 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/jd-$f.key"
  install_private 0644 "$H/$f/keys/mini.key.next.pub" "$H/sponsor/keys/jd-$f.key.next.pub"
  q sponsor "enroll plan jd-$f jd-$f.key" || die "enroll plan $f: $(refused)"
  q sponsor "enroll seal jd-$f" || die "enroll seal $f"
  q sponsor "enroll submit jd-$f" || die "enroll submit $f: $(refused)"
  subject=$(jq -r '.subject // empty' "$LAST")
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
q alice "room new vault" || die "room new vault"
q alice "invoke v-c2 vault create 2 4242"; q alice "submit v-c2" || die "field 2"
q alice "law v-law vault \"any [ not (verb == write), field 2 <= 3 ]\""; q alice "submit v-law" || die "vault law"
q alice "room invite v-bob vault $BOB --verbs observe --fields 1"; share alice bob v-bob vault
q alice "room invite v-carl vault $CARL --verbs observe,mutate --fields 1"; share alice carl v-carl vault
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
HITS=$(grep -rl 4242 "$WS/carl" "$H/carl" "$WS/bob" "$H/bob" 2>/dev/null | wc -l)
row narrow-homes "no file of bob's or carl's holds 4242" "$HITS files" "$([ "$HITS" = 0 ] && echo 1 || echo 0)"
q alice "law v-open vault open"; q alice "submit v-open"
q alice "invoke v-c9 vault write 2 9 4242"; q alice "submit v-c9" || die "field 2 := 9"
q alice "law v-law2 vault \"any [ not (verb == write), field 2 <= 3 ]\""; q alice "submit v-law2"
q carl "invoke v-w2 vault write 1 1 0"; q carl "submit v-w2"; E2=$(enc)
row narrow-frame-identical "carl's refusal frame equal for field 2 = 4242 and 9" "$(printf %s "$E1" | sha256sum | cut -c1-12) $(printf %s "$E2" | sha256sum | cut -c1-12)" \
  "$([ -n "$E1" ] && [ "$E1" = "$E2" ] && echo 1 || echo 0)"
q alice "invoke v-wa vault write 1 1 0"; q alice "submit v-wa"; R=$(refused)
row narrow-owner "the owner is told the clause and the value" "$R" "$([[ $R == *"field 2 <= 3 (value 9)"* ]] && echo 1 || echo 0)"

# ------------------------------------------------ B. authentication before any target is read
mkdir -p -m 700 "$H/mallory"; q mallory "keygen mini.key" || die "mallory keygen"
VAULT=$(jq -r .target "$WS/alice/refs/vault.json"); BOBCAP=$(jq -r .observeCapability "$WS/bob/refs/vault.json")
probe() {  # probe LABEL TARGET CAP I
  printf '{"grants":[{"capability":"%s","kind":"object","target":"%s"}],"nonce":"8%035d","purpose":{"kind":"object","target":"%s","type":"query","view":"resource"},"subject":"%s"}\n' \
    "$3" "$2" "$4" "$2" "$A" >"$D/raw/$1-$4.json"
  timeout 600 "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" --intent "$D/raw/$1-$4.json" \
    --key "$H/mallory/keys/mini.key" --view resource --dir "$D/raw/$1-$4" >"$LAST" 2>"$LASTERR"
  printf '%s|%s\n' "$(enc)" "$(grep -o 'Host refused [a-z]*' "$LASTERR" | head -1)"
}
for i in 1 2 3; do
  P=$(probe present "$VAULT" "$BOBCAP" $i); X=$(probe absent 999999999999 1234567890123 $i)
  row "unenrolled-$i" "present and absent: one frame, refused at challenge, bad-signature" "$(printf %s "$P" | sha256sum | cut -c1-12) $(printf %s "$X" | sha256sum | cut -c1-12) ${P#*|}" \
    "$([ -n "${P%|*}" ] && [ "$P" = "$X" ] && [[ $P == *challenge* ]] && echo 1 || echo 0)"
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
q alice "room invite st-carl lab $CARL --verbs observe"; q alice "room invite st-eve lab $EVE --verbs observe"; q alice "submit st-eve"
q alice "submit st-carl"; row d8-descent-hint "a stale delegation names its cure" "$(grep -m1 'hint:' "$LASTERR" | cut -c1-80)" \
  "$(grep -q 'Propose it again' "$LASTERR" && echo 1 || echo 0)"
q bob "whoami"; ENC_B=$(jq -r .encryptionKey "$LAST")
q alice "chat new porch" || die "chat new porch"; q alice "chat invite porch $BOB bob"; INV=$(grep '^chat join porch ' "$LAST" | tail -1); q bob "$INV" || die "bob join porch"
q alice "room kick k-bob porch $BOB"; q alice "submit k-bob" || die "kick bob"
q alice "tail --in porch"; HD=$(head -1 "$LAST")
row d7-tail-members "tail counts current members only" "$HD" "$([[ $HD == *"1 members: me"* && $HD == *"no longer members: bob"* ]] && echo 1 || echo 0)"
q alice "chat new hush --private" || die "hush"; q alice "chat invite hush $BOB bob --enc $ENC_B"; INV=$(grep '^chat join hush ' "$LAST" | tail -1); q bob "$INV" || die "bob join hush"
q alice "doc new secrets --in hush" || die "secrets"; q alice "doc append da1 secrets PRIVATE-DOC-LINE-7731"; q alice "submit da1" || die "da1"
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
