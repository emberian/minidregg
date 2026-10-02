#!/usr/bin/env bash
# journey.d/jpriv1.sh — J-PRIV-1 (PRIVACY §3.1, row 7): a private room on this
# journey's live Store (after J5), through `mini shell` for the room verbs and
# the client contract for stream appends and tails (the `say`/`tail` verbs are
# P-CHAT's; they call the same sealing this hook drives with `--private`).
#
#   setup     alice, bob, carl, dave enrolled, provisioned, initialized; each
#             friend's encryption key is read from its own `whoami`.
#   room      alice founds `lab --private` (k^0 in her cache, the keys cell, her
#             own wrap) and a public control room `pub`; invites bob with his
#             encryption key (the grant + the wrap in one keys write); bob imports.
#   say       alice and bob each append a sealed line to their own stream in lab;
#             each reads the other's line. Every sealed payload, on the wire (the
#             signed intent) and in the tail view, is whole 64-byte blocks.
#   operator  the operator (the sponsor subject) holds an observe grant under lab
#             and no wrap: its signed tail returns the envelopes, the plaintext is
#             absent from its view and from every byte under the Store; the same
#             text said in `pub` IS found by the same scan (both poles).
#   outsider  carl (no grant) is refused the read by the kernel.
#   keyslaw   bob holds mutate under lab and is still refused writing a wrap (the
#             keys cell's law: only the founder writes); alice's link into the keys
#             cell is refused (only atoms); a second wrap at the same (epoch,
#             member) is refused (one atom id per pair).
#   kick      alice kicks bob: revoke + rotate to epoch 1 + rewrap. bob's read is
#             refused; bob's client cannot open the epoch-1 line from the bytes
#             (the sealed marker) and still opens the epoch-0 line from its cache.
#   carl      alice invites carl at epoch 1 (the default: current only): carl
#             opens epoch-1 lines and sees the marker for epoch 0; invited again
#             with --past he opens both.
#   keys      `room keys` lists the epochs each holds; `forget lab 0` and carl's
#             next read prints the marker for epoch 0 again (not re-learned).
#   hosted    dave is listed as a hosted subject: his invite is refused without
#             --i-know and says why; with --i-know it is written.
#   chat      alice founds a private CHAT room (`chat new pc --private`), invites
#             carl with his encryption key; both `say`; the signed say holds no
#             plaintext; carl and alice `tail` each other's lines (P-CHAT wired to
#             seal_for_room / open_in_room); the final Store scan counts them too.
#   restart   the Host restarts; `audit` re-admits the Store; alice still opens.
#
# Hook contract: journey.sh (executed). Last stdout line: the row table. Last
# stderr line: the detail. Exit 0 only when every row is ok.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" \
  "${SPONSOR_WS:?}" "${SPONSOR_SUBJECT:?}" "${JOURNEY_WORLD:?}"
SD=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
H=$SD/h; WS=$SD/w; L=$SD/log; RQ=$SD/req
mkdir -p -m 700 "$H" "$WS" "$L" "$RQ"
TABLE=$SD/jpriv1.tsv
printf 'n\tstep\twho\tline\texpect\trc\tverdict\tnote\n' >"$TABLE"
N=0; FAILED=0; FIRST_FAIL=""
export MINI_HOSTED_SUBJECTS=$SD/hosted-subjects
: >"$MINI_HOSTED_SUBJECTS"

ws_of() { if [ "$1" = sponsor ]; then echo "$SPONSOR_WS"; else echo "$WS/$1"; fi; }
# Each friend's key cache has its own passphrase; the operator (sponsor) has none.
pass_of() { if [ "$1" = sponsor ]; then echo ""; else echo "cache-pass-$1"; fi; }
with_pass() { local who=$1; shift
  if [ -n "$(pass_of "$who")" ]; then MINI_KEYCACHE_PASSPHRASE=$(pass_of "$who") "$@"
  else env -u MINI_KEYCACHE_PASSPHRASE "$@"; fi; }

line() {
  local who=$1 text=$2
  N=$((N + 1))
  local stem; stem=$(printf '%03d-%s' "$N" "$who")
  printf '%s\n' "$text" >"$L/$stem.line"
  with_pass "$who" "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$(ws_of "$who")" --home "$H/$who" --line "$text" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?
  OUT=$L/$stem.out; ERR=$L/$stem.err
}

record() { # step who line expect verdict note
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$1" "$2" "$3" "$4" "$RC" "$5" "$6" >>"$TABLE"
  if [ "$5" != ok ]; then
    FAILED=$((FAILED + 1))
    [ -n "$FIRST_FAIL" ] || FIRST_FAIL="row $N ($1 $2: $3): $6"
  fi
}

first_line() { grep -m1 -E '^(refused|undecided|error|usage): ' "$1"; }
host_words() {
  cat "$1"
  grep -oE 'encoded( refusal)?: [0-9a-f]+' "$1" | awk '{print $NF}' | while read -r hex; do
    printf '%s' "$hex" | xxd -r -p 2>/dev/null | tr -c '[:print:]' ' '; echo
  done
}

ok() {
  line "$2" "$3"
  if [ "$RC" = 0 ]; then record "$1" "$2" "$3" 0 ok ""
  else record "$1" "$2" "$3" 0 FAIL "$(first_line "$ERR") $(tail -1 "$ERR" | cut -c1-200)"; fi
}

# fails STEP WHO LINE RC TEXT: exit RC and TEXT in stderr (the client's or the Host's words).
fails() {
  line "$2" "$3"
  if [ "$RC" = "$4" ] && host_words "$ERR" | grep -q -- "$5"; then
    record "$1" "$2" "$3" "$4" ok "[$5] $(first_line "$ERR" | cut -c1-160)"
  else
    record "$1" "$2" "$3" "$4" FAIL "want rc $4 naming $5; got rc $RC: $(first_line "$ERR") $(tail -1 "$ERR" | cut -c1-200)"
  fi
}

check() {
  local step=$1 what=$2; shift 2
  N=$((N + 1)); RC=-
  if "$@" >/dev/null 2>&1; then record "$step" check "$what" - ok ""
  else record "$step" check "$what" - FAIL "condition false"; fi
}

# expectgot STEP WHAT EXPECT GOT: a row whose verdict is EXPECT == GOT, both printed.
expectgot() {
  N=$((N + 1)); RC=-
  if [ "$3" = "$4" ]; then record "$1" check "$2" "$3" ok "got $4"
  else record "$1" check "$2" "$3" FAIL "got $4"; fi
}

operator() {
  local step=$1 what=$2; shift 2
  N=$((N + 1))
  local stem; stem=$(printf '%03d-operator' "$N")
  "$@" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?
  OUT=$L/$stem.out; ERR=$L/$stem.err
  if [ "$RC" = 0 ]; then record "$step" OPERATOR "$what" 0 ok ""
  else record "$step" OPERATOR "$what" 0 FAIL "$(tail -1 "$ERR")"; fi
}

# raw STEP WHO WHAT EXPECT(ok|TEXT) COMMAND…: a client command outside the shell,
# run with WHO's cache passphrase. EXPECT ok = exit 0; else non-zero naming TEXT.
raw() {
  local step=$1 who=$2 what=$3 expect=$4; shift 4
  N=$((N + 1))
  local stem; stem=$(printf '%03d-%s-raw' "$N" "$who")
  with_pass "$who" "$@" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?
  OUT=$L/$stem.out; ERR=$L/$stem.err
  if [ "$expect" = ok ]; then
    if [ "$RC" = 0 ]; then record "$step" "$who" "$what" 0 ok ""
    else record "$step" "$who" "$what" 0 FAIL "$(tail -1 "$ERR" | cut -c1-240)"; fi
  elif [ "$RC" != 0 ] && host_words "$ERR" | grep -q -- "$expect"; then
    record "$step" "$who" "$what" refused ok "[$expect] $(host_words "$ERR" | grep -o -- "$expect.\{0,80\}" | head -1)"
  else
    record "$step" "$who" "$what" refused FAIL "rc $RC; not naming $expect: $(tail -1 "$ERR" | cut -c1-240)"
  fi
}

finish() {
  echo "$TABLE"
  if [ "$FAILED" = 0 ]; then
    echo "JPRIV1: $N rows ok ($TABLE)" >&2; exit 0
  fi
  echo "JPRIV1: $FAILED of $N rows failed; first: $FIRST_FAIL" >&2; exit 1
}

mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"

# ------------------------------------------------ friends: enroll, provision, init
declare -A SUBJ ENC
for f in alice bob carl dave; do
  mkdir -p -m 700 "$H/$f"
  ok setup "$f" "keygen mini.key"
  operator setup "CUSTODY: copy $f's secret into the sponsor home (enroll plan+seal sign with both keys)" \
    install -D -m 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/jp-$f.key"
  ok setup sponsor "enroll plan jp-$f jp-$f.key $(xxd -p -c 256 "$H/$f/keys/mini.key.next.pub") $(xxd -p -c 256 "$H/$f/keys/mini.key.next.cosign")"
  ok setup sponsor "enroll seal jp-$f"
  ok setup sponsor "enroll submit jp-$f"
  SUBJ[$f]=$(jq -r '.subject // empty' "$OUT")
  check setup "$f is enrolled as its own subject" test -n "${SUBJ[$f]}"
  operator setup "CUSTODY: remove the copy" rm -f "$H/sponsor/keys/jp-$f.key"
  operator setup "PROVISION: factory observation + a funded account owned by $f" \
    "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "jp-$f" --holder "${SUBJ[$f]}" \
      --funding 1000 --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator setup "DELIVER: the birth context into $f's HOME/provision/" \
    install -D -m 0600 "$SPONSOR_WS/provisions/jp-$f/birth-context.json" "$H/$f/provision/birth-context.json"
  ok setup "$f" "init mini.key ${SUBJ[$f]}"
  ok setup "$f" "whoami"
  ENC[$f]=$(jq -r '.encryptionKey // empty' "$OUT")
  check setup "$f's whoami prints a 32-byte encryption key that is not its signing key" \
    sh -c "[ \${#1} = 64 ] && [ \"\$1\" != \"\$(od -An -tx1 -v '$H/$f/keys/mini.key.pub' | tr -d ' \n')\" ]" _ "${ENC[$f]}"
done
A=${SUBJ[alice]} B=${SUBJ[bob]} C=${SUBJ[carl]} D=${SUBJ[dave]}
SPONSOR_ENC=$("$MINI" enc-public --secret "$(jq -r .key "$SPONSOR_WS/workspace.json")")

handoff() { # STEP WHO ID: submit, publish, export a delegation; the reference lands in REF.
  ok "$1" "$2" "submit $3"
  ok "$1" "$2" "publish $3"
  ok "$1" "$2" "export $3"
  REF=$(cat "$OUT")
}

# ------------------------------------------------ the room
ok room alice "room new lab --private"
check room "lab's reference is private and names its keys cell" \
  jq -e '.room == "private" and (.private.keys | test("^[0-9]+$"))' "$WS/alice/refs/lab.json"
LAB=$(jq -r .target "$WS/alice/refs/lab.json")
KEYS=$(jq -r .private.keys "$WS/alice/refs/lab.json")
check room "the keys cell was born in lab under the keys law naming alice" \
  jq -e --arg a "$A" '.predicates[1].predicates[0].value == $a' \
    "$WS/alice/sources/roomkey-law-lab-keys.json"
ok room alice "room keys lab"
expectgot room "alice holds epoch 0" '[0]' "$(jq -c .held "$OUT")"
ok room alice "room new pub"
ok room alice "room invite i-bob lab $B ${ENC[bob]} --verbs observe,place,append,mutate"
check room "the grant is K-ROOM's delegation under lab (not yet submitted)" \
  jq -e --arg lab "$LAB" '.purpose.draft.command.child.room == $lab' "$WS/alice/proposals/i-bob/intent.json"
check room "the wrap went into the keys cell in the same line (admitted)" \
  jq -e '.type == "confirmed"' "$WS/alice/attempts/i-bob-keys/outcome.json"
handoff room alice i-bob
check room "bob's invitation names lab's keys cell" jq -e --arg k "$KEYS" '.private.keys == $k' <(printf '%s' "$REF")
ok room bob "import lab $REF"
ok room alice "room invite i-bob-pub pub $B --verbs observe,place,append"
handoff room alice i-bob-pub
ok room bob "import pub $REF"

# ------------------------------------------------ streams (K-STREAM), born by the founder
law() { jq -n --arg s "$1" '{type:"any",predicates:[
    {type:"not",predicate:{type:"memberOf",slot:"request/verb",values:["2","7"]}},
    {type:"eq",slot:"request/subject",value:$s}]}' >"$2"; }
law "$A" "$RQ/law-a.json"; law "$B" "$RQ/law-b.json"
raw say alice "births her stream sa in lab" ok "$MINI" workspace --action create --dir "$WS/alice" \
  --name sa --storage stream --predicate "$RQ/law-a.json" --in lab
check say "sa's reference is sealed in lab" jq -e '.sealedIn == "lab"' "$WS/alice/refs/sa.json"
raw say alice "births a stream in lab owned by bob: refused (a room birth is owned by its creator)" ownerNotCreator \
  "$MINI" workspace --action create --dir "$WS/alice" \
  --name sbgift --storage stream --predicate "$RQ/law-b.json" --in lab --owner "$B"
raw say alice "births bob's stream sb in lab (bob's author law; alice owns it)" ok "$MINI" workspace --action create --dir "$WS/alice" \
  --name sb --storage stream --predicate "$RQ/law-b.json" --in lab
raw say alice "births her stream pa in pub" ok "$MINI" workspace --action create --dir "$WS/alice" \
  --name pa --storage stream --predicate "$RQ/law-a.json" --in pub
SA=$(jq -r .target "$WS/alice/refs/sa.json"); SB=$(jq -r .target "$WS/alice/refs/sb.json")
PA=$(jq -r .target "$WS/alice/refs/pa.json")
BCAP=$(jq -r .observeCapability "$WS/bob/refs/lab.json")
raw say bob "imports his own stream with his room grant" ok "$MINI" workspace --action import --dir "$WS/bob" \
  --name sb --kind object --target "$SB" --observe-capability "$BCAP" --operation-capability "$BCAP"
raw say bob "imports alice's stream with his room grant" ok "$MINI" workspace --action import --dir "$WS/bob" \
  --name sa --kind object --target "$SA" --observe-capability "$BCAP"
ACAP=$(jq -r .observeCapability "$WS/alice/refs/lab.json")
raw say alice "imports bob's stream with her room grant" ok "$MINI" workspace --action import --dir "$WS/alice" \
  --name sb-view --kind object --target "$SB" --observe-capability "$ACAP"

T_A0="PRIVATE-ALPHA the lab key is under the third flowerpot"
T_B0="PRIVATE-BRAVO bring the soldering iron on thursday"
T_A1="PRIVATE-DELTA after bob left we moved the meeting"
T_PUB="PUBLIC-CONTROL this line is said in the public room"
SAYN=0
# say WHO STREAM TEXT [--private ROOM]: one append (plan + submit), its proposal id in SAID.
say() {
  local who=$1 stream=$2 text=$3; shift 3
  SAYN=$((SAYN + 1)); SAID="say-$who-$SAYN"
  jq -n --arg n "$stream" --arg x "$text" '{type:"minidregg-workspace-proposal-v1",action:"invoke",
    targets:[{name:$n,payload:{type:"append",topic:"",text:$x}}]}' >"$RQ/$SAID.json"
  raw say "$who" "plans: $text" ok "$MINI" workspace --action propose --dir "$WS/$who" \
    --request "$RQ/$SAID.json" --proposal-id "$SAID" "$@"
  raw say "$who" "submits $SAID" ok "$MINI" workspace --action submit --dir "$WS/$who" \
    --intent "$WS/$who/proposals/$SAID/intent.json" --attempt "$WS/$who/attempts/$SAID"
}
# wire_payload WHO ID: the append payload hex the signed intent carried.
wire_payload() { jq -r '.purpose.draft.command.targets[0].payload.payload' "$WS/$1/proposals/$2/intent.json"; }
FRAME_HEX=$(printf 'DREGG/PRIVATE-CELL/v2' | xxd -p | tr -d '\n')
sealed_on_wire() { # WHO ID: an envelope (frame), whole 64-byte blocks, no plaintext hex
  local p; p=$(wire_payload "$1" "$2")
  case "$p" in "$FRAME_HEX"*) ;; *) return 1;; esac
  [ $(( ${#p} / 2 % 64 )) = 0 ] && ! printf '%s' "$p" | grep -q "$(printf '%s' "$3" | xxd -p | tr -d '\n' | cut -c1-24)"
}

say alice sa "$T_A0"; SAY_A0=$SAID
check say "alice's line left her machine sealed: the envelope frame, $(( $(wire_payload alice "$SAY_A0" | wc -c) / 2 )) bytes = whole 64-byte blocks, no plaintext" \
  sealed_on_wire alice "$SAY_A0" "$T_A0"
say bob sb "$T_B0" --private lab; SAY_B0=$SAID
check say "bob's line left his machine sealed (whole 64-byte blocks)" sealed_on_wire bob "$SAY_B0" "$T_B0"
check say "bob learned epoch 0 from the keys cell on his first sealed write" \
  grep -q "learned epoch(s) \[0\]" "$(ls -t "$L"/*-bob-raw.err | sed -n 2p)"
say alice pa "$T_PUB"; SAY_PUB=$SAID
check say "the public control line left in plaintext" sh -c "[ \"\$1\" = \"\$(printf '%s' '$T_PUB' | xxd -p | tr -d '\n')\" ]" _ "$(wire_payload alice "$SAY_PUB")"

tail_of() { # WHO NAME [--private ROOM]: the signed tail, retained in OUT
  local who=$1 name=$2; shift 2
  raw read "$who" "tail $name $*" ok "$MINI" workspace --action tail --dir "$(ws_of "$who")" --name "$name" --from 1 --count 16 "$@"
}
tail_of bob sa --private lab
expectgot read "bob opens alice's line" "$T_A0" "$(jq -r '.entries[0].private.text' "$OUT")"
check read "every payload in bob's view is whole 64-byte blocks" \
  jq -e '[.entries[].payload | length / 2 % 64] | all(. == 0)' "$OUT"
cp "$OUT" "$SD/bob-tail-sa-e0.json"
tail_of alice sb-view --private lab
expectgot read "alice opens bob's line" "$T_B0" "$(jq -r '.entries[0].private.text' "$OUT")"

# ------------------------------------------------ what the operator sees
jq -n --arg s "$SPONSOR_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"lab",
  recipient:$s,verbs:["observe"],maxCost:"100",room:true}' >"$RQ/op-lab.json"
raw operator alice "grants the operator an observe-only grant under lab (no wrap)" ok "$MINI" workspace --action propose \
  --dir "$WS/alice" --request "$RQ/op-lab.json" --proposal-id op-lab
handoff operator alice op-lab
printf '%s\n' "$REF" >"$SD/op-lab-ref.json"
jq -n --arg s "$SPONSOR_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"pub",
  recipient:$s,verbs:["observe"],maxCost:"100",room:true}' >"$RQ/op-pub.json"
raw operator alice "grants the operator an observe-only grant under pub" ok "$MINI" workspace --action propose \
  --dir "$WS/alice" --request "$RQ/op-pub.json" --proposal-id op-pub
handoff operator alice op-pub
printf '%s\n' "$REF" >"$SD/op-pub-ref.json"
operator operator "imports lab" "$MINI" workspace --action import --dir "$SPONSOR_WS" --name jp-lab --from-ref "$SD/op-lab-ref.json"
operator operator "imports pub" "$MINI" workspace --action import --dir "$SPONSOR_WS" --name jp-pub --from-ref "$SD/op-pub-ref.json"
OCAP=$(jq -r .observeCapability "$SPONSOR_WS/refs/jp-lab.json")
OPCAP=$(jq -r .observeCapability "$SPONSOR_WS/refs/jp-pub.json")
operator operator "imports sa with its lab grant" "$MINI" workspace --action import --dir "$SPONSOR_WS" \
  --name jp-sa --kind object --target "$SA" --observe-capability "$OCAP"
operator operator "imports pa with its pub grant" "$MINI" workspace --action import --dir "$SPONSOR_WS" \
  --name jp-pa --kind object --target "$PA" --observe-capability "$OPCAP"
tail_of sponsor jp-sa
cp "$OUT" "$SD/operator-tail-sa.json"
check operator "the operator's signed view of sa carries the entry, digest-verified, as an envelope" \
  jq -e --arg f "$FRAME_HEX" '.entries[0].payloadState == "verified" and (.entries[0].payload | startswith($f))' "$OUT"
check operator "the plaintext is absent from the operator's view (raw and hex)" \
  sh -c "! grep -q 'PRIVATE-ALPHA' \"\$1\" && ! grep -q \"\$(printf PRIVATE-ALPHA | xxd -p)\" \"\$1\"" _ "$OUT"
tail_of sponsor jp-sa --private jp-lab
expectgot operator "the operator's client, holding no key, prints the sealed marker" \
  "[sealed under epoch 0 — you do not hold that key]" "$(jq -r '.entries[0].private' "$OUT")"
tail_of sponsor jp-pa
check operator "control: the operator's view of the public room carries the text (hex of the plaintext)" \
  sh -c "grep -q \"\$(printf PUBLIC-CONTROL | xxd -p)\" \"\$1\"" _ "$OUT"

# The Store's own bytes: every file under the world's store directory, scanned for
# each text raw, hex, and base64-aligned. Private: 0. Public control: > 0.
cat >"$SD/scan.py" <<'PY'
import base64, os, sys
root, texts = sys.argv[1], sys.argv[2:]
blobs = []
for d, _, fs in os.walk(root):
    for f in fs:
        try:
            blobs.append(open(os.path.join(d, f), "rb").read())
        except OSError:
            pass
out = []
for t in texts:
    b = t.encode()
    pats = {"raw": b, "hex": b.hex().encode(), "HEX": b.hex().upper().encode()}
    for k in range(3):
        pats[f"b64_{k}"] = base64.b64encode(b"\0" * k + b)[4 * ((k + 2) // 3):][:16]
    hits = {k: sum(x.count(v) for x in blobs) for k, v in pats.items()}
    out.append(t.split()[0] + ":" + ",".join(f"{k}={v}" for k, v in hits.items()))
print(" ".join(out), f"files={len(blobs)} bytes={sum(map(len, blobs))}")
PY
SCAN=$(python3 "$SD/scan.py" "$W/store" "$T_A0" "$T_B0" "$T_PUB")
echo "$SCAN" >"$SD/store-scan-1.txt"
total_hits() { echo "$SCAN" | tr ' ' '\n' | grep "^$1:" | tr ',' '\n' | grep -o '=[0-9]*' | tr -d = | awk '{s+=$1} END {print s+0}'; }
expectgot operator "the Store's bytes hold alice's private line 0 times in any encoding ($(echo "$SCAN" | grep -o 'files=[0-9]* bytes=[0-9]*'))" 0 "$(total_hits PRIVATE-ALPHA)"
expectgot operator "the Store's bytes hold bob's private line 0 times" 0 "$(total_hits PRIVATE-BRAVO)"
N=$((N + 1)); RC=-
if [ "$(total_hits PUBLIC-CONTROL)" -gt 0 ]; then
  record operator check "control: the same scan finds the public line ($(echo "$SCAN" | tr ' ' '\n' | grep '^PUBLIC-CONTROL:'))" ">0" ok ""
else record operator check "control: the same scan finds the public line" ">0" FAIL "$SCAN"; fi

# ------------------------------------------------ an outsider
operator outsider "carl imports sa with no grant" "$MINI" workspace --action import --dir "$WS/carl" \
  --name sa --kind object --target "$SA" --observe-capability 1
raw outsider carl "reads sa" "no-grant" "$MINI" workspace --action tail --dir "$WS/carl" --name sa --from 1 --count 16
operator outsider "carl imports sa with bob's capability number" "$MINI" workspace --action import --dir "$WS/carl" \
  --name sa-bob --kind object --target "$SA" --observe-capability "$BCAP"
raw outsider carl "reads sa with bob's capability number" "no-grant" "$MINI" workspace --action tail --dir "$WS/carl" --name sa-bob --from 1 --count 16

# ------------------------------------------------ the keys cell's law, on the live Host
raw keyslaw bob "holds mutate under lab and writes a wrap for carl: refused (only the founder writes the keys cell)" "law-denied" \
  "$MINI" workspace --action room-key --op invite --dir "$WS/bob" --name lab --member "$C" --enc-pub "${ENC[carl]}" \
  --proposal-id i-carl-by-bob
check keyslaw "bob's client did plan the wrap write (the Host refused it, not his client)" \
  test -f "$WS/bob/proposals/i-carl-by-bob-keys/intent.json"
jq -n --arg k "$KEYS" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:"lab-keys",
  payload:{type:"content",actions:[{type:"link",link:"77",source:null,target:{type:"document",id:$k},relation:"1"}]}}]}' \
  >"$RQ/keys-link.json"
raw keyslaw alice "plans a link into the keys cell" ok "$MINI" workspace --action propose --dir "$WS/alice" \
  --request "$RQ/keys-link.json" --proposal-id keys-link
raw keyslaw alice "submits it: refused (only atoms)" "law-denied" "$MINI" workspace --action submit --dir "$WS/alice" \
  --intent "$WS/alice/proposals/keys-link/intent.json" --attempt "$WS/alice/attempts/keys-link"
BWRAP=$(jq -c '.purpose.draft.command.targets[0].payload.actions[0]' "$WS/alice/proposals/i-bob-keys/intent.json")
jq -n --argjson a "$BWRAP" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:"lab-keys",
  payload:{type:"content",actions:[$a]}}]}' >"$RQ/dup-wrap.json"
raw keyslaw alice "plans a second wrap at bob's (epoch 0, bob) atom id" ok "$MINI" workspace --action propose --dir "$WS/alice" \
  --request "$RQ/dup-wrap.json" --proposal-id dup-wrap
raw keyslaw alice "submits it: refused (one atom per pair)" "duplicateAddress" "$MINI" workspace --action submit --dir "$WS/alice" \
  --intent "$WS/alice/proposals/dup-wrap/intent.json" --attempt "$WS/alice/attempts/dup-wrap"

# ------------------------------------------------ kick: revoke + rotate + rewrap
ok kick alice "room kick k-bob lab $B"
check kick "the rotation moved lab to epoch 1, wrapped for alice only, and left bob out" \
  jq -e --arg a "$A" --arg b "$B" '.epoch == 1 and .wrappedFor == [$a] and (.leftOut | index($b))' "$OUT"
raw kick bob "reads sa after the kick" "revoked" "$MINI" workspace --action tail --dir "$WS/bob" --name sa --from 1 --count 16
say alice sa "$T_A1"; SAY_A1=$SAID
check kick "alice's epoch-1 line left sealed under epoch 1" \
  sh -c "[ \"\$(printf '%s' \"\$1\" | cut -c$(( ${#FRAME_HEX} + 1 ))-$(( ${#FRAME_HEX} + 8 )))\" = 00000001 ]" _ "$(wire_payload alice "$SAY_A1")"
tail_of alice sa
cp "$OUT" "$SD/alice-tail-sa-e1.json"
expectgot kick "alice opens her epoch-1 line" "$T_A1" "$(jq -r '.entries[1].private.text' "$OUT")"
P1=$(jq -r '.entries[1].payload' "$OUT"); P0=$(jq -r '.entries[0].payload' "$SD/bob-tail-sa-e0.json")
raw kick bob "opens the epoch-1 line from its bytes (given out of band)" ok "$MINI" workspace --action room-key --op open \
  --dir "$WS/bob" --name lab --stream "$SA" --sequence 2 --payload "$P1"
expectgot kick "bob's client cannot: the sealed marker, never a guess" \
  "[sealed under epoch 1 — you do not hold that key]" "$(jq -r .private "$OUT")"
raw kick bob "opens the epoch-0 line he fetched before the kick (his cache)" ok "$MINI" workspace --action room-key --op open \
  --dir "$WS/bob" --name lab --stream "$SA" --sequence 1 --payload "$P0"
expectgot kick "bob keeps the past" "$T_A0" "$(jq -r .private.text "$OUT")"
ok kick bob "room keys lab"
expectgot kick "bob holds epoch 0 only" '[0]' "$(jq -c .held "$OUT")"

# ------------------------------------------------ carl: invited after the kick
ok carl alice "room invite i-carl lab $C ${ENC[carl]} --verbs observe,place,append"
handoff carl alice i-carl
ok carl carl "import lab $REF"
CCAP=$(jq -r .observeCapability "$WS/carl/refs/lab.json")
operator carl "carl imports sa with his room grant" "$MINI" workspace --action import --dir "$WS/carl" \
  --name sa-c --kind object --target "$SA" --observe-capability "$CCAP"
tail_of carl sa-c --private lab
expectgot carl "carl opens the epoch-1 line" "$T_A1" "$(jq -r '.entries[1].private.text' "$OUT")"
expectgot carl "carl does not hold epoch 0: the marker (default: current epoch only)" \
  "[sealed under epoch 0 — you do not hold that key]" "$(jq -r '.entries[0].private' "$OUT")"
ok carl alice "room invite i-carl-past lab $C ${ENC[carl]} --past --verbs observe"
# The wrap of (epoch 0, generation 0, carl): (0 + 1) * 2^96 + carl (Kernel/PrivateRoomKeys.lean wrapAtomId).
check carl "--past wrote only the epoch carl lacked (epoch 0)" \
  jq -e --arg c "$(echo "2^96 + $C" | BC_LINE_LENGTH=0 bc)" '[.purpose.draft.command.targets[0].payload.actions[].atom] == [$c]' \
    "$WS/alice/proposals/i-carl-past-keys/intent.json"
tail_of carl sa-c --private lab
expectgot carl "with --past carl opens the epoch-0 line too" "$T_A0" "$(jq -r '.entries[0].private.text' "$OUT")"

# ------------------------------------------------ room keys; forget
ok keys alice "room keys lab"
expectgot keys "alice holds epochs 0 and 1" '[0,1]' "$(jq -c .held "$OUT")"
ok keys carl "room keys lab"
expectgot keys "carl holds epochs 0 and 1" '[0,1]' "$(jq -c .held "$OUT")"
ok keys carl "forget lab 0"
tail_of carl sa-c --private lab
expectgot keys "after forget, carl's read prints the marker for epoch 0 (not re-learned)" \
  "[sealed under epoch 0 — you do not hold that key]" "$(jq -r '.entries[0].private' "$OUT")"
expectgot keys "and still opens epoch 1" "$T_A1" "$(jq -r '.entries[1].private.text' "$OUT")"
ok keys carl "room keys lab"
expectgot keys "carl's cache: held [1], forgotten [0]" '[1]/[0]' "$(jq -c .held "$OUT")/$(jq -c .forgotten "$OUT")"

# ------------------------------------------------ chat in a private room (P-CHAT x PRIVATE-ROOMS)
# `chat new --private` births the chat room as a private room; `say` seals every
# entry under the room key (empty kernel topic); `tail` opens what this reader
# holds a key for. The text is on no wire and in no Store byte.
T_CA="PRIVATE-ECHO alice says this in pc"
T_CC="PRIVATE-FOXTROT carl answers in pc"
ok chat alice "chat new pc --private"
check chat "pc's reference is a private room naming its keys cell" \
  jq -e '.private.keys | test("^[0-9]+$")' "$WS/alice/refs/pc.json"
ok chat alice "chat invite pc $C carl --enc ${ENC[carl]}"
INV_PC=$(grep '^chat join pc ' "$OUT" | tail -1)
ok chat carl "$INV_PC"
ok chat alice "say $T_CA"
SAY_A=$(ls -td "$WS/alice/proposals"/say-* | head -1)
check chat "alice's signed say (intent.bin, intent.json, proposal.json: the wire) holds no plaintext, raw or hex (it landed: a sealed append refuses a kernel topic); only her local request.json does" \
  sh -c "! grep -q PRIVATE-ECHO \"\$1\"/intent.bin \"\$1\"/intent.json \"\$1\"/proposal.json && ! grep -q \"\$(printf PRIVATE-ECHO | xxd -p)\" \"\$1\"/intent.bin \"\$1\"/intent.json \"\$1\"/proposal.json && grep -q PRIVATE-ECHO \"\$1\"/request.json" _ "$SAY_A"
ok chat carl "say $T_CC"
ok chat carl "tail --json -n 100"
check chat "carl (a member holding the wrap) reads both private lines in the merged feed" \
  sh -c "grep -q 'PRIVATE-ECHO' \"\$1\" && grep -q 'PRIVATE-FOXTROT' \"\$1\"" _ "$OUT"
ok chat alice "tail"
check chat "alice reads carl's private line" grep -q 'PRIVATE-FOXTROT' "$OUT"

# ------------------------------------------------ a member rotates its signing key (FIX-IDENTITY B)
# rotate-key keeps the old encryption secret (KEY.enc-ring) and publishes the new
# public key as carl's record in every private room he is in; the founder's next
# rotation wraps to the record; the keys law lets only carl write his record.
ENC_OLD=${ENC[carl]}
ok rotkey carl "rotate-key mini.key.next"
check rotkey "rotate-key published carl's new encryption key to lab and pc" \
  jq -s -e 'last | [.privateRooms[] | select(.record == "published") | .room] | sort == ["lab","pc"]' "$OUT"
check rotkey "carl's keyring kept the old encryption secret (0600, one entry)" \
  sh -c "[ \"\$(stat -c %a \"\$1\")\" = 600 ] && [ \"\$(jq '.keys | length' \"\$1\")\" = 1 ]" _ "$H/carl/keys/mini.key.enc-ring"
ok rotkey carl "whoami"
ENC_NEW=$(jq -r .encryptionKey "$OUT")
check rotkey "carl's encryption key changed with the seed" test "$ENC_NEW" != "$ENC_OLD"
T_RK="PRIVATE-GOLF alice says this after carl rotated"
ok rotkey alice "room rotate r-pc pc"
# pc's epoch 1 for carl at generation 2 (his key epoch): (1 + 1) * 2^96 + 2 * 2^64 + carl.
RK_ID=$(echo "2 * 2^96 + 2 * 2^64 + $C" | BC_LINE_LENGTH=0 bc)
check rotkey "the rotation wrapped pc's new epoch to carl's RECORD (generation = his key epoch 2, his new key)" \
  jq -e --arg id "$RK_ID" --arg k "$ENC_NEW" '[.purpose.draft.command.targets[0].payload.actions[] | select(.atom == $id and (.payload | startswith($k)))] | length == 1' \
    "$WS/alice/proposals/r-pc/intent.json"
ok rotkey alice "say $T_RK"
ok rotkey carl "tail --json -n 100"
check rotkey "carl opens the epoch sealed after his rotation, and still the line before it" \
  sh -c "grep -q 'PRIVATE-GOLF' \"\$1\" && grep -q 'PRIVATE-ECHO' \"\$1\"" _ "$OUT"
jq -n --arg a "$A" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:"pc-keys",
  payload:{type:"content",actions:[{type:"createAtom",atom:$a,kind:{type:"text"},payload:"00"}]}}]}' >"$RQ/foreign-record.json"
raw rotkey carl "plans alice's record (atom id = alice) in pc's keys cell" ok "$MINI" workspace --action propose \
  --dir "$WS/carl" --request "$RQ/foreign-record.json" --proposal-id foreign-record
raw rotkey carl "submits it: refused (each subject writes only its own record)" "law-denied" "$MINI" workspace --action submit \
  --dir "$WS/carl" --intent "$WS/carl/proposals/foreign-record/intent.json" --attempt "$WS/carl/attempts/foreign-record"
jq -n --arg d "$D" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:"pc-keys",
  payload:{type:"content",actions:[{type:"createAtom",atom:$d,kind:{type:"text"},payload:"00"}]}}]}' >"$RQ/squat-record.json"
raw rotkey alice "the founder plans dave's record (atom id = dave; dave has none yet)" ok "$MINI" workspace --action propose \
  --dir "$WS/alice" --request "$RQ/squat-record.json" --proposal-id squat-record
raw rotkey alice "submits it: refused (the founder cannot write a member's record either)" "law-denied" "$MINI" workspace --action submit \
  --dir "$WS/alice" --intent "$WS/alice/proposals/squat-record/intent.json" --attempt "$WS/alice/attempts/squat-record"

# ------------------------------------------------ a hosted subject (B6)
echo "$D  # dave stands in for hosted Hermes: his key is a session-home file" >"$MINI_HOSTED_SUBJECTS"
fails hosted alice "room invite i-dave lab $D ${ENC[dave]}" 1 "hosted subject"
check hosted "the refusal says why: root could read the room key, and Hermes's provider" \
  grep -q "readable on the box" "$ERR"
check hosted "nothing was proposed or written for dave" sh -c "[ ! -e '$WS/alice/proposals/i-dave' ] && [ ! -e '$WS/alice/proposals/i-dave-keys' ]"
ok hosted alice "room invite i-dave2 lab $D ${ENC[dave]} --i-know --verbs observe"

# ------------------------------------------------ restart; audit
pidfile=$W/public/server.pid
restart() {
  local pid; pid=$(cat "$pidfile")
  kill -TERM "$pid"
  for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$pid" 2>/dev/null && { echo "server $pid alive after TERM" >&2; return 1; }
  "$MINI" audit --host "$HOST" --config "$CONFIG" >"$SD/audit-$1.out" 2>"$SD/audit-$1.err"
  echo $? >"$SD/audit-$1.rc"
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$W/public/serve-jpriv1-$1.log" 2>&1 </dev/null &
  echo $! >"$pidfile"
  for i in $(seq 1 6000); do
    [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-jpriv1-$1.log" 2>/dev/null && break; sleep 0.1
  done
}
operator restart "stop the Host, audit the closed Store, serve again" restart r1
check restart "audit re-admitted the Store (exit 0)" test "$(cat "$SD/audit-r1.rc")" = 0
tail_of alice sa
expectgot restart "alice still opens epoch 1 after the restart" "$T_A1" "$(jq -r '.entries[1].private.text' "$OUT")"
raw restart bob "bob is still refused" "revoked" "$MINI" workspace --action tail --dir "$WS/bob" --name sa --from 1 --count 16
SCAN=$(python3 "$SD/scan.py" "$W/store" "$T_A0" "$T_B0" "$T_A1" "$T_PUB" "$T_CA" "$T_CC")
echo "$SCAN" >"$SD/store-scan-2.txt"
expectgot restart "after everything, the Store holds no private line in any encoding" 0 \
  "$(( $(total_hits PRIVATE-ALPHA) + $(total_hits PRIVATE-BRAVO) + $(total_hits PRIVATE-DELTA) + $(total_hits PRIVATE-ECHO) + $(total_hits PRIVATE-FOXTROT) ))"

finish
