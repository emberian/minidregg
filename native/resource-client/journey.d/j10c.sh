#!/usr/bin/env bash
# journey.d/j10c.sh — K-ROOM 3c: rooms as friends use them, through `mini shell`,
# on this journey's live Store (after J5; extends K10's rows).
#
# Friends are enrolled, provisioned and `init`ed exactly as J12 does. Every
# friend line is typed into that friend's own shell session (`--line`).
#
#   room      alice founds `lab` (open law) and invites bob with narrowed verbs
#             and fields (one delegation `under lab`); bob bears a doc into lab
#             (admitted by the birth gate) and alice reads it through her room
#             grant; `room list` and `room members` show the room.
#   gate      carl (enrolled, provisioned, no grant) is refused bearing a cell
#             into lab by name (`notRoomMember`), with no capability and with
#             bob's capability number.
#   redeleg   bob (not the sponsor) invites dave; dave bears a doc into lab. The
#             journey's newcomer (a workspace with no shared namespace root)
#             re-delegates its own invite: the client fix.
#   J7        alice changes lab's ordinary law: bob's grant still reads and still
#             places. alice installs a law refusing placement by anyone but
#             herself: bob's placement is refused by name (`birthRefused`), his
#             read still admitted — the law decides birth, revocation decides
#             membership.
#   leave     (K-RENOUNCE) carl, invited to observe, tries to renounce bob's
#             grant: refused `notHolder`. bob leaves lab (`room leave`: a renounce
#             of his room grant, signed by him, no management grant): his read is
#             refused `revoked`, his births into lab `notRoomMember`, and dave's
#             grant (delegated from bob's) is dead too; the leave says so. alice
#             and carl are unaffected. A second leave is refused `alreadyRevoked`;
#             the exact retry returns the original receipt. alice re-invites bob:
#             a NEW grant, which reads and places.
#   kick      alice kicks carl (the founder's revocation still works): carl's read
#             is refused. Then the tooth PLACE names (J10): bob bears notes6
#             into lab with his new grant, writes it, and delegates it to dave;
#             alice kicks bob (`room kick` revokes every standing grant he holds
#             under lab). bob's own doc is refused `revoked` (show, append,
#             delegate), and so is dave's delegation of it: a born grant carries
#             the creator's room-grant lineage (`RoomKick.kick_revokes_room_born_
#             authority`). alice still reads and writes it through her room grant
#             (`founder_keeps_room_after_kick`); `room members` drops bob. After
#             the leave, bob's first doc (`notes`) was already refused the same way.
#   realm     alice founds `tide` (--law realm): bob, invited with `place`, is refused
#             bearing a well by the realm's law; carl is refused as a non-member;
#             alice's well is admitted (`fake_realm_asset_refused`).
#   restart   the Host restarts; `audit` re-admits the Store; the refusals and
#             reads stand.
#
# Hook contract: journey.sh (executed). Exported: MINI HOST CONFIG SOCKET
# SHELL_BIN SPONSOR_WS SPONSOR_SUBJECT NEWCOMER_WS NEWCOMER_SUBJECT JOURNEY_WORLD
# JOURNEY_STEP_DIR. Last stdout line: the row table. Last stderr line: the
# detail. Exit 0 only when every row is ok.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" \
  "${SPONSOR_WS:?}" "${SPONSOR_SUBJECT:?}" "${NEWCOMER_WS:?}" "${NEWCOMER_SUBJECT:?}" "${JOURNEY_WORLD:?}"
SD=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
H=$SD/h; WS=$SD/w; L=$SD/log
mkdir -p -m 700 "$H" "$WS" "$L"
TABLE=$SD/j10c.tsv
printf 'n\tstep\twho\tline\texpect\trc\tverdict\tnote\n' >"$TABLE"
N=0; FAILED=0; FIRST_FAIL=""

ws_of() { if [ "$1" = sponsor ]; then echo "$SPONSOR_WS"; else echo "$WS/$1"; fi; }

say() {
  local who=$1 line=$2
  N=$((N + 1))
  local stem; stem=$(printf '%03d-%s' "$N" "$who")
  printf '%s\n' "$line" >"$L/$stem.line"
  "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$(ws_of "$who")" --home "$H/$who" --line "$line" >"$L/$stem.out" 2>"$L/$stem.err"
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

# The Host's words in a stderr file: the text itself, and every hex-encoded
# refusal frame in it (`encoded: HEX` from the shell, `encoded refusal: HEX`
# from the client) decoded to printable bytes.
host_words() {
  cat "$1"
  grep -oE 'encoded( refusal)?: [0-9a-f]+' "$1" | awk '{print $NF}' | while read -r hex; do
    printf '%s' "$hex" | xxd -r -p 2>/dev/null | tr -c '[:print:]' ' '; echo
  done
}

ok() {
  say "$2" "$3"
  if [ "$RC" = 0 ]; then record "$1" "$2" "$3" 0 ok ""
  else record "$1" "$2" "$3" 0 FAIL "$(first_line "$ERR")"; fi
}

# named STEP WHO LINE TEXT: refused by the Host (exit 3), and the Host's own
# words (the shell's stderr or its retained decoding) name TEXT.
named() {
  local step=$1 who=$2 line=$3 text=$4 evidence decoded
  say "$who" "$line"
  if [ "$RC" != 3 ]; then record "$step" "$who" "$line" 3 FAIL "rc $RC: $(first_line "$ERR")"; return; fi
  evidence=$(sed -n 's/^  evidence: //p' "$ERR" | head -1)
  decoded=${evidence%.bin}.json
  if host_words "$ERR" | grep -q -- "$text" || { [ -n "$evidence" ] && grep -q -- "$text" "$decoded" 2>/dev/null; }; then
    record "$step" "$who" "$line" 3 ok "$(first_line "$ERR" | cut -c1-140) [$text]"
  else
    record "$step" "$who" "$line" 3 FAIL "refused, but not naming $text: $(first_line "$ERR")"
  fi
}

# refused STEP WHO LINE REASON: exit 3 with `refused: REASON:` first.
refused() {
  local first
  say "$2" "$3"
  first=$(first_line "$ERR")
  case "$RC:$first" in
    "3:refused: $4: "*) record "$1" "$2" "$3" 3 ok "$first" ;;
    *) record "$1" "$2" "$3" 3 FAIL "want refused: $4; got rc $RC: $first" ;;
  esac
}

fails() {
  local first
  say "$2" "$3"
  first=$(first_line "$ERR")
  case "$RC:$first" in
    "$4:"*"$5"*) record "$1" "$2" "$3" "$4" ok "$first" ;;
    *) record "$1" "$2" "$3" "$4" FAIL "want rc $4 with …$5…; got rc $RC: $first" ;;
  esac
}

check() {
  local step=$1 what=$2; shift 2
  N=$((N + 1)); RC=-
  if "$@" >/dev/null 2>&1; then record "$step" check "$what" - ok ""
  else record "$step" check "$what" - FAIL "condition false"; fi
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

# raw STEP WHO WHAT EXPECT(ok|TEXT) COMMAND…: a client command outside the
# shell (the well verb has no shell spelling); EXPECT ok = exit 0, else the
# Host refused (non-zero) naming TEXT.
raw() {
  local step=$1 who=$2 what=$3 expect=$4; shift 4
  N=$((N + 1))
  local stem; stem=$(printf '%03d-%s-raw' "$N" "$who")
  "$@" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?
  OUT=$L/$stem.out; ERR=$L/$stem.err
  if [ "$expect" = ok ]; then
    if [ "$RC" = 0 ]; then record "$step" "$who" "$what" 0 ok ""
    else record "$step" "$who" "$what" 0 FAIL "$(tail -1 "$ERR" | cut -c1-200)"; fi
  elif [ "$RC" != 0 ] && host_words "$ERR" | grep -q -- "$expect"; then
    record "$step" "$who" "$what" refused ok "[$expect] $(host_words "$ERR" | grep -o -- "$expect[^ ]*" | head -1)"
  else
    record "$step" "$who" "$what" refused FAIL "rc $RC; not naming $expect: $(tail -1 "$ERR" | cut -c1-200)"
  fi
}

finish() {
  echo "$TABLE"
  if [ "$FAILED" = 0 ]; then
    echo "K10C: $N rows ok ($TABLE)" >&2; exit 0
  fi
  echo "K10C: $FAILED of $N rows failed; first: $FIRST_FAIL" >&2; exit 1
}

mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"

# ------------------------------------------------ friends: enroll, provision, init
declare -A SUBJ
for f in alice bob carl dave; do
  mkdir -p -m 700 "$H/$f"
  ok setup "$f" "keygen mini.key"
  operator setup "CUSTODY: copy $f's secret into the sponsor home (enroll plan+seal sign with both keys)" \
    install -D -m 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/k10c-$f.key"
  ok setup sponsor "enroll plan k10c-$f k10c-$f.key $(xxd -p -c 256 "$H/$f/keys/mini.key.next.pub") $(xxd -p -c 256 "$H/$f/keys/mini.key.next.cosign")"
  ok setup sponsor "enroll seal k10c-$f"
  ok setup sponsor "enroll submit k10c-$f"
  SUBJ[$f]=$(jq -r '.subject // empty' "$OUT")
  check setup "$f is enrolled as its own subject" test -n "${SUBJ[$f]}"
  operator setup "CUSTODY: remove the copy" rm -f "$H/sponsor/keys/k10c-$f.key"
  operator setup "PROVISION: factory observation + a funded account owned by $f" \
    "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "k10c-$f" --holder "${SUBJ[$f]}" \
      --funding 1000 --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator setup "DELIVER: the birth context into $f's HOME/provision/" \
    install -D -m 0600 "$SPONSOR_WS/provisions/k10c-$f/birth-context.json" "$H/$f/provision/birth-context.json"
  ok setup "$f" "init mini.key ${SUBJ[$f]}"
done
A=${SUBJ[alice]} B=${SUBJ[bob]} C=${SUBJ[carl]} D=${SUBJ[dave]}

# export STEP WHO ID: publish + export a delegation; the reference lands in REF.
handoff() {
  ok "$1" "$2" "submit $3"
  ok "$1" "$2" "publish $3"
  ok "$1" "$2" "export $3"
  REF=$(cat "$OUT")
}

# ------------------------------------------------ the room
ok room alice "room new lab"
check room "lab's reference records it as an open room alice founded" \
  jq -e '.room == "open"' "$WS/alice/refs/lab.json"
LAB=$(jq -r .target "$WS/alice/refs/lab.json")
LABCAP=$(jq -r .operationCapability "$WS/alice/refs/lab.json")
ok room alice "room invite i-bob lab $B --verbs observe,place,delegate --fields 1,2"
check room "the invite is one delegation under lab, narrowed to observe/place/delegate and fields 1,2" \
  jq -e --arg lab "$LAB" '.purpose.draft.command.child.room == $lab
    and (.purpose.draft.command.child.verbs | sort) == ["delegate","observe","place"]
    and .purpose.draft.command.child.fields == ["1","2"]' "$WS/alice/proposals/i-bob/intent.json"
handoff room alice i-bob
ok room bob "import lab $REF"
ok room bob "room list"
check room "bob's room list shows lab as a member's room" grep -q "^lab	member	object $LAB	" "$OUT"
ok room bob "read lab"
ok room bob "doc new notes --in lab"
check room "bob's birth names lab and bob's invite as its placing capability" \
  jq -e --arg lab "$LAB" --arg cap "$(jq -r .operationCapability "$WS/bob/refs/lab.json")" \
    '.birth.resources[0].room == $lab and .birth.resources[0].placement == $cap' \
    "$WS/bob/sources/create-notes.json"
NOTES=$(jq -r .target "$WS/bob/refs/notes.json")
ok room alice "import notes-via-lab object $NOTES $LABCAP"
ok room alice "doc show notes-via-lab"

# ------------------------------------------------ the birth gate
ok gate carl "import lab object $LAB 1"
named gate carl "doc new spam --in lab" notRoomMember
BOBCAP=$(jq -r .operationCapability "$WS/bob/refs/lab.json")
ok gate carl "import lab-bob object $LAB $BOBCAP"
named gate carl "doc new spam2 --in lab-bob" notRoomMember

# ------------------------------------------------ re-delegation by a non-sponsor
ok redeleg bob "room invite i-dave lab $D --verbs observe,place"
handoff redeleg bob i-dave
ok redeleg dave "import lab $REF"
ok redeleg dave "read lab"
ok redeleg dave "doc new dnotes --in lab"
ok redeleg alice "room members lab"
check redeleg "room members lists alice, bob and dave" \
  jq -e --arg a "$A" --arg b "$B" --arg d "$D" '[.members[].subject] as $s
    | ($s | index($a)) and ($s | index($b)) and ($s | index($d))' "$OUT"
check redeleg "the journey newcomer's workspace has no shared namespace root" \
  jq -e '.namespaceRoot == null' "$NEWCOMER_WS/workspace.json"
ok redeleg alice "room invite i-nc lab $NEWCOMER_SUBJECT --verbs observe,place,delegate"
handoff redeleg alice i-nc
printf '%s\n' "$REF" >"$SD/nc-ref.json"
operator redeleg "the newcomer imports its invite" \
  "$MINI" workspace --action import --dir "$NEWCOMER_WS" --name lab3c --from-ref "$SD/nc-ref.json"
# (to the sponsor: a grant to dave here would keep dave a member after bob's kick)
jq -n --arg s "$SPONSOR_SUBJECT" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"lab3c",
  recipient:$s,verbs:["observe"],maxCost:"100",room:true}' >"$SD/nc-redeleg.json"
raw redeleg newcomer "re-delegates its invite to the sponsor (own namespace)" ok \
  "$MINI" workspace --action propose --dir "$NEWCOMER_WS" --request "$SD/nc-redeleg.json" --proposal-id k10c-nc
raw redeleg newcomer "submits the re-delegation" ok \
  "$MINI" workspace --action submit --dir "$NEWCOMER_WS" \
    --intent "$NEWCOMER_WS/proposals/k10c-nc/intent.json" --attempt "$NEWCOMER_WS/attempts/k10c-nc"

# ------------------------------------------------ the J7 pole
ok J7 alice "law l1 lab any [ not (verb == write), field 1 <= 100 ]"
ok J7 alice "submit l1"
ok J7 bob "read lab"
ok J7 bob "doc new notes2 --in lab"
ok J7 alice "law l2 lab any [ not (verb == place), subject in {$A} ]"
ok J7 alice "submit l2"
named J7 bob "doc new notes3 --in lab" birthRefused
ok J7 bob "read lab"
ok J7 alice "doc new anotes --in lab"

# ------------------------------------------------ leave (K-RENOUNCE)
BOBCAP=$(jq -r .operationCapability "$WS/bob/refs/lab.json")
DAVECAP=$(jq -r .operationCapability "$WS/dave/refs/lab.json")
ok leave alice "room invite i-carl lab $C --verbs observe"
handoff leave alice i-carl
ok leave carl "import labc $REF"
ok leave carl "read labc"
ok leave carl "renounce c-bob $BOBCAP"
named leave carl "submit c-bob" notHolder
ok leave bob "read lab"
ok leave bob "room leave l-bob lab"
check leave "the leave is a renounce of bob's own room grant, signed by bob, naming no management grant" \
  jq -e --arg cap "$BOBCAP" --arg b "$B" '.purpose.draft.type == "renounce-source"
    and .purpose.draft.command.capability == $cap and .purpose.draft.command.subject == $b
    and .grants == []' "$WS/bob/proposals/l-bob/intent.json"
check leave "the proposal names dave's grant (delegated from bob's) as ending with it" \
  jq -e --arg d "$DAVECAP" '[.renounce.alsoEnds[].capability] | index($d)' "$WS/bob/proposals/l-bob/proposal.json"
ok leave bob "submit l-bob"
check leave "the leave says what ended with it" grep -q "renounced capability $BOBCAP (object); ended with it: $DAVECAP" "$ERR"
refused leave bob "read lab" revoked
refused leave dave "read lab" revoked
# The tooth for `ancestors`: the doc bob bore with the grant he renounced falls with it.
refused leave bob "doc show notes" revoked
ok leave alice "doc show notes-via-lab"
named leave bob "doc new notes4 --in lab" notRoomMember
ok leave alice "read lab"
ok leave alice "doc new anotes2 --in lab"
ok leave carl "read labc"
ok leave alice "room members lab"
check leave "room members no longer lists bob or dave; still lists alice and carl" \
  jq -e --arg a "$A" --arg b "$B" --arg c "$C" --arg d "$D" '[.members[].subject] as $s
    | (($s | index($b)) | not) and (($s | index($d)) | not) and ($s | index($a)) and ($s | index($c))' "$OUT"
ok leave bob "room leave l-bob2 lab"
named leave bob "submit l-bob2" alreadyRevoked
ok leave bob "retry l-bob"
check leave "the exact retry returns the original receipt (replayed, same transaction)" \
  jq -e -s '.[0].transactionId == .[1].transactionId and .[0].eventId == .[1].eventId
    and .[1].confirmation == "replayed"' "$WS/bob/attempts/l-bob/outcome.json" "$WS/bob/attempts/l-bob/retry-0001.json"
fails leave alice "room leave l-alice lab" 1 "not a room you joined"
ok leave alice "room invite i-bob2 lab $B --verbs observe,place"
handoff leave alice i-bob2
ok leave bob "import lab2 $REF"
check leave "the re-invite is a new capability, not the renounced one" \
  test "$(jq -r .operationCapability "$WS/bob/refs/lab2.json")" != "$BOBCAP"
ok leave bob "read lab2"
# lab's placement law (J7's l2) still admits only alice: the new grant passes
# the membership gate and the law refuses (birthRefused, not notRoomMember).
named leave bob "doc new notes5 --in lab2" birthRefused
ok leave alice "law l3 lab any [ not (verb == write), field 1 <= 100 ]"
ok leave alice "submit l3"
ok leave bob "doc new notes6 --in lab2"
refused leave bob "read lab" revoked

# ------------------------------------------------ kick (the founder's revocation)
ok kick alice "room kick k-carl lab $C"
ok kick alice "submit k-carl"
refused kick carl "read labc" revoked
ok kick bob "read lab2"

# ------------------------------------------------ kick: a doc bob bore falls with him (PLACE J10)
ok kickdoc bob "doc append b-n6 notes6 written-before-the-kick"
ok kickdoc bob "submit b-n6"
ok kickdoc bob "delegate d-n6 notes6 $D observe 1000"
handoff kickdoc bob d-n6
ok kickdoc dave "import n6 $REF"
ok kickdoc dave "doc show n6"
# A grant on one cell under the room, not on the room (as a private room's keys
# cell write): alice's own doc adoc, delegated to bob. The kick reaches it too.
ok kickdoc alice "doc new adoc --in lab"
ok kickdoc alice "delegate d-adoc adoc $B observe 1000"
handoff kickdoc alice d-adoc
ok kickdoc bob "import adoc $REF"
ok kickdoc bob "doc show adoc"
ok kickdoc alice "room kick k-bob lab $B"
check kickdoc "the kick names every standing grant bob holds under lab (his re-invite), from the Host's who view" \
  jq -e --arg cap "$(jq -r .operationCapability "$WS/bob/refs/lab2.json")" '[.capabilities[].capability] | index($cap)' "$OUT"
check kickdoc "and alice's own delegation of adoc (a grant on one cell under lab, revoked through adoc's control)" \
  jq -e --arg cap "$(jq -r .operationCapability "$WS/bob/refs/adoc.json")" '[.capabilities[] | select(.via == "adoc") | .capability] | index($cap)' "$OUT"
ok kickdoc alice "submit k-bob"
refused kickdoc bob "read lab2" revoked
refused kickdoc bob "doc show notes6" revoked
refused kickdoc bob "doc append b-n6b notes6 written-AFTER-the-kick" revoked
refused kickdoc bob "delegate d-n6b notes6 $C observe 1000" revoked
refused kickdoc dave "doc show n6" revoked
refused kickdoc bob "doc show adoc" revoked
named kickdoc bob "doc new notes7 --in lab2" notRoomMember
ok kickdoc alice "import n6a object $(jq -r .target "$WS/bob/refs/notes6.json") $LABCAP"
ok kickdoc alice "doc show n6a"
check kickdoc "the founder reads the line bob wrote before the kick" grep -q written-before-the-kick "$OUT"
ok kickdoc alice "doc append a-n6 n6a the-founder-keeps-the-room"
ok kickdoc alice "submit a-n6"
ok kickdoc alice "room members lab"
check kickdoc "room members no longer lists bob" \
  jq -e --arg b "$B" '[.members[].subject] | index($b) | not' "$OUT"

# ------------------------------------------------ a realm
ok realm alice "room new tide --law realm"
TIDE=$(jq -r .target "$WS/alice/refs/tide.json")
ok realm alice "room invite i-tide tide $B --verbs observe,place"
handoff realm alice i-tide
ok realm bob "import tide $REF"
raw realm bob "bears a well into the realm" birthRefused \
  "$MINI" well --action new --dir "$WS/bob" --name fakegold --in tide --law "$SD/permit-all.json"
ok realm carl "import tide object $TIDE 1"
raw realm carl "bears a well into the realm" notRoomMember \
  "$MINI" well --action new --dir "$WS/carl" --name fakegold --in tide --law "$SD/permit-all.json"
raw realm alice "bears the realm's well" ok \
  "$MINI" well --action new --dir "$WS/alice" --name gold --in tide --law "$SD/permit-all.json"

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
    >"$W/public/serve-k10c-$1.log" 2>&1 </dev/null &
  echo $! >"$pidfile"
  for i in $(seq 1 6000); do
    [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-k10c-$1.log" 2>/dev/null && break; sleep 0.1
  done
}
operator restart "stop the Host, audit the closed Store, serve again" restart r1
check restart "audit re-admitted the Store (exit 0)" test "$(cat "$SD/audit-r1.rc")" = 0
ok restart alice "read lab"
refused restart bob "read lab" revoked
refused restart dave "read lab" revoked
refused restart bob "read lab2" revoked
refused restart bob "doc show notes6" revoked
refused restart dave "doc show n6" revoked
refused restart carl "read labc" revoked
ok restart alice "doc show notes-via-lab"
named restart carl "doc new spam3 --in lab" notRoomMember

finish
