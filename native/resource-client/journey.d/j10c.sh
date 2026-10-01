#!/usr/bin/env bash
# journey.d/j10c.sh — K-ROOM 3c: rooms as friends use them, through `mini shell`,
# on this journey's live Store (after J5; extends K10's rows).
#
# Friends are enrolled, provisioned and `init`ed exactly as J12 does. Every
# friend line is typed into that friend's own shell session (`--line`).
#
#   room      alice founds `lab` (workroom) and invites bob with narrowed verbs
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
#   kick      alice kicks bob: bob's read is refused, and dave's (attenuated from
#             bob's) too (`ancestor_revocation_rejected`). `room leave` names its
#             missing kernel half (K-RENOUNCE).
#   realm     alice founds `tide` (realm): bob, invited with `place`, is refused
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
  ok setup sponsor "enroll plan k10c-$f k10c-$f.key"
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
check room "lab's reference records it as a workroom alice founded" \
  jq -e '.room == "workroom"' "$WS/alice/refs/lab.json"
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

# ------------------------------------------------ kick, and leave
ok kick alice "room kick k-bob lab $B"
ok kick alice "submit k-bob"
refused kick bob "read lab" revoked
refused kick dave "read lab" revoked
named kick bob "doc new notes4 --in lab" notRoomMember
ok kick alice "read lab"
ok kick alice "room members lab"
check kick "room members no longer lists bob or dave" \
  jq -e --arg b "$B" --arg d "$D" '[.members[].subject] as $s
    | (($s | index($b)) | not) and (($s | index($d)) | not)' "$OUT"
fails kick bob "room leave lab" 1 "K-RENOUNCE"

# ------------------------------------------------ a realm
ok realm alice "room new tide --template realm"
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
ok restart alice "doc show notes-via-lab"
named restart carl "doc new spam3 --in lab" notRoomMember

finish
