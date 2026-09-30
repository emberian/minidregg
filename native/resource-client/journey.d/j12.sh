#!/usr/bin/env bash
# J12 (PLACE §2.2, §2.4, §5 item 1): two friends co-write a document through
# `mini shell`, on this journey's live Store.
#
# Every friend is enrolled and provisioned the way OPERATOR.md does it (the
# sponsor's shell enrolls; the sponsor's `provision` writes a birth context
# that the operator delivers to HOME/provision/), then runs `init` in their own
# shell with no other operator step. Every line after that is typed into a
# friend's own `mini shell` session (`--line`, the ssh forced command's mode).
#
# Refusal rows assert exit 3, the reason and its text on the shell's first
# stderr line, and the same reason in the Host's own decoding of the retained
# frame (HOME/refusals/*.json, written by the Host's `inspect outcome`).
#
# Hook contract: journey.sh (executed, not sourced). Last stdout line: the row
# table. Last stderr line: the detail. Exit 0 only when every row is ok.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}"
SD=$JOURNEY_STEP_DIR
H=$SD/h; WS=$SD/w; L=$SD/log
mkdir -p -m 700 "$H" "$WS" "$L"
TABLE=$SD/j12.tsv
printf 'n\tstep\twho\tline\texpect\trc\tverdict\tnote\n' >"$TABLE"
N=0; FAILED=0; FIRST_FAIL=""

ws_of() { if [ "$1" = sponsor ]; then echo "$SPONSOR_WS"; else echo "$WS/$1"; fi; }

# say WHO LINE: one line in WHO's own shell session; sets RC, OUT, ERR.
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

# ok STEP WHO LINE: the line must succeed.
ok() {
  say "$2" "$3"
  if [ "$RC" = 0 ]; then record "$1" "$2" "$3" 0 ok ""
  else record "$1" "$2" "$3" 0 FAIL "$(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR")"; fi
}

# refused STEP WHO LINE REASON TEXT: exit 3; stderr's first line is
# `refused: REASON: …TEXT…`; the Host's decoding of the retained frame, when
# the refusal was a frame, names the same reason.
refused() {
  local step=$1 who=$2 line=$3 reason=$4 text=$5 first evidence decoded
  say "$who" "$line"
  first=$(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR")
  if [ "$RC" != 3 ]; then record "$step" "$who" "$line" 3 FAIL "rc $RC: $first"; return; fi
  case "$first" in
    "refused: $reason: "*"$text"*) ;;
    *) record "$step" "$who" "$line" 3 FAIL "want refused: $reason: …$text…; got: $first"; return ;;
  esac
  evidence=$(sed -n 's/^  evidence: //p' "$ERR" | head -1)
  if [ -n "$evidence" ]; then
    decoded=${evidence%.bin}.json
    if [ "$(jq -r '.reason // empty' "$decoded" 2>/dev/null)" != "$reason" ]; then
      record "$step" "$who" "$line" 3 FAIL "the Host's decoding $decoded does not name $reason"; return
    fi
  fi
  record "$step" "$who" "$line" 3 ok "$first"
}

# fails STEP WHO LINE RC TEXT: a client-side ending (usage 2 / error 1) with TEXT.
fails() {
  local first
  say "$2" "$3"
  first=$(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR")
  case "$RC:$first" in
    "$4:"*"$5"*) record "$1" "$2" "$3" "$4" ok "$first" ;;
    *) record "$1" "$2" "$3" "$4" FAIL "want rc $4 with …$5…; got rc $RC: $first" ;;
  esac
}

# check STEP DESCRIPTION COMMAND…: a condition on retained artifacts.
check() {
  local step=$1 what=$2; shift 2
  N=$((N + 1)); RC=-
  if "$@" >/dev/null 2>&1; then record "$step" check "$what" - ok ""
  else record "$step" check "$what" - FAIL "condition false"; fi
}

# operator STEP WHAT COMMAND…: an operator action outside any shell.
operator() {
  local step=$1 what=$2; shift 2
  N=$((N + 1))
  "$@" >"$L/$(printf '%03d' "$N")-operator.out" 2>"$L/$(printf '%03d' "$N")-operator.err"
  RC=$?
  if [ "$RC" = 0 ]; then record "$step" OPERATOR "$what" 0 ok ""
  else record "$step" OPERATOR "$what" 0 FAIL "$(tail -1 "$L/$(printf '%03d' "$N")-operator.err")"; fi
}

finish() {
  echo "$TABLE"
  if [ "$FAILED" = 0 ]; then
    echo "J12: $N rows ok ($TABLE)" >&2; exit 0
  fi
  echo "J12: $FAILED of $N rows failed; first: $FIRST_FAIL" >&2; exit 1
}

# conditions the check rows use
blame_ok() { grep -q "^  1  created-by $A .*then Alice\.\$" "$1" && grep -q "^  2  created-by $B .*Bob: a second paragraph\.\$" "$1"; }
history_ok() { [ "$(grep -cE "^attempt	(b1|b2|l1)	confirmed installed" "$1")" = 3 ]; }
banner_ok() { [ "$(head -1 "$1")" = "hosted shell: your signing key is a file on this box; root can read and sign; for a key that never leaves your machine use \`mini --remote\` (see FRIENDS.md)" ]; }

mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"

# ------------------------------------------------ friends: enroll, provision, init
declare -A SUBJ
for f in alice bob rev eve; do
  mkdir -p -m 700 "$H/$f"
  ok setup "$f" "keygen mini.key"
  operator setup "CUSTODY: copy $f's secret into the sponsor home (enroll plan+seal sign with both keys; m4-shell Deviations 1)" \
    install -D -m 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/$f.key"
  ok setup sponsor "enroll plan $f $f.key"
  ok setup sponsor "enroll seal $f"
  ok setup sponsor "enroll submit $f"
  SUBJ[$f]=$(jq -r '.subject // empty' "$OUT")
  check setup "$f is enrolled as its own subject" test -n "${SUBJ[$f]}"
  operator setup "CUSTODY: remove the copy" rm -f "$H/sponsor/keys/$f.key"
  operator setup "PROVISION (OPERATOR step 6): factory observation + a funded account owned by $f" \
    "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "$f" --holder "${SUBJ[$f]}" \
      --funding 1000 --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator setup "DELIVER (OPERATOR step 6): the birth context into $f's HOME/provision/" \
    install -D -m 0600 "$SPONSOR_WS/provisions/$f/birth-context.json" "$H/$f/provision/birth-context.json"
  ok setup "$f" "init mini.key ${SUBJ[$f]}"
  check setup "$f's workspace is bound to its birth context and a session namespace" \
    jq -e --arg ns "$H/$f/namespace" '.birthContext != null and .namespaceRoot == $ns' "$WS/$f/workspace.json"
done
A=${SUBJ[alice]} B=${SUBJ[bob]} R=${SUBJ[rev]} E=${SUBJ[eve]}

# a friend who inits before being provisioned gets one line, and no workspace
mkdir -p -m 700 "$H/early"
ok setup early "keygen mini.key"
fails setup early "init mini.key 4242" 1 "init needs your provisioning at $H/early/provision/birth-context.json"
check setup "no workspace was made for the unprovisioned session" test ! -e "$WS/early"

# ------------------------------------------------ J12: a shared document
ok J12 alice "doc new paper"
ok J12 alice "doc new index"
for d in paper index; do
  ok J12 alice "delegate g-bob-$d $d $B observe,mutate 50000"
  ok J12 alice "submit g-bob-$d"
  ok J12 alice "publish g-bob-$d"
  ok J12 alice "export g-bob-$d"
  ok J12 bob "import $d $(cat "$OUT")"
done
ok J12 alice "delegate g-rev paper $R observe 50000"
ok J12 alice "submit g-rev"
ok J12 alice "publish g-rev"
ok J12 alice "export g-rev"
ok J12 rev "import paper $(cat "$OUT")"
ok J12 bob "inbox"
check J12 "bob's inbox: paper addressed to bob, imported" grep -q "^paper	object .* (to me)	imported$" "$OUT"

ok J12 alice "doc append a1 paper 'Alice: the first paragraph.'"
ok J12 alice "submit a1"
ok J12 alice "doc show paper"
ok J12 bob "doc show paper"
check J12 "bob reads alice's line 1" grep -q "^  1  created-by $A .*Alice: the first paragraph.$" "$OUT"
ok J12 bob "doc append b1 paper 'Bob: a second paragraph.'"
ok J12 bob "submit b1"
ok J12 bob "doc edit b2 paper 1 'Alice: the first paragraph, tightened by Bob.'"
ok J12 bob "submit b2"
# alice edits line 1 as she last read it; bob changed it since: the Host refuses
ok J12 alice "doc edit a2 paper 1 'Alice: my own rewrite.'"
refused J12 alice "submit a2" operation-rejected "ContentResource.Reject.staleAtom"
ok J12 alice "doc show paper"
check J12 "alice rereads: line 1 is bob's edit" grep -q "^  1  created-by $A .*tightened by Bob.$" "$OUT"
ok J12 alice "doc edit a3 paper 1 'Alice: the first paragraph, tightened by Bob, then Alice.'"
ok J12 alice "submit a3"
ok J12 bob "doc link l1 index paper"
ok J12 bob "submit l1"
ok J12 alice "doc show paper"
check J12 "blame: line 1 created by alice, line 2 created by bob" blame_ok "$OUT"
ok J12 alice "doc show index"
check J12 "index links to paper, created by bob" grep -q "^link .* -> paper (document .*) relation 0 created-by $B$" "$OUT"
ok J12 alice "doc backlinks paper"
check J12 "backlinks of paper: index's link by bob" grep -q "^index link .* relation 0 created-by $B$" "$OUT"
ok J12 bob "history"
check J12 "bob's history holds his three accepted writes" history_ok "$OUT"

# ------------------------------------------------ refusals the Host names
# a third enrolled key with no grant, holding bob's capability number
CHILD=$(jq -r .capability "$H/bob/inbox/paper.json")
TARGET=$(jq -r .target "$H/bob/inbox/paper.json")
ok J12 eve "import stolen object $TARGET $CHILD"
refused J12 eve "doc show stolen" no-grant "no grant"
refused J12 eve "doc append e1 stolen 'Eve was here.'" no-grant "no grant"
# Refusals at submission (admission) are the public uniform outcome
# (`public_refusal_uniform`): the Host names no reason to the submitter. Each
# such row has an admitted control that differs only in the refused cause.
ADMISSION="request refused (phase admission)"
# a reviewer who holds observe only: reads, and a write is refused
# (control: bob's appends to the same document were admitted)
ok J12 rev "doc show paper"
ok J12 rev "doc append r1 paper 'Reviewer: a note.'"
refused J12 rev "submit r1" undisclosed "$ADMISSION"
# J12d (K-FIELDS): annotate-but-not-edit is not expressible on this store
fails J12d rev "doc annotate paper 1 'Reviewer: cite this.'" 1 "needs K-CONTENT-ACTIONS, and annotate-but-not-edit needs K-FIELDS"
# an append-only note: the law's clause refuses an edit
ok J12 alice "doc new log note"
ok J12 alice "doc append n1 log 'Decided: we write the paper together.'"
ok J12 alice "submit n1"
ok J12 alice "doc show log"
ok J12 alice "doc edit n2 log 1 'Decided: something else.'"
# (control: the same edit shape was admitted on paper, whose law is draft)
refused J12 alice "submit n2" undisclosed "$ADMISSION"

# ------------------------------------------------ the board
ok J12 alice "board new tasks"
ok J12 alice "delegate g-bob-tasks tasks $B observe,mutate 50000"
ok J12 alice "submit g-bob-tasks"
ok J12 alice "publish g-bob-tasks"
ok J12 alice "export g-bob-tasks"
ok J12 bob "import tasks $(cat "$OUT")"
ok J12 alice "board add t0 tasks 0"
ok J12 alice "submit t0"
ok J12 bob "board take k0 tasks 0"
ok J12 bob "submit k0"
ok J12 bob "board move m1 tasks 0 todo doing"
ok J12 bob "submit m1"
ok J12 bob "board move m2 tasks 0 doing done"
ok J12 bob "submit m2"
ok J12 bob "read tasks"
check J12 "task 0 is done (field 2 = 2) and owned by bob (field 3)" \
  jq -e --arg b "$B" '[.page.entries[] | {(.key.field): .value}] | add | .["2"] == "2" and .["3"] == $b' "$OUT"
# (control: the forward moves m1 and m2 were admitted)
ok J12 bob "board move m3 tasks 0 done todo"
refused J12 bob "submit m3" undisclosed "$ADMISSION"
# a second task needs fields 4 and 5: the declared page holds four entries
ok J12 alice "board add t1 tasks 1"
refused J12 alice "submit t1" operation-rejected "RejectReason.overflow"

# ------------------------------------------------ revoke
ok J12 alice "revoke cut-bob paper $B"
ok J12 alice "submit cut-bob"
refused J12 bob "doc show paper" revoked "revoked"
ok J12 alice "doc show paper"
check J12 "control: alice still reads her document" grep -q "then Alice.$" "$OUT"

# ------------------------------------------------ the guide
if [ -f /usr/local/lib/mini/FRIENDS.md ]; then
  ok J12 bob "help guide"
else
  fails J12 bob "help guide" 1 "not installed at /usr/local/lib/mini/FRIENDS.md"
fi
ok J12 bob "help"
check J12 "help's first line is the hosted-custody banner" banner_ok "$OUT"

finish
