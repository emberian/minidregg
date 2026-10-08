#!/usr/bin/env bash
# journey.d/j15.sh — P-STORY (PLACE §2.8, item 8; journey step J15): a story is a
# table its author seals, and then the table is the law on every player's cell.
#
#   author    alice: `story law tale` prints the law sealing will install;
#             `story new tale --from tale --gm DANA` births the room (template
#             `story`: index, chapters, scenes, cast) and the table document
#             (14 rows); before the seal her edit of the table is admitted and
#             `story invite` is refused (a story is played only once sealed);
#             `story seal tale`; then her edit of the table is refused
#             `sealed` and her re-law of it is refused by its clause.
#   cast      alice invites bob and carl as players (each cell born at the
#             start under the law the table generates for them) and dana as
#             GM; each joins with `story join tale @FILE`.
#   play      bob and carl play: legal moves admitted; a skip, a rewind (by
#             scene and by turn), a take of an absent item, a second take, a
#             conditional exit without the item each refused naming the
#             table's clause; bob cannot move carl's cell; alice can neither
#             move bob's cell nor re-law it; dana narrates, bob's narrate is
#             refused; the law on bob's cell, as the Host decodes it, is the
#             generated law.player.json with bob bound.
#   restart   mid-story the Host stops, a cold audit re-admits every record,
#             the Host serves again; each player's `look` is where they left.
#   end       bob reaches the lamp room, carl the glasshouse: both end scenes;
#             a last cold audit re-admits every record.
#
# Hook contract: journey.sh (executed). Exported: MINI HOST CONFIG SOCKET
# SHELL_BIN SPONSOR_WS SPONSOR_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. Last
# stdout line: the row table. Last stderr line: the detail. Exit 0 only when
# every row is as expected.
set -u
. "$(dirname "${BASH_SOURCE[0]}")/../journey-private.sh"
umask 077
: "${JOURNEY_STEP_DIR:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" \
  "${SPONSOR_WS:?}" "${SPONSOR_SUBJECT:?}" "${JOURNEY_WORLD:?}"
SD=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
H=$SD/h; WS=$SD/w; L=$SD/log
TALE=$(CDPATH='' cd -- "$(dirname -- "$0")/../../../deploy/shell/templates/story/tale" && pwd)
mkdir -p -m 700 "$H" "$WS" "$L"
TABLE=$SD/j15.tsv
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

ok() {
  say "$2" "$3"
  if [ "$RC" = 0 ]; then record "$1" "$2" "$3" 0 ok "$(head -1 "$OUT" | cut -c1-120)"
  else record "$1" "$2" "$3" 0 FAIL "$(first_line "$ERR")"; fi
}

# says STEP WHO LINE TEXT: admitted (exit 0) and stdout holds TEXT (fixed string).
says() {
  say "$2" "$3"
  if [ "$RC" = 0 ] && grep -qF -- "$4" "$OUT"; then record "$1" "$2" "$3" 0 ok "[$4]"
  else record "$1" "$2" "$3" 0 FAIL "rc $RC; stdout lacks [$4]; $(first_line "$ERR")"; fi
}

# clause STEP WHO LINE N NAME: refused by the Host (exit 3) as law-denied, and
# the story client names the table's clause N (NAME).
clause() {
  local first
  say "$2" "$3"
  first=$(first_line "$ERR")
  if [ "$RC" = 3 ] && [[ "$first" == "refused: law-denied: "* ]] && grep -qF -- "the table's clause $4: $5" "$ERR"; then
    record "$1" "$2" "$3" "3 clause $4" ok "$(echo "$first" | cut -c1-150) [clause $4: $5]"
  else
    record "$1" "$2" "$3" "3 clause $4" FAIL "rc $RC; $first; $(grep -m1 "the table's clause" "$ERR")"
  fi
}

# refused STEP WHO LINE TEXT: exit 3, `refused: law-denied: ` first, naming TEXT.
refused() {
  local first
  say "$2" "$3"
  first=$(first_line "$ERR")
  if [ "$RC" = 3 ] && [[ "$first" == "refused: law-denied: "* ]] && grep -qF -- "$4" <<<"$first"; then
    record "$1" "$2" "$3" 3 ok "$(echo "$first" | cut -c1-150)"
  else
    record "$1" "$2" "$3" 3 FAIL "want law-denied naming [$4]; got rc $RC: $first"
  fi
}

# fails STEP WHO LINE RC TEXT: exit RC and stderr holds TEXT.
fails() {
  say "$2" "$3"
  if [ "$RC" = "$4" ] && grep -qF -- "$5" "$ERR"; then record "$1" "$2" "$3" "$4" ok "$(first_line "$ERR" | cut -c1-150)"
  else record "$1" "$2" "$3" "$4" FAIL "want rc $4 with [$5]; got rc $RC: $(first_line "$ERR")"; fi
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

finish() {
  echo "$TABLE"
  if [ "$FAILED" = 0 ]; then
    echo "J15: $N rows as expected ($TABLE)" >&2; exit 0
  fi
  echo "J15: $FAILED of $N rows failed; first: $FIRST_FAIL" >&2; exit 1
}

mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"

# ------------------------------------------------ friends: enroll, provision, init
declare -A SUBJ
for f in alice bob carl dana; do
  mkdir -p -m 700 "$H/$f"
  ok setup "$f" "keygen mini.key"
  operator setup "CUSTODY: copy $f's secret into the sponsor home (enroll plan+seal sign with both keys)" \
    install_private 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/j15-$f.key"
  ok setup sponsor "enroll plan j15-$f j15-$f.key $(xxd -p -c 256 "$H/$f/keys/mini.key.next.pub") $(xxd -p -c 256 "$H/$f/keys/mini.key.next.cosign")"
  ok setup sponsor "enroll seal j15-$f"
  ok setup sponsor "enroll submit j15-$f"
  SUBJ[$f]=$(jq -r '.subject // empty' "$OUT")
  check setup "$f is enrolled as its own subject" test -n "${SUBJ[$f]}"
  operator setup "CUSTODY: remove the copy" rm -f "$H/sponsor/keys/j15-$f.key"
  operator setup "PROVISION: factory observation + a funded account owned by $f" \
    "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "j15-$f" --holder "${SUBJ[$f]}" \
      --funding 1000 --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator setup "DELIVER: the birth context into $f's HOME/provision/" \
    install_private 0600 "$SPONSOR_WS/provisions/j15-$f/birth-context.json" "$H/$f/provision/birth-context.json"
  ok setup "$f" "init mini.key ${SUBJ[$f]}"
done
A=${SUBJ[alice]} B=${SUBJ[bob]} C=${SUBJ[carl]} D=${SUBJ[dana]}
AW=$WS/alice/refs

# ------------------------------------------------ the author writes a story and seals it
says author alice "story law tale" "# clause 3: exits"
check author "story law prints the generated law.player (the same 8 clauses, {S} unbound)" \
  sh -c "grep -v '^#' '$OUT' | tr -d '\n' >'$SD/law-printed.txt'; grep -v '^--' '$TALE/law.player' | tr -d '\n' >'$SD/law-file.txt'; cmp -s '$SD/law-printed.txt' '$SD/law-file.txt'"
says author alice "story new tale --from tale --gm $D" "story tale: The Lamplighter's House (5 scenes, 4 ways, 1 items)"
check author "the room template ran: 15 lines done" grep -qF "template story/template.shell: 15 line(s) done" "$ERR"
for leaf in tale tale.index tale.chapters tale.scenes tale.cast tale.table; do
  check author "alice holds a reference $leaf" test -f "$AW/$leaf.json"
done
check author "tale/table is born in the room under the author-only law" \
  jq -e --arg a "$A" '. == {"type":"any","predicates":[{"type":"eq","slot":"request/subject","value":$a},{"type":"not","predicate":{"type":"eq","slot":"request/verb","value":"2"}}]}' \
    "$H/alice/requests/chat-law-tale.table.json"
ok author alice "doc show tale/table"
check author "the table document holds the table's 14 rows" \
  sh -c "[ \$(grep -cE '^ +[0-9]+  created-by' '$OUT') = 14 ] && grep -q 'exit 1 north 3 needs key' '$OUT'"
ok author alice "doc show tale/index"
check author "the map links the table" grep -qE -- "-> tale/table \(document" "$OUT"
ok author alice "doc append t0 tale/table '# a note before the seal (not a row)'"
ok author alice "submit t0"
fails author alice "story invite tale $B" 1 "is not sealed"
says author alice "story seal tale" "story tale sealed"
check author "seal lists the 8 clauses by name" sh -c "grep -c '^ *[0-9] ' '$OUT' | grep -qx 8 && grep -q 'needs key (exit 1 -> 3)' '$OUT'"
ok author alice "doc append t1 tale/table 'item lamp 4'"
refused author alice "submit t1" "sealed"
ok author alice "law t2 tale/table open"
# A refused installation is masked `undisclosed` by blind submission (K-LAW-LEAF names
# clauses on the read and invoke-prepare paths only); the same verb by the same author
# through the same control capability installed the seal four rows up, so this
# refusal is the sealed law's.
fails author alice "submit t2" 3 "refused: undisclosed"
ok author alice "doc show tale/table"
check author "the sealed table still holds its 15 lines (14 rows and the note) and no lamp" \
  sh -c "[ \$(grep -cE '^ +[0-9]+  created-by' '$OUT') = 15 ] && ! grep -q 'item lamp' '$OUT'"

# ------------------------------------------------ the cast
invite() { # PLAYER [gm]
  says cast alice "story invite tale ${SUBJ[$1]}${2:+ $2}" "story join tale "
  mkdir -p -m 700 "$H/$1/requests"
  sed -n 's/^story join tale //p' "$OUT" >"$H/$1/requests/tale-invite.json"
  check cast "the invitation to $1 is JSON addressed to $1" \
    jq -e --arg s "${SUBJ[$1]}" '.grant.recipient == $s' "$H/$1/requests/tale-invite.json"
  says cast "$1" "story join tale @tale-invite.json" "joined tale as ${2:-player}"
}
invite bob
invite carl
invite dana gm
BCELL=$(jq -r .cell "$H/bob/requests/tale-invite.json"); CCELL=$(jq -r .cell "$H/carl/requests/tale-invite.json")
check cast "each player's cell is born in the room by the author, under the author-only staging law" \
  sh -c "test -f '$AW/tale.p-$B.json' && test -f '$AW/tale.p-$C.json' && jq -e --arg a '$A' '.predicates[1].value == \$a' '$H/alice/requests/chat-law-tale.p-$B.json'"

# ------------------------------------------------ play
says play bob "look" "The hallway (scene 0, turn 0)"
# bob's look retained its signed policy reads; the Host's own decoder renders them.
decoded() { # LABEL OUT: the newest retained signed read LABEL of bob's, decoded by the Host
  local d; d=$(ls -td "$H"/bob/chat/reads/story-tale/"$1".* | head -1)
  "$HOST" "$CONFIG" inspect view-policy "$d/view.bin" "$2"
}
operator play "decode bob's retained signed read of his cell's law (Host inspect view-policy)" decoded cell-law "$SD/bob-cell-law.json"
check play "the law on bob's cell, as the Host decodes it, is law.player.json with {S} = bob" \
  bash -c "diff <(jq -S .predicate '$SD/bob-cell-law.json') <(sed 's/{S}/$B/' '$TALE/law.player.json' | jq -S .)"
operator play "decode bob's retained signed read of the table's law" decoded table-law "$SD/table-law.json"
check play "the law on the table, as the Host decodes it, is law.table.json" \
  bash -c "diff <(jq -S .predicate '$SD/table-law.json') <(jq -S . '$TALE/law.table.json')"
clause play bob "take key" 5 "here key (scene 1)"
clause play bob "go 3" 3 "exits"
says play bob "go north" "The anteroom (scene 1, turn 1)"
clause play bob "go north" 4 "needs key (exit 1 -> 3)"
says play bob "take key" "you carry: key"
clause play bob "take key" 7 "progress"
clause play bob "go 0" 3 "exits"
ok play bob "invoke r1 tale/me write 1 0 2"
refused play bob "submit r1" "field 1 delta == 1"
check play "the rewind of the turn is refused by the turn clause (the shell names the Host's clause)" grep -qF "field 1 delta == 1 (value -2)" "$ERR"
says play carl "look" "The hallway (scene 0, turn 0)"
says play carl "go north" "The anteroom (scene 1, turn 1)"
BCAP=$(jq -r .observeCapability "$WS/bob/refs/tale.json")
ok play bob "import tale-cell object $CCELL $BCAP $BCAP"
ok play bob "invoke x1 tale-cell write 0 2 1"
refused play bob "submit x1" "subject == $C"
ok play alice "invoke a1 tale/p-$B write 0 3 1"
refused play alice "submit a1" "subject == $B"
ok play alice "law a2 tale/p-$B open"
# Masked `undisclosed` like the table's re-law; the control is `story invite`, where alice
# installed this cell's law through the same verb and control capability.
fails play alice "submit a2" 3 "refused: undisclosed"
says play dana "narrate 'the lamp upstairs hums, low and patient'" "narrated in tale"
fails play bob "narrate 'I am the GM now'" 3 "refused: law-denied: "
check play "bob's narrate is refused by the scenes stream's clause naming dana" grep -qF "subject == $D" "$ERR"
says play bob "look" "the GM: "
check play "bob reads dana's narration" grep -qF "the lamp upstairs hums" "$OUT"
says play carl "go west" "THE END"

# ------------------------------------------------ restart mid-story; a cold audit
pidfile=$W/public/server.pid
restart() {
  local pid; pid=$(cat "$pidfile")
  kill -TERM "$pid"
  for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$pid" 2>/dev/null && { echo "server $pid alive after TERM" >&2; return 1; }
  "$MINI" audit --host "$HOST" --config "$CONFIG" >"$SD/audit-$1.out" 2>"$SD/audit-$1.err"
  echo $? >"$SD/audit-$1.rc"
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$W/public/serve-j15-$1.log" 2>&1 </dev/null &
  echo $! >"$pidfile"
  for i in $(seq 1 6000); do
    [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-j15-$1.log" 2>/dev/null && break; sleep 0.1
  done
}
operator restart "stop the Host, audit the closed Store, serve again" restart r1
check restart "audit re-admitted the Store (exit 0)" test "$(cat "$SD/audit-r1.rc")" = 0
check restart "the cold audit re-admitted every accepted record" grep -qE '^audited [0-9]+ accepted records: every signed ingress re-admitted' "$SD/audit-r1.out"
says restart bob "look" "The anteroom (scene 1, turn 2)"
check restart "bob still carries the key" grep -qF "you carry: key" "$OUT"
says restart carl "look" "The glasshouse (scene 2, turn 2)"
clause restart carl "go 1" 3 "exits"

# ------------------------------------------------ both reach an end
says end bob "go north" "The landing (scene 3, turn 3)"
says end bob "act open" "The lamp room (scene 4, turn 4)"
check end "bob is at an end scene" grep -qF "THE END" "$OUT"
clause end bob "go 3" 3 "exits"
operator end "stop the Host, audit the closed Store, serve again" restart r2
check end "the last cold audit re-admitted every accepted record" grep -qE '^audited [0-9]+ accepted records: every signed ingress re-admitted' "$SD/audit-r2.out"
says end bob "look" "The lamp room (scene 4, turn 4)"
says end carl "look" "The glasshouse (scene 2, turn 2)"

finish
