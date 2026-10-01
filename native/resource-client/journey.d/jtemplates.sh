#!/usr/bin/env bash
# journey.d/jtemplates.sh — P-DOC-TEMPLATES (DEOS §9 row 6; J23 row 1): a room
# born from a template has a map, and the template is the lines a friend types.
#
#   list      `room template list` names workroom, social, story; `room template
#             show workroom` prints deploy/shell/templates/room/workroom/template.shell
#             byte for byte.
#   workroom  alice: `room new lab --template workroom` births lab, lab/index (the
#             map: a doc only alice writes, that only grows), lab/wall (a stream),
#             lab/notes (a draft), lab/tasks (a note); `doc show lab/index` lists
#             the links by name; `doc backlinks lab/wall` finds the index.
#   by hand   the file `room template show` printed, with $ROOM and $ME replaced
#             by sed, piped into `mini shell` (script mode) births lab2: the same
#             shape (doc show / read outputs equal modulo the room's name, ids,
#             roots and heights).
#   member    bob, invited with observe,place,mutate, reads lab/index and is
#             refused editing it by its law, naming the clause; his write to
#             lab/notes (same grant) is admitted — the refusal is the index's law,
#             not a missing grant. (`can lab/index` is P-AFFORDANCES, not in this
#             base: the refusal is shown on a real edit.)
#   bad       a friend's own template whose line 3 is not a verb is refused at
#             line 3 before anything is born; one whose line 8 is refused by the
#             Host stops there, names the line and the clause, and births nothing
#             after it.
#   social    `room new pub --template social` births pub/index, pub/wall,
#             pub/intro; `room welcome pub CARL --template social` invites carl and
#             births pub/stream-CARL owned by carl (PLACE §2.3 (a)): carl appends
#             to it, alice (room founder) is refused by its law, naming the clause.
#   story     `room new tale --template story` births tale/index, tale/chapters,
#             tale/scenes (a stream), tale/cast, with the map's links.
#   restart   the Host restarts; a cold `audit` of the closed Store exits 0; the
#             map reads the same.
#
# Hook contract: journey.sh (executed). Exported: MINI HOST CONFIG SOCKET
# SHELL_BIN SPONSOR_WS SPONSOR_SUBJECT NEWCOMER_WS NEWCOMER_SUBJECT JOURNEY_WORLD
# JOURNEY_STEP_DIR. Last stdout line: the row table. Last stderr line: the
# detail. Exit 0 only when every row is ok.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" \
  "${SPONSOR_WS:?}" "${SPONSOR_SUBJECT:?}" "${JOURNEY_WORLD:?}"
SD=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
H=$SD/h; WS=$SD/w; L=$SD/log
TPL=$(CDPATH='' cd -- "$(dirname -- "$0")/../../../deploy/shell/templates/room" && pwd)
mkdir -p -m 700 "$H" "$WS" "$L"
TABLE=$SD/jtemplates.tsv
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

# script STEP WHO WHAT FILE: FILE piped into WHO's `mini shell` (script mode:
# one line at a time, the first failure stops it). Expect exit 0.
script() {
  local step=$1 who=$2 what=$3 file=$4
  N=$((N + 1))
  local stem; stem=$(printf '%03d-%s-script' "$N" "$who")
  "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$(ws_of "$who")" --home "$H/$who" <"$file" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?
  OUT=$L/$stem.out; ERR=$L/$stem.err
  if [ "$RC" = 0 ]; then record "$step" "$who" "$what" 0 ok ""
  else record "$step" "$who" "$what" 0 FAIL "$(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR")"; fi
}

# stderr STEP WHO LINE RC TEXT...: the line ends with exit RC and its stderr
# holds every TEXT (fixed strings).
stderr_says() {
  local step=$1 who=$2 line=$3 want=$4 missing=""; shift 4
  say "$who" "$line"
  for text in "$@"; do grep -qF -- "$text" "$ERR" || missing="$missing [$text]"; done
  if [ "$RC" = "$want" ] && [ -z "$missing" ]; then
    record "$step" "$who" "$line" "$want" ok "$(grep -m1 -E '^(refused|undecided|error|usage): |^template ' "$ERR" | cut -c1-160)"
  else
    record "$step" "$who" "$line" "$want" FAIL "rc $RC; missing$missing; $(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR" | cut -c1-160)"
  fi
}

# The shape of a room's map, modulo the room's name and every number (ids,
# roots, heights, subjects): what `doc show` / `read` printed, sorted (link
# entries sit in canonical address order, which differs between two rooms).
shape() { # ROOM FILE
  sed -E -e "s#\b$1\b#ROOM#g" -e 's/[0-9]{2,}/N/g' "$2" | sort
}
same_shape() { diff <(shape "$1" "$2") <(shape "$3" "$4") >"$SD/last-shape.diff"; } # ROOM FILE ROOM FILE
same_birth() { # FILE FILE: the same storage and law
  diff <(jq -S '{storage,predicate}' "$1") <(jq -S '{storage,predicate}' "$2")
}

finish() {
  echo "$TABLE"
  if [ "$FAILED" = 0 ]; then
    echo "KT: $N rows ok ($TABLE)" >&2; exit 0
  fi
  echo "KT: $FAILED of $N rows failed; first: $FIRST_FAIL" >&2; exit 1
}

mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"

# ------------------------------------------------ friends: enroll, provision, init
declare -A SUBJ
for f in alice bob carl; do
  mkdir -p -m 700 "$H/$f"
  ok setup "$f" "keygen mini.key"
  operator setup "CUSTODY: copy $f's secret into the sponsor home (enroll plan+seal sign with both keys)" \
    install -D -m 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/ktpl-$f.key"
    install -D -m 0644 "$H/$f/keys/mini.key.next.pub" "$H/sponsor/keys/ktpl-$f.key.next.pub"  # K-PREROTATE: the record commits to the next key
  ok setup sponsor "enroll plan ktpl-$f ktpl-$f.key"
  ok setup sponsor "enroll seal ktpl-$f"
  ok setup sponsor "enroll submit ktpl-$f"
  SUBJ[$f]=$(jq -r '.subject // empty' "$OUT")
  check setup "$f is enrolled as its own subject" test -n "${SUBJ[$f]}"
  operator setup "CUSTODY: remove the copy" rm -f "$H/sponsor/keys/ktpl-$f.key"
  operator setup "PROVISION: factory observation + a funded account owned by $f" \
    "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "ktpl-$f" --holder "${SUBJ[$f]}" \
      --funding 1000 --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator setup "DELIVER: the birth context into $f's HOME/provision/" \
    install -D -m 0600 "$SPONSOR_WS/provisions/ktpl-$f/birth-context.json" "$H/$f/provision/birth-context.json"
  ok setup "$f" "init mini.key ${SUBJ[$f]}"
done
A=${SUBJ[alice]} B=${SUBJ[bob]} C=${SUBJ[carl]}
AW=$WS/alice/refs

handoff() {
  ok "$1" "$2" "submit $3"
  ok "$1" "$2" "publish $3"
  ok "$1" "$2" "export $3"
  REF=$(cat "$OUT")
}

# ------------------------------------------------ the templates are files
ok list alice "room template list"
check list "room template list names workroom, social and story" \
  sh -c "grep -q '^workroom	' '$OUT' && grep -q '^social	' '$OUT' && grep -q '^story	' '$OUT'"
for t in workroom social story; do
  ok list alice "room template show $t"
  check list "room template show $t prints deploy/shell/templates/room/$t/template.shell byte for byte" \
    cmp -s "$OUT" "$TPL/$t/template.shell"
done
cp "$TPL/workroom/template.shell" "$SD/workroom.shell"
ok list alice "room template show social member"
check list "room template show social member prints member.shell" cmp -s "$OUT" "$TPL/social/member.shell"

# ------------------------------------------------ a workroom
stderr_says workroom alice "room new lab --template workroom" 0 \
  "template workroom/template.shell: 15 line(s) done"
for leaf in lab lab.index lab.wall lab.notes lab.tasks; do
  check workroom "alice holds a reference $leaf" test -f "$AW/$leaf.json"
done
check workroom "lab's reference records an open room" jq -e '.room == "open"' "$AW/lab.json"
LAB=$(jq -r .target "$AW/lab.json")
for leaf in index wall notes tasks; do
  check workroom "lab/$leaf was born in lab by alice's room grant (birth source names lab)" \
    jq -e --arg lab "$LAB" '.birth.resources[0].room == $lab' "$WS/alice/sources/create-lab.$leaf.json"
done
check workroom "lab/index's law: only alice writes, and nothing is edited or struck" \
  jq -e --arg a "$A" '.predicate as $p | $p.type == "any"
    and ($p.predicates[0] == {"type":"not","predicate":{"type":"eq","slot":"request/verb","value":"2"}})
    and ($p.predicates[1].predicates | index({"type":"eq","slot":"request/subject","value":$a}))
    and ($p.predicates[1].predicates | index({"type":"eq","slot":"content/atom-edits","value":"0"}))
    and ($p.predicates[1].predicates | index({"type":"eq","slot":"content/tombstones","value":"0"}))' \
  "$WS/alice/sources/create-lab.index.request.json"
check workroom "lab/wall is a stream; notes, tasks and index are content" \
  jq -e '.storage == "stream"' "$WS/alice/sources/create-lab.wall.request.json"
for leaf in index notes tasks; do
  check workroom "lab/$leaf is content" jq -e '.storage == "content"' "$WS/alice/sources/create-lab.$leaf.request.json"
done
ok workroom alice "read lab/wall"
check workroom "read lab/wall: an empty stream (nextSeq 1, no entries)" \
  sh -c "grep -q 'nextSeq' '$OUT'"
cp "$OUT" "$SD/lab-wall.read"
ok workroom alice "doc show lab/index"
cp "$OUT" "$SD/lab-index.show"
check workroom "doc show lab/index: the map's line" grep -q "workroom lab: wall is what we say" "$OUT"
check workroom "doc show lab/index: a link to lab/wall by name (a stream: mini:object/ID)" grep -qE -- "-> lab/wall \(object [0-9]+\)" "$OUT"
check workroom "doc show lab/index: a link to lab/notes by name" grep -qE -- "-> lab/notes \(document [0-9]+\)" "$OUT"
check workroom "doc show lab/index: a link to lab/tasks by name" grep -qE -- "-> lab/tasks \(document [0-9]+\)" "$OUT"
check workroom "doc show lab/index: exactly three links" test "$(grep -c '^link ' "$OUT")" = 3
ok workroom alice "doc show lab/notes"
cp "$OUT" "$SD/lab-notes.show"
check workroom "doc show lab/notes links back to lab/index" grep -qE -- "-> lab/index \(document [0-9]+\)" "$OUT"
ok workroom alice "doc show lab/tasks"
cp "$OUT" "$SD/lab-tasks.show"
ok workroom alice "doc backlinks lab/wall"
check workroom "doc backlinks lab/wall: the index links to the wall" \
  sh -c "grep -q '^lab/index link ' '$OUT' && grep -q '^# 1 backlink' '$OUT'"
ok workroom alice "doc backlinks lab/index"
check workroom "doc backlinks lab/index: notes links back" sh -c "grep -q '^lab/notes link ' '$OUT'"
ok workroom alice "room list"
check workroom "room list shows lab (open)" grep -q "^lab	open	object $LAB	" "$OUT"

# ------------------------------------------------ the same room, by hand
sed -e 's/[$]ROOM/lab2/g' -e "s/[\$]ME/$A/g" "$SD/workroom.shell" >"$SD/lab2-by-hand.shell"
check hand "the hand copy binds no placeholder twice and leaves none" sh -c "! grep -v '^#' '$SD/lab2-by-hand.shell' | grep -q '[$]'"
script hand alice "the workroom file, \$ROOM=lab2 \$ME=alice by sed, piped into mini shell" "$SD/lab2-by-hand.shell"
for leaf in lab2 lab2.index lab2.wall lab2.notes lab2.tasks; do
  check hand "the hand-made room holds $leaf" test -f "$AW/$leaf.json"
done
ok hand alice "doc show lab2/index"
check hand "lab2/index has lab/index's shape (lines, links by name, authors)" \
  same_shape lab2 "$OUT" lab "$SD/lab-index.show"
cp "$OUT" "$SD/lab2-index.show"
ok hand alice "doc show lab2/notes"
check hand "lab2/notes has lab/notes's shape" same_shape lab2 "$OUT" lab "$SD/lab-notes.show"
ok hand alice "doc show lab2/tasks"
check hand "lab2/tasks has lab/tasks's shape" same_shape lab2 "$OUT" lab "$SD/lab-tasks.show"
ok hand alice "read lab2/wall"
check hand "lab2/wall reads as lab/wall did (an empty stream)" same_shape lab2 "$OUT" lab "$SD/lab-wall.read"
for leaf in index wall notes tasks; do
  check hand "lab2/$leaf was born with lab/$leaf's storage and law" \
    same_birth "$WS/alice/sources/create-lab2.$leaf.request.json" "$WS/alice/sources/create-lab.$leaf.request.json"
done

# ------------------------------------------------ a member reads the map, cannot edit it
ok member alice "room invite i-bob lab $B --verbs observe,place,mutate"
handoff member alice i-bob
ok member bob "import lab $REF"
BOBCAP=$(jq -r .operationCapability "$WS/bob/refs/lab.json")
INDEX=$(jq -r .target "$AW/lab.index.json"); NOTES=$(jq -r .target "$AW/lab.notes.json")
ok member bob "import lab/index object $INDEX $BOBCAP"
ok member bob "import lab/notes object $NOTES $BOBCAP"
ok member bob "doc show lab/index"
check member "bob reads the map: the line and three links" \
  sh -c "grep -q 'workroom lab: wall is what we say' '$OUT' && test \$(grep -c '^link ' '$OUT') = 3"
check member "bob's map names lab/notes by bob's own reference" grep -qE -- "-> lab/notes \(document $NOTES\)" "$OUT"
ok member bob "doc edit b1 lab/index 1 'bob rewrites the map'"
refused member bob "submit b1" law-denied
check member "the refusal names the index's clause (alice is the only writer)" grep -q "$A" "$ERR"
cp "$ERR" "$SD/bob-index-edit.err"
ok member bob "doc append b2 lab/index 'bob adds to the map'"
refused member bob "submit b2" law-denied
check member "an append is refused by the same clause" grep -q "$A" "$ERR"
ok member bob "doc append b3 lab/notes 'bob writes in notes'"
ok member bob "submit b3"
ok member bob "doc show lab/notes"
check member "bob's line is in lab/notes (his grant writes; only the index's law refused him)" grep -q "bob writes in notes" "$OUT"
ok member alice "doc show lab/index"
check member "the map is unchanged after bob's refusals" same_shape lab "$OUT" lab "$SD/lab-index.show"

# ------------------------------------------------ a bad template
printf '%s\n' '# bad: line 3 is not a verb' 'room new $ROOM --law open' 'doc new $ROOM/x castle --in $ROOM' \
  'doc new $ROOM/y draft --in $ROOM' >"$SD/bad-usage.shell"
operator bad "a friend's own template (line 3 is not a verb) into alice's HOME/requests" \
  install -D -m 0600 "$SD/bad-usage.shell" "$H/alice/requests/bad-usage.shell"
stderr_says bad alice "room new bad1 --template @bad-usage.shell" 2 \
  "template @bad-usage.shell line 3: doc new bad1/x castle --in bad1"
check bad "nothing was born: no bad1 room" test ! -e "$AW/bad1.json"
printf '%s\n' '# bad: line 8 edits a note' 'room new $ROOM --law open' 'doc new $ROOM/log note --in $ROOM' \
  'doc append $ROOM-a1 $ROOM/log one' 'submit $ROOM-a1' 'doc show $ROOM/log' "doc edit \$ROOM-e1 \$ROOM/log 1 'one, rewritten'" \
  'submit $ROOM-e1' 'doc new $ROOM/after draft --in $ROOM' >"$SD/bad-host.shell"
operator bad "a friend's own template (line 8 is refused by the note's law) into alice's HOME/requests" \
  install -D -m 0600 "$SD/bad-host.shell" "$H/alice/requests/bad-host.shell"
stderr_says bad alice "room new bad2 --template @bad-host.shell" 3 \
  "refused: law-denied: " "template @bad-host.shell stopped at line 8: submit bad2-e1" "the 6 line(s) before it stand"
check bad "the lines before line 8 stand: bad2 and bad2/log exist" sh -c "test -f '$AW/bad2.json' && test -f '$AW/bad2.log.json'"
check bad "nothing after line 8 was born: no bad2/after" test ! -e "$AW/bad2.after.json"
check bad "nothing after line 8 was even planned: no request for bad2/after" test ! -e "$H/alice/requests/create-bad2.after.json"

# ------------------------------------------------ social: a stream per member
stderr_says social alice "room new pub --template social" 0 "template social/template.shell: 10 line(s) done"
for leaf in pub pub.index pub.wall pub.intro; do
  check social "alice holds a reference $leaf" test -f "$AW/$leaf.json"
done
check social "pub/wall is a stream" jq -e '.storage == "stream"' "$WS/alice/sources/create-pub.wall.request.json"
ok social alice "doc show pub/index"
check social "pub's map links pub/wall and pub/intro by name" \
  sh -c "grep -qE -- '-> pub/wall \(object [0-9]+\)' '$OUT' && grep -qE -- '-> pub/intro \(document [0-9]+\)' '$OUT'"
stderr_says social alice "room welcome pub $C --template social" 0 "template social/member.shell: 4 line(s) done"
check social "carl's stream: born in pub, owned by carl (the founder pays, holds nothing on it)" \
  jq -e --arg c "$C" --arg pub "$(jq -r .target "$AW/pub.json")" \
    '.birth.resources[0].room == $pub and .birth.resources[0].owner == $c and .birth.resources[0].storage == "stream"' \
    "$WS/alice/sources/create-pub.stream-$C.json"
ok social alice "export pub-invite-$C"
ok social carl "import pub $(cat "$OUT")"
CS=$(jq -r .target "$AW/pub.stream-$C.json"); COWN=$(jq -r .observeCapability "$AW/pub.stream-$C.json")
ok social carl "import mine object $CS $COWN"
ok social carl "propose s1 {\"type\":\"minidregg-workspace-proposal-v1\",\"action\":\"invoke\",\"targets\":[{\"name\":\"mine\",\"payload\":{\"type\":\"append\",\"topic\":\"hello\",\"text\":\"carl speaks\"}}]}"
ok social carl "submit s1"
ok social carl "read mine"
check social "carl's entry is in his stream, authored by carl" jq -e --arg c "$C" '[.. | objects | select(has("author")) | .author] | index($c)' "$OUT"
PUBCAP=$(jq -r .operationCapability "$AW/pub.json")
ok social alice "import carl-via-pub object $CS $PUBCAP"
ok social alice "propose s2 {\"type\":\"minidregg-workspace-proposal-v1\",\"action\":\"invoke\",\"targets\":[{\"name\":\"carl-via-pub\",\"payload\":{\"type\":\"append\",\"topic\":\"hello\",\"text\":\"alice speaks for carl\"}}]}"
refused social alice "submit s2" law-denied
check social "the refusal names carl's stream's clause (subject == carl)" grep -q "$C" "$ERR"

# ------------------------------------------------ story
stderr_says story alice "room new tale --template story" 0 "template story/template.shell: 15 line(s) done"
for leaf in tale tale.index tale.chapters tale.scenes tale.cast; do
  check story "alice holds a reference $leaf" test -f "$AW/$leaf.json"
done
check story "tale/scenes is a stream; chapters a note" \
  sh -c "jq -e '.storage == \"stream\"' '$WS/alice/sources/create-tale.scenes.request.json' && jq -e '.predicate.predicates[1].predicates[1].slot == \"content/atom-edits\"' '$WS/alice/sources/create-tale.chapters.request.json'"
ok story alice "doc show tale/index"
check story "tale's map links chapters, scenes and cast by name" \
  sh -c "grep -qE -- '-> tale/chapters \(document' '$OUT' && grep -qE -- '-> tale/scenes \(object' '$OUT' && grep -qE -- '-> tale/cast \(document' '$OUT'"
ok story alice "doc show tale/chapters"
check story "tale/chapters links tale/cast" grep -qE -- "-> tale/cast \(document" "$OUT"

# ------------------------------------------------ restart; a cold audit
pidfile=$W/public/server.pid
restart() {
  local pid; pid=$(cat "$pidfile")
  kill -TERM "$pid"
  for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$pid" 2>/dev/null && { echo "server $pid alive after TERM" >&2; return 1; }
  "$MINI" audit --host "$HOST" --config "$CONFIG" >"$SD/audit-$1.out" 2>"$SD/audit-$1.err"
  echo $? >"$SD/audit-$1.rc"
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$W/public/serve-ktpl-$1.log" 2>&1 </dev/null &
  echo $! >"$pidfile"
  for i in $(seq 1 6000); do
    [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-ktpl-$1.log" 2>/dev/null && break; sleep 0.1
  done
}
operator restart "stop the Host, audit the closed Store, serve again" restart r1
check restart "audit re-admitted the Store (exit 0)" test "$(cat "$SD/audit-r1.rc")" = 0
check restart "the cold audit re-admitted every accepted record" grep -qE '^audited [0-9]+ accepted records: every signed ingress re-admitted' "$SD/audit-r1.out"
ok restart alice "doc show lab/index"
check restart "the map reads the same after the restart" same_shape lab "$OUT" lab "$SD/lab-index.show"
ok restart bob "doc show lab/index"
ok restart bob "doc edit b4 lab/index 1 'bob tries again after the restart'"
refused restart bob "submit b4" law-denied

finish
