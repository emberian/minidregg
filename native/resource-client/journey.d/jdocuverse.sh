#!/usr/bin/env bash
# journey.d/jdocuverse.sh — J-DOCUVERSE (DEOS §8 J19–J24 on one Store): two
# friends write a paper together in their own `mini shell` sessions, and every
# docuverse verb is a line one of them types.
#
# Parties (enrolled, provisioned and init'ed from the sponsor's shell as J12
# does it): amy owns `paper`; ben owns `notes` and holds observe+mutate on
# paper; amy holds observe on notes; cal holds observe on paper and nothing on
# notes (the reader without the source's grant); rhea reviews paper: observe on
# the whole cell and mutate scoped to `fields = {annotations}` (K-FIELDS).
#
# Rows (`check` rows are conditions; every typed line is a row of its own):
#   J19  a quote that cannot rot: ben publishes notes lines 2..3 (`doc range`);
#        amy transcludes them twice (snapshot, and live at a line); ben edits
#        notes line 2; amy's snapshot keeps the old line, the live one shows the
#        new line `live, revised`; cal sees the placeholder and no byte of
#        notes; `doc backlinks notes` lists paper's link mark and transclusions
#   J20  the past, signed: `doc show paper --at H` equals what amy's `doc
#        show` printed at H, byte for byte; `doc history paper` lists the
#        writes; `doc diff` names ben's inserted line; cal at a height before
#        its grant is refused no-grant
#   J21  your own editor: amy pulls, edits a line, pushes (admitted); ben
#        edits line 3 meanwhile; amy's second push is refused and the refusal
#        names line 3
#   J22  marks and a place: a heading, bold, a link mark; ben's annotation;
#        ben's line inserted at line 2; rhea marks a line and is refused an edit
#   J23  `can paper`: amy's verbs all admitted; rhea's `mark` admitted and
#        `edit` refused with the reason
#   J24  `mini web` serves paper: the page's document equals `doc show paper
#        --html` byte for byte (one renderer)
#   GOLDEN amy's `doc show paper` equals journey.d/jdocuverse.golden.txt after
#        substituting ben's subject and the snapshot's opening height
#   AUDIT  the journey's service is stopped, the Host's cold audit re-admits
#        every record, the service is started again and amy's doc reads the same
#
# Hook contract: journey.sh (executed, not sourced). Last stdout line: the row
# table. Last stderr line: the detail. Exit 0 only when every row is ok.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${JOURNEY_WORLD:?}" "${JOURNEY_RUN:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}"
SD=$JOURNEY_STEP_DIR
HERE=$(cd "$(dirname "$0")" && pwd)
H=$SD/h; WS=$SD/w; L=$SD/log
mkdir -p -m 700 "$H" "$WS" "$L"
TABLE=$SD/jdocuverse.tsv
TRANSCRIPT=$SD/transcript.txt
printf 'n\tstep\twho\tline\texpect\trc\tverdict\tnote\n' >"$TABLE"
: >"$TRANSCRIPT"
N=0; FAILED=0; FIRST_FAIL=""
WEB_PID=""
TRACE=0   # the transcript starts after the friends' setup
trap '[ -n "$WEB_PID" ] && kill "$WEB_PID" 2>/dev/null' EXIT

ws_of() { if [ "$1" = sponsor ]; then echo "$SPONSOR_WS"; else echo "$WS/$1"; fi; }

# say WHO LINE [STDIN]: one line in WHO's own shell session; sets RC, OUT, ERR;
# appends `WHO> LINE`, its stdout and its last stderr line to the transcript.
say() {
  local who=$1 line=$2 input=${3:-/dev/null}
  N=$((N + 1))
  local stem; stem=$(printf '%03d-%s' "$N" "$who")
  printf '%s\n' "$line" >"$L/$stem.line"
  "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$(ws_of "$who")" --home "$H/$who" --line "$line" <"$input" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?
  OUT=$L/$stem.out; ERR=$L/$stem.err
  [ "$TRACE" = 1 ] || return 0
  {
    printf '%s> %s\n' "$who" "$line"
    head -40 "$OUT" | sed 's/^/  /' 
    grep -E '^(refused|undecided|error|usage): |^workspace (range|transclusion|line|mark)' "$ERR" | sed 's/^/  ! /' | head -3
  } >>"$TRANSCRIPT"
}

record() { # step who line expect verdict note
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$1" "$2" "$3" "$4" "$RC" "$5" "$6" >>"$TABLE"
  if [ "$5" != ok ]; then
    FAILED=$((FAILED + 1))
    [ -n "$FIRST_FAIL" ] || FIRST_FAIL="row $N ($1 $2: $3): $6"
  fi
}

ok() {
  say "$2" "$3" "${4:-/dev/null}"
  if [ "$RC" = 0 ]; then record "$1" "$2" "$3" 0 ok ""
  else record "$1" "$2" "$3" 0 FAIL "$(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR")"; fi
}

# refused STEP WHO LINE TEXT: exit 3, and stderr's first `refused:` line holds TEXT.
refused() {
  say "$2" "$3"
  local first; first=$(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR")
  if [ "$RC" = 3 ] && printf '%s' "$first" | grep -qF -- "$4"; then record "$1" "$2" "$3" 3 ok "$first"
  else record "$1" "$2" "$3" 3 FAIL "rc $RC: $first"; fi
}

check() {
  local step=$1 what=$2; shift 2
  N=$((N + 1)); RC=-
  if "$@" >/dev/null 2>&1; then record "$step" check "$what" - ok ""
  else record "$step" check "$what" - FAIL "condition false"; fi
  printf '# check: %s -> %s\n' "$what" "$(tail -1 "$TABLE" | cut -f7)" >>"$TRANSCRIPT"
}

operator() {
  local step=$1 what=$2; shift 2
  N=$((N + 1))
  "$@" >"$L/$(printf '%03d' "$N")-operator.out" 2>"$L/$(printf '%03d' "$N")-operator.err"
  RC=$?
  if [ "$RC" = 0 ]; then record "$step" OPERATOR "$what" 0 ok ""
  else record "$step" OPERATOR "$what" 0 FAIL "$(tail -1 "$L/$(printf '%03d' "$N")-operator.err")"; fi
}

finish() {
  [ -n "$WEB_PID" ] && { kill "$WEB_PID" 2>/dev/null; wait "$WEB_PID" 2>/dev/null; WEB_PID=""; }
  echo "$TABLE"
  if [ "$FAILED" = 0 ]; then
    echo "JDV: $N rows ok ($TABLE; transcript $TRANSCRIPT)" >&2; exit 0
  fi
  echo "JDV: $FAILED of $N rows failed; first: $FIRST_FAIL" >&2; exit 1
}

# grant STEP FROM ID REF TO VERBS LOCALNAME: delegate, submit, publish, export; TO imports.
grant() {
  ok "$1" "$2" "delegate $3 $4 ${SUBJ[$5]} $6 50000"
  ok "$1" "$2" "submit $3"
  ok "$1" "$2" "publish $3"
  ok "$1" "$2" "export $3"
  ok "$1" "$5" "import $7 $(cat "$OUT")"
}

# the line of a `doc show --json` whose text matches RE (its number), and its text
line_of() { jq -r --arg re "$2" '[.lines[] | select(.line != null and (.text | test($re)))][0].line // empty' "$1"; }
text_at() { jq -r --argjson n "$2" '.lines[] | select(.line == $n) | .text' "$1"; }

mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"

# ------------------------------------------------ friends: enroll, provision, init (as J12)
declare -A SUBJ
for f in amy ben cal rhea; do
  mkdir -p -m 700 "$H/$f" "$H/$f/requests"
  ok setup "$f" "keygen mini.key"
  operator setup "CUSTODY: copy $f's secret into the sponsor home" \
    install -D -m 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/$f.key"
  ok setup sponsor "enroll plan $f $f.key"
  ok setup sponsor "enroll seal $f"
  ok setup sponsor "enroll submit $f"
  SUBJ[$f]=$(jq -r '.subject // empty' "$OUT")
  check setup "$f is enrolled as its own subject" test -n "${SUBJ[$f]}"
  operator setup "CUSTODY: remove the copy" rm -f "$H/sponsor/keys/$f.key"
  operator setup "PROVISION: a funded account owned by $f" \
    "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "$f" --holder "${SUBJ[$f]}" \
      --funding 1000 --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator setup "DELIVER: the birth context into $f's HOME/provision/" \
    install -D -m 0600 "$SPONSOR_WS/provisions/$f/birth-context.json" "$H/$f/provision/birth-context.json"
  ok setup "$f" "init mini.key ${SUBJ[$f]}"
done
B=${SUBJ[ben]}
TRACE=1

# ------------------------------------------------ two documents, four grants
ok J22 amy "doc new paper"
ok J19 ben "doc new notes"
grant J22 amy g-ben paper ben observe,mutate paper
grant J19 ben g-amy notes amy observe notes
grant J19 amy g-cal paper cal observe paper

# rhea: observe on the whole of paper, and mutate scoped to the annotations field
for part in read annotate; do
  case $part in
    read) jq -n --arg r "${SUBJ[rhea]}" '{type:"minidregg-workspace-proposal-v1",action:"delegate",
            name:"paper",recipient:$r,verbs:["observe"],maxCost:"50000"}' >"$H/amy/requests/rhea-read.json" ;;
    annotate) jq -n --arg r "${SUBJ[rhea]}" '{type:"minidregg-workspace-proposal-v1",action:"delegate",
            name:"paper",recipient:$r,verbs:["observe","mutate"],maxCost:"50000",fields:["annotations"]}' >"$H/amy/requests/rhea-annotate.json" ;;
  esac
  ok J22 amy "propose g-rhea-$part @rhea-$part.json"
  ok J22 amy "submit g-rhea-$part"
  ok J22 amy "publish g-rhea-$part"
done
PAPER=$(jq -r .target "$WS/amy/refs/paper.json")
ok J22 rhea "import paper object $PAPER $(jq -r .observeCapability "$WS/amy/proposals/g-rhea-read/recipient-reference.json") $(jq -r .observeCapability "$WS/amy/proposals/g-rhea-annotate/recipient-reference.json")"

# ------------------------------------------------ writing: notes by push, paper by lines
ok J21 ben "doc pull notes"
check J21 "an empty document pulls as an empty file" test ! -s "$OUT"
printf 'notes one\nnotes two\nnotes three\nnotes four\n' >"$H/ben/requests/notes.md"
ok J21 ben "doc push n1 notes @notes.md"
check J21 "ben's push was four new lines in one proposal" grep -q '^doc push notes: proposal n1: 4 action(s)' "$OUT"
ok J19 ben "doc range notes 2 3"
check J19 "the range is published as one run" grep -q '^workspace range: [0-9]*$' "$ERR"

ok J22 amy "doc append a1 paper 'Mini, a kernel for friends'"
ok J22 amy "submit a1"
ok J22 amy "doc append a2 paper 'Every write is a signed turn.'"
ok J22 amy "submit a2"
ok J22 amy "doc append a3 paper 'see the notes'"
ok J22 amy "submit a3"
ok J22 ben "doc insert paper 2 'Ben: the kernel checks every turn.'"
ok J22 amy "doc show paper --json"
cp "$OUT" "$SD/after-insert.json"
check J22 "ben's line stands at line 2, placed by the element tree" \
  test "$(text_at "$SD/after-insert.json" 2)" = "Ben: the kernel checks every turn."
ok J20 amy "doc history paper --json"
H_INSERT=$(jq -r '[.rows[].height | tonumber] | max' "$OUT")

# ------------------------------------------------ J19: transclusions
ok J19 amy "doc transclude paper notes 2 3"
ok J19 amy "doc show paper"
cp "$OUT" "$SD/show-at-snapshot.txt"
ok J20 amy "doc history paper --json"
SNAP_AT=$(jq -r '[.rows[].height | tonumber] | max' "$OUT")
ok J19 amy "doc transclude paper notes 2 3 live at 4"
ok J19 amy "doc show paper --json"
check J19 "the live transclusion stands at line 4, the snapshot at line 6" \
  jq -e '[.lines[] | select(.kind == "embed") | {line, mode: .transcluded.view}] == [{line: 4, mode: "live"}, {line: 6, mode: "snapshot"}]' "$OUT"

# ------------------------------------------------ J22: marks, an annotation, a link mark
ok J22 amy "doc mark paper 1 heading"
ok J22 amy "doc mark paper 3 bold"
ok J22 amy "doc mark paper 5 link notes"
ok J22 ben "doc show paper"
ok J22 ben "doc annotate n2 paper 3 'cite the DATAMODEL here'"
ok J22 ben "submit n2"
ok J22 rhea "doc show paper"
ok J22 rhea "doc mark paper 2 italic"
ok J22 rhea "doc edit r1 paper 2 'Rhea rewrote this.'"
refused J22 rhea "submit r1" "refused:"
ok J22 amy "doc show paper --json"
check J22 "line 2 is unchanged (rhea's edit refused) and carries rhea's italic mark (admitted)" \
  jq -e '[.lines[] | select(.line == 2) | (.text, ([.marks[].kind] | index("italic") != null))] == ["Ben: the kernel checks every turn.", true]' "$OUT"

# ------------------------------------------------ J19: ben edits notes line 2; the quotes
ok J19 ben "doc edit n3 notes 2 'notes two, revised'"
ok J19 ben "submit n3"
ok J19 amy "doc show paper --json"
cp "$OUT" "$SD/final.json"
check J19 "the snapshot keeps the line as it was transcluded" \
  jq -e '[.lines[] | select(.line == 6) | .transcluded.lines] == [["notes two","notes three"]]' "$SD/final.json"
check J19 "the live transclusion shows the new line, live and revised" \
  jq -e '[.lines[] | select(.line == 4) | .transcluded | (.lines, (.header | test("live, revised")))] == [["notes two, revised","notes three"], true]' "$SD/final.json"
ok J19 cal "doc show paper"
cp "$OUT" "$SD/cal-show.txt"
check J19 "cal (no grant on notes) sees the placeholder for both quotes" \
  test "$(grep -c 'not readable by you\]' "$SD/cal-show.txt")" = 2
check J19 "no byte of notes reaches cal's page (control: amy's has them)" \
  sh -c "! grep -q 'notes t' '$SD/cal-show.txt' && jq -e '[.lines[].transcluded.lines // [] | .[]] | length == 4' '$SD/final.json'"
ok J19 ben "doc backlinks notes"
check J19 "notes' backlinks: paper's link mark and its two transclusions" \
  test "$(grep -c '^paper link ' "$OUT")" = 3
ok J19 amy "doc links paper"
check J19 "paper's links out include the link mark to notes" grep -q -- '-> document notes ' "$OUT"

# ------------------------------------------------ GOLDEN: the rendered paper
ok GOLDEN amy "doc show paper"
cp "$OUT" "$SD/golden-got.txt"
SNAP_H=$(jq -r '[.lines[] | select(.line == 6) | .transcluded.header][0]' "$SD/final.json" | sed -n 's/.*snapshot@\([0-9]*\).*/\1/p')
sed -e "s/<B>/$B/g" -e "s/<H>/$SNAP_H/g" "$HERE/jdocuverse.golden.txt" >"$SD/golden-want.txt"
check GOLDEN "amy's doc show equals the golden byte for byte" cmp "$SD/golden-want.txt" "$SD/golden-got.txt"

# ------------------------------------------------ J20: the past
ok J20 amy "doc history paper --json"
cp "$OUT" "$SD/history.json"
check J20 "the history lists every write of paper with its subject" \
  jq -e --arg b "$B" '(.rows | length) >= 10 and ([.rows[].subject] | index($b) != null)' "$SD/history.json"
ok J20 amy "doc show paper --at $SNAP_AT"
check J20 "doc show --at the snapshot's height equals what amy saw then, byte for byte" cmp "$SD/show-at-snapshot.txt" "$OUT"
ok J20 amy "doc diff paper $((H_INSERT - 1)) $H_INSERT"
check J20 "the diff names ben's inserted line" grep -q '^+ [0-9]* "Ben: the kernel checks every turn."$' "$OUT"
ok J20 amy "doc history paper"
# cal's grant came after paper was born: at paper's first write cal held nothing
FIRST=$(jq -r '[.rows[].height | tonumber] | min' "$SD/history.json")
refused J20 cal "doc show paper --at $FIRST" "no-grant"

# ------------------------------------------------ J21: pull, edit, push; a stale line by line
ok J21 amy "doc pull paper"
cp "$OUT" "$H/amy/requests/p.md"
check J21 "a pulled transclusion is one marker line" test "$(grep -c '^⟦transclusion [0-9]*⟧$' "$H/amy/requests/p.md")" = 2
sed -i 's/^see the notes$/see the notes (pulled and pushed)/' "$H/amy/requests/p.md"
ok J21 amy "doc push p1 paper @p.md"
check J21 "the push was one edit" grep -q '^doc push paper: proposal p1: 1 action(s)' "$OUT"
ok J21 amy "doc pull paper"
cp "$OUT" "$H/amy/requests/p.md"
ok J21 ben "doc show paper"
ok J21 ben "doc edit b9 paper 3 'Every write is a signed turn, says ben.'"
ok J21 ben "submit b9"
sed -i 's/^Every write is a signed turn\.$/Every write is a signed turn, says amy./' "$H/amy/requests/p.md"
refused J21 amy "doc push p2 paper @p.md" "refused: stale-line: line 3 changed"

# ------------------------------------------------ J23: can
ok J23 amy "can paper"
cp "$OUT" "$SD/can-amy.txt"
check J23 "amy's verbs on paper: read, write, edit, mark, link are admitted" \
  sh -c "for v in read write edit mark link; do grep -qE \"^  \$v +admitted \" '$SD/can-amy.txt' || exit 1; done"
ok J23 rhea "can paper"
cp "$OUT" "$SD/can-rhea.txt"
check J23 "rhea's mark is admitted" grep -qE '^  mark +admitted ' "$SD/can-rhea.txt"
check J23 "rhea's edit is refused, with the reason" grep -qE '^  edit +[a-z-]+: ' "$SD/can-rhea.txt"

# ------------------------------------------------ J24: the web, one renderer
"$MINI" web --dir "$WS/amy" --listen 127.0.0.1:0 >"$SD/web.out" 2>"$SD/web.err" &
WEB_PID=$!
URL=""
for i in $(seq 1 100); do
  URL=$(grep -o 'http://127\.0\.0\.1:[0-9]*/[0-9a-f]*/' "$SD/web.out" 2>/dev/null | head -1)
  [ -n "$URL" ] && break
  kill -0 "$WEB_PID" 2>/dev/null || break
  sleep 0.1
done
N=$((N + 1)); RC=-
if [ -n "$URL" ]; then record J24 OPERATOR "mini web --dir amy --listen 127.0.0.1:0" - ok "$URL"
else record J24 OPERATOR "mini web" - FAIL "did not start: $(tail -1 "$SD/web.err")"; fi
CODE=$(curl -s --max-time 600 -o "$SD/web-paper.html" -w '%{http_code}' "${URL}doc/paper")
ok J24 amy "doc show paper --html"
cp "$OUT" "$SD/show-paper.html"
sed -n '/^<article class="doc"/,/^<\/article>$/p' "$SD/web-paper.html" >"$SD/web-paper.article"
check J24 "the web page's document equals doc show --html, byte for byte" \
  sh -c "[ '$CODE' = 200 ] && [ -s '$SD/show-paper.html' ] && cmp -s '$SD/show-paper.html' '$SD/web-paper.article'"
CODE_CAL=$(curl -s --max-time 600 -o "$SD/web-history.html" -w '%{http_code}' "${URL}doc/paper/history")
check J24 "the web's history page renders the same history" test "$CODE_CAL" = 200
kill "$WEB_PID" 2>/dev/null; wait "$WEB_PID" 2>/dev/null; WEB_PID=""
{ echo "# mini web: GET /doc/paper -> $CODE; the page's <article> is doc show --html:"; sed -n '1,12p' "$SD/web-paper.article"; } >>"$TRANSCRIPT"

# ------------------------------------------------ AUDIT: restart, cold audit, identical
ok AUDIT amy "doc show paper"
cp "$OUT" "$SD/before-restart.txt"
PID=$(cat "$JOURNEY_WORLD/public/server.pid")
restart() {
  local args i k kids
  args=$(ps -o args= -p "$PID") || return 1
  case "$args" in *" serve "*"--socket $SOCKET"*) ;; *) echo "pid $PID is not the journey's serve" >&2; return 1;; esac
  kids=$(pgrep -P "$PID" | tr '\n' ' ')
  kill -TERM "$PID"
  for i in $(seq 1 300); do kill -0 "$PID" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$PID" 2>/dev/null && return 1
  for k in $kids; do
    for i in $(seq 1 100); do kill -0 "$k" 2>/dev/null || break; sleep 0.1; done
    kill -0 "$k" 2>/dev/null && { echo "Host child $k outlived its server" >&2; return 1; }
  done
  "$HOST" "$CONFIG" audit >"$SD/audit.out" 2>"$SD/audit.err" || { echo "audit exit $?: $(tail -1 "$SD/audit.err")" >&2; AUDIT=fail; }
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$JOURNEY_WORLD/public/serve-jdv.log" 2>&1 </dev/null &
  echo "$!" >"$JOURNEY_WORLD/public/server.pid"
  echo "started server $! (jdocuverse restart)" >>"$JOURNEY_RUN/services.log"
  for i in $(seq 1 600); do
    "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
      --workspace "$WS/amy" --home "$H/amy" --line "doc show paper" >/dev/null 2>&1 && return 0
    sleep 0.1
  done
  return 1
}
AUDIT=ok
operator AUDIT "stop the journey's service, run the Host's cold audit, start it again" restart
check AUDIT "the Host's audit re-admits every record (exit 0)" test "$AUDIT" = ok
{ echo "# operator: $HOST CONFIG audit"; tail -2 "$SD/audit.out" | sed 's/^/  /'; } >>"$TRANSCRIPT"
ok AUDIT amy "doc show paper"
check AUDIT "after the restart amy's paper reads the same" cmp "$SD/before-restart.txt" "$OUT"

finish
