#!/usr/bin/env bash
# J12 (PLACE §2.2, §2.4, §5 item 1): two friends co-write a document through
# J12W (DEOS §2.2 item #4, P-DOC-WRITE): a friend writes in their own editor;
# the kernel still judges per line.
#
#   doc pull NAME           prints the document's live lines, bytes exact, and
#                           retains the read as seen/NAME.json (doc show's path)
#   doc push ID NAME @FILE  diffs FILE against seen/NAME.json into the minimal
#                           createAtom / editAtom / editAtom{tombstone} actions,
#                           ONE proposal, then submits it
#
# Two friends (wa, wb) are enrolled, provisioned and init'ed exactly as J12
# does it, on this journey's Store. The "editor" is this script writing the
# pulled file in the friend's HOME/requests/. Then: wa seeds four lines by a
# push; edits lines 1 and 3 and adds a line between 2 and 3 → admitted, and
# the pull and doc show equal the file byte for byte; wb pulls; wa edits line
# 2 and pushes; wb edits line 2 and pushes → refused, the first line naming
# line 2, the Host's decoding naming staleAtom, wb's seen record untouched,
# nothing of the push landed; wb re-pulls, edits line 4 → admitted; a push
# with no change submits nothing; the trailing-newline rule; a deletion is a
# tombstone; a push from standard input. Then the journey's service is stopped
# (by its pid file, the journey's own process), the Host's audit re-admits
# every record, the service is started again with the journey's own command
# and pid file, and the document reads the same.
#
# Hook contract: journey.sh (executed, not sourced). Last stdout line: the row
# table. Last stderr line: the detail. Exit 0 only when every row is ok.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${JOURNEY_WORLD:?}" "${JOURNEY_RUN:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}"
SD=$JOURNEY_STEP_DIR
H=$SD/h; WS=$SD/w; L=$SD/log
mkdir -p -m 700 "$H" "$WS" "$L"
TABLE=$SD/j12w.tsv
printf 'n\tstep\twho\tline\texpect\trc\tverdict\tnote\n' >"$TABLE"
N=0; FAILED=0; FIRST_FAIL=""; ACTIONS=0

ws_of() { if [ "$1" = sponsor ]; then echo "$SPONSOR_WS"; else echo "$WS/$1"; fi; }

# say WHO LINE [STDIN-FILE]: one line in WHO's own shell session; sets RC, OUT, ERR.
say() {
  local who=$1 line=$2 input=${3:-/dev/null}
  N=$((N + 1))
  local stem; stem=$(printf '%03d-%s' "$N" "$who")
  printf '%s\n' "$line" >"$L/$stem.line"
  "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$(ws_of "$who")" --home "$H/$who" --line "$line" <"$input" >"$L/$stem.out" 2>"$L/$stem.err"
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

ok() {
  say "$2" "$3" "${4:-/dev/null}"
  if [ "$RC" = 0 ]; then record "$1" "$2" "$3" 0 ok ""
  else record "$1" "$2" "$3" 0 FAIL "$(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR")"; fi
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
  "$@" >"$L/$(printf '%03d' "$N")-operator.out" 2>"$L/$(printf '%03d' "$N")-operator.err"
  RC=$?
  if [ "$RC" = 0 ]; then record "$step" OPERATOR "$what" 0 ok ""
  else record "$step" OPERATOR "$what" 0 FAIL "$(tail -1 "$L/$(printf '%03d' "$N")-operator.err")"; fi
}

# push STEP WHO ID FILE ACTIONS: an admitted push of HOME/requests/FILE that
# says it submitted ACTIONS actions and that the document now reads as the file.
push() {
  say "$2" "doc push $3 paper @$4"
  local said
  said=$(grep -m1 -oE '[0-9]+ action\(s\)' "$OUT" | cut -d' ' -f1)
  if [ "$RC" != 0 ]; then record "$1" "$2" "doc push $3 paper @$4" 0 FAIL "$(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR")"
  elif [ "$said" != "$5" ]; then record "$1" "$2" "doc push $3 paper @$4" 0 FAIL "want $5 actions, push said ${said:-none}"
  elif ! grep -q "reads exactly as your file" "$OUT"; then record "$1" "$2" "doc push $3 paper @$4" 0 FAIL "push did not confirm the document reads as the file"
  else ACTIONS=$((ACTIONS + said)); record "$1" "$2" "doc push $3 paper @$4" 0 ok "$said actions"; fi
}

# pull STEP WHO FILE: doc pull into HOME/requests/FILE (the friend's editor's file).
pull() {
  ok "$1" "$2" "doc pull paper"
  cp "$OUT" "$H/$2/requests/$3"
}

# shown_equals FILE SHOW-OUTPUT: doc show's live line texts are FILE's lines.
shown_equals() {
  python3 - "$1" "$2" <<'PY'
import re, sys
want = open(sys.argv[1], 'rb').read()
lines = []
for raw in open(sys.argv[2], 'rb').read().decode().split('\n'):
    m = re.match(r'^\s*(\d+)  created-by (\S+)', raw)
    if not m:
        continue
    rest = raw[m.end():][max(0, 20 - len(m.group(2))):]
    if rest.startswith(' (struck)'):
        continue
    assert rest.startswith('  '), raw
    lines.append(rest[2:])
got = ''.join(l + '\n' for l in lines).encode()
sys.exit(0 if got == want else 1)
PY
}

finish() {
  echo "$TABLE"
  if [ "$FAILED" = 0 ]; then
    echo "J12W: $N rows ok, $ACTIONS content actions admitted by push ($TABLE)" >&2; exit 0
  fi
  echo "J12W: $FAILED of $N rows failed; first: $FIRST_FAIL" >&2; exit 1
}

mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"

# ------------------------------------------------ friends: enroll, provision, init (as J12)
declare -A SUBJ
for f in wa wb; do
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
B=${SUBJ[wb]}

ok J12W wa "doc new paper"
ok J12W wa "delegate g-wb paper $B observe,mutate 50000"
ok J12W wa "submit g-wb"
ok J12W wa "publish g-wb"
ok J12W wa "export g-wb"
ok J12W wb "import paper $(cat "$OUT")"

# ------------------------------------------------ A: pull, write, push
pull J12W wa a.md
check J12W "an empty document pulls as an empty file" test ! -s "$H/wa/requests/a.md"
printf 'one\ntwo\nthree\nfour\n' >"$H/wa/requests/a.md"
push J12W wa p0 a.md 4
# the editor: lines 1 and 3 edited, a line added between 2 and 3
printf 'ONE, edited by A\ntwo\nA added this between two and three\nTHREE, edited by A\nfour\n' >"$H/wa/requests/a.md"
push J12W wa p1 a.md 3
pull J12W wa a-check.md
check J12W "A's pull equals A's file byte for byte" cmp "$H/wa/requests/a.md" "$H/wa/requests/a-check.md"
ok J12W wa "doc show paper"
check J12W "doc show's lines are A's file, inserted line in place" shown_equals "$H/wa/requests/a.md" "$OUT"

# ------------------------------------------------ B pulls; A and B both edit line 2
pull J12W wb b.md
check J12W "B's pull is A's file" cmp "$H/wa/requests/a.md" "$H/wb/requests/b.md"
sed -i '2s/.*/two, edited by A/' "$H/wa/requests/a.md"
push J12W wa p2 a.md 1
sed -i '2s/.*/two, edited by B/' "$H/wb/requests/b.md"
SEEN_B=$(sha256sum "$WS/wb/seen/paper.json" | cut -d' ' -f1)
say wb "doc push b1 paper @b.md"
FIRST=$(grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR")
case "$RC:$FIRST" in
  "3:refused: stale-line: line 2 changed (now \"two, edited by A\") since you pulled paper at "*)
    record J12W wb "doc push b1 paper @b.md" 3 ok "$FIRST" ;;
  *) record J12W wb "doc push b1 paper @b.md" 3 FAIL "rc $RC: $FIRST" ;;
esac
EVIDENCE=$(sed -n 's/^  evidence: //p' "$ERR" | head -1)
check J12W "the Host's own refusal line names staleAtom" grep -q '^refused: operation-rejected: .*ContentResource.Reject.staleAtom' "$ERR"
check J12W "the Host's decoding of the retained frame is operation-rejected" \
  test "$(jq -r '.reason // empty' "${EVIDENCE%.bin}.json" 2>/dev/null)" = operation-rejected
check J12W "B's seen record is untouched by the refusal" \
  test "$(sha256sum "$WS/wb/seen/paper.json" | cut -d' ' -f1)" = "$SEEN_B"
pull J12W wa a-check.md
check J12W "nothing of B's push landed: the document is A's file" cmp "$H/wa/requests/a.md" "$H/wa/requests/a-check.md"

# ------------------------------------------------ B re-pulls and edits line 4
pull J12W wb b.md
check J12W "B's re-pull shows A's line 2" grep -qx 'two, edited by A' "$H/wb/requests/b.md"
sed -i '4s/.*/THREE, edited by A, then line 4 by B/' "$H/wb/requests/b.md"
push J12W wb b2 b.md 1

# ------------------------------------------------ nothing to push; the trailing-newline rule
say wb "doc push b3 paper @b.md"
if [ "$RC" = 0 ] && grep -q "nothing submitted" "$OUT"; then record J12W wb "doc push b3 paper @b.md" 0 ok "$(head -1 "$OUT")"
else record J12W wb "doc push b3 paper @b.md" 0 FAIL "rc $RC: $(head -1 "$OUT")"; fi
check J12W "no attempt was made for the empty push" test ! -e "$WS/wb/attempts/b3"
head -c -1 "$H/wb/requests/b.md" >"$H/wb/requests/b-nonl.md"
say wb "doc push b4 paper @b-nonl.md"
if [ "$RC" = 0 ] && grep -q "nothing submitted" "$OUT"; then record J12W wb "doc push b4 paper @b-nonl.md (no final newline)" 0 ok "the final newline is not content"
else record J12W wb "doc push b4 paper @b-nonl.md" 0 FAIL "rc $RC: $(head -1 "$OUT")"; fi
sed -i '1s/$/  /' "$H/wb/requests/b.md"
push J12W wb b5 b.md 1
pull J12W wb b-check.md
check J12W "trailing spaces are content: line 1 ends with two spaces" grep -qx 'ONE, edited by A  ' "$H/wb/requests/b-check.md"

# ------------------------------------------------ a deletion is a tombstone
sed -i '3d' "$H/wb/requests/b.md"
push J12W wb b6 b.md 1
ok J12W wb "doc show paper"
check J12W "the deleted line is struck in doc show, unnumbered, and absent from the file" \
  grep -q '^  -  created-by .*(struck)  A added this between two and three$' "$OUT"
check J12W "doc show's live lines are B's file" shown_equals "$H/wb/requests/b.md" "$OUT"

# ------------------------------------------------ a push from standard input
pull J12W wa a.md
printf '%s\n' "a last line, from A's standard input" >>"$H/wa/requests/a.md"
say wa "doc push p3 paper @-" "$H/wa/requests/a.md"
if [ "$RC" = 0 ] && grep -q "reads exactly as your file" "$OUT"; then ACTIONS=$((ACTIONS + 1)); record J12W wa "doc push p3 paper @- < a.md" 0 ok "1 actions"
else record J12W wa "doc push p3 paper @- < a.md" 0 FAIL "rc $RC: $(grep -m1 -E '^(refused|error|usage): ' "$ERR")"; fi

# ------------------------------------------------ restart; audit re-admits
pull J12W wa before.md
ok J12W wa "doc show paper"
tail -n +2 "$OUT" >"$SD/show-before.txt"
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
    >"$JOURNEY_WORLD/public/serve-j12w.log" 2>&1 </dev/null &
  echo "$!" >"$JOURNEY_WORLD/public/server.pid"
  echo "started server $! (j12w restart)" >>"$JOURNEY_RUN/services.log"
  for i in $(seq 1 600); do
    "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
      --workspace "$WS/wa" --home "$H/wa" --line "doc show paper" >/dev/null 2>&1 && return 0
    sleep 0.1
  done
  return 1
}
AUDIT=ok
operator J12W "stop the journey's service, run the Host's audit, start it again" restart
check J12W "the Host's audit re-admits every record (exit 0)" test "$AUDIT" = ok
pull J12W wa after.md
check J12W "after the restart the pull is identical" cmp "$H/wa/requests/before.md" "$H/wa/requests/after.md"
ok J12W wa "doc show paper"
tail -n +2 "$OUT" >"$SD/show-after.txt"
check J12W "after the restart doc show is identical (below its header)" cmp "$SD/show-before.txt" "$SD/show-after.txt"
cp "$WS/wa/seen/paper.json" "$SD/seen-wa-paper.json"

finish
