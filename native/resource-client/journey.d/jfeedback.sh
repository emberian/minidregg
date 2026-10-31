#!/usr/bin/env bash
# JFEEDBACK (docs/PLACE.md §2.3, §5 item 4, client half): a member reports a problem
# into its own feedback room through `mini shell` on this journey's live Store;
# the operator reads it with its context; no other member can read it.
#
# Three friends are enrolled and provisioned the way OPERATOR.md does it (as in
# j12; the enrollment names are prefixed `jchat-`, see the body). alice is the
# operator: she founds `feedback-NAME` and invites the member, who joins it as
# `feedback` -- the exact lines infra adds at enrolment. Every chat line is
# typed into a friend's own `mini shell --line` session.
#
# Rows print `name<TAB>expect=…<TAB>got=…<TAB>detail`. bob reports from a
# refusal context (`feedback --from w-refused1 --clause … --page /doc/paper …`);
# the operator's `reports` shows the text with its client, attempt, clause and
# page; `reports --digest` is the one relay line; `tail --in feedback-bob`
# renders the report kind; carol's own room shows her report and never bob's;
# carol importing bob's room grant and crafting a room record for it is still
# refused `no-grant` at her first signed read (a capability is held by its
# grantee: RefusalReason.capabilityChecks' holder check answers `noGrant`).
#
# Not claimed here: `feedback --via discord` (the mirror is JCHAT's surface) and
# the day limit (10/day), which no law shape counts posts per day yet (owed).
# Hook contract: journey.sh. Last stdout line: the row table.
set -u
. "$(dirname "${BASH_SOURCE[0]}")/../journey-private.sh"
umask 077
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}" "${JOURNEY_WORLD:?}"
SH=${SHELL_BIN:-}; [ -n "$SH" ] || SH=$MINI
SD=$JOURNEY_STEP_DIR
H=$SD/h; WS=$SD/w; L=$SD/log
mkdir -p -m 700 "$H" "$WS" "$L"
ROWS=$SD/jfeedback-rows.tsv
: >"$ROWS"
N=0; BAD=0; FIRST=""

ws_of() { if [ "$1" = sponsor ]; then echo "$SPONSOR_WS"; else echo "$WS/$1"; fi; }
now() { date +%s.%N; }

# line WHO LINE: one line in WHO's own shell session; sets RC OUT ERR SECS.
line() {
  local who=$1 text=$2 t0 t1
  N=$((N + 1))
  local stem; stem=$(printf '%03d-%s' "$N" "$who")
  printf '%s\n' "$text" >"$L/$stem.line"
  t0=$(now)
  "$SH" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$(ws_of "$who")" --home "$H/$who" --line "$text" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?
  t1=$(now)
  SECS=$(echo "$t1 - $t0" | bc)
  OUT=$L/$stem.out; ERR=$L/$stem.err
}

row() { # NAME EXPECT GOT DETAIL
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "$4" >>"$ROWS"
  if [ "$2" != "$3" ]; then
    BAD=$((BAD + 1)); [ -n "$FIRST" ] || FIRST="$1: expect $2 got $3 ($4)"
  fi
}
first_ending() { grep -m1 -E '^(refused|undecided|error|usage): ' "$1" | cut -c1-200; }
# ok NAME WHO LINE
ok() {
  line "$2" "$3"
  if [ "$RC" = 0 ]; then row "$1" ok ok "$2: $(printf '%s' "$3" | cut -c1-90) (${SECS}s)"
  else row "$1" ok "rc$RC" "$2: $3: $(first_ending "$ERR")"; fi
}
# refused NAME WHO LINE REASON: exit 3 and the first line names REASON
refused() {
  line "$2" "$3"
  local f; f=$(first_ending "$ERR")
  case "$RC:$f" in
    "3:refused: $4"*) row "$1" "refused:$4" "refused:$4" "$2: $3: $f" ;;
    *) row "$1" "refused:$4" "rc$RC" "$2: $3: $f" ;;
  esac
}
# fails NAME WHO LINE RC TEXT: a client-side ending with TEXT
fails() {
  line "$2" "$3"
  local f; f=$(first_ending "$ERR")
  case "$RC:$f" in
    "$4:"*"$5"*) row "$1" "rc$4" "rc$4" "$2: $f" ;;
    *) row "$1" "rc$4" "rc$RC" "$2: $3: $f" ;;
  esac
}
# check NAME DESCRIPTION COMMAND…
check() {
  local name=$1 what=$2; shift 2
  if "$@" >/dev/null 2>&1; then row "$name" true true "$what"
  else row "$name" true false "$what"; fi
}
setup() { # WHO LINE: a setup line that must succeed
  line "$1" "$2"
  [ "$RC" = 0 ] || { echo "setup failed: $1: $2: $(first_ending "$ERR") $(tail -2 "$ERR")" >&2; finish; }
}
operator() { # WHAT COMMAND…
  local what=$1; shift
  "$@" >"$L/op-$N.out" 2>"$L/op-$N.err" || { echo "operator step failed: $what: $(tail -1 "$L/op-$N.err")" >&2; finish; }
}
finish() {
  [ -n "${FAKE_PID:-}" ] && kill "$FAKE_PID" 2>/dev/null
  cat "$ROWS" >&2
  echo "$ROWS"
  if [ "$BAD" = 0 ] && [ "$(wc -l <"$ROWS")" -gt 0 ]; then
    echo "JFEEDBACK: $(wc -l <"$ROWS") rows as expected" >&2; exit 0
  fi
  echo "JFEEDBACK: $BAD of $(wc -l <"$ROWS") rows differ; first: $FIRST" >&2; exit 1
}

# ------------------------------------------------ friends: enroll, provision, init (j12's way)
mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"
declare -A S
# The enrollment names are prefixed `jchat-`: they are keys of the demo world's sponsor namespace (one request
# per name, participant_namespace.rs), and J12 has already enrolled alice and bob there with other keys. The
# petnames readers use for each other stay plain.
for f in alice bob carol; do
  mkdir -p -m 700 "$H/$f"
  setup "$f" "keygen mini.key"
  operator "custody copy" install_private 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/jchat-$f.key"
  setup sponsor "enroll plan jchat-$f jchat-$f.key $(xxd -p -c 256 "$H/$f/keys/mini.key.next.pub") $(xxd -p -c 256 "$H/$f/keys/mini.key.next.cosign")"
  setup sponsor "enroll seal jchat-$f"
  setup sponsor "enroll submit jchat-$f"
  S[$f]=$(jq -r '.subject // empty' "$OUT")
  [ -n "${S[$f]}" ] || { echo "no subject for $f" >&2; finish; }
  operator "custody remove" rm -f "$H/sponsor/keys/jchat-$f.key"
  operator "provision $f" "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "jchat-$f" --holder "${S[$f]}" \
      --funding 1000 --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator "deliver $f" install_private 0600 "$SPONSOR_WS/provisions/jchat-$f/birth-context.json" "$H/$f/provision/birth-context.json"
  setup "$f" "init mini.key ${S[$f]}"
done
A=${S[alice]} B=${S[bob]} C=${S[carol]}
# petnames: each reader names the others (names are local to each reader)
for r in alice bob carol dave bridge; do
  for f in alice bob carol; do
    [ "$r" = "$f" ] || setup "$r" "chat name ${S[$f]} $f"
  done
done

# ------------------------------------------------ the room
# critical NAME WHO LINE: a row that later rows depend on; stop when it fails
critical() { ok "$@"; [ "$RC" = 0 ] || { echo "critical row $1 failed" >&2; finish; }; }

# alice is the operator. Per member: the operator founds feedback-NAME and invites the member;
# the member joins it as `feedback`. These are the exact lines infra adds at enrolment.
enrol_feedback() { # NAME
  critical "new-$1" alice "chat new feedback-$1"
  critical "invite-$1" alice "chat invite feedback-$1 ${S[$1]} $1"
  local inv; inv=$(grep '^chat join feedback-' "$OUT" | tail -1 | sed "s/^chat join feedback-$1 /chat join feedback /")
  [ -n "$inv" ] || { row "invitation-$1" "a chat join line" none "$(head -3 "$OUT")"; finish; }
  critical "join-$1" "$1" "$inv"
}
for f in bob carol; do enrol_feedback "$f"; done
for f in bob carol; do setup alice "chat name ${S[$f]} $f"; done

# bob reports from a refusal context; the operator reads it with its context
ok bob-report bob "feedback --from w-refused1 --clause \"refused: law-denied: field 2 monotone\" --page /doc/paper the save button is gone"
ok op-reports alice "reports"
check op-sees-text "the operator reads bob's text" grep -q "the save button is gone" "$OUT"
check op-sees-context "with the clause, the attempt and the page" sh -c "grep -q 'clause: refused: law-denied: field 2 monotone' '$OUT' && grep -q 'from w-refused1' '$OUT' && grep -q 'page: /doc/paper' '$OUT'"
ok op-digest alice "reports --digest"
check digest-line "one line: height, member, text" grep -qE '^h[0-9]+ bob: the save button is gone$' "$OUT"
ok op-tail alice "tail --in feedback-bob"
check tail-renders "tail renders the report kind" grep -q "reported: the save button is gone" "$OUT"

# carol cannot read bob's report: she holds no grant on bob's room, and her own room has none of it
ok carol-report carol "feedback carol's own report"
ok carol-own-tail carol "tail"
check carol-sees-only-hers "carol's room shows hers, never bob's" sh -c "grep -q \"carol's own report\" '$OUT' && ! grep -q 'save button' '$OUT'"
BOBROOM=$(jq -r .target "$WS/alice/refs/feedback-bob.json")
BCAP=$(jq -r .observeCapability "$WS/bob/refs/feedback.json")
ok carol-import-bobs carol "import fb-bob object $BOBROOM $BCAP"
operator "carol crafts a room record for bob's room" sh -c "mkdir -p -m 700 '$H/carol/chat/rooms' && printf '%s\n' '{\"type\":\"mini-chat-room-v1\",\"room\":\"fb-bob\",\"grant\":\"fb-bob\",\"stream\":null}' >'$H/carol/chat/rooms/fb-bob.json'"
refused carol-reads-bobs carol "tail --in fb-bob" "no-grant"

# the day limit: owed (docs: no law shape counts posts per day yet), so no row claims it
finish
