#!/usr/bin/env bash
# journey.d/j14.sh — P-HERMES-ROOM (PLACE §2.7 J14, §2.10 budgets): Hermes as
# librarian.
#
# On this journey's live Store (after J5). Friends are enrolled, provisioned
# and `init`ed exactly as J17 does; Hermes is enrolled the same way (the
# node's Hermes: the operator enrolls it once and writes its subject into each
# friend's HOME/hermes/node.json). Every friend line is typed into that
# friend's own shell session (`--line`). Hermes's controller is
# `grain-runtime hermes-room step` over Hermes's own workspace, speaking to
# the DETERMINISTIC provider (`mini-hermes-test-provider --room-librarian`:
# the librarian program, decided only from this attach's signed reads; no
# model, no network: loopback port >= 7700).
#
#   setup     alice (founder, 5000), bob (100), hermes (0) enrolled; the node file.
#   room      alice: `chat new lab`, the map `lab-index` (founder-only), `tariff
#             lab set hermes/turn 10`; bob invited with place.
#   summon    alice: `summon lab as librarian --budget 100`: the till, Hermes's
#             account (100 from alice), Hermes on the roster, lab-index relawed
#             to admit Hermes, lab-digest born, the program DOCUMENT; bob reads
#             the program and is refused editing it; alice edits it.
#   attach 1  B creates two docs and says three things; Hermes links both from
#             lab-index and writes a digest section; 3 turns paid (10 + fee).
#   ask       A asks "what changed since H0"; Hermes answers in its stream from
#             the signed history (both docs named).
#   no-grant  B asks Hermes to append to B's paper; Hermes's append is refused
#             no-grant by the Host (the turn is still paid); Hermes says why.
#   budget    more says and a question: a digest, then the next turn is refused
#             bookRefused at plan; Hermes says "out of budget"; `topup` resumes.
#   kill      Hermes is SIGKILLed with a signed call out (M5 j4 shape); the
#             restart proves the submitter stopped and resolves the attempt by
#             exact lookup; nothing is submitted twice; the index links once.
#   send      Hermes is SIGKILLed after a provider request crossed the send
#             boundary (the provider stopped); the restart abandons it and
#             never resends (each id once in the provider's own log).
#   dismiss   alice: `dismiss lab` revokes; Hermes returns the remainder; its
#             read of lab is refused.
#   balances  Hermes's account: 100 + topup - (10 + fee)*turns - returned - fee = 0;
#             the till holds 10*turns, one `hermes` ledger entry per turn.
#   audit     stop, cold audit re-admits every record (exit 0), serve; Hermes
#             sends nothing more.
#
# Hook contract: journey.sh (executed). Needs GRAIN_RUNTIME (grain-runtime)
# and TEST_PROVIDER (mini-hermes-test-provider). Exported by journey.sh: MINI
# HOST CONFIG SOCKET SHELL_BIN SPONSOR_WS SPONSOR_SUBJECT JOURNEY_WORLD
# JOURNEY_STEP_DIR. Last stdout line: the row table. Last stderr line: the
# detail. Exit 0 only when every row is as expected.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" \
  "${SPONSOR_WS:?}" "${SPONSOR_SUBJECT:?}" "${JOURNEY_WORLD:?}" \
  "${GRAIN_RUNTIME:?GRAIN_RUNTIME names the grain-runtime binary}" \
  "${TEST_PROVIDER:?TEST_PROVIDER names mini-hermes-test-provider}"
SD=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
H=$SD/h; WS=$SD/w; L=$SD/log
mkdir -p -m 700 "$H" "$WS" "$L"
TABLE=$SD/j14.tsv
printf 'n\tstep\twho\tline\texpect\tgot\tverdict\twall_s\tload1\tnote\n' >"$TABLE"
N=0; FAILED=0; FIRST_FAIL=""
PRICE=10
BUDGET=100
TOPUP=100
PORT=${J14_PROVIDER_PORT:-7743}
PROVIDER_PID=""
RPID=""
cleanup() {
  [ -n "$RPID" ] && kill -KILL "$RPID" 2>/dev/null
  if [ -n "$PROVIDER_PID" ]; then kill -CONT "$PROVIDER_PID" 2>/dev/null; kill -TERM "$PROVIDER_PID" 2>/dev/null; wait "$PROVIDER_PID" 2>/dev/null; fi
}
trap cleanup EXIT

ws_of() { if [ "$1" = sponsor ]; then echo "$SPONSOR_WS"; else echo "$WS/$1"; fi; }
load1() { cut -d' ' -f1 /proc/loadavg 2>/dev/null; }

T0=0
say() {
  local who=$1 line=$2
  N=$((N + 1))
  local stem; stem=$(printf '%03d-%s' "$N" "$who")
  printf '%s\n' "$line" >"$L/$stem.line"
  T0=$(date +%s.%N)
  "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$(ws_of "$who")" --home "$H/$who" --line "$line" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?
  WALL=$(awk -v a="$T0" -v b="$(date +%s.%N)" 'BEGIN{printf "%.2f", b-a}')
  OUT=$L/$stem.out; ERR=$L/$stem.err
  { printf '%s> %s\n' "$who" "$line"; cat "$OUT"; grep -E '^(refused|error|usage|undecided|not here): ' "$ERR"; } >>"$SD/transcript.txt" 2>/dev/null
}

record() { # step who line expect got verdict note
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$1" "$2" "$3" "$4" "$5" "$6" "${WALL:--}" "$(load1)" "$7" >>"$TABLE"
  if [ "$6" != ok ]; then
    FAILED=$((FAILED + 1))
    [ -n "$FIRST_FAIL" ] || FIRST_FAIL="row $N ($1 $2: $3): $7"
  fi
}

first_line() { grep -m1 -E '^(refused|undecided|error|usage|not here): ' "$1"; }

host_words() {
  cat "$1"
  grep -oE 'encoded( refusal)?: [0-9a-f]+' "$1" | awk '{print $NF}' | while read -r hex; do
    printf '%s' "$hex" | xxd -r -p 2>/dev/null | tr -c '[:print:]' ' '; echo
  done
  for j in $(sed -n 's/^  evidence: //p' "$1"); do cat "${j%.bin}.json" 2>/dev/null; done
}

ok() {
  say "$2" "$3"
  if [ "$RC" = 0 ]; then record "$1" "$2" "$3" "admitted" "rc 0" ok "$(head -c 160 "$OUT" | tr '\n\t' '  ')"
  else record "$1" "$2" "$3" "admitted" "rc $RC" FAIL "$(first_line "$ERR")"; fi
}

named() {
  local step=$1 who=$2 line=$3 text=$4
  say "$who" "$line"
  if [ "$RC" = 0 ]; then record "$step" "$who" "$line" "refused $text" "rc 0 (admitted)" FAIL "$(head -c 160 "$OUT")"; return; fi
  if host_words "$ERR" | grep -qE -- "$text"; then
    record "$step" "$who" "$line" "refused $text" "rc $RC" ok "$(first_line "$ERR" | cut -c1-150) [$text]"
  else
    record "$step" "$who" "$line" "refused $text" "rc $RC" FAIL "refused, not naming $text: $(first_line "$ERR" | cut -c1-200)"
  fi
}

# STEP WHO LINE1 LINE2 TEXT: LINE1 proposes; the Host refuses at the
# proposal's preparation or at LINE2's submission, naming TEXT either way.
two_step_refused() {
  say "$2" "$3"
  if [ "$RC" != 0 ]; then
    if host_words "$ERR" | grep -qE -- "$5"; then
      record "$1" "$2" "$3" "refused $5" "rc $RC (at propose)" ok "$(first_line "$ERR" | cut -c1-150) [$5]"
    else
      record "$1" "$2" "$3" "refused $5" "rc $RC" FAIL "refused at propose, not naming $5: $(first_line "$ERR" | cut -c1-200)"
    fi
    return
  fi
  named "$1" "$2" "$4" "$5"
}

check() {
  local step=$1 what=$2 want=$3 got=$4
  N=$((N + 1)); WALL=-
  if [ "$want" = "$got" ]; then record "$step" check "$what" "$want" "$got" ok ""
  else record "$step" check "$what" "$want" "$got" FAIL "want $want got $got"; fi
}

checkp() {
  local step=$1 what=$2; shift 2
  N=$((N + 1)); WALL=-
  if "$@" >/dev/null 2>&1; then record "$step" check "$what" true true ok ""
  else record "$step" check "$what" true false FAIL "condition false"; fi
}

operator() {
  local step=$1 what=$2; shift 2
  N=$((N + 1))
  local stem; stem=$(printf '%03d-operator' "$N")
  T0=$(date +%s.%N)
  "$@" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?
  WALL=$(awk -v a="$T0" -v b="$(date +%s.%N)" 'BEGIN{printf "%.2f", b-a}')
  OUT=$L/$stem.out; ERR=$L/$stem.err
  if [ "$RC" = 0 ]; then record "$step" OPERATOR "$what" "rc 0" "rc 0" ok ""
  else record "$step" OPERATOR "$what" "rc 0" "rc $RC" FAIL "$(tail -1 "$ERR" | cut -c1-200)"; fi
}

finish() {
  echo "$TABLE"
  if [ "$FAILED" = 0 ]; then
    echo "J14: $N rows as expected ($TABLE)" >&2; exit 0
  fi
  echo "J14: $FAILED of $N rows not as expected; first: $FIRST_FAIL" >&2; exit 1
}

deliver() { # FROM-DIR TO-DIR: copy every json file not already there
  mkdir -p -m 700 "$2"
  local f
  for f in "$1"/*.json; do [ -e "$f" ] || continue; [ -e "$2/$(basename "$f")" ] || install -m 0600 "$f" "$2/"; done
}

room_height() { "$MINI" credit --action room --dir "$WS/alice" --room lab 2>/dev/null | jq -r .height; }
credit_of() { "$MINI" credit --action balance --dir "$(ws_of "$1")" ${2:+--account "$2"} 2>/dev/null | sed -n 's/^credit \([0-9]*\) .*/\1/p'; }
JOURNAL=$H/hermes/runner/journal.jsonl
PLOG=$SD/provider.log
paid_turns() { jq -s '[.[] | select(.event == "paid" and .payment.paid == true)] | length' "$JOURNAL" 2>/dev/null; }
hermes() { # STEP WHAT: one attach of Hermes's controller
  operator "$1" "hermes attach: $2" "$GRAIN_RUNTIME" hermes-room step "$SD/hermes-lab.json"
  cp "$OUT" "$SD/attach-$1.jsonl"
  { echo "# hermes attach ($1): $2"; jq -c 'select(.event != "send") | del(.at)' "$OUT" 2>/dev/null | cut -c1-400; } >>"$SD/transcript.txt"
}
tail_json() { "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" --workspace "$WS/alice" \
  --home "$H/alice" --line "tail --in lab --json -n 200" 2>/dev/null; }

mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"

# ------------------------------------------------ friends and Hermes: enroll, provision, init
declare -A SUBJ FUND
FUND[alice]=5000; FUND[bob]=100; FUND[hermes]=0
for f in alice bob hermes; do
  mkdir -p -m 700 "$H/$f"
  ok setup "$f" "keygen mini.key"
  operator setup "CUSTODY: copy $f's secret into the sponsor home (enroll plan+seal sign with both keys)" \
    install -D -m 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/j14-$f.key"
  ok setup sponsor "enroll plan j14-$f j14-$f.key"
  ok setup sponsor "enroll seal j14-$f"
  ok setup sponsor "enroll submit j14-$f"
  SUBJ[$f]=$(jq -r '.subject // empty' "$OUT")
  checkp setup "$f is enrolled as its own subject" test -n "${SUBJ[$f]}"
  operator setup "CUSTODY: remove the copy" rm -f "$H/sponsor/keys/j14-$f.key"
  operator setup "PROVISION: factory observation + an account owned by $f funded ${FUND[$f]}" \
    "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "j14-$f" --holder "${SUBJ[$f]}" \
      --funding "${FUND[$f]}" --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator setup "DELIVER: the birth context into $f's HOME/provision/" \
    install -D -m 0600 "$SPONSOR_WS/provisions/j14-$f/birth-context.json" "$H/$f/provision/birth-context.json"
  ok setup "$f" "init mini.key ${SUBJ[$f]}"
done
A=${SUBJ[alice]} B=${SUBJ[bob]} HS=${SUBJ[hermes]}
FEE=$(jq -r '.tariffBase' "$CONFIG")
TURN=$((PRICE + FEE))
operator setup "NODE: the node's Hermes is subject $HS (HOME/hermes/node.json)" \
  sh -c "mkdir -p -m 700 '$H/alice/hermes' && printf '{\"subject\":\"%s\"}\n' '$HS' >'$H/alice/hermes/node.json'"
ok setup alice "credit"
A0=$(credit_of alice)

# ------------------------------------------------ the room
ok room alice "chat new lab"
LAB=$(jq -r .target "$WS/alice/refs/lab.json")
ok room alice "doc new lab-index 'any [ not (verb == write), subject == $A ]' --in lab"
ok room alice "doc append map lab-index 'lab: what we are writing, linked from here'"
ok room alice "submit map"
ok room alice "tariff lab set hermes/turn $PRICE"
ok room alice "chat invite lab $B bob --verbs observe,place,append"
operator room "DELIVER: bob's invitation" install -D -m 0600 "$H/alice/chat/invites/lab-$B.json" "$H/bob/requests/lab-invite.json"
ok room bob "chat join lab @lab-invite.json"

# ------------------------------------------------ summon
ok summon alice "summon lab as librarian --budget $BUDGET"
cp "$OUT" "$SD/summon.out"
OUTBOX=$H/alice/outbox/$HS
checkp summon "the hand-off: account, invitation, index, digest, manifest" \
  sh -c "for f in lab-hermes lab-invite lab-index lab-digest summon-lab; do test -s '$OUTBOX/'\$f.json || exit 1; done"
checkp summon "Hermes's account is owned by Hermes and funded $BUDGET" \
  jq -e --arg h "$HS" --arg b "$BUDGET" '.owner == $h and .funding == $b' "$OUTBOX/lab-hermes.json"
PROGRAM_T=$(jq -r .program.target "$OUTBOX/summon-lab.json")
ACCOUNT_T=$(jq -r .account.target "$OUTBOX/summon-lab.json")
A1=$(credit_of alice)
N=$((N + 1)); WALL=-
record summon check "alice paid the budget and the births (signed reads before/after)" "A0 - A1 >= $BUDGET" "$A0 - $A1 = $((A0 - A1))" \
  "$([ $((A0 - A1)) -ge "$BUDGET" ] && echo ok || echo FAIL)" "births: till, account, Hermes's stream, digest, program, and their fees"
ok summon alice "room status lab"
checkp summon "room status names Hermes and its budget account" grep -q "hermes: $HS, budget account $ACCOUNT_T" "$OUT"
ok summon alice "tariff lab"
checkp summon "the tariff: hermes/turn $PRICE; hermes = $HS" sh -c "grep -q '^  hermes/turn *$PRICE\$' '$OUT' && grep -q '^  hermes  *$HS\$' '$OUT'"
# the program is a document members read and the founder edits
BCAP=$(jq -r .observeCapability "$WS/bob/refs/lab.json")
ok program bob "import lab-program object $PROGRAM_T $BCAP $BCAP"
ok program bob "doc show lab-program"
checkp program "bob reads the librarian's program" grep -q "Librarian of lab" "$OUT"
# bob holds observe/place/append under lab, not mutate, and the program's
# law admits only the founder's writes; the Host's prepare reports the law's
# failing clause first (the clause names alice).
two_step_refused program bob "doc append bp lab-program 'bob: be nicer'" "submit bp" "law-denied: subject == $A"
ok program alice "doc append ap lab-hermes-librarian 'Founder: keep answers short.'"
ok program alice "submit ap"

# ------------------------------------------------ Hermes's controller and the deterministic provider
operator hermes "DELIVER: alice's hand-off into Hermes's inbox" deliver "$OUTBOX" "$H/hermes/inbox"
cat >"$SD/hermes-lab.json" <<EOF
{"type":"mini-hermes-room-runner-v1",
 "tools":{"mini":"$MINI","host":"$HOST","hostConfig":"$CONFIG","socket":"$SOCKET",
   "workspace":"$WS/hermes","home":"$H/hermes","room":"lab","account":"lab-hermes"},
 "inbox":"$H/hermes/inbox","state":"$H/hermes/runner",
 "provider":{"url":"http://127.0.0.1:$PORT/v1","model":"mini-hermes-protocol-fixture"},"maxRounds":8}
EOF
if ss -ltn 2>/dev/null | grep -q ":$PORT "; then echo "j14: port $PORT is taken" >&2; exit 2; fi
"$TEST_PROVIDER" "127.0.0.1:$PORT" "$PLOG" --room-librarian >"$SD/provider.out" 2>"$SD/provider.err" &
PROVIDER_PID=$!
for i in $(seq 1 100); do grep -q "^http://" "$SD/provider.out" 2>/dev/null && break; sleep 0.1; done
checkp hermes "the deterministic provider listens on loopback $PORT (pid $PROVIDER_PID)" grep -q "^http://127.0.0.1:$PORT/v1" "$SD/provider.out"

# ------------------------------------------------ attach 1: two docs, three things said
H0=$(room_height lab)
ok attach1 bob "doc new paper --in lab"
PAPER_T=$(jq -r .target "$WS/bob/refs/paper.json")
ok attach1 bob "doc append p1 paper 'paper: what the librarian is for'"
ok attach1 bob "submit p1"
ok attach1 bob "doc new data --in lab"
DATA_T=$(jq -r .target "$WS/bob/refs/data.json")
ok attach1 bob "doc append d1 data 'data: the numbers'"
ok attach1 bob "submit d1"
ok attach1 bob "say I put a draft in paper"
ok attach1 bob "say and the numbers are in data"
ok attach1 bob "say the librarian should find both"
hermes attach1 "links both docs and digests three entries"
checkp attach1 "Hermes joined lab and read its program document" sh -c "grep -q '\"event\":\"joined\"' '$JOURNAL'"
ok attach1 alice "doc show lab-index"
cp "$OUT" "$SD/index-1.txt"
check attach1 "lab-index links paper once" 1 "$(grep -c "^link .*$PAPER_T" "$OUT")"
check attach1 "lab-index links data once" 1 "$(grep -c "^link .*$DATA_T" "$OUT")"
checkp attach1 "Hermes made both links (created-by $HS)" sh -c "[ \$(grep -E '^link .*($PAPER_T|$DATA_T).*created-by $HS' '$OUT' | wc -l) = 2 ]"
DIGEST_REF=lab-digest
ok attach1 alice "doc show $DIGEST_REF"
cp "$OUT" "$SD/digest-1.txt"
checkp attach1 "lab-digest has a section by Hermes covering the three entries" sh -c "grep -E 'created-by $HS' '$OUT' | grep -q 'entries #'"
T1=$(paid_turns)
check attach1 "three turns paid (two links, one digest)" 3 "$T1"
check attach1 "Hermes's account = $BUDGET - 3*($PRICE + fee $FEE) (Hermes's signed read)" "$((BUDGET - 3 * TURN))" "$(credit_of hermes lab-hermes)"

# ------------------------------------------------ ask: answered from the history
ok ask alice "ask lab what changed since $H0"
hermes ask "answers alice from the signed history"
tail_json >"$SD/tail-ask.jsonl"
ASKN=$(jq -s --arg h "$HS" --arg a "$A" '[.[] | select(.author == $a and .to == $h)] | .[-1].n' "$SD/tail-ask.jsonl")
ANSWER=$(jq -s -r --arg h "$HS" --argjson n "${ASKN:-0}" '[.[] | select(.author == $h and .re == $n)] | .[0].text // ""' "$SD/tail-ask.jsonl")
printf '%s\n' "$ANSWER" >"$SD/answer-1.txt"
checkp ask "Hermes's answer replies to alice's entry #$ASKN, addressed to alice" \
  jq -s -e --arg h "$HS" --arg a "$A" --argjson n "${ASKN:-0}" 'any(.[]; .author == $h and .re == $n and .to == $a)' "$SD/tail-ask.jsonl"
checkp ask "the answer is the history: it names paper and data by their cells" \
  sh -c "grep -q 'Since height $H0' '$SD/answer-1.txt' && grep -q '$PAPER_T' '$SD/answer-1.txt' && grep -q '$DATA_T' '$SD/answer-1.txt'"

# ------------------------------------------------ no-grant: Hermes holds nothing on paper
ok nogrant bob "ask lab please append 'typo fixed' to cell $PAPER_T"
OPLOG0=$(cat "$W"/public/serve*.log 2>/dev/null | grep -c 'submission refused (operator log)')
hermes nogrant "tries the edit and reports the refusal"
cat "$W"/public/serve*.log 2>/dev/null | grep 'submission refused (operator log)' | tail -n +$((OPLOG0 + 1)) >"$SD/operator-refusals-nogrant.txt"
EDIT=$(jq -c 'select(.event == "resolved" and .resolution == "refused")' "$JOURNAL" | tail -1)
printf '%s\n' "$EDIT" >"$SD/edit-refusal.json"
# A blind submission's refusal is uniform on the submitter's channel
# (Kernel/NativeHost.lean publicSubmissionOutcome, theorem
# public_refusal_uniform): Hermes is told `undisclosed`; the Host's operator
# log names the decision: the invoke controller rejected the capability (the
# grant does not cover a write to paper).
checkp nogrant "Hermes's append to paper was refused at admission; Hermes's channel says undisclosed" \
  sh -c "printf '%s' '$EDIT' | grep -q 'refused: undisclosed: request refused (phase admission)'"
checkp nogrant "the Host's operator log names it: capabilityRejected (no grant covers the write)" \
  sh -c "[ \$(wc -l <'$SD/operator-refusals-nogrant.txt') = 1 ] && grep -q 'DeclaredResourceController.Reject.capabilityRejected' '$SD/operator-refusals-nogrant.txt'"
checkp nogrant "the refused edit was a paid turn (refusals cost)" \
  jq -s -e --argjson op "$(printf '%s' "$EDIT" | jq .op)" 'any(.[]; .event == "paid" and .op == $op)' "$JOURNAL"
tail_json >"$SD/tail-nogrant.jsonl"
checkp nogrant "Hermes said why in its stream (the Host's refusal, verbatim), replying to bob" \
  jq -s -e --arg h "$HS" --arg b "$B" 'any(.[]; .author == $h and .to == $b and (.text | test("refused: undisclosed")))' "$SD/tail-nogrant.jsonl"
check nogrant "paper is unchanged: bob's one line" 1 "$(cd "$WS/bob" && "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" --workspace "$WS/bob" --home "$H/bob" --line "doc show paper" 2>/dev/null | grep -cE '^ +[0-9]+  created-by')"

# ------------------------------------------------ budget: out, then topped up
ok budget bob "say one more thing"
ok budget bob "say and another"
H1=$(room_height lab)
ok budget alice "ask lab what changed since $H1"
hermes budget "a digest, then a turn the account cannot pay"
BAL=$(credit_of hermes lab-hermes)
checkp budget "the turn was refused bookRefused at plan and not attempted" \
  jq -s -e 'any(.[]; .event == "unpaid" and (.reason | test("bookRefused")))' "$JOURNAL"
checkp budget "Hermes's account holds less than one turn ($BAL < $TURN)" test "$BAL" -lt "$TURN"
tail_json >"$SD/tail-budget.jsonl"
checkp budget "Hermes says \"out of budget\" in its stream" \
  jq -s -e --arg h "$HS" 'any(.[]; .author == $h and (.text | startswith("out of budget")))' "$SD/tail-budget.jsonl"
ok budget alice "topup lab $TOPUP"
check budget "topup lands on Hermes's account" "$((BAL + TOPUP))" "$(credit_of hermes lab-hermes)"

# ------------------------------------------------ kill mid-write (M5 j4 shape)
ok kill bob "doc new notes --in lab"
NOTES_T=$(jq -r .target "$WS/bob/refs/notes.json")
ok kill bob "doc append n1 notes 'notes: loose ends'"
ok kill bob "submit n1"
touch "$SD/mark-kill"
"$GRAIN_RUNTIME" hermes-room step "$SD/hermes-lab.json" >"$SD/attach-kill.jsonl" 2>"$SD/attach-kill.err" &
RPID=$!
CALL=""
for i in $(seq 1 3000); do
  CALL=$(find "$WS/hermes/attempts" -path '*/hr-*/call.bin' -newer "$SD/mark-kill" 2>/dev/null | head -1)
  [ -n "$CALL" ] && break
  kill -0 "$RPID" 2>/dev/null || break
  sleep 0.05
done
OUTCOME_AT_KILL=no; [ -n "$CALL" ] && [ -e "$(dirname "$CALL")/outcome.json" ] && OUTCOME_AT_KILL=yes
kill -KILL "$RPID" 2>/dev/null; wait "$RPID" 2>/dev/null; KILLED_RC=$?; RPID=""
KOP=$(basename "$(dirname "${CALL:-/x/hr-0/call.bin}")" | sed 's/^hr-//')
N=$((N + 1)); WALL=-
record kill OPERATOR "SIGKILL the controller once a write's signed call is out (hr-$KOP)" "killed with call.bin" \
  "rc $KILLED_RC, call ${CALL:+present}, outcome at kill: $OUTCOME_AT_KILL" "$([ -n "$CALL" ] && [ "$KILLED_RC" = 137 ] && echo ok || echo FAIL)" "$CALL"
checkp kill "the journal holds op $KOP paid and submitted, unresolved" \
  jq -s -e --argjson op "${KOP:-0}" 'any(.[]; .event == "submitter" and .op == $op) and (any(.[]; .event == "resolved" and .op == $op) | not)' "$JOURNAL"
hermes restart "restart: the submitter is proven stopped, the attempt resolves by exact lookup"
RES=$(jq -c --argjson op "${KOP:-0}" 'select(.event == "resolved" and .op == $op)' "$JOURNAL" | tail -1)
printf '%s\n' "$RES" >"$SD/kill-resolution.json"
checkp restart "op $KOP resolved after the restart (recovered, performed or refused, with its basis)" \
  sh -c "printf '%s' '$RES' | jq -e '.recovered == true and (.resolution == \"performed\" or .resolution == \"refused\") and (.basis | length > 0)'"
checkp restart "the submitter was proven stopped before the lookup" \
  jq -s -e --argjson op "${KOP:-0}" 'any(.[]; .event == "submitter-stopped" and .op == $op)' "$JOURNAL"
check restart "op $KOP was submitted once (one attempt directory)" 1 "$(ls -d "$WS/hermes/attempts/hr-$KOP"* 2>/dev/null | wc -l)"
ok restart alice "doc show lab-index"
check restart "lab-index links notes exactly once" 1 "$(grep -c "^link .*$NOTES_T" "$OUT")"

# ------------------------------------------------ kill after send: never resent
H2=$(room_height lab)
ok send bob "ask lab what changed since $H2"
SENT_BEFORE=$(jq -s '[.[] | select(.event == "send")] | length' "$JOURNAL")
kill -STOP "$PROVIDER_PID"
"$GRAIN_RUNTIME" hermes-room step "$SD/hermes-lab.json" >"$SD/attach-send.jsonl" 2>"$SD/attach-send.err" &
RPID=$!
for i in $(seq 1 3000); do
  [ "$(jq -s '[.[] | select(.event == "send")] | length' "$JOURNAL")" -gt "$SENT_BEFORE" ] && break
  kill -0 "$RPID" 2>/dev/null || break
  sleep 0.05
done
sleep 0.5
KREQ=$(jq -s '[.[] | select(.event == "send")] | .[-1].request' "$JOURNAL")
kill -KILL "$RPID" 2>/dev/null; wait "$RPID" 2>/dev/null; KILLED_RC=$?; RPID=""
kill -CONT "$PROVIDER_PID"
sleep 3
N=$((N + 1)); WALL=-
record send OPERATOR "SIGKILL the controller with provider request $KREQ sent and unanswered (provider stopped)" "killed" \
  "rc $KILLED_RC" "$([ "$KILLED_RC" = 137 ] && echo ok || echo FAIL)" ""
checkp send "request $KREQ: send journaled, no reply recorded" \
  jq -s -e --argjson k "$KREQ" 'any(.[]; .event == "send" and .request == $k) and (any(.[]; .event == "recv" and .request == $k) | not)' "$JOURNAL"
hermes send "restart: request $KREQ is abandoned, a new request answers"
checkp send "request $KREQ is journaled abandoned, never resent" \
  jq -s -e --argjson k "$KREQ" 'any(.[]; .event == "abandoned" and .request == $k) and ([.[] | select(.event == "send" and .request == $k)] | length == 1)' "$JOURNAL"
SENDS=$(jq -s '[.[] | select(.event == "send")] | length' "$JOURNAL")
check send "the provider's own log: every request the journal sent received once ($SENDS sends)" "$SENDS $SENDS" \
  "$(sed -n 's/^received id=\([^ ]*\).*/\1/p' "$PLOG" | wc -l) $(sed -n 's/^received id=\([^ ]*\).*/\1/p' "$PLOG" | sort -u | wc -l)"
check send "the provider received request $KREQ exactly once" 1 "$(grep -c "^received id=hermes-room-$KREQ " "$PLOG")"
tail_json >"$SD/tail-send.jsonl"
checkp send "the question asked before the kill is answered after it" \
  jq -s -e --arg h "$HS" --arg b "$B" 'any(.[]; .author == $h and .to == $b and (.text | test("Since height")))' "$SD/tail-send.jsonl"

# ------------------------------------------------ dismiss: revoke, return the rest
BEFORE_RETURN=$(credit_of hermes lab-hermes)
A2=$(credit_of alice)
ok dismiss alice "dismiss lab"
cp "$OUT" "$SD/dismiss.out"
operator dismiss "DELIVER: the dismissal into Hermes's inbox" deliver "$OUTBOX" "$H/hermes/inbox"
hermes dismiss "returns the remainder"
RETURNED=$(jq -s -r '[.[] | select(.event == "returned")] | .[0].result.returned // "none"' "$JOURNAL")
check dismiss "Hermes returned its balance less the fee" "$((BEFORE_RETURN - FEE))" "$RETURNED"
check dismiss "Hermes's account is empty" 0 "$(credit_of hermes lab-hermes)"
check dismiss "alice received the remainder" "$((A2 + RETURNED))" "$(credit_of alice)"
named dismiss hermes "read lab" "revoked|no-grant|noGrant"
named dismiss hermes "doc show lab-index" "revoked|no-grant|noGrant"
ok dismiss alice "room status lab"
checkp dismiss "room status no longer names a Hermes" sh -c "! grep -q '^  hermes:' '$OUT'"

# ------------------------------------------------ balances: conservation
T=$(paid_turns)
check balances "Hermes's account: $BUDGET + $TOPUP - $T turns*($PRICE + fee $FEE) - returned - fee = 0" \
  0 "$((BUDGET + TOPUP - T * TURN - RETURNED - FEE))"
operator balances "lab's till, read by the founder" "$MINI" credit --action balance --dir "$WS/alice" --account lab-till
check balances "lab's till = $T turns * $PRICE" "$((T * PRICE))" "$(sed -n 's/^credit \([0-9]*\) .*/\1/p' "$OUT")"
operator balances "the till's hermes ledger (op 140)" "$MINI" credit --action ledger --dir "$WS/alice" --account lab-till --topic hermes
cp "$OUT" "$SD/till-ledger.json"
check balances "one hermes ledger entry per paid turn, each $PRICE from Hermes" "$T" \
  "$(jq --arg h "$HS" '[.entries[] | select(.subject == $h and .amount == "'"$PRICE"'")] | length' "$OUT")"

# ------------------------------------------------ cold audit
pidfile=$W/public/server.pid
restart() {
  local pid; pid=$(cat "$pidfile")
  kill -TERM "$pid"
  for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$pid" 2>/dev/null && { echo "server $pid alive after TERM" >&2; return 1; }
  "$MINI" audit --host "$HOST" --config "$CONFIG" >"$SD/audit-$1.out" 2>"$SD/audit-$1.err"
  echo $? >"$SD/audit-$1.rc"
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$W/public/serve-j14-$1.log" 2>&1 </dev/null &
  echo $! >"$pidfile"
  for i in $(seq 1 6000); do
    [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-j14-$1.log" 2>/dev/null && break; sleep 0.1
  done
}
operator audit "stop the Host, cold audit re-admits every record, serve again" restart r1
check audit "cold audit exit 0" 0 "$(cat "$SD/audit-r1.rc")"
PLINES=$(wc -l <"$PLOG")
hermes audit "after the cold audit: dismissed, nothing to do"
check audit "Hermes sent the provider nothing more" "$PLINES" "$(wc -l <"$PLOG")"
ok audit bob "tail --in lab -n 100"
cp "$OUT" "$SD/tail-final.txt"
checkp audit "bob's tail after the audit shows Hermes's entries" grep -q "$HS\|hermes" "$OUT"

finish
