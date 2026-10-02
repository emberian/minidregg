#!/usr/bin/env bash
# journey.d/j17.sh — P-CREDIT (PLACE §2.10, J17): a week in the place.
#
# On this journey's live Store (after J5). Friends are enrolled, provisioned
# and `init`ed exactly as J12/K10C do; every friend line is typed into that
# friend's own shell session (`--line`). The concierge is `grain-runtime
# concierge step` over the concierge subject's own workspace.
#
#   setup     alice (founder; 5000 credit), bob (B; provisioned with 0 credit),
#             carl (50 credit), con (the concierge subject).
#   room      alice: `room new lab --template workroom --concierge CON --period P`
#             (the room's lines, then the till, the runner account, the tariff's
#             account fields and the concierge's grants); `tariff lab set week 100`.
#   guest     B is a guest in lab (observe, append): reads it; B holds 0 credit;
#             B's `room new` is refused at plan bookRefused (birth fee); B's
#             `doc new --in lab` is refused notRoomMember (a guest does not place);
#             B's `pay lab week` with 0 credit is refused bookRefused.
#   credit    the sponsor's transfer credits B 1000 (devnet mint); `credit` = 1000.
#   week 1    `room status` before (guest); B `pay lab week`: the posting lands,
#             `renew` is on B's topic and on lab's till ledger (op 180); the
#             concierge delegates member under lab with notAfter = h + P and its
#             journal names the entry; B adopts the window (`room status`), and
#             bears a doc into lab.
#   restart   the service restarts (audit exit 0); the concierge re-reads its
#             journal and issues nothing twice; B's window stands.
#   expiry    heights advance by issued turns past notAfter: B's placement is
#             refused naming outside-validity, B's read through the window too;
#             `room status` says ENDED.
#   week 2    B pays again; the concierge re-issues; B writes.
#   carl      carl (50 credit) `pay lab week` refused bookRefused; carl pays 40:
#             the concierge refunds it (underpaid) and issues nothing.
#   race      eve (a guest) pays a week at 100; alice raises the week to 200
#             before the concierge runs: the payment names the price and the
#             height it read, and the concierge decides against the tariff AT
#             that height: issued. A memo quoting a price the tariff never had
#             is refunded (quote-differs). No decision depends on when the
#             concierge runs (01a0f9e1-c59a).
#   kick      alice kicks eve: `room kick` revokes eve's guest grant AND the
#             concierge's window (every standing grant, from the who view); eve
#             is refused, `room members` drops her; eve pays the till directly:
#             refunded (not-admitted). dave, never invited, pays the till:
#             refunded (01a0f9e1-50ef).
#   free      `commons` with week 0: B's `pay commons week` files a request;
#             the concierge issues on request after a signed who read; a forged
#             request for carl (no grant in commons) is journaled not-a-member.
#   balances  B = 1000 − 2·week − 2·fee − births·birthFee; lab's till = 2·week + 40.
#   audit     stop, cold audit re-admits every record (exit 0), serve.
#
# Hook contract: journey.sh (executed). Needs GRAIN_RUNTIME (the grain-runtime
# binary). Exported by journey.sh: MINI HOST CONFIG SOCKET SHELL_BIN SPONSOR_WS
# SPONSOR_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. Last stdout line: the row
# table. Last stderr line: the detail. Exit 0 only when every row is as expected.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" \
  "${SPONSOR_WS:?}" "${SPONSOR_SUBJECT:?}" "${JOURNEY_WORLD:?}" "${GRAIN_RUNTIME:?GRAIN_RUNTIME names the grain-runtime binary}"
SD=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
H=$SD/h; WS=$SD/w; L=$SD/log
mkdir -p -m 700 "$H" "$WS" "$L"
TABLE=$SD/j17.tsv
printf 'n\tstep\twho\tline\texpect\tgot\tverdict\twall_s\tload1\tnote\n' >"$TABLE"
N=0; FAILED=0; FIRST_FAIL=""
WEEK=100
PERIOD=${J17_PERIOD:-12}

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
}

record() { # step who line expect got verdict note
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$1" "$2" "$3" "$4" "$5" "$6" "${WALL:--}" "$(load1)" "$7" >>"$TABLE"
  if [ "$6" != ok ]; then
    FAILED=$((FAILED + 1))
    [ -n "$FIRST_FAIL" ] || FIRST_FAIL="row $N ($1 $2: $3): $7"
  fi
}

first_line() { grep -m1 -E '^(refused|undecided|error|usage): ' "$1"; }

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

# named STEP WHO LINE TEXT: refused (non-zero) and the Host's words name TEXT
# (an extended regex: the birth gate prints RefusalReason's constructor name,
# `outsideValidity`; the observation path prints its slug, `outside-validity`).
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

check() {
  local step=$1 what=$2 want=$3 got=$4
  N=$((N + 1)); WALL=-
  if [ "$want" = "$got" ]; then record "$step" check "$what" "$want" "$got" ok ""
  else record "$step" check "$what" "$want" "$got" FAIL "want $want got $got"; fi
}

checkp() { # STEP WHAT COMMAND... (a predicate)
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
    echo "J17: $N rows as expected ($TABLE)" >&2; exit 0
  fi
  echo "J17: $FAILED of $N rows not as expected; first: $FIRST_FAIL" >&2; exit 1
}

deliver() { # FROM-DIR TO-DIR: copy every json file not already there
  mkdir -p -m 700 "$2"
  local f
  for f in "$1"/*.json; do [ -e "$f" ] || continue; [ -e "$2/$(basename "$f")" ] || install -m 0600 "$f" "$2/"; done
}

room_height() { "$MINI" credit --action room --dir "$WS/alice" --room "$1" 2>/dev/null | jq -r .height; }
credit_of() { # WHO: the balance a signed read of WHO's account states
  "$MINI" credit --action balance --dir "$(ws_of "$1")" 2>/dev/null | sed -n 's/^credit \([0-9]*\) .*/\1/p'
}
concierge() { # STEP ROOM WHAT: one pass of the concierge program for ROOM
  operator "$1" "concierge pass ($2): $3" "$GRAIN_RUNTIME" concierge step "$SD/concierge-$2.json"
  PASS=$OUT
}

mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"

# ------------------------------------------------ friends: enroll, provision, init
declare -A SUBJ FUND
FUND[alice]=5000; FUND[bob]=0; FUND[carl]=50; FUND[con]=10; FUND[eve]=1000; FUND[dave]=500
for f in alice bob carl con eve dave; do
  mkdir -p -m 700 "$H/$f"
  ok setup "$f" "keygen mini.key"
  operator setup "CUSTODY: copy $f's secret into the sponsor home (enroll plan+seal sign with both keys)" \
    install -D -m 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/j17-$f.key"
  ok setup sponsor "enroll plan j17-$f j17-$f.key $(xxd -p -c 256 "$H/$f/keys/mini.key.next.pub") $(xxd -p -c 256 "$H/$f/keys/mini.key.next.cosign")"
  ok setup sponsor "enroll seal j17-$f"
  ok setup sponsor "enroll submit j17-$f"
  SUBJ[$f]=$(jq -r '.subject // empty' "$OUT")
  checkp setup "$f is enrolled as its own subject" test -n "${SUBJ[$f]}"
  operator setup "CUSTODY: remove the copy" rm -f "$H/sponsor/keys/j17-$f.key"
  operator setup "PROVISION: factory observation + an account owned by $f funded ${FUND[$f]}" \
    "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "j17-$f" --holder "${SUBJ[$f]}" \
      --funding "${FUND[$f]}" --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator setup "DELIVER: the birth context into $f's HOME/provision/" \
    install -D -m 0600 "$SPONSOR_WS/provisions/j17-$f/birth-context.json" "$H/$f/provision/birth-context.json"
  ok setup "$f" "init mini.key ${SUBJ[$f]}"
done
A=${SUBJ[alice]} B=${SUBJ[bob]} C=${SUBJ[carl]} CON=${SUBJ[con]} E=${SUBJ[eve]} D=${SUBJ[dave]}
BACCT=$(jq -r .feePayer "$WS/bob/birth-context.json")
FEE=$(jq -r '.tariffBase' "$CONFIG"); BIRTH=$(jq -r '.tariffPerBirth' "$CONFIG"); GRANT=$(jq -r '.tariffPerGrant' "$CONFIG")

# ------------------------------------------------ the room, its tariff, its concierge
ok room alice "room new lab --template workroom --concierge $CON --period $PERIOD"
LAB=$(jq -r .target "$WS/alice/refs/lab.json")
checkp room "the founder holds the till lab-till (an account)" jq -e '.kind == "account"' "$WS/alice/refs/lab-till.json"
checkp room "the program names lab, its till and the concierge" \
  jq -e --arg r "$LAB" --arg c "$CON" '.room == $r and .concierge == $c and .topic == "renew"' "$H/alice/concierge/lab.json"
ok room alice "tariff lab set week $WEEK"
ok room alice "tariff lab set hermes/turn 2"
ok room alice "tariff lab"
checkp room "tariff lab shows week $WEEK, period $PERIOD, the till and the concierge" \
  sh -c "grep -q '^  week *$WEEK\$' '$OUT' && grep -q '^  period *$PERIOD\$' '$OUT' && grep -q '^  concierge *$CON\$' '$OUT'"
TILL=$(jq -r .target "$WS/alice/refs/lab-till.json")

# the concierge's controller config, and its grants delivered
cat >"$SD/concierge-lab.json" <<EOF
{"type":"minidregg-concierge-controller-v1","mini":"$MINI","workspace":"$WS/con",
 "program":"$H/con/programs/lab.json","inbox":"$H/con/inbox","outbox":"$H/con/outbox",
 "journal":"$H/con/journal-lab.jsonl"}
EOF
operator room "DELIVER: alice's grants to the concierge into its inbox" deliver "$H/alice/outbox/$CON" "$H/con/inbox"
operator room "INSTALL: the program alice's room concierge wrote" install -D -m 0600 "$H/alice/concierge/lab.json" "$H/con/programs/lab.json"
concierge room lab "adopts its grants; nothing paid yet"
check room "the first pass issues nothing" 0 "$(jq '.decisions | length' "$PASS" 2>/dev/null)"
checkp room "the concierge holds lab (room) and lab-till (observe on the till)" \
  sh -c "jq -e '.room == \"member\"' '$WS/con/refs/lab.json' && jq -e '.kind == \"account\"' '$WS/con/refs/lab-till.json'"

# ------------------------------------------------ B, a guest with no credit
ok guest alice "room invite i-bob lab $B --verbs observe,append"
ok guest alice "submit i-bob"
ok guest alice "publish i-bob"
ok guest alice "export i-bob"
REF=$(cat "$OUT")
ok guest bob "import lab $REF"
ok guest bob "read lab"
ok guest bob "credit"
check guest "B holds 0 credit (signed read)" 0 "$(credit_of bob)"
# A birth's Book refusal is named by the birth controller: the descriptor's
# resource batch (funding legs + the creation fee) does not apply to an empty
# account (ResourceBirthController PreparationReject.resourceBatch). The fleet
# plan's name for the same Book refusal is bookRefused (pay, below).
named guest bob "room new bobroom" resourceBatch
named guest bob "doc new early --in lab" notRoomMember
named guest bob "pay lab week" bookRefused
ok status bob "room status lab"
cp "$OUT" "$SD/status-before.txt"
checkp status "room status before paying: a guest, no window" grep -q 'my window: none (guest' "$OUT"

# ------------------------------------------------ the devnet mint: the sponsor's transfer
operator credit "SPONSOR: name the sponsor's account" "$MINI" credit --action balance --dir "$SPONSOR_WS"
operator credit "SPONSOR: transfer 1000 credit to B's account $BACCT (the devnet mint)" \
  "$MINI" fleet --action transfer --dir "$SPONSOR_WS" --account account --to "$BACCT" --amount 1000
ok credit bob "credit"
check credit "B holds 1000 credit" 1000 "$(credit_of bob)"
ok credit bob "room new bobroom2"

# ------------------------------------------------ week 1
ok week1 bob "pay lab week"
cp "$OUT" "$SD/pay-1.txt"
operator week1 "B's renew topic carries the payment (B's receipt)" \
  "$MINI" fleet --action poll --dir "$WS/bob" --account account --topic renew
checkp week1 "renew #1 on B's topic names lab, the price and the height it read" \
  jq -e --arg r "room $LAB week $WEEK at " '.events | length == 1 and (.[0].payloadText | startswith($r))' "$OUT"
operator week1 "lab's till ledger (op 180, read by the founder)" \
  "$MINI" credit --action ledger --dir "$WS/alice" --account lab-till
checkp week1 "the till's renew ledger holds B's 100 at one height" \
  jq -e --arg b "$B" '.entries | length == 1 and .[0].subject == $b and .[0].amount == "100"' "$OUT"
H1=$(jq -r '.entries[0].height' "$OUT"); TX1=$(jq -r '.entries[0].transactionId' "$OUT")
concierge week1 lab "issues B's first week"
cp "$PASS" "$SD/pass-week1.json"
check week1 "the concierge delegated member to B with notAfter = h + $PERIOD" "issued $B $((H1 + PERIOD))" \
  "$(jq -r '.decisions[0] | "\(.decision) \(.subject) \(.notAfter)"' "$PASS" 2>/dev/null)"
check week1 "its journal names the entry it acted on (height, transaction, amount)" "$H1 $TX1 100" \
  "$(jq -r 'select(.decision == "issued") | "\(.entry.height) \(.entry.transactionId) \(.entry.amount)"' "$H/con/journal-lab.jsonl" | head -1)"
operator week1 "DELIVER: the concierge's reference into B's inbox" deliver "$H/con/outbox/$B" "$H/bob/inbox"
ok week1 bob "room status lab"
cp "$OUT" "$SD/status-week1.txt"
checkp week1 "room status: B adopted a member window until $((H1 + PERIOD))" grep -q "member until height $((H1 + PERIOD))" "$OUT"
ok week1 bob "doc new bnotes --in lab"
checkp week1 "B's doc names lab and B's window as its placing capability" \
  jq -e --arg lab "$LAB" --arg cap "$(jq -r .operationCapability "$WS/bob/refs/lab.json")" \
    '.birth.resources[0].room == $lab and .birth.resources[0].placement == $cap' "$WS/bob/sources/create-bnotes.json"

# ------------------------------------------------ restart
pidfile=$W/public/server.pid
restart() {
  local pid; pid=$(cat "$pidfile")
  kill -TERM "$pid"
  for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$pid" 2>/dev/null && { echo "server $pid alive after TERM" >&2; return 1; }
  "$MINI" audit --host "$HOST" --config "$CONFIG" >"$SD/audit-$1.out" 2>"$SD/audit-$1.err"
  echo $? >"$SD/audit-$1.rc"
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$W/public/serve-j17-$1.log" 2>&1 </dev/null &
  echo $! >"$pidfile"
  for i in $(seq 1 6000); do
    [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-j17-$1.log" 2>/dev/null && break; sleep 0.1
  done
}
operator restart "stop the Host, audit the closed Store, serve again" restart r1
check restart "audit re-admitted the Store" 0 "$(cat "$SD/audit-r1.rc")"
concierge restart lab "after the restart: re-reads its journal"
check restart "the concierge issues nothing twice" 0 "$(jq '.decisions | length' "$PASS" 2>/dev/null)"
ok restart bob "room status lab"
checkp restart "B's window stands after the restart" grep -q "member until height $((H1 + PERIOD))" "$OUT"
ok restart bob "read lab"

# ------------------------------------------------ expiry: heights advance by issued turns
ok expiry alice "credit"
ticks=0
while :; do
  h=$(room_height lab)
  [ -n "$h" ] && [ "$h" -gt $((H1 + PERIOD)) ] && break
  ticks=$((ticks + 1))
  [ "$ticks" -le 40 ] || break
  "$MINI" fleet --action publish --dir "$WS/alice" --account account --topic tick --payload "$ticks" \
    >"$L/tick-$ticks.out" 2>"$L/tick-$ticks.err"
done
N=$((N + 1)); WALL=-
record expiry OPERATOR "advance the height past $((H1 + PERIOD)) by alice's fleet publishes" "height > $((H1 + PERIOD))" \
  "height $h after $ticks turns" "$([ "$h" -gt $((H1 + PERIOD)) ] && echo ok || echo FAIL)" ""
named expiry bob "doc new late --in lab" "notRoomMember.*outsideValidity"
named expiry bob "read lab" "refused: outside-validity"
ok expiry bob "room status lab"
cp "$OUT" "$SD/status-expired.txt"
checkp expiry "room status: B's window ENDED" grep -q "my window: ENDED at height $((H1 + PERIOD))" "$OUT"

# ------------------------------------------------ week 2
ok week2 bob "pay lab week"
operator week2 "lab's till ledger above the first payment" \
  "$MINI" credit --action ledger --dir "$WS/alice" --account lab-till --since "$H1"
H2=$(jq -r '.entries[0].height' "$OUT")
concierge week2 lab "re-issues B's week"
check week2 "the concierge re-issued B's window from the new payment: notAfter = h2 + $PERIOD" "issued $B $((H2 + PERIOD))" \
  "$(jq -r '.decisions[0] | "\(.decision) \(.subject) \(.notAfter)"' "$PASS" 2>/dev/null)"
operator week2 "DELIVER: the concierge's reference into B's inbox" deliver "$H/con/outbox/$B" "$H/bob/inbox"
ok week2 bob "room status lab"
cp "$OUT" "$SD/status-week2.txt"
checkp week2 "room status: member until $((H2 + PERIOD))" grep -q "member until height $((H2 + PERIOD))" "$OUT"
ok week2 bob "doc new again --in lab"
ok week2 bob "read lab"

# ------------------------------------------------ carl: insufficient, then underpaid
ok carl alice "room invite i-carl lab $C --verbs observe"
ok carl alice "submit i-carl"
ok carl alice "publish i-carl"
ok carl alice "export i-carl"
REF=$(cat "$OUT")
ok carl carl "import lab $REF"
named carl carl "pay lab week" bookRefused
ok carl carl "pay lab 40"
concierge carl lab "an underpayment"
check carl "the concierge refunds the underpayment and issues nothing" "refunded underpaid $C" \
  "$(jq -r '.decisions[0] | "\(.decision) \(.reason) \(.subject)"' "$PASS" 2>/dev/null)"
checkp carl "no reference was left for carl" test ! -e "$H/con/outbox/$C"

TILL=$(jq -r .target "$WS/alice/refs/lab-till.json")
# ------------------------------------------------ the price race (01a0f9e1-c59a)
ok race alice "room invite i-eve lab $E --verbs observe"
ok race alice "submit i-eve"
ok race alice "publish i-eve"
ok race alice "export i-eve"
REF=$(cat "$OUT")
ok race eve "import lab $REF"
ok race eve "pay lab week"
checkp race "eve's payment says the price and the height it read" grep -q "at the price $WEEK read at height" "$OUT"
ok race alice "tariff lab set week 200"
concierge race lab "the founder raised the price between the payment and the pass"
check race "eve's payment is honoured at the price it read" "issued $E" \
  "$(jq -r '.decisions[0] | "\(.decision) \(.subject)"' "$PASS" 2>/dev/null)"
checkp race "the decision names the height the price was read at" jq -e '.decisions[0].priceReadAt != null' "$PASS"
operator race "DELIVER: the concierge's reference into eve's inbox" deliver "$H/con/outbox/$E" "$H/eve/inbox"
ok race eve "room status lab"
checkp race "room status: eve holds a member window" grep -q "my window: member until height" "$OUT"
ok race alice "tariff lab set week $WEEK"
HQ=$(room_height lab)
operator race "eve pays with a memo quoting a price the tariff never had (50 at $HQ)" \
  "$MINI" fleet --action send --dir "$WS/eve" --account account --topic renew \
    --payload "room $LAB week 50 at $HQ" --to "$TILL" --amount "$WEEK"
concierge race lab "a quote that disagrees with the tariff at its height"
check race "refunded, never kept" "refunded quote-differs $E" \
  "$(jq -r '.decisions[0] | "\(.decision) \(.reason) \(.subject)"' "$PASS" 2>/dev/null)"

# ------------------------------------------------ kick and the concierge (01a0f9e1-50ef)
ok kick alice "room kick k-eve lab $E"
check kick "the kick names both of eve's standing grants: the guest invite and the concierge's window" 2 \
  "$(jq '.capabilities | length' "$OUT" 2>/dev/null)"
ok kick alice "submit k-eve"
named kick eve "read lab" "revoked"
named kick eve "doc new evedoc --in lab" "notRoomMember"
ok kick alice "room members lab"
checkp kick "room members does not list eve" jq -e --arg e "$E" '[.members[].subject] | index($e) | not' "$OUT"
EBEFORE=$(credit_of eve)
operator kick "kicked eve pays the till directly, quoting the current price" \
  "$MINI" fleet --action send --dir "$WS/eve" --account account --topic renew \
    --payload "room $LAB week $WEEK at $(room_height lab)" --to "$TILL" --amount "$WEEK"
concierge kick lab "a kicked subject's payment"
check kick "refunded: the room does not admit eve" "refunded not-admitted $E" \
  "$(jq -r '.decisions[0] | "\(.decision) \(.reason) \(.subject)"' "$PASS" 2>/dev/null)"
checkp kick "no window was left for eve" sh -c "test \$(ls '$H/con/outbox/$E' | wc -l) = 1"
check kick "eve is down only her payment's fee" "$((EBEFORE - FEE))" "$(credit_of eve)"
DBEFORE=$(credit_of dave)
operator never "dave, never invited, pays the till" \
  "$MINI" fleet --action send --dir "$WS/dave" --account account --topic renew \
    --payload "room $LAB week $WEEK at $(room_height lab)" --to "$TILL" --amount "$WEEK"
concierge never lab "a never-invited subject's payment"
check never "refunded: the room does not admit dave" "refunded not-admitted $D" \
  "$(jq -r '.decisions[0] | "\(.decision) \(.reason) \(.subject)"' "$PASS" 2>/dev/null)"
checkp never "no window for dave" test ! -e "$H/con/outbox/$D"
check never "dave is down only his payment's fee" "$((DBEFORE - FEE))" "$(credit_of dave)"

# ------------------------------------------------ a free room
ok free alice "room new commons --concierge $CON --period $PERIOD"
COMMONS=$(jq -r .target "$WS/alice/refs/commons.json")
ok free alice "tariff commons"
checkp free "commons is free (week 0)" grep -q '^  week *0$' "$OUT"
cat >"$SD/concierge-commons.json" <<EOF
{"type":"minidregg-concierge-controller-v1","mini":"$MINI","workspace":"$WS/con",
 "program":"$H/con/programs/commons.json","inbox":"$H/con/inbox","outbox":"$H/con/outbox",
 "journal":"$H/con/journal-commons.jsonl"}
EOF
operator free "DELIVER: alice's commons grants to the concierge" deliver "$H/alice/outbox/$CON" "$H/con/inbox"
operator free "INSTALL: the commons program" install -D -m 0600 "$H/alice/concierge/commons.json" "$H/con/programs/commons.json"
ok free alice "room invite i-bob-c commons $B --verbs observe"
ok free alice "submit i-bob-c"
ok free alice "publish i-bob-c"
ok free alice "export i-bob-c"
REF=$(cat "$OUT")
ok free bob "import commons $REF"
ok free bob "pay commons week"
checkp free "B's request is filed in B's outbox" sh -c "ls '$H/bob/outbox/$CON'/request-$COMMONS-$B-*.json"
operator free "DELIVER: B's request to the concierge" deliver "$H/bob/outbox/$CON" "$H/con/inbox"
jq -n --arg r "$COMMONS" --arg s "$C" '{type:"minidregg-room-request-v1",room:$r,subject:$s,height:"1"}' \
  >"$H/con/inbox/request-$COMMONS-$C-1.json"
concierge free commons "issues on request"
check free "B (a standing member of commons) is issued a window; carl (no grant) is not" "issued $B|not-a-member $C" \
  "$(jq -r '[.decisions[] | "\(.decision) \(.subject)"] | sort | join("|")' "$PASS" 2>/dev/null)"
operator free "DELIVER: the concierge's commons reference into B's inbox" deliver "$H/con/outbox/$B" "$H/bob/inbox"
ok free bob "room status commons"
checkp free "room status commons: B is a member" grep -q "my window: member until height" "$OUT"
ok free bob "doc new cnotes --in commons"

# ------------------------------------------------ balances: conservation
ok balances bob "credit"
BFINAL=$(credit_of bob)
# B paid two weeks (each with the fleet fee) and bore four cells (bobroom2, bnotes, again, cnotes).
# A birth's quoted fee (Theory/ResourceBirth.lean Descriptor.quotedFee): base +
# perBirth*1 + perGrant*2 (owner and control grants) + perByte*0.
check balances "B = 1000 - 2*$WEEK - 2*fee($FEE) - 4 births*(base $FEE + birth $BIRTH + 2 grants*$GRANT)" \
  "$((1000 - 2 * WEEK - 2 * FEE - 4 * (FEE + BIRTH + 2 * GRANT)))" "$BFINAL"
operator balances "lab's till, read by the founder" "$MINI" credit --action balance --dir "$WS/alice" --account lab-till
# The till keeps exactly the weeks it honoured (bob's two, eve's one) and pays
# the fee of each of its four refunds (carl, eve's bad quote, eve kicked, dave).
check balances "lab's till = 3*$WEEK - 4 refund fees" "$((3 * WEEK - 4 * FEE))" "$(sed -n 's/^credit \([0-9]*\) .*/\1/p' "$OUT")"
check balances "carl = 50 - fee($FEE): his 40 came back" "$((50 - FEE))" "$(credit_of carl)"
ok balances bob "room status lab"
cp "$OUT" "$SD/status-after.txt"
HB=$(room_height lab)
checkp balances "room status after: the week-2 window (to $((H2 + PERIOD))) has ended by height $HB" \
  grep -q "my window: ENDED at height $((H2 + PERIOD))" "$OUT"

# ------------------------------------------------ cold audit
operator audit "stop the Host, cold audit re-admits every record, serve again" restart r2
check audit "cold audit exit 0" 0 "$(cat "$SD/audit-r2.rc")"
named audit bob "read lab" "refused: outside-validity"
ok audit bob "read lab-guest"
concierge audit lab "after the cold audit"
check audit "nothing re-issued" 0 "$(jq '.decisions | length' "$PASS" 2>/dev/null)"

finish
