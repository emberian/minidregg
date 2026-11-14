#!/usr/bin/env bash
# JFLEETIN (R10, FLEET-SURFACE.md; the north star "could helm run on this"): the incoming ledger
# (Host op 180) through the helm adapter, on this journey's live Store.
#
# `dregg-client-sign incoming` is `mini fleet-sign incoming`: the accepted fleet turns that paid the
# profile's account, behind the profile's signed observation of it. Two profiles join under the
# sponsor's factory grant (admitted, funded accounts). Before any payment the Host's ledger for B is
# empty. A pays B 25: the transfer is confirmed and B's ledger holds exactly that turn (amount 25,
# the transaction id of A's receipt). A refused overdraw by B (the Host's bookRefused) leaves B's
# ledger as it was. A `fleet send --to B` with a topic and a payload appears under that topic with
# the payload text; reading above the returned cursor answers empty. The shim a harness installs
# (`dregg-client-sign`) answers byte-for-byte what `mini fleet-sign` does.
#
# Hook contract: journey.sh (executed). Needs MINI HOST CONFIG SOCKET SPONSOR_WS JOURNEY_STEP_DIR.
# Last stdout line: the row table. Last stderr line: the detail.
set -u
umask 077
HERE=$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
. "$HERE/lib/rows.sh"
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}"
rows_init JFLEETIN
export MINI_FLEET_HOME=$D/fleet-home MINI_FLEET_SPONSOR=$SPONSOR_WS
SUF=$(od -An -N3 -tx1 /dev/urandom | tr -d ' \n')
PA=fia$SUF; PB=fib$SUF
FS() { "$MINI" fleet-sign "$@"; }

run joina FS join --profile "$PA" --fund 1000; A=$(jq -r '.cell // empty' "$OUT" 2>/dev/null)
row "join: A's key is admitted and its owned account funded" "joined, balance 1000, a cell" \
  "rc $RC, $(jq -c '{joined,balance,cell}' "$OUT" 2>/dev/null | cut -c1-120)" \
  "$([ "$RC" = 0 ] && jq -e '.joined == true and .balance == 1000 and (.cell | length > 0)' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"
run joinb FS join --profile "$PB" --fund 500; B=$(jq -r '.cell // empty' "$OUT" 2>/dev/null)
row "join: B's key is admitted and its owned account funded" "joined, balance 500, a cell" \
  "rc $RC, $(jq -c '{joined,balance,cell}' "$OUT" 2>/dev/null | cut -c1-120)" \
  "$([ "$RC" = 0 ] && jq -e '.joined == true and .balance == 500 and (.cell | length > 0)' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"

run in0 FS incoming --profile "$PB"
row "incoming: the Host's ledger for B before any payment" "type minidregg-fleet-incoming-v1, B's account, no entries" \
  "rc $RC, $(jq -c '{type,account,n:(.entries|length)}' "$OUT" 2>/dev/null | cut -c1-120)" \
  "$([ "$RC" = 0 ] && jq -e '.type == "minidregg-fleet-incoming-v1" and (.entries | length) == 0 and .cell == "'"$B"'"' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"

run pay FS transfer --profile "$PA" --to "$B" --amount 25
row "transfer: A pays B 25 and the Host confirms it" "committed, to B, amount 25, a receipt" \
  "rc $RC, $(jq -c '{committed,amount,tx:.receipt.transactionId}' "$OUT" 2>/dev/null | cut -c1-120)" \
  "$([ "$RC" = 0 ] && jq -e '.committed == true and .amount == 25 and .to == "'"$B"'" and (.receipt.transactionId | length > 0)' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"
TX=$(jq -r '.receipt.transactionId // empty' "$D/log/pay.out" 2>/dev/null)
run in1 FS incoming --profile "$PB"
row "incoming: B's ledger holds exactly A's transfer" "one entry: amount 25, the transaction id of A's receipt" \
  "rc $RC, $(jq -c '[.entries[] | {amount,transactionId}]' "$OUT" 2>/dev/null | cut -c1-140), receipt tx '${TX:-none}'" \
  "$([ "$RC" = 0 ] && [ -n "$TX" ] && jq -e --arg t "$TX" '(.entries | length) == 1 and .entries[0].amount == "25" and .entries[0].transactionId == $t' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"

run overdraw FS transfer --profile "$PB" --to "$A" --amount 100000
row "transfer: B overdrawing its account is refused by the Host's book" "rc != 0 naming bookRefused or not admitted, nothing committed" \
  "rc $RC, $(tail -1 "$ERR" | cut -c1-140)" \
  "$([ "$RC" != 0 ] && grep -Eq 'bookRefused|not admitted' "$ERR" && ! grep -q '"committed"' "$OUT" && echo 1 || echo 0)"
run in2 FS incoming --profile "$PB"
row "incoming: the refused overdraw left B's ledger as it was" "still one entry, amount 25" \
  "rc $RC, $(jq -c '[.entries[] | {amount,transactionId}]' "$OUT" 2>/dev/null | cut -c1-140)" \
  "$([ "$RC" = 0 ] && jq -e --arg t "$TX" '(.entries | length) == 1 and .entries[0].transactionId == $t' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"

run topic "$MINI" fleet --action send --dir "$MINI_FLEET_HOME/profiles/$PA/workspace" --account account --topic inbox --payload "hello from $PA" --to "$B" --amount 3
row "fleet send: a topic event that also pays B 3 is confirmed" "a receipt and a publication" \
  "rc $RC, $(jq -c '{fee,amount:.transfer.amount,seq:.publication.sequence}' "$OUT" 2>/dev/null | cut -c1-120)" \
  "$([ "$RC" = 0 ] && jq -e '.transfer.amount == "3" and (.receipt.transactionId | length > 0)' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"
run in3 FS incoming --profile "$PB" --topic inbox
row "incoming --topic inbox: the entry carries the topic's payload text" "one entry on inbox, amount 3, payloadText 'hello from $PA'" \
  "rc $RC, $(jq -c '[.entries[] | {amount,payloadText}]' "$OUT" 2>/dev/null | cut -c1-140)" \
  "$([ "$RC" = 0 ] && jq -e --arg p "hello from $PA" '(.entries | length) == 1 and .entries[0].amount == "3" and .entries[0].payloadText == $p' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"
run in4 FS incoming --profile "$PB"
CUR=$(jq -r '.nextCursor // empty' "$OUT" 2>/dev/null)
row "incoming: every topic lists both payments, ascending" "two entries (25 then 3)" \
  "rc $RC, $(jq -c '[.entries[] | .amount]' "$OUT" 2>/dev/null)" \
  "$([ "$RC" = 0 ] && jq -e '[.entries[] | .amount] == ["25","3"]' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"
run in5 FS incoming --profile "$PB" --since "${CUR:-0}"
row "incoming --since the returned cursor: nothing newer" "no entries" \
  "rc $RC, cursor '${CUR:-none}', $(jq -c '(.entries|length)' "$OUT" 2>/dev/null) entries" \
  "$([ "$RC" = 0 ] && [ -n "$CUR" ] && [ "$CUR" != 0 ] && jq -e '(.entries | length) == 0' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"

SEQ=$(jq -r '.resumeSeq // empty' "$D/log/in4.out" 2>/dev/null)
run in6 FS incoming --profile "$PB" --after-seq 0 --limit 1
row "incoming --after-seq 0 --limit 1: one page of rows from the first position" "page.state rows, firstSeq 1, one entry (25), resumeSeq 1" \
  "rc $RC, $(jq -c '{page,resumeSeq,amounts:[.entries[] | .amount]}' "$OUT" 2>/dev/null | cut -c1-160)" \
  "$([ "$RC" = 0 ] && jq -e '.page.state == "rows" and .page.firstSeq == "1" and .resumeSeq == "1" and [.entries[] | .amount] == ["25"]' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"
run in7 FS incoming --profile "$PB" --after-seq 1
row "incoming --after-seq 1: the page resumes at the next payment, none repeated" "page.state rows, firstSeq 2, one entry (3), resumeSeq 2" \
  "rc $RC, $(jq -c '{page,resumeSeq,amounts:[.entries[] | .amount]}' "$OUT" 2>/dev/null | cut -c1-160)" \
  "$([ "$RC" = 0 ] && jq -e '.page.state == "rows" and .page.firstSeq == "2" and .resumeSeq == "2" and [.entries[] | .amount] == ["3"]' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"
run in8 FS incoming --profile "$PB" --after-seq "${SEQ:-0}"
row "incoming --after-seq the returned resumeSeq: the tip, named" "page.state tip with count 2, no entries" \
  "rc $RC, resumeSeq '${SEQ:-none}', $(jq -c '{page,n:(.entries|length)}' "$OUT" 2>/dev/null | cut -c1-120)" \
  "$([ "$RC" = 0 ] && [ "$SEQ" = 2 ] && jq -e '.page.state == "tip" and .page.count == "2" and (.entries | length) == 0' "$OUT" >/dev/null 2>&1 && echo 1 || echo 0)"
run in9 FS incoming --profile "$PB" --after-seq 1 --max-bytes 1
row "incoming --max-bytes 1: a payment larger than the budget refuses by name, not skipped" "rc != 0 naming incomingOversize at position 2, no entries printed" \
  "rc $RC, $(tail -1 "$ERR" | cut -c1-140)" \
  "$([ "$RC" != 0 ] && grep -q 'incomingOversize: the member at position 2 ' "$ERR" && ! grep -q '"entries"' "$OUT" && echo 1 || echo 0)"
run in10 FS incoming --profile "$PB" --after-seq 0 --limit 2 --max-bytes 1
row "incoming --limit 2 --max-bytes 1 from the start: the first payment also exceeds the budget" "rc != 0 naming incomingOversize at position 1" \
  "rc $RC, $(tail -1 "$ERR" | cut -c1-140)" \
  "$([ "$RC" != 0 ] && grep -q 'incomingOversize: the member at position 1 ' "$ERR" && echo 1 || echo 0)"

cp "$D/log/in4.out" "$D/in4.expected"
run shim env MINI_BIN="$MINI" "$HERE/../dregg-client-sign" incoming --profile "$PB"
row "the helm adapter (dregg-client-sign) answers what mini fleet-sign does" "byte-identical incoming answer" \
  "rc $RC, identical=$(cmp -s "$OUT" "$D/in4.expected" && echo yes || echo no)" \
  "$([ "$RC" = 0 ] && [ -s "$OUT" ] && cmp -s "$OUT" "$D/in4.expected" && echo 1 || echo 0)"
rows_finish
