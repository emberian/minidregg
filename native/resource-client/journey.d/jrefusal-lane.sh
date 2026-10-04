#!/usr/bin/env bash
# JRLANE (R2-1 #5, Kernel/RefusalLane.lean; DeclaredResourceController.withAcceptedLoadedFrom):
# refusal work is charged to the signer, and only to an AUTHENTICATED signer.
#
# Two fresh subjects A and B each hold one write signed for the same height and
# NOT submitted (`workspace submit --prepare-only true`: call.bin). Nothing commits
# until the last row, so every altered copy below is judged at that one height.
# Altered copies are byte edits of the exact signed call (journey.d/lib/hostraw.py
# flip): the authority envelope's signature inverted ("wrongly signed") or zeroed
# ("unsigned"), or a TARGET envelope's signature inverted -- the authority still
# authenticates, so the command is prepared and then refused at its target leg:
# an authenticated refusal, which the lane charges (>= 50 ms each).
#
#   1. wrongly signed / unsigned copies are refused by name;
#   2. 1500 wrongly signed copies, then one authenticated refusal: it is refused
#      at its leg, NOT refusalLane -- the 1500 cost nothing (75 s of fee if they did);
#   3. authenticated refusals, at full speed, close A's lane (refusalLane) after
#      no fewer than capacity / base fee = 600 of them;
#   4. once closed the lane admits at most one charged refusal per fee x 10 of
#      wall time (100 ms/s refill: "at most a tenth of the time");
#   5. B's lane is untouched: B's authenticated refusal reads its leg, not refusalLane;
#   6. A's own unaltered call is refused refusalLane right after a charged refusal,
#      and admitted once the lane has refilled.
# Row 2 is evidence only while row 3 holds (a lane that never closes cannot show
# a charge); it says so when it is not.
#
# The public channel names no refusal ("request refused" for every one of these:
# an unauthenticated sender learns nothing), so each refusal's NAME is read from
# the Host's operator log (the live `mini serve` log), entry by entry: the Host
# is serial and this hook's client is serial, so the n-th new entry is the n-th
# refused request (journey.d/lib/hostraw.py refusals).
#
# Hook contract: journey.sh exports MINI HOST CONFIG SOCKET SPONSOR_WS JOURNEY_STEP_DIR.
# Last stdout line = artifact; last stderr line = detail.
set -u
umask 077
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
RAW="python3 $HERE/lib/hostraw.py"
D=$JOURNEY_STEP_DIR/jrl
mkdir -p -m 700 "$D" "$D/req"
T=$D/jrlane.tsv; : >"$T"
N=0; BAD=0
run() {  # run NAME CMD... : records cmd/out/err/rc
  local name=$1; shift
  { printf '%q ' "$@"; echo; } >"$D/$name.cmd"
  timeout 900 "$@" >"$D/$name.out" 2>"$D/$name.err"
  echo $? >"$D/$name.rc"
  return "$(cat "$D/$name.rc")"
}
row() {  # row CHECK EXPECTED OBSERVED OK(0/1)
  N=$((N + 1))
  if [ "$4" = 1 ]; then printf 'PASS\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"
  else printf 'FAIL\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"; BAD=$((BAD + 1)); fi
}
die() { echo "$T"; echo "JRLANE: $*" >&2; exit 1; }
# decode REPLY.bin NAME : the Host's own decoding of a reply frame -> $D/NAME.json
decode() {
  tail -c +2 "$1" >"$D/$2.outcome.bin"
  "$HOST" "$CONFIG" inspect outcome "$D/$2.outcome.bin" "$D/$2.json" >"$D/$2.inspect.out" 2>&1
}
detail() { jq -r '[.type, .reason, (.detail // "" | tostring)] | join(" ")' "$D/$1.json" 2>/dev/null | cut -c1-300; }
OPLOG=$(ls -t "$JOURNEY_WORLD"/public/serve-*.log 2>/dev/null | head -1)
[ -f "$OPLOG" ] || { echo "JRLANE: no operator log under $JOURNEY_WORLD/public" >&2; exit 1; }
marks() { $RAW refusals "$OPLOG" 0 | wc -l; }          # refusal entries so far
since() { $RAW refusals "$OPLOG" "$1"; }                # entries after mark $1
# named CALLFILE NAME : one request; $D/NAME.reason = its operator-log entry ("" if none)
named() {
  local m; m=$(marks)
  $RAW call "$SOCKET" "$CONFIG" "$HOST" 2 "$1" "$D/r-$2.bin" >"$D/r-$2.ms"
  since "$m" >"$D/$2.reason"
}
kind() { cut -f2 "$D/$1.reason" | paste -sd, -; }       # lane | authsig | legsig | other (one per entry)
why() { cut -f3 "$D/$1.reason" | head -1 | cut -c1-240; }

enroll() {  # enroll NAME : sets SUBJ; workspace at $D/NAME-ws
  local n=$1
  "$MINI" keygen --secret "$D/$n.key" --public "$D/$n.pub" --no-prerotation >"$D/$n-keygen.out" 2>"$D/$n-keygen.err" \
    || die "$n keygen: $(tail -1 "$D/$n-keygen.err")"
  run "$n-plan" "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
    --name "jrl-$n" --new-key "$D/$n.key" --no-prerotation --dir "$D/enroll-$n" || die "$n plan: $(tail -1 "$D/$n-plan.err")"
  run "$n-seal" "$MINI" enroll --action seal --dir "$D/enroll-$n" || die "$n seal: $(tail -1 "$D/$n-seal.err")"
  run "$n-submit" "$MINI" enroll --action submit --dir "$D/enroll-$n" || die "$n submit: $(tail -1 "$D/$n-submit.err")"
  run "$n-init" "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --enrollment "$D/enroll-$n/enrollment.json" --no-prerotation --dir "$D/$n-ws" || die "$n init: $(tail -1 "$D/$n-init.err")"
  SUBJ=$(jq -r .subject "$D/enroll-$n/enrollment.json")
}
enroll a; A=$SUBJ
enroll b; B=$SUBJ

# The sponsor's resource, and a mutate grant to each.
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
run create "$MINI" workspace --action create --dir "$SPONSOR_WS" --name jrl --storage declared \
  --predicate "$D/req/permit-all.json" --fields 2,3,4 || die "create jrl: $(tail -1 "$D/create.err")"
for who in a b; do
  subject=$A; [ "$who" = b ] && subject=$B
  jq -n --arg r "$subject" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"jrl",
    recipient:$r,verbs:["observe","mutate"],maxCost:"50000"}' >"$D/req/delegate-$who.json"
  run "dprop-$who" "$MINI" workspace --action propose --dir "$SPONSOR_WS" --request "$D/req/delegate-$who.json" \
    --proposal-id "jrl-grant-$who" || die "delegate $who: $(tail -1 "$D/dprop-$who.err")"
  run "dsub-$who" "$MINI" workspace --action submit --dir "$SPONSOR_WS" \
    --intent "$SPONSOR_WS/proposals/jrl-grant-$who/intent.json" --attempt "$SPONSOR_WS/attempts/jrl-grant-$who" \
    || die "delegate submit $who: $(tail -1 "$D/dsub-$who.err")"
  run "dpub-$who" "$MINI" workspace --action publish-delegation --dir "$SPONSOR_WS" --proposal-id "jrl-grant-$who" \
    --attempt "$SPONSOR_WS/attempts/jrl-grant-$who" || die "publish $who: $(tail -1 "$D/dpub-$who.err")"
  run "imp-$who" "$MINI" workspace --action import --dir "$D/$who-ws" --name jrl \
    --from-ref "$SPONSOR_WS/proposals/jrl-grant-$who/recipient-reference.json" || die "import $who"
done

# One signed, unsubmitted write each, both at the current height.
for who in a b; do
  field=2; [ "$who" = b ] && field=3
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"jrl","payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"%s"},"value":"1"}]}}]}\n' "$field" \
    >"$D/req/write-$who.json"
  run "wprop-$who" "$MINI" workspace --action propose --dir "$D/$who-ws" --request "$D/req/write-$who.json" \
    --proposal-id "w-$who" || die "write propose $who: $(tail -1 "$D/wprop-$who.err")"
  run "wprep-$who" "$MINI" workspace --action submit --dir "$D/$who-ws" --intent "$D/$who-ws/proposals/w-$who/intent.json" \
    --attempt "$D/$who-ws/attempts/w-$who" --prepare-only true || die "prepare-only $who: $(tail -1 "$D/wprep-$who.err")"
done
CA=$D/a-ws/attempts/w-a; CB=$D/b-ws/attempts/w-b
row "each subject holds one signed write, prepared and not submitted" "call.bin, no outcome" \
  "a=$(stat -c %s "$CA/call.bin" 2>/dev/null)B b=$(stat -c %s "$CB/call.bin" 2>/dev/null)B" \
  "$([ -s "$CA/call.bin" ] && [ -s "$CB/call.bin" ] && [ ! -e "$CA/outcome.bin" ] && [ ! -e "$CB/outcome.bin" ] && echo 1 || echo 0)"
# The signature the call carries; single-target writes sign one request for the
# target leg and the authority leg, so it occurs twice: first the target, last the authority
# (SignedCommand: commandBytes, targetEnvelopes, observeEnvelopes, authorityEnvelope).
SA=$(jq -r '.[-1]' "$CA/transaction-signatures.json"); SB=$(jq -r '.[-1]' "$CB/transaction-signatures.json")
nA=$($RAW flip "$CA/call.bin" "$SA" last "$D/a-wrong.bin") || die "signature of A not in its call"
$RAW flip "$CA/call.bin" "$SA" first "$D/a-target.bin" >/dev/null
$RAW flip "$CB/call.bin" "$SB" first "$D/b-target.bin" >/dev/null
python3 - "$CA/call.bin" "$SA" "$D/a-unsigned.bin" <<'PY'
import sys
data = bytearray(open(sys.argv[1], "rb").read()); sig = bytes.fromhex(sys.argv[2])
i = data.rfind(sig); data[i:i + 64] = bytes(64); open(sys.argv[3], "wb").write(bytes(data))
PY
row "the signature sits once per leg in the call (target, authority)" "2 occurrences" "$nA" "$([ "$nA" = 2 ] && echo 1 || echo 0)"

# 1. wrongly signed and unsigned: refused, by name in the operator log; the
#    public reply says only "request refused", the same for every refusal here.
named "$D/a-wrong.bin" wrong; named "$D/a-unsigned.bin" unsigned; named "$D/a-target.bin" target
decode "$D/r-wrong.bin" wrong
row "a wrongly signed copy is refused, named in the operator log (an authentication refusal)" \
  "one entry, Reject.authoritySignature" "$(kind wrong): $(why wrong)" "$([ "$(kind wrong)" = authsig ] && echo 1 || echo 0)"
row "an unsigned copy (zero signature) is refused, named in the operator log" \
  "one entry, Reject.authoritySignature" "$(kind unsigned): $(why unsigned)" "$([ "$(kind unsigned)" = authsig ] && echo 1 || echo 0)"
row "a copy whose TARGET leg signature is wrong (the authority authenticates) is refused at its leg" \
  "one entry, Reject.legSignature (a name distinct from the authority's), not refusalLane" "$(kind target): $(why target)" "$([ "$(kind target)" = legsig ] && echo 1 || echo 0)"
row "the public reply discloses nothing: wrongly signed, unsigned and leg refusals answer the same bytes" \
  "identical replies, refused" "$(detail wrong)" \
  "$(cmp -s "$D/r-wrong.bin" "$D/r-unsigned.bin" && cmp -s "$D/r-wrong.bin" "$D/r-target.bin" && jq -e '.type == "refused"' "$D/wrong.json" >/dev/null 2>&1 && echo 1 || echo 0)"

# 2. 1500 wrongly signed copies, then one authenticated refusal.
m=$(marks)
$RAW repeat "$SOCKET" "$CONFIG" "$HOST" 2 "$D/a-wrong.bin" 1500 "$D/flood-wrong" || die "wrong-signature flood failed"
since "$m" >"$D/flood-wrong/reasons.tsv"
row "1500 wrongly signed copies: 1500 refusals, every one Reject.authoritySignature, none refusalLane" "1500 authsig" \
  "$(cut -f2 "$D/flood-wrong/reasons.tsv" | sort | uniq -c | tr -s ' ' | paste -sd, -)" \
  "$([ "$(grep -c "	authsig	" "$D/flood-wrong/reasons.tsv")" = 1500 ] && [ "$(wc -l <"$D/flood-wrong/reasons.tsv")" = 1500 ] && echo 1 || echo 0)"
named "$D/a-target.bin" after-wrong
AFTER_WRONG_OPEN=$([ "$(kind after-wrong)" = legsig ] && echo 1 || echo 0)

# 3. authenticated refusals, 20 at a time, until the operator log names refusalLane.
m=$(marks); t0=$(date +%s.%N); sent=0; CLOSED=0
mkdir -p "$D/flood-target"; : >"$D/flood-target/replies.tsv"
while [ "$sent" -lt 1500 ]; do
  rm -rf "$D/flood-target/chunk"
  $RAW repeat "$SOCKET" "$CONFIG" "$HOST" 2 "$D/a-target.bin" 20 "$D/flood-target/chunk" || die "authenticated flood failed"
  cat "$D/flood-target/chunk/replies.tsv" >>"$D/flood-target/replies.tsv"
  sent=$((sent + 20))
  since "$m" >"$D/flood-target/reasons.tsv"
  grep -q "	lane	" "$D/flood-target/reasons.tsv" && { CLOSED=1; break; }
done
t1=$(date +%s.%N)
K=$(awk -F '\t' '$2 == "lane" {print NR - 1; exit}' "$D/flood-target/reasons.tsv")
# Fees are max(50 ms, the Host's work) and the Host's work is at most the round trip:
# a lane that closes after K refusals must have Sum max(50, rtt) >= 30 000 ms over them.
upper=$(head -n "${K:-0}" "$D/flood-target/replies.tsv" | awk -F '\t' '{f = ($3 > 50) ? $3 : 50; s += f} END {printf "%d", s}')
row "authenticated refusals at full speed close A's lane: refusalLane in the operator log, and not before 30 s of fee could have accrued" \
  "refusalLane; Sum max(50, rtt) over the refusals before it >= 30000 ms" \
  "$sent sent in $(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.1f", b-a}') s; first refusalLane after ${K:-none} charged (fee bound ${upper:-0} ms); $(cut -f2 "$D/flood-target/reasons.tsv" | sort | uniq -c | tr -s ' ' | paste -sd, -)" \
  "$([ "$CLOSED" = 1 ] && [ "${upper:-0}" -ge 30000 ] && echo 1 || echo 0)"
row "the 1500 wrongly signed copies cost A nothing: the next authenticated refusal read its leg, not refusalLane (75 s of fee had they been charged)" \
  "legsig; meaningful only while the lane closes (row above)" \
  "$(kind after-wrong); lane-closes control $([ "$CLOSED" = 1 ] && echo held || echo DID-NOT-HOLD)" \
  "$([ "$AFTER_WRONG_OPEN" = 1 ] && [ "$CLOSED" = 1 ] && echo 1 || echo 0)"
mw=$(cut -f3 "$D/flood-wrong/replies.tsv" | sort -n | awk '{a[NR]=$1} END{print a[int((NR+1)/2)]}')
mt=$(head -n "${K:-$sent}" "$D/flood-target/replies.tsv" | cut -f3 | sort -n | awk '{a[NR]=$1} END{print a[int((NR+1)/2)]}')
row "a wrongly signed refusal is answered faster than an authenticated one (it stops at authentication, before preparation)" \
  "median wrong < median authenticated" "wrong ${mw} ms, authenticated ${mt} ms" \
  "$(awk -v a="$mw" -v b="$mt" 'BEGIN{print (a < b) ? 1 : 0}')"

# 4. once closed: charged refusals fit the refill (100 ms/s of 50 ms+ fees). The
#    lane was closed (balance <= 0, a debt since D1) at the refusalLane that ended
#    row 3, before t1; the wall clock runs from there, so the refill of the gap
#    between the rows is counted, and the bound is exact: before each charge the
#    balance is positive, so the charges before the last are paid by the refill
#    (<= 0.1 wall) and the last adds one fee.
if [ "$CLOSED" = 1 ]; then
  m=$(marks); t0=$t1
  $RAW repeat "$SOCKET" "$CONFIG" "$HOST" 2 "$D/a-target.bin" 200 "$D/flood-closed" || die "closed flood failed"
  t1=$(date +%s.%N)
  since "$m" >"$D/flood-closed/reasons.tsv"
  wall=$(awk -v a="$t0" -v b="$t1" 'BEGIN{printf "%.0f", (b-a)*1000}')
  charged=$(grep -c "	legsig	" "$D/flood-closed/reasons.tsv")
  maxfee=$(awk -F '\t' '{f = ($3 > 50) ? $3 : 50; if (f > m) m = f} END {printf "%d", m}' "$D/flood-closed/replies.tsv")
  row "a closed lane admits only what the refill pays for: charged x 50 ms <= wall x 0.1 + one fee" \
    "charged <= (0.1 wall + max fee) / 50" "$charged charged, $(grep -c "	lane	" "$D/flood-closed/reasons.tsv") refusalLane of 200 in ${wall} ms" \
    "$(awk -v c="$charged" -v w="$wall" -v f="$maxfee" 'BEGIN{print (c * 50 <= 0.1 * w + f) ? 1 : 0}')"
else
  row "a closed lane admits only what the refill pays for" "lane closed first" "the lane never closed" 0
fi

# 5. B is untouched.
named "$D/b-target.bin" b-target
row "B's lane is untouched while A's is charged: B's authenticated refusal is named at its leg, not refusalLane" \
  "legsig" "$(kind b-target): $(why b-target)" "$([ "$(kind b-target)" = legsig ] && echo 1 || echo 0)"

# 6. A's own valid call: refused right after a charged refusal, admitted after refill.
for i in $(seq 1 100); do   # until a charged (leg) refusal: the lane then owes a fee
  named "$D/a-target.bin" charge
  [ "$(kind charge)" = legsig ] && break
  sleep 0.1
done
named "$CA/call.bin" valid-closed
decode "$D/r-valid-closed.bin" valid-closed
row "A's own unaltered call, right after a charged refusal, is refused refusalLane (and commits nothing)" \
  "refused; operator log refusalLane" "$(detail valid-closed); $(kind valid-closed)" \
  "$([ "$(kind valid-closed)" = lane ] && ! jq -e '.type == "confirmed"' "$D/valid-closed.json" >/dev/null 2>&1 && echo 1 || echo 0)"
sleep 5
named "$CA/call.bin" valid-open
decode "$D/r-valid-open.bin" valid-open
row "after 5 s of refill the same call is installed (not replayed): it was valid all along, and the refused one committed nothing" \
  "confirmed installed" "$(jq -r '"\(.type) \(.confirmation)"' "$D/valid-open.json" 2>/dev/null)" \
  "$(jq -e '.type == "confirmed" and .confirmation == "installed"' "$D/valid-open.json" >/dev/null 2>&1 && echo 1 || echo 0)"

echo "$T"
if [ "$BAD" = 0 ]; then
  echo "JRLANE: $N/$N checks; A=$A closed after ${K:-?} authenticated refusals; 1500 wrongly signed cost nothing; B=$B open" >&2
  exit 0
fi
echo "JRLANE: $BAD of $N checks failed (see $T)" >&2
exit 1
