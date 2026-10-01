#!/usr/bin/env bash
# JMKT (SEALED-MARKET; PRIVACY §3.4, MUD §2.7/§2.8): a sealed-bid market through `mini shell`, on
# this journey's live Store. Supersedes KHQ (journey.d/jhasheq.sh, the single-value K-HASHEQ probe).
#
# alice opens market `fish` (supply 8) with a close height and a reveal end; bob bids twice and carol
# once, each a commitment to (price, qty) under a fresh blinder kept in the bidder's own workspace.
# Before the close neither the Store nor alice's signed read holds a sealed price; a public order's
# price, written in the clear, is found by the same scan (the pole). bob reveals (admitted); carol
# reveals a wrong opening (refused, naming the `opens` clause) and never reveals; bob's opening,
# replayed into the twin market `crab` over a copied commitment, is refused; a re-reveal, a late bid,
# an early reveal, an early settlement, a stranger's settlement and a forged fill on carol's
# unrevealed slot are refused by name. After the reveal end alice's runner settles on the revealed
# bids only: carol's unrevealed slot (the highest price) is skipped.
#
# Every friend line runs in that friend's own `mini shell --line` session (J12's mechanism). Refusal
# rows assert exit 3 and `refused: law-denied: …` with the clause the Host rendered.
#
# Hook contract: journey.sh (executed, not sourced). Last stdout line: the row table. Last stderr
# line: the detail. Exit 0 only when every row is as expected.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${SHELL_BIN:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}" "${JOURNEY_WORLD:?}"
SD=$JOURNEY_STEP_DIR
H=$SD/h; WS=$SD/w; L=$SD/log
mkdir -p -m 700 "$H" "$WS" "$L" "$SD/req"
TABLE=$SD/jmarket.tsv
printf 'n\tstep\twho\tline\texpect\tgot\tverdict\tnote\n' >"$TABLE"
N=0; ROWS=0; FAILED=0; FIRST_FAIL=""
G=$(jq -r .genesisHeight "$CONFIG")

ws_of() { if [ "$1" = sponsor ]; then echo "$SPONSOR_WS"; else echo "$WS/$1"; fi; }

say() { # WHO LINE: one line in WHO's own shell session; sets RC, OUT, ERR.
  local who=$1 line=$2 stem
  N=$((N + 1)); stem=$(printf '%03d-%s' "$N" "$who")
  printf '%s\n' "$line" >"$L/$stem.line"
  "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$(ws_of "$who")" --home "$H/$who" --line "$line" >"$L/$stem.out" 2>"$L/$stem.err"
  RC=$?; OUT=$L/$stem.out; ERR=$L/$stem.err
  printf '%s> %s\n' "$who" "$line" >>"$SD/transcript.txt"
  sed 's/^/    /' "$OUT" "$ERR" >>"$SD/transcript.txt"
}
record() { # STEP WHO LINE EXPECT GOT VERDICT NOTE
  ROWS=$((ROWS + 1))
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$1" "$2" "$3" "$4" "$5" "$6" "$7" >>"$TABLE"
  if [ "$6" != ok ]; then FAILED=$((FAILED + 1)); [ -n "$FIRST_FAIL" ] || FIRST_FAIL="row $N ($1 $2: $3): $7"; fi
}
first_line() { grep -m1 -E '^(refused|undecided|error|usage): ' "$ERR"; }
ok() { # STEP WHO LINE
  say "$2" "$3"
  if [ "$RC" = 0 ]; then record "$1" "$2" "$3" admitted admitted ok "$(tail -1 "$ERR" | cut -c1-200)"
  else record "$1" "$2" "$3" admitted "rc $RC" FAIL "$(first_line)"; fi
}
refused() { # STEP WHO LINE TEXT: exit 3, `refused: law-denied: …TEXT…`
  local first; say "$2" "$3"; first=$(first_line)
  if [ "$RC" = 3 ] && case "$first" in "refused: law-denied: "*"$4"*) true ;; *) false ;; esac; then
    record "$1" "$2" "$3" "law-denied …$4…" law-denied ok "$first"
  else record "$1" "$2" "$3" "law-denied …$4…" "rc $RC" FAIL "$first"; fi
}
fails() { # STEP WHO LINE RC TEXT: a client-side ending with TEXT, nothing sent
  local first; say "$2" "$3"; first=$(first_line)
  case "$RC:$first" in
    "$4:"*"$5"*) record "$1" "$2" "$3" "rc $4 …$5…" "rc $RC" ok "$first" ;;
    *) record "$1" "$2" "$3" "rc $4 …$5…" "rc $RC" FAIL "$first" ;;
  esac
}
check() { # STEP WHAT EXPECT COMMAND…: a condition on artifacts
  local step=$1 what=$2 expect=$3; shift 3
  N=$((N + 1))
  if "$@" >"$L/$(printf '%03d' "$N")-check.out" 2>&1; then record "$step" check "$what" "$expect" "$expect" ok "$(tail -1 "$L/$(printf '%03d' "$N")-check.out" | cut -c1-200)"
  else record "$step" check "$what" "$expect" "not $expect" FAIL "$(tail -1 "$L/$(printf '%03d' "$N")-check.out" | cut -c1-200)"; fi
}
operator() { # STEP WHAT COMMAND…
  local step=$1 what=$2 o; shift 2
  N=$((N + 1)); o=$L/$(printf '%03d' "$N")-operator
  if "$@" >"$o.out" 2>"$o.err"; then record "$step" OPERATOR "$what" ok ok ok ""
  else record "$step" OPERATOR "$what" ok "rc $?" FAIL "$(tail -1 "$o.err")"; fi
}
finish() {
  echo "$TABLE"
  if [ "$FAILED" = 0 ]; then echo "JMKT: $ROWS of $ROWS rows as expected ($TABLE)" >&2; exit 0; fi
  echo "JMKT: $FAILED of $ROWS rows not as expected; first: $FIRST_FAIL" >&2; exit 1
}

# read_height MARKET: HEIGHT := the next request height, as alice's signed read of MARKET reports it
# (`# market M at height H:`). A function, not a command substitution: `say` numbers the rows.
read_height() { say alice "bids $1"; HEIGHT=$(sed -n 's/^# market [^ ]* at height \([0-9]*\):.*/\1/p' "$OUT"); }
# The next request height from the largest accepted count any retained outcome reports.
next_height() {
  local n
  n=$(find "$WS" "$SPONSOR_WS/attempts" -name outcome.json -print0 2>/dev/null \
    | xargs -0 -r jq -r '.acceptedCount // empty' 2>/dev/null | sort -n | tail -1)
  echo $((G + ${n:-0}))
}
TICK=0
tick_until() { # MARKET HEIGHT: alice appends to `tick` until the next request height is HEIGHT
  local h
  while :; do
    read_height "$1"; h=$HEIGHT
    [ -n "$h" ] || { record tick alice "bids $1" height none FAIL "no height in $OUT"; finish; }
    [ "$h" -lt "$2" ] || break
    TICK=$((TICK + 1))
    say alice "doc append t$TICK tick 'tick $TICK'"; [ "$RC" = 0 ] || { record tick alice "doc append" admitted "rc $RC" FAIL "$(first_line)"; finish; }
    say alice "submit t$TICK"; [ "$RC" = 0 ] || { record tick alice "submit t$TICK" admitted "rc $RC" FAIL "$(first_line)"; finish; }
  done
  [ "$h" = "$2" ] || { record tick alice "bids $1" "height $2" "height $h" FAIL "overshot"; finish; }
}
scan() { # LABEL VALUE...: byte-pattern hits for each value over the Store and operator files
  scan_in "$JOURNEY_WORLD/store:$JOURNEY_WORLD/deployment:$JOURNEY_WORLD/operator.json:$JOURNEY_WORLD/genesis.json" "$@"
}
scan_in() { # PATHS(:-separated) LABEL VALUE...
  python3 - "$@" <<'PY'
import os, sys
roots, label, values = sys.argv[1].split(":"), sys.argv[2], [int(v) for v in sys.argv[3:]]
files = []
for p in roots:
    if os.path.isfile(p): files.append(p)
    for d, _, fs in os.walk(p): files += [os.path.join(d, f) for f in fs]
blob = [open(f, "rb").read() for f in files]
def b255(n):
    out = []
    while n: out.append(n % 255); n //= 255
    return bytes(out) + b"\xff"
out = []
for v in values:
    z = 2 * v if v >= 0 else -2 * v - 1
    be = v.to_bytes((v.bit_length() + 7) // 8 or 1, "big")
    pats = {"ascii": str(v).encode(), "b255": b255(z), "be": be, "hex": be.hex().encode()}
    out.append(f"{v}:" + ",".join(f"{k}={sum(b.count(p) for b in blob)}" for k, p in pats.items()))
print(f"{label} files={len(files)} bytes={sum(map(len, blob))} " + " ".join(out))
PY
}
hits() { echo "$1" | tr ' ' '\n' | grep "^$2:" | tr ',' '\n' | grep -o '=[0-9]*' | tr -d = | awk '{s+=$1} END {print s+0}'; }
zero_hits() { local s; s=$(scan "$@"); echo "$s"; for v in "${@:2}"; do [ "$(hits "$s" "$v")" = 0 ] || return 1; done; }
zero_hits_in() { local s; s=$(scan_in "$@"); echo "$s"; for v in "${@:3}"; do [ "$(hits "$s" "$v")" = 0 ] || return 1; done; }
some_hits() { local s; s=$(scan "$@"); echo "$s"; for v in "${@:2}"; do [ "$(hits "$s" "$v")" != 0 ] || return 1; done; }
grep_none() { ! grep -rqaE "$1" "${@:2}"; }
opening() { jq -r ".$2" "$WS/$1/market/$3/$4.json"; } # WHO FIELD MARKET PROPOSAL
write_req() { # FILE MARKET [FIELD VALUE EXPECTED]...: a hand-written scalar write (a friend editing a request)
  local file=$1 market=$2; shift 2
  local actions="[]"
  mkdir -p -m 700 "$(dirname "$file")"
  while [ $# -ge 3 ]; do
    actions=$(jq -c --arg f "$1" --arg v "$2" --arg e "$3" '. + [{type:"write",key:{type:"object",field:$f},value:$v,expected:$e}]' <<<"$actions")
    shift 3
  done
  jq -n --arg m "$market" --argjson a "$actions" '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:$m,payload:{type:"scalar",actions:$a}}]}' >"$file"
}
: >"$SD/transcript.txt"

# ------------------------------------------------ friends: enroll, provision, init (J12's way)
mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"
declare -A SUBJ
for f in alice bob carol; do
  mkdir -p -m 700 "$H/$f"
  ok setup "$f" "keygen mini.key"
  operator setup "CUSTODY: copy $f's secret into the sponsor home (enroll plan+seal sign with both keys)" \
    install -D -m 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/$f.key"
  ok setup sponsor "enroll plan $f $f.key"
  ok setup sponsor "enroll seal $f"
  ok setup sponsor "enroll submit $f"
  SUBJ[$f]=$(jq -r '.subject // empty' "$OUT")
  operator setup "CUSTODY: remove the copy" rm -f "$H/sponsor/keys/$f.key"
  operator setup "PROVISION: a funded account owned by $f" \
    "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "$f" --holder "${SUBJ[$f]}" \
      --funding 1000 --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator setup "DELIVER: the birth context into $f's HOME/provision/" \
    install -D -m 0600 "$SPONSOR_WS/provisions/$f/birth-context.json" "$H/$f/provision/birth-context.json"
  ok setup "$f" "init mini.key ${SUBJ[$f]}"
done
A=${SUBJ[alice]} B=${SUBJ[bob]} C=${SUBJ[carol]}
[ -n "$A" ] && [ -n "$B" ] && [ -n "$C" ] || { record setup - subjects three none FAIL "an enrollment returned no subject"; finish; }

# Prices are distinctive so the byte scan can see them; quantities are small.
PB0=271828182845; QB0=5     # bob, slot 0
PC=314159265358;  QC=4      # carol, slot 1: the highest price, never revealed
PB2=161803398874; QB2=6     # bob, slot 2
PUB=141421356237            # a public order's price, written in the clear (the scan's pole)
SUPPLY=8

ok setup alice "doc new tick"
H0=$(next_height)
CLOSE=$((H0 + 30)); REVEAL_END=$((CLOSE + 14))
echo "$H0 $CLOSE $REVEAL_END" >"$SD/heights"

# ------------------------------------------------ open: the market, its twin, the deposit refusal
N=$((N + 1))
if "$MINI" workspace --action market-open --dir "$WS/alice" --name dep --close "$CLOSE" --reveal-end "$REVEAL_END" \
    --supply 1 --deposit 10 >"$L/$N-dep.out" 2>"$L/$N-dep.err"; then
  record open alice-client "market-open dep … --deposit 10" "rc 1 depositUnavailable" "rc 0" FAIL "a deposit market opened"
else
  rc=$?; d=$(tail -1 "$L/$N-dep.err")
  case "$rc:$d" in 1:*depositUnavailable*) record open alice-client "market-open dep … --deposit 10" "rc 1 depositUnavailable" "rc 1" ok "$d" ;;
    *) record open alice-client "market-open dep … --deposit 10" "rc 1 depositUnavailable" "rc $rc" FAIL "$d" ;; esac
fi
ok open alice "market open fish $CLOSE $REVEAL_END $SUPPLY"
ok open alice "market open crab $CLOSE $REVEAL_END $SUPPLY"
ok open alice "law show fish"
cp "$OUT" "$SD/fish-law.txt"
check open "law show prints the Host's rendering, which names each slot's opening" rendered \
  grep -q 'field 17 opens (field 18, field 19) with field 20' "$SD/fish-law.txt"
operator open "copy the shown law into alice's requests" install -D -m 0600 "$SD/fish-law.txt" "$H/alice/requests/fish-law.txt"
ok open alice "law relaw fish @fish-law.txt"
ok open alice "describe fish"
cp "$OUT" "$SD/fish-describe.json"
check open "round trip: the shown text parses back to exactly the installed law" equal \
  bash -c 'diff <(jq -S .predicate "$1") <(jq -S .predicate "$2")' _ "$SD/fish-describe.json" "$H/alice/requests/relaw.json"
say alice "submit relaw"
if [ "$RC" = 3 ]; then record open alice "submit relaw" refused refused ok "$(first_line) (nobody installs: the law cannot be swapped)"
else record open alice "submit relaw" refused "rc $RC" FAIL "$(first_line)"; fi
for f in bob carol; do
  for m in fish crab; do
    [ "$f:$m" = "bob:crab" ] && continue
    ok grant alice "delegate g-$f-$m $m ${SUBJ[$f]} observe,mutate 50000"
    ok grant alice "submit g-$f-$m"
    ok grant alice "publish g-$f-$m"
    ok grant alice "export g-$f-$m"
    ok grant "$f" "import $m $(cat "$OUT")"
  done
done

# ------------------------------------------------ sealed: bids, a public order, the scans
ok sealed bob "bid fish $PB0 $QB0"
ok sealed bob "submit bid-fish"
ok sealed carol "bid fish $PC $QC"
ok sealed carol "submit bid-fish"
ok sealed bob "bid fish $PB2 $QB2 bid2-fish"
ok sealed bob "submit bid2-fish"
COMMIT_B0=$(opening bob commit fish bid-fish)
# carol copies bob's (public) commitment into crab's slot 0 while crab is sealed
write_req "$H/carol/requests/copy.req.json" crab 16 "$C" 0 17 "$COMMIT_B0" 0
ok sealed carol "propose copy @copy.req.json"
ok sealed carol "submit copy"
# the public order: bob writes a price in the clear in an ordinary cell
ok sealed bob "create pub declared {\"type\":\"all\",\"predicates\":[]}"
ok sealed bob "invoke po pub create 3 $PUB"
ok sealed bob "submit po"
ok sealed alice "bids fish"
cp "$OUT" "$SD/bids-sealed.txt"
check sealed "alice's signed read: three bids, every price and quantity sealed" three-sealed \
  sh -c '[ "$(grep -c "	sealed	sealed	" "$1")" = 3 ]' _ "$SD/bids-sealed.txt"
check sealed "no sealed price in alice's printed bids" absent grep_none "$PB0|$PC|$PB2" "$SD/bids-sealed.txt"
check sealed "no sealed price, in any encoding, in alice's retained signed reads" 0-hits \
  zero_hits_in "$WS/alice/attempts" alice-reads "$PB0" "$PC" "$PB2"
check sealed "Store before the close: no sealed price in any encoding" 0-hits zero_hits before "$PB0" "$PC" "$PB2"
check sealed "the scan sees a stored field: bob's commitment" found some_hits commit "$COMMIT_B0"
check sealed "the pole: a public order's price IS on the Store" found some_hits public "$PUB"
check sealed "bob's own opening is in his workspace, not the Store" kept test "$(opening bob price fish bid-fish)" = "$PB0"
# reveals before the close are refused
ok sealed bob "reveal fish r0"
refused sealed bob "submit r0" 'all [ not (slot "request/height" <= '"$((CLOSE - 1))"'), slot "request/height" <= '"$((REVEAL_END - 1))"' ]'

# ------------------------------------------------ the close
tick_until fish "$CLOSE"
read_height fish
check close "the next request height is the close" "h=$CLOSE" test "$HEIGHT" = "$CLOSE"
ok close alice "bid fish 99 1 late"
refused close alice "submit late" "field 40 before == 0, field 40 == subject"

# ------------------------------------------------ reveal
ok reveal bob "reveal fish r1"
ok reveal bob "submit r1"
read_height fish; H2=$HEIGHT
# carol reveals a wrong opening: her kept opening with the price raised by one
CP=$(opening carol price fish bid-fish); CQ=$(opening carol qty fish bid-fish); CR=$(opening carol blinder fish bid-fish)
write_req "$H/carol/requests/wrong.req.json" fish 26 $((CP + 1)) 0 27 "$CQ" 0 28 "$CR" 0
ok reveal carol "propose wrong @wrong.req.json"
refused reveal carol "submit wrong" "field 25 opens (field 26, field 27) with field 28"
# a partial reveal: the price and blinder, not the quantity
write_req "$H/carol/requests/partial.req.json" fish 26 "$CP" 0 28 "$CR" 0
ok reveal carol "propose partial @partial.req.json"
refused reveal carol "submit partial" "field 25 opens (field 26, field 27) with field 28"
# bob's opening, now public, replayed into crab over the copied commitment: same commit, other cell
write_req "$H/carol/requests/replay.req.json" crab 18 "$PB0" 0 19 "$QB0" 0 20 "$(opening bob blinder fish bid-fish)" 0
ok reveal carol "propose replay @replay.req.json"
refused reveal carol "submit replay" "field 17 opens (field 18, field 19) with field 20"
# bob re-opens slot 0 to another price
write_req "$H/bob/requests/again.req.json" fish 18 $((PB0 - 1)) "$PB0"
ok reveal bob "propose again @again.req.json"
refused reveal bob "submit again" "field 17 opens (field 18, field 19) with field 20"
read_height fish
check reveal "no refused attempt moved the height (4 refusals since bob's reveal)" "h=$H2" test "$HEIGHT" = "$H2"
ok reveal alice "bids fish"
cp "$OUT" "$SD/bids-revealed.txt"
check reveal "alice's read now carries bob's revealed tuples; carol's slot is still sealed" bob-open,carol-sealed \
  sh -c 'grep -q "^0	$2	.*	$3	$4	0$" "$1" && grep -q "^2	$2	.*	$5	$6	0$" "$1" && grep -q "^1	$7	.*	sealed	sealed	" "$1"' _ \
    "$SD/bids-revealed.txt" "$B" "$PB0" "$QB0" "$PB2" "$QB2" "$C"
S1=$(scan after "$PB0" "$PB2" "$PC"); echo "$S1" >"$SD/scan-after.txt"
N=$((N + 1))
if [ "$(hits "$S1" "$PB0")" != 0 ] && [ "$(hits "$S1" "$PB2")" != 0 ] && [ "$(hits "$S1" "$PC")" = 0 ]; then
  record reveal check "Store after the reveals: bob's prices found, carol's absent" bob-found,carol-0 bob-found,carol-0 ok "$S1"
else record reveal check "Store after the reveals: bob's prices found, carol's absent" bob-found,carol-0 other FAIL "$S1"; fi

# ------------------------------------------------ settle
fails settle alice "market settle fish early" 1 "still admits reveals"
write_req "$H/alice/requests/s-early.req.json" fish 1 1 0 5 1 0
ok settle alice "propose s-early @s-early.req.json"
refused settle alice "submit s-early" "field 1 before == 0, field 1 == 1"
tick_until fish "$REVEAL_END"
ok settle carol "reveal fish late"
refused settle carol "submit late" 'all [ not (slot "request/height" <= '"$((CLOSE - 1))"'), slot "request/height" <= '"$((REVEAL_END - 1))"' ]'
write_req "$H/bob/requests/s-bob.req.json" fish 1 1 0 5 1 0
ok settle bob "propose s-bob @s-bob.req.json"
refused settle bob "submit s-bob" "subject == $A"
# a forged fill on carol's unrevealed slot (quantity 0)
write_req "$H/alice/requests/s-forge.req.json" fish 1 1 0 5 "$PC" 0 29 3 0
ok settle alice "propose s-forge @s-forge.req.json"
refused settle alice "submit s-forge" "field 29 <= field 27"
ok settle alice "market settle fish"
cp "$ERR" "$SD/settle.txt"
check settle "the runner skipped carol's unrevealed slot and forfeits nothing it holds (depositUnavailable)" skipped \
  grep -q "slot 1 ($C) never revealed: skipped; deposit forfeit: depositUnavailable" "$SD/settle.txt"
ok settle alice "submit settle-fish"
ok settle alice "bids fish"
cp "$OUT" "$SD/bids-settled.txt"
check settle "settled: slot 0 fills 5, slot 2 fills 3, slot 1 nothing; clearing price is bob's second price" "5,3,0 @ $PB2" \
  sh -c 'grep -q "phase settled" "$1" && grep -q "clearing price $2" "$1" && grep -q "^0	.*	5$" "$1" && grep -q "^2	.*	3$" "$1" && grep -q "^1	.*	sealed	sealed	0$" "$1"' _ \
    "$SD/bids-settled.txt" "$PB2"
fails settle alice "market settle fish twice" 1 "already settled"
write_req "$H/alice/requests/s-again.req.json" fish 5 1 "$PB2"
ok settle alice "propose s-again @s-again.req.json"
refused settle alice "submit s-again" "field 1 before == 0, field 1 == 1"

finish
