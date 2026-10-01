#!/usr/bin/env bash
# journey.d/jchan-client.sh — `mini channel join / say / tail`: two friends talk through the relay in sealed
# cells, a third member and the relay cannot read them, and the wire is the same whatever they say
# (CH-CLIENT-1 and CH-J-TRACE, CHANNELS.md §9 rows 10 and 11).
#
# The sponsor A is the relay and sequencer, as in KCHR: room `chcroom`, one channel stream per run born --in
# chcroom under "every write is by the sponsor". Domain 7, class P1 (C 256, 1 Hz, E 16), n = 3: slot 0 =
# alice (unix socket), slot 1 = bob (TCP loopback, class P1phone: δ = 600 ms), slot 2 = carol (unix socket).
#
#   t1  CHC_TICKS ticks (default 180 = 3 min): alice says three messages to bob (the second > one cell),
#       carol says one to alice
#   t2  the same length, different traffic: bob and carol talk, alice writes carol a long message
#   t3  the same length, nobody says anything
#   p   t3's traffic (none) with carol KILLED (-9) after tick CHC_KILL_AT (default 90): the presence pole
#   f   CHC_FAULT_TICKS ticks (default 48): alice says a 3-cell message to bob; the relay drops alice's
#       cell once (--fault-drop 0:CHC_DROP_AT, default 14; the message is 5 cells from tick 11 or 12, so the
#       drop always hits one of its fragments)
#
# Rows (expect; every refusal names its reason):
#   t1-delivered         bob's tail: alice's three messages, byte-exact, in order (#0 #1 #2)
#   t1-multi-cell        the long message rode 3 cells (sent.jsonl fragments)
#   t1-carol-reply       alice's tail: carol's message
#   t1-nonrecipient      carol opened 0 cells and her tail is empty; every view-tag hit was refused by the AEAD
#   relay-cannot-read    no message text, raw or hex, anywhere under the world, the relay's dirs or a member's
#                        wire log (the senders' own outbox/sent and the recipients' inbox excepted)
#   sizes-<run>          every (tick, slot) on the relay's byte log: 887 B down and 256 B up for all three
#                        members, whether or not they spoke; every member log: 887 B in, 256 B out
#   trace-t1-t2, trace-t1-t3   diff of the relay's (k, slot, route, down, up) log and of every member's
#                        (k, rx, tx) log between runs with different traffic: 0 lines
#   presence-members     p against t3: alice's and bob's (k, rx, tx) logs identical (0 diff lines)
#   presence-relay       p against t3: the relay's log first differs when carol goes silent, on her slot only
#                        (her route turns mailbox, her uplink 0 B); the witness's opening marks her absent
#   fault-detected       alice's own-slot check names the dropped tick and re-queues its bytes
#   fault-record         alice's record check for that epoch names the same tick
#   fault-delivered      bob still receives the message byte-exact, once
#   records-<run>        every member checked every complete epoch's record: roots equal the frames'
#   appends-<run>        the kernel admitted floor(ticks / 16) records
#   seal-inside-mu       every member's seal, taken at the cutoff emission - μ, finished inside μ on every tick
#   cold-audit           service stopped: `audit` re-admits every record; service restarted
# Artifacts: transcript.txt (who said what, and each tail), latency.csv (say -> tail), startup.txt.
# Tunables: CHC_TICKS CHC_KILL_AT CHC_FAULT_TICKS CHC_DROP_AT CHC_LEAN_LIB CHC_SOCK_ROOT (short: 108-byte paths).
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
AW=$SPONSOR_WS
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
LIB=${CHC_LEAN_LIB:-$ROOT/.lake/build/lib/libminidregg-channel.so}
TICKS=${CHC_TICKS:-180}
KILL_AT=${CHC_KILL_AT:-90}
FAULT_TICKS=${CHC_FAULT_TICKS:-48}
DROP_AT=${CHC_DROP_AT:-14}
SOCKROOT=${CHC_SOCK_ROOT:-/home/ember/build/chc}
mkdir -p "$D/req" "$SOCKROOT"
SK=$(mktemp -d "$SOCKROOT/s.XXXX")
rows=$D/client-rows.tsv
: >"$rows"
bad=0
PIDS=()
cleanup() { local p; for p in "${PIDS[@]}"; do kill -TERM "$p" 2>/dev/null; done; rm -rf "$SK"; }
trap cleanup EXIT
[ -f "$LIB" ] || { echo "no channel library at $LIB (native/resource-client/channel-lib/build.sh)" >&2; exit 1; }

run() { local name=$1; shift; "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"; }
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -1 "$D/$1.err")" >&2; exit 1; }; }
check() { # NAME EXPECT GOT [DETAIL]
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "${4:-}" >>"$rows"
  [ "$2" = "$3" ] || bad=$((bad + 1))
}
load() { cut -d' ' -f1-3 /proc/loadavg; }

A=$SPONSOR_SUBJECT
jq -n --arg s "$A" '{type:"any",predicates:[
  {type:"not",predicate:{type:"memberOf",slot:"request/verb",values:["2","7"]}},
  {type:"eq",slot:"request/subject",value:$s}]}' >"$D/req/law-seq.json"
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
run create-room "$MINI" workspace --action create --dir "$AW" --name chcroom --storage declared \
  --predicate "$D/req/permit-all.json"; ok create-room
for s in chc-t1 chc-t2 chc-t3 chc-p chc-f; do
  run "create-$s" "$MINI" workspace --action create --dir "$AW" --name "$s" --storage stream \
    --predicate "$D/req/law-seq.json" --in chcroom; ok "create-$s"
done

# keys: an ed25519 seed per slot (the relay's lease file), an X25519 key per member (the roster)
NAMES=(alice bob carol)
: >"$D/leases.txt"; : >"$D/roster"
for slot in 0 1 2; do
  name=${NAMES[$slot]}
  pk=$("$MINI" relay-key --key "$D/member$slot.key") || { echo "relay-key failed" >&2; exit 1; }
  echo "$slot $((10 + slot)) $pk 0 1000" >>"$D/leases.txt"
  xk=$("$MINI" channel key friends --home "$D/keys/$name") || { echo "channel key failed" >&2; exit 1; }
  echo "$name $slot $xk" >>"$D/roster"
done

# a member's last logged k (its wire log), or -1
lastk() { local f=$1/friends/wire.csv; [ -f "$f" ] && tail -1 "$f" | cut -d, -f1 | grep -E '^[0-9]+$' || echo -1; }
wait_k() { # HOME K: until that member has logged tick K (bounded)
  local i
  for i in $(seq 1 $(( ($2 + 120) * 10 ))); do [ "$(lastk "$1")" -ge "$2" ] 2>/dev/null && return 0; sleep 0.1; done
  return 1
}

# one run: NAME STREAM TICKS KILL_AT TRAFFIC-FILE [extra relay flags...]
# TRAFFIC-FILE lines: K FROM TO TEXT  (FROM says TEXT to @TO once FROM has logged tick K)
chan_run() {
  local name=$1 stream=$2 ticks=$3 kill_at=$4 traffic=$5; shift 5
  local R=$D/$name sock=$SK/${name}r.sock wsock=$SK/${name}w.sock wpid rpid slot conn k from to text
  local -a mpids=()
  mkdir -p "$R"
  for n in "${NAMES[@]}"; do cp -a "$D/keys/$n" "$R/home-$n"; done
  echo "$(date +%s) $(load)" >"$R/load-start"
  "$MINI" relay-witness --lean-lib "$LIB" --unix "$wsock" --out "$R/witness.csv" >"$R/witness.out" 2>"$R/witness.err" &
  wpid=$!; PIDS+=("$wpid")
  for i in $(seq 1 200); do [ -S "$wsock" ] && break; sleep 0.1; done
  "$MINI" relay --lean-lib "$LIB" --class 1 --domain 7 --n 3 --leases "$D/leases.txt" --ticks "$ticks" \
    --unix "$sock" --tcp 127.0.0.1:0 --witness "$wsock" --state-dir "$D/relay-state" --out-dir "$R/relay" \
    --append-ws "$AW" --stream "$stream" --records-dir "$R/records" --wait-members-ms 120000 --start-delay-ms 2000 \
    "$@" >"$R/relay.out" 2>"$R/relay.err" &
  rpid=$!; PIDS+=("$rpid")
  for i in $(seq 1 300); do [ -S "$sock" ] && break; sleep 0.1; done
  for i in $(seq 1 1800); do [ -s "$R/relay/tcp-addr" ] && break; sleep 0.1; done
  for slot in 0 1 2; do
    n=${NAMES[$slot]}
    if [ "$slot" = 1 ]; then conn="tcp:$(cat "$R/relay/tcp-addr")"; cls=P1phone; else conn="unix:$sock"; cls=P1; fi
    "$MINI" channel join friends --home "$R/home-$n" --lean-lib "$LIB" --connect "$conn" --domain 7 \
      --leases "$D/leases.txt" --key "$D/member$slot.key" --roster "$D/roster" --class "$cls" \
      --records-dir "$R/records" >"$R/join-$n.out" 2>"$R/join-$n.err" &
    mpids+=($!); PIDS+=($!)
  done
  echo "${mpids[*]}" >"$R/member-pids"
  # traffic, in K order
  while read -r k from to text; do
    [ -n "$k" ] || continue
    wait_k "$R/home-$from" "$k" || echo "traffic: $from never reached tick $k" >>"$R/traffic.err"
    "$MINI" channel say friends "@$to" "$text" --home "$R/home-$from" >>"$R/say-$from.out" 2>>"$R/say-$from.err"
    printf '%s\t%s\t%s\t%s\n' "$(lastk "$R/home-$from")" "$from" "$to" "$text" >>"$R/said.tsv"
  done <"$traffic"
  if [ "$kill_at" -gt 0 ]; then
    wait_k "$R/home-carol" "$kill_at"
    kill -9 "${mpids[2]}"; echo "$(date +%s) killed carol pid ${mpids[2]} after tick $(lastk "$R/home-carol")" >"$R/killed"
  fi
  wait "$rpid"; echo $? >"$R/relay.rc"
  for p in "${mpids[@]}"; do
    for i in $(seq 1 100); do kill -0 "$p" 2>/dev/null || break; sleep 0.1; done
    kill -TERM "$p" 2>/dev/null; wait "$p" 2>/dev/null
  done
  for i in $(seq 1 50); do kill -0 "$wpid" 2>/dev/null || break; sleep 0.1; done
  kill -TERM "$wpid" 2>/dev/null; wait "$wpid" 2>/dev/null
  echo "$(date +%s) $(load)" >"$R/load-end"
  for n in "${NAMES[@]}"; do
    "$MINI" channel tail friends --home "$R/home-$n" >"$R/tail-$n.txt" 2>"$R/tail-$n.err"
    "$MINI" channel status friends --home "$R/home-$n" >"$R/status-$n.json" 2>/dev/null
  done
}

LONG="Bob - this one is long on purpose, so it cannot fit one cell: a P1 cell carries 195 payload bytes in X25519 mode, and this message is about four hundred bytes, so it rides three consecutive cells of my slot, each sealed to you with its own ephemeral key, each with the same view-tag rule, and you put it back together from the fragment headers. Nobody else in the room can tell that I said anything at all. -alice"
cat >"$D/traffic-t1" <<EOF
8 alice bob hi bob, it's alice. message one.
16 alice bob $LONG
40 alice bob message three: see you at the relay.
48 carol alice hello alice, carol here.
EOF
LONG2=$(printf 'carol, the plan for saturday, in full: %.0s' 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18)
cat >"$D/traffic-t2" <<EOF
5 bob carol carol? are you there
9 carol bob yes. what is it
14 alice carol $LONG2
30 bob carol nothing, never mind
33 bob carol one more
70 carol bob ok
EOF
: >"$D/traffic-none"
FTEXT=$(printf 'bob, five cells of it this time, so the relay has something of mine to drop: %.0s' 1 2 3 4 5 6 7 8 9 10 11)
cat >"$D/traffic-f" <<EOF
10 alice bob $FTEXT
EOF

chan_run t1 chc-t1 "$TICKS" 0 "$D/traffic-t1"
chan_run t2 chc-t2 "$TICKS" 0 "$D/traffic-t2"
chan_run t3 chc-t3 "$TICKS" 0 "$D/traffic-none"
chan_run p chc-p "$TICKS" "$KILL_AT" "$D/traffic-none"
chan_run f chc-f "$FAULT_TICKS" 0 "$D/traffic-f" --fault-drop "0:$DROP_AT"

inbox_texts() { jq -r '[.from, (.seq|tostring), .text] | join("\t")' "$1/friends/inbox.jsonl" 2>/dev/null; }

# --- t1: delivery, multi-cell, the reply, the non-recipient
want=$(awk -F'\t' '$2 == "alice" && $3 == "bob" {printf "%salice\t%d\t%s", (n ? "\n" : ""), n, $4; n++}' "$D/t1/said.tsv")
got=$(inbox_texts "$D/t1/home-bob")
check t1-delivered "3 in order" "$([ "$got" = "$want" ] && echo "3 in order" || echo "differ: $(echo "$got" | wc -l) entries")" "$(cut -c1-160 "$D/t1/tail-bob.txt" | tr '\n' '|')"
frags=$(jq -r --argjson n ${#LONG} 'select(.bytes == $n) | .fragments' "$D/t1/home-alice/friends/sent.jsonl" 2>/dev/null)
check t1-multi-cell "3" "$frags" "the ${#LONG}-byte message: sent.jsonl $(jq -c --argjson n ${#LONG} 'select(.bytes == $n)' "$D/t1/home-alice/friends/sent.jsonl" 2>/dev/null)"
check t1-carol-reply "carol 0 hello alice, carol here." "$(inbox_texts "$D/t1/home-alice" | tr '\t' ' ')" "$(cat "$D/t1/tail-alice.txt")"
cst=$D/t1/status-carol.json
copen=$(jq -r '.trialDecrypt.opened' "$cst"); chit=$(jq -r '.trialDecrypt.viewTagHits' "$cst"); cfail=$(jq -r '.trialDecrypt.aeadFail' "$cst")
check t1-nonrecipient "opened=0 tail=0 lines" "opened=$copen tail=$(wc -l <"$D/t1/tail-carol.txt") lines" \
  "carol trial-decrypted $(jq -r '.trialDecrypt.cells' "$cst") cells; $chit view-tag hits, $cfail refused by the AEAD; alice's cells to bob were among them"
check t1-nonrecipient-aead "$chit" "$cfail" "every view-tag hit at carol (a 1/256 coincidence) was refused by ChaCha20-Poly1305"

# --- the relay (and the operator's disk) cannot read: no message text anywhere outside the endpoints' own files
python3 - "$W" "$D" <<'EOF' >"$D/plaintext-grep.txt"
import sys, os, glob
world, d = sys.argv[1], sys.argv[2]
texts = set()
for f in glob.glob(f"{d}/*/said.tsv"):
    for line in open(f):
        texts.add(line.rstrip("\n").split("\t", 3)[3])
# a short text ("ok") is no evidence either way: it occurs in ordinary files. Search the distinctive ones.
long = [t for t in texts if len(t) >= 16]
needles = [t.encode() for t in long] + [t.encode().hex().encode() for t in long]
needles += [t[:40].encode() for t in long]  # a prefix: a fragment would carry one
allowed = ("outbox", "/inbox.jsonl", "/sent.jsonl", "said.tsv", "traffic-", "/tail-", "say-", "transcript", "plaintext-grep", "client-rows")
hits, files = [], 0
for root in (world, d):
    for r, _, fs in os.walk(root):
        for f in fs:
            p = os.path.join(r, f)
            if any(a in p for a in allowed):
                continue
            try: b = open(p, "rb").read()
            except Exception: continue
            files += 1
            for n in needles:
                if n in b:
                    hits.append(p); break
print(f"files={files} texts={len(texts)} searched={len(long)} (>= 16 bytes; raw, hex, 40-byte prefix) hits={len(hits)} " + " ".join(sorted(set(hits))[:5]))
EOF
check relay-cannot-read "hits=0" "$(grep -o 'hits=[0-9]*' "$D/plaintext-grep.txt")" "$(cat "$D/plaintext-grep.txt")"

# --- sizes on the wire, per (tick, slot), every run
for r in t1 t2 t3 f; do
  R=$D/$r
  rel=$(awk -F, 'NR>1 && $1>=2 {print "down=" $4 " up=" $5}' "$R/relay/wire.csv" | sort | uniq -c | tr -s ' ' | tr '\n' ';')
  shape=$(awk -F, 'NR>1 && $1>=2 {print "down=" $4 " up=" $5}' "$R/relay/wire.csv" | sort -u | tr '\n' ' ' | sed 's/ $//')
  mem=$(for n in "${NAMES[@]}"; do awk -F, 'NR>1 && $3>0 {print "rx=" $2 " tx=" $3}' "$R/home-$n/friends/wire.csv"; done | sort -u | tr '\n' ' ' | sed 's/ $//')
  check "sizes-$r" "relay[down=887 up=256] members[rx=887 tx=256]" "relay[$shape] members[$mem]" "relay rows k>=2: $rel"
done

# --- the trace test: the (tick, slot, size) logs of runs with different traffic
tracediff() { # RUN-A RUN-B -> number of differing lines over the relay log and the three member logs
  local a=$1 b=$2 n=0 m
  diff <(cut -d, -f1-5 "$D/$a/relay/wire.csv") <(cut -d, -f1-5 "$D/$b/relay/wire.csv") >"$D/trace-$a-$b-relay.diff"
  n=$((n + $(grep -c '^[<>]' "$D/trace-$a-$b-relay.diff")))
  for m in "${NAMES[@]}"; do
    diff "$D/$a/home-$m/friends/wire.csv" "$D/$b/home-$m/friends/wire.csv" >"$D/trace-$a-$b-$m.diff"
    n=$((n + $(grep -c '^[<>]' "$D/trace-$a-$b-$m.diff")))
  done
  echo "$n"
}
check trace-t1-t2 "0" "$(tracediff t1 t2)" "diff of (k, slot, route, down, up) at the relay and (k, rx, tx) at alice, bob, carol: t1 (alice->bob x3, carol->alice) vs t2 (bob<->carol, alice->carol)"
check trace-t1-t3 "0" "$(tracediff t1 t3)" "t1 vs t3 (nobody speaks)"

# --- the presence pole: p (carol killed) against t3 (same traffic: none)
diff "$D/t3/home-alice/friends/wire.csv" "$D/p/home-alice/friends/wire.csv" >"$D/presence-alice.diff"
diff "$D/t3/home-bob/friends/wire.csv" "$D/p/home-bob/friends/wire.csv" >"$D/presence-bob.diff"
check presence-members "0" "$(( $(grep -c '^[<>]' "$D/presence-alice.diff") + $(grep -c '^[<>]' "$D/presence-bob.diff") ))" "alice and bob: (k, rx, tx) identical with carol present (t3) and killed (p)"
diff <(cut -d, -f1-5 "$D/t3/relay/wire.csv") <(cut -d, -f1-5 "$D/p/relay/wire.csv") >"$D/presence-relay.diff"
first=$(grep -m1 '^>' "$D/presence-relay.diff" | sed 's/^> //')
firstk=$(echo "$first" | cut -d, -f1); firstslot=$(echo "$first" | cut -d, -f2)
others=$(grep '^>' "$D/presence-relay.diff" | sed 's/^> //' | awk -F, '$2 != 2' | wc -l)
absent=$(awk -F, 'NR>1 {print $6}' "$D/p/witness.csv" | awk '{s+=$1} END {print s+0}')
check presence-relay "slot 2 only" "$([ "$firstslot" = 2 ] && [ "$others" = 0 ] && echo "slot 2 only" || echo "other: first [$first], $others other-slot lines")" \
  "first differing relay line (k,slot,route,down,up): [$first] (t3: [$(grep -m1 '^<' "$D/presence-relay.diff" | sed 's/^< //')]); $(cat "$D/p/killed"); witness: $absent absent marks in p's openings, $(awk -F, 'NR>1 {print $6}' "$D/t3/witness.csv" | awk '{s+=$1} END {print s+0}') in t3's"

# --- the own-slot check against a dropping relay
ev=$D/f/home-alice/friends/events.log
check fault-detected "tick $DROP_AT re-queued" "$(grep -q "committed cell at tick $DROP_AT is not the one I sent (own_omission_evident): re-queued" "$ev" && echo "tick $DROP_AT re-queued" || echo none)" \
  "$(grep -m1 'own slot' "$ev" | cut -d' ' -f2- | cut -c1-200); relay: $(grep -m1 fault "$D/f/relay/relay.log")"
e_drop=$((DROP_AT / 16)); t_drop=$((DROP_AT % 16))
check fault-record "replaced at ticks [$t_drop]" "$(grep "record: epoch $e_drop:" "$ev" | grep -o 'replaced at ticks \[[0-9, ]*\]' | head -1)" "$(grep "record: epoch $e_drop:" "$ev" | cut -d' ' -f2- | cut -c1-240)"
fgot=$(inbox_texts "$D/f/home-bob")
fsaid=$(cut -f4 "$D/f/said.tsv")
check fault-delivered "once, byte-exact" "$([ "$fgot" = "$(printf 'alice\t0\t%s' "$fsaid")" ] && echo "once, byte-exact" || echo "differ: $(echo "$fgot" | wc -l) entries")" \
  "alice status: resends $(jq -r .resends "$D/f/status-alice.json"), ownReplaced $(jq -r .ownReplaced "$D/f/status-alice.json"); sent.jsonl $(jq -c '{fragments,resends,first_k,final_k}' "$D/f/home-alice/friends/sent.jsonl" 2>/dev/null)"

# --- records: every complete epoch checked by every live member; appends admitted
for r in t1 t2 t3 p f; do
  R=$D/$r; t=$TICKS; [ "$r" = f ] && t=$FAULT_TICKS
  want=$((t / 16))
  rc=""
  for n in "${NAMES[@]}"; do
    [ "$r" = p ] && [ "$n" = carol ] && continue
    rc="$rc $n:$(jq -r '"\(.recordRootsAgree)/\(.recordsChecked) mismatch \(.recordRootsMismatch)"' "$R/status-$n.json" 2>/dev/null)"
  done
  agreeall=$(for n in "${NAMES[@]}"; do [ "$r" = p ] && [ "$n" = carol ] && continue; jq -r '.recordRootsMismatch' "$R/status-$n.json"; done | sort -u | tr '\n' ' ' | sed 's/ $//')
  check "records-$r" "0" "$agreeall" "per member agree/checked:$rc; complete epochs $want (the last is checked only if a TICK followed it)"
  check "appends-$r" "$want" "$(grep -c ',admitted,' "$R/relay/appends.csv")" "not admitted: $(awk -F, 'NR>1 && $2!="admitted"' "$R/relay/appends.csv" | wc -l); relay missed $(jq -r .missed "$R/relay/summary.json" 2>/dev/null)"
done

# --- latency say -> tail (t1, t2, f): delivered_unix_ms - queued_unix_ms, matched on (from, to, seq)
python3 - "$D" <<'EOF' >"$D/latency.csv"
import sys, json, glob, os
d = sys.argv[1]
print("run,from,to,seq,bytes,fragments,latency_ms")
for run in ("t1", "t2", "f"):
    sent = {}
    for f in glob.glob(f"{d}/{run}/home-*/friends/sent.jsonl"):
        frm = f.split("/home-")[1].split("/")[0]
        for line in open(f):
            v = json.loads(line); sent[(frm, v["to"], v["seq"])] = v
    for f in glob.glob(f"{d}/{run}/home-*/friends/inbox.jsonl"):
        to = f.split("/home-")[1].split("/")[0]
        for line in open(f):
            v = json.loads(line); s = sent.get((v["from"], to, v["seq"]))
            if s: print(f"{run},{v['from']},{to},{v['seq']},{v['bytes']},{s['fragments']},{v['delivered_unix_ms'] - s['queued_unix_ms']}")
EOF
one=$(awk -F, 'NR>1 && $6==1 {print $7}' "$D/latency.csv" | sort -n | tr '\n' ' ')
multi=$(awk -F, 'NR>1 && $6>1 {print $6 " cells: " $7}' "$D/latency.csv" | tr '\n' ';')
echo "one-cell say->tail ms: $one | multi-cell: $multi" >"$D/latency.txt"

# --- every seal finished inside the window μ (50 ms) on every tick, real payload or padding (§4's obligation)
ov=$(for r in t1 t2 t3 p f; do for n in "${NAMES[@]}"; do jq -r '.sealOverruns' "$D/$r/status-$n.json" 2>/dev/null; done; done | awk '{s+=$1} END {print s+0}')
mx=$(for r in t1 t2 t3 p f; do for n in "${NAMES[@]}"; do awk -F, 'NR>1 && $13>0 {print $10}' "$D/$r/home-$n/friends/member.csv"; done; done | sort -n | tail -1)
p50=$(for r in t1 t2 t3 p f; do for n in "${NAMES[@]}"; do awk -F, 'NR>1 && $13>0 {print $10}' "$D/$r/home-$n/friends/member.csv"; done; done | sort -n | awk '{a[NR]=$1} END {print a[int((NR+1)/2)]}')
check seal-inside-mu "0" "$ov" "seals that did not finish inside mu = 50 ms, all runs and members; seal time p50 ${p50} us, max ${mx} us"

# --- start-up (the Lean library's init, as each member logged it)
grep -h "lean init" "$D"/*/home-*/friends/events.log | grep -o 'lean init [0-9]* ms' | sort | uniq -c >"$D/startup.txt"

# --- transcript
{
  echo "== t1: what was said (tick, from, to, text)"; cat "$D/t1/said.tsv"
  for n in "${NAMES[@]}"; do echo "== t1: mini channel tail friends  (as $n)"; cat "$D/t1/tail-$n.txt"; done
  echo "== t1: carol's status (the non-recipient)"; jq -c '{trialDecrypt, delivered, ownKept, ownReplaced, recordsChecked, recordRootsAgree}' "$D/t1/status-carol.json"
  echo "== f: alice's events"; cut -d' ' -f2- "$D/f/home-alice/friends/events.log"
  echo "== f: bob's tail"; cat "$D/f/tail-bob.txt"
  echo "== latency"; cat "$D/latency.txt"
} >"$D/transcript.txt"

# --- cold audit: stop our service, audit the closed Store, start it again on the same socket
pidfile=$W/public/server.pid
pid=$(cat "$pidfile")
kids=$(pgrep -P "$pid" | tr '\n' ' ')
kill -TERM "$pid"
for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
for k in $kids; do for i in $(seq 1 100); do kill -0 "$k" 2>/dev/null || break; sleep 0.1; done; done
"$MINI" audit --host "$HOST" --config "$CONFIG" >"$D/audit.out" 2>"$D/audit.err"; arc=$?
check cold-audit "exit=0" "exit=$arc" "$(cat "$D/audit.out" "$D/audit.err" | grep -i audit | tail -1 | cut -c1-200)"
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-jchc.log" 2>&1 </dev/null &
echo $! >"$pidfile"
for i in $(seq 1 6000); do
  [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-jchc.log" 2>/dev/null && break; sleep 0.1
done

cat "$rows" >&2
n=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $n client rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$n/$n client rows as expected: sealed delivery, non-recipient blind, constant sizes, trace diff 0, presence pole at the relay only, own-slot re-send, records checked, cold audit" >&2
echo "$rows"
