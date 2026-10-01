#!/usr/bin/env bash
# journey.d/jchan-relay.sh — `mini relay` on one node: real ticks, the kernel's exported assemble /
# fan-out / tick root / seal, one epoch record appended per epoch (CH-RELAY-1, CHANNELS.md §9 row 9).
#
# A (the sponsor) is the domain's relay and sequencer. A opens `chrroom` and births three channel streams
# --in chrroom under "every write is by A": chan-a (run 1), chan-b (run 2), chan-f (the fault run).
# Domain 7, class P1 (id 1: C 256, 1 Hz, E 16), n = 3 slots held by subjects 10, 11, 12.
#
#   run 1  three emitters for CHR_TICKS ticks (default 600 = 10 min)               relay.csv, members, appends
#   run 2  the same, the slot-2 emitter KILLED (-9) at tick CHR_KILL_AT (default 300)
#   fault  CHR_FAULT_TICKS ticks (default 48 = 3 epochs) with --fault-gap-at-epoch 1: the record sealed for
#          epoch 1 is labelled 2, a gap after epoch 0
#
# Rows (expect; every refusal must name its reason):
#   r1-missed / r2-missed          the relay's summary: 0 ticks whose vector was not ready at the next frame
#   r1-records / r2-records        appends admitted = complete epochs = floor(ticks / 16) (37 at 600)
#   r1-sends / r2-sends            every tick sent to every slot: sends = 3 on every tick
#   r2-presence                    after the kill: live 2 + mailbox 1, and still 3 sends
#   r2-receipt-shape               a surviving member's receipts: every TICK 887 B in both runs, and the same
#                                  inter-arrival buckets (10 ms) histogram support in both runs
#   r1-member-checks               every TICK's frame signature and tick root verify at the members
#   witness-opened                 the witness opens every record's absent commitment (kernel openRecord) and
#                                  refuses a one-bit-tampered opening notOpening
#   store-has-record (control)     a record's raw bytes are in the Store
#   store-lacks-opening            no opening (raw or hex), and no opening salt, is anywhere under the world
#   tail-a                         chan-a holds the records in epoch order under channel topics
#   fault-gap                      the gap record is refused by the kernel: epochGap
#   cold-audit                     service stopped: `audit` re-admits every record; service restarted
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS JOURNEY_WORLD JOURNEY_STEP_DIR.
# CHR_LEAN_LIB: the channel library (default: this checkout's .lake/build/lib/libminidregg-channel.so).
# CHR_SOCK_ROOT: a SHORT directory for unix sockets (default /home/ember/build/chr; 108-byte limit).
# Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
AW=$SPONSOR_WS
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
ROOT=${CHE_LEAN_ROOT:-$(cd "$HERE/../../.." && pwd)}
LIB=${CHR_LEAN_LIB:-$ROOT/.lake/build/lib/libminidregg-channel.so}
TICKS=${CHR_TICKS:-600}
KILL_AT=${CHR_KILL_AT:-300}
FAULT_TICKS=${CHR_FAULT_TICKS:-48}
SOCKROOT=${CHR_SOCK_ROOT:-/home/ember/build/chr}
mkdir -p "$D/req" "$SOCKROOT"
SK=$(mktemp -d "$SOCKROOT/s.XXXX")
rows=$D/relay-rows.tsv
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
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
jq -n --arg s "$A" '{type:"any",predicates:[
  {type:"not",predicate:{type:"memberOf",slot:"request/verb",values:["2","7"]}},
  {type:"eq",slot:"request/subject",value:$s}]}' >"$D/req/law-seq.json"
run create-room "$MINI" workspace --action create --dir "$AW" --name chrroom --storage declared \
  --predicate "$D/req/permit-all.json"; ok create-room
for s in chan-a chan-b chan-f; do
  run "create-$s" "$MINI" workspace --action create --dir "$AW" --name "$s" --storage stream \
    --predicate "$D/req/law-seq.json" --in chrroom; ok "create-$s"
done

# member keys and the lease file: slots 0, 1, 2 held by subjects 10, 11, 12 for epochs [0, 1000)
: >"$D/leases.txt"
for slot in 0 1 2; do
  pk=$("$MINI" relay-key --key "$D/member$slot.key") || { echo "relay-key failed" >&2; exit 1; }
  echo "$slot $((10 + slot)) $pk 0 1000" >>"$D/leases.txt"
done

# one run: NAME STREAM TICKS [KILL_AT] [extra relay flags...]
relay_run() {
  local name=$1 stream=$2 ticks=$3 kill_at=$4; shift 4
  local R=$D/$name sock=$SK/${name:0:1}r.sock wsock=$SK/${name:0:1}w.sock wpid rpid slot
  local -a epids=()
  mkdir -p "$R"
  echo "$(date +%s) $(load)" >"$R/load-start"
  "$MINI" relay-witness --lean-lib "$LIB" --unix "$wsock" --out "$R/witness.csv" >"$R/witness.out" 2>"$R/witness.err" &
  wpid=$!; PIDS+=("$wpid")
  for i in $(seq 1 200); do [ -S "$wsock" ] && break; sleep 0.1; done
  "$MINI" relay --lean-lib "$LIB" --class 1 --domain 7 --n 3 --leases "$D/leases.txt" --ticks "$ticks" \
    --unix "$sock" --tcp 127.0.0.1:0 --witness "$wsock" --state-dir "$D/relay-state" --out-dir "$R" \
    --append-ws "$AW" --stream "$stream" --wait-members-ms 120000 --start-delay-ms 2000 "$@" >"$R/relay.out" 2>"$R/relay.err" &
  rpid=$!; PIDS+=("$rpid")
  for i in $(seq 1 300); do [ -S "$sock" ] && break; sleep 0.1; done
  for i in $(seq 1 1800); do [ -s "$R/tcp-addr" ] && break; sleep 0.1; done
  for slot in 0 1 2; do
    # slot 1 rides TCP loopback, slots 0 and 2 the unix socket
    if [ "$slot" = 1 ]; then conn="tcp:$(cat "$R/tcp-addr")"; else conn="unix:$sock"; fi
    "$MINI" relay-emit --lean-lib "$LIB" --connect "$conn" --domain 7 --slot "$slot" --subject $((10 + slot)) \
      --key "$D/member$slot.key" --out "$R/member$slot.csv" >"$R/emit$slot.out" 2>"$R/emit$slot.err" &
    epids+=($!); PIDS+=($!)
  done
  if [ "$kill_at" -gt 0 ]; then
    # wait until slot 2's member has logged tick kill_at, then kill it
    for i in $(seq 1 $(( (kill_at + 400) * 10 ))); do
      [ "$(tail -1 "$R/member2.csv" 2>/dev/null | cut -d, -f1)" -ge "$kill_at" ] 2>/dev/null && break; sleep 0.1
    done
    kill -9 "${epids[2]}"; echo "$(date +%s) killed slot 2 pid ${epids[2]} after tick $(tail -1 "$R/member2.csv" | cut -d, -f1)" >"$R/killed"
  fi
  wait "$rpid"; echo $? >"$R/relay.rc"
  for p in "${epids[@]}"; do
    for i in $(seq 1 50); do kill -0 "$p" 2>/dev/null || break; sleep 0.1; done
    kill -TERM "$p" 2>/dev/null; wait "$p" 2>/dev/null
  done
  for i in $(seq 1 50); do kill -0 "$wpid" 2>/dev/null || break; sleep 0.1; done
  kill -TERM "$wpid" 2>/dev/null; wait "$wpid" 2>/dev/null
  echo "$(date +%s) $(load)" >"$R/load-end"
}

csvcol() { # FILE COLUMN -> the column's values (header skipped)
  awk -F, -v c="$2" 'NR==1{for(i=1;i<=NF;i++) if($i==c) k=i; next} {print $k}' "$1"
}
receipt_shape() { # MEMBER.csv -> "bytes=<sizes> | <10 ms inter-arrival bucket>ms:<count> ..." after the first TICK
  local b h
  b=$(awk -F, 'NR>2 {print $4}' "$1" | sort -u | tr '\n' ' ')
  h=$(awk -F, 'NR>2 {print int(($6 + 5000) / 10000) * 10}' "$1" | sort -n | uniq -c | awk '{printf "%sms:%s ", $2, $1}')
  echo "bytes=$b| $h"
}

relay_run r1 chan-a "$TICKS" 0
relay_run r2 chan-b "$TICKS" "$KILL_AT"
relay_run rf chan-f "$FAULT_TICKS" 0 --fault-gap-at-epoch 1

want_records=$((TICKS / 16))
for r in r1 r2; do
  R=$D/$r
  check "$r-relay-exit" "0" "$(cat "$R/relay.rc")" "$(tail -1 "$R/relay.err" | cut -c1-200)"
  check "$r-missed" "0" "$(jq -r .missed "$R/summary.json" 2>/dev/null)" \
    "ticks $(jq -r .ticks "$R/summary.json" 2>/dev/null); load start $(cut -d' ' -f2- "$R/load-start"), end $(cut -d' ' -f2- "$R/load-end")"
  check "$r-records" "$want_records" "$(grep -c ',admitted,' "$R/appends.csv")" \
    "sealed $(jq -r .sealed "$R/summary.json" 2>/dev/null); not admitted $(awk -F, 'NR>1 && $2!="admitted"' "$R/appends.csv" | wc -l); lean init $(jq -r .leanInitMs "$R/summary.json" 2>/dev/null) ms"
  check "$r-sends" "3" "$(csvcol "$R/relay.csv" sends | sort -u | tr '\n' ' ' | sed 's/ $//')" \
    "rows $(($(wc -l <"$R/relay.csv") - 1))"
done
post=$(awk -F, -v k="$KILL_AT" 'NR>1 && $1>k+2 {print $6"+"$7"="$5}' "$D/r2/relay.csv" | sort | uniq -c | tr -s ' ' | tr '\n' ';')
check r2-presence "live2+mailbox1=3" "$(awk -F, -v k="$KILL_AT" 'NR>1 && $1>k+2 {print "live"$6"+mailbox"$7"="$5}' "$D/r2/relay.csv" | sort -u | tr '\n' ' ' | sed 's/ $//')" "$post"
# a surviving member's receipts: sizes must be identical; timing, the share of inter-arrivals in the
# 990-1010 ms buckets (the 1 s tick) and the modal bucket, in run 1, run 2 before the kill and run 2 after it
s1=$(receipt_shape "$D/r1/member0.csv"); s2=$(receipt_shape "$D/r2/member0.csv")
sb1=${s1%%|*}; sb2=${s2%%|*}
if [ "$sb1" = "$sb2" ] && [ "$sb1" = "bytes=887 " ]; then got=same-sizes; else got=differ; fi
check r2-receipt-sizes "same-sizes" "$got" "run1 $sb1 run2 $sb2 (member 0; member 1 rides TCP: $(receipt_shape "$D/r2/member1.csv" | cut -d'|' -f1))"
shape() { # MEMBER.csv FROM TO -> "mode=<bucket> in1s=<permille>"
  awk -F, -v a="$2" -v b="$3" 'NR>2 && $1>=a && $1<b {x=int(($6 + 5000) / 10000) * 10; h[x]++; n++}
    END {m=-1; for (k in h) if (m<0 || h[k]>h[m]) m=k; printf "mode=%sms in1s=%d", m, int(1000*(h[990]+h[1000]+h[1010])/(n?n:1))}' "$1"
}
k1=$KILL_AT
p1=$(shape "$D/r1/member0.csv" 0 999999); pre=$(shape "$D/r2/member0.csv" 0 "$k1"); postk=$(shape "$D/r2/member0.csv" $((k1 + 2)) 999999)
mode_of() { echo "$1" | cut -d' ' -f1; }
in1s_of() { echo "$1" | sed 's/.*in1s=//'; }
if [ "$(mode_of "$p1")" = "$(mode_of "$postk")" ] && [ "$(mode_of "$pre")" = "$(mode_of "$postk")" ] && \
   [ "$(in1s_of "$p1")" -ge 990 ] && [ "$(in1s_of "$postk")" -ge 990 ]; then got=same-shape; else got=differ; fi
check r2-receipt-timing "same-shape" "$got" "run1 [$p1] run2-before-kill [$pre] run2-after-kill [$postk]; full: run1 [$s1] run2 [$s2]"
sigbad=$(cat "$D"/r1/member*.csv | awk -F, 'NR>1 && $1!="k" && ($7!=1 || $8!=1)' | wc -l)
check r1-member-checks "0" "$sigbad" "TICKs whose frame signature or tick root failed at a member, run 1"
own=$(awk -F, 'NR>1 {print $9}' "$D/r1/member0.csv" "$D/r1/member1.csv" "$D/r1/member2.csv" | grep -v '^own$' | sort | uniq -c | tr -s ' ' | tr '\n' ';')
check r1-own-slot "0" "$(awk -F, 'NR>1 && $9=="replaced"' "$D"/r1/member*.csv | wc -l)" "own-slot checks: $own"

nw=$(($(wc -l <"$D/r1/witness.csv") - 1))
wok=$(awk -F, 'NR>1 && $2=="opened" && $3=="refused-notOpening"' "$D/r1/witness.csv" | wc -l)
check witness-opened "$want_records" "$wok" "$nw openings received; each opened by openRecord, each tampered copy refused notOpening"

# the Store holds the record (control) and no opening, salt, or opening hex (the opening went to the witness)
rec=$(jq -r '.targets[0].payload.payloadHex' "$D/r1/append-requests/chr-chan-a-e1.json")
python3 - "$W" "$rec" "$D/r1/witness.csv" "$D/r2/witness.csv" "$D/rf/witness.csv" >"$D/store-grep.txt" <<'EOF'
import sys, os, csv
world, rec_hex, wfiles = sys.argv[1], sys.argv[2], sys.argv[3:]
rec = bytes.fromhex(rec_hex)
openings = [bytes.fromhex(r["opening_hex"]) for w in wfiles if os.path.exists(w) for r in csv.DictReader(open(w))]
needles = {"record-raw": [rec]}
needles["opening-raw"] = openings
needles["opening-hex"] = [o.hex().encode() for o in openings] + [o.hex().upper().encode() for o in openings]
needles["salt-raw"] = [o[-32:] for o in openings]
needles["salt-hex"] = [o[-32:].hex().encode() for o in openings]
hits = {k: 0 for k in needles}
files = 0
for root, _, fs in os.walk(world):
    for f in fs:
        try: b = open(os.path.join(root, f), "rb").read()
        except Exception: continue
        files += 1
        for k, ns in needles.items():
            hits[k] += sum(1 for n in ns if n in b)
print(f"files={files} openings={len(openings)} " + " ".join(f"{k}={v}" for k, v in hits.items()))
EOF
g=$(cat "$D/store-grep.txt")
check store-has-record "found" "$([[ "$g" == *"record-raw=0"* ]] && echo absent || echo found)" "$g"
check store-lacks-opening "0" "$(echo "$g" | tr ' ' '\n' | grep -E '^(opening|salt)-' | cut -d= -f2 | awk '{s+=$1} END {print s+0}')" "$g"

run tail-a "$MINI" workspace --action tail --dir "$AW" --name chan-a --from 1 --count 64
want=$(for e in $(seq 0 $((want_records - 1))); do jq -r '.targets[0].payload.topicHex' "$D/r1/append-requests/chr-chan-a-e$e.json"; done | tr '\n' ' ' | sed 's/ $//')
gotT=$(jq -r '[.entries[].topic] | join(" ")' "$D/tail-a.out" 2>/dev/null)
check tail-a "epochs 0..$((want_records - 1)) in order" "$([ "$gotT" = "$want" ] && echo "epochs 0..$((want_records - 1)) in order" || echo other)" \
  "$(jq -r '.entries | length' "$D/tail-a.out" 2>/dev/null) entries"

fault=$(awk -F, 'NR>1 && $1==2' "$D/rf/appends.csv")
case "$fault" in *refused*epochGap*) got="refused epochGap";; *) got="other";; esac
check fault-gap "refused epochGap" "$got" "$(echo "$fault" | cut -c1-260); first record: $(awk -F, 'NR==2 {print $1","$2}' "$D/rf/appends.csv")"

# cold audit: stop our service, audit the closed Store, start it again on the same socket
pidfile=$W/public/server.pid
pid=$(cat "$pidfile")
kids=$(pgrep -P "$pid" | tr '\n' ' ')
kill -TERM "$pid"
for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
for k in $kids; do for i in $(seq 1 100); do kill -0 "$k" 2>/dev/null || break; sleep 0.1; done; done
"$MINI" audit --host "$HOST" --config "$CONFIG" >"$D/audit.out" 2>"$D/audit.err"; arc=$?
check cold-audit "exit=0" "exit=$arc" "$(cat "$D/audit.out" "$D/audit.err" | grep -i audit | tail -1 | cut -c1-200)"
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-jchr.log" 2>&1 </dev/null &
echo $! >"$pidfile"
for i in $(seq 1 6000); do
  [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-jchr.log" 2>/dev/null && break; sleep 0.1
done

cat "$rows" >&2
n=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $n relay rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$n/$n relay rows as expected: $TICKS ticks x2 at P1 n=3, 0 missed, $want_records records admitted per run, 3 sends every tick with a member killed, openings at the witness only, gap refused epochGap, cold audit" >&2
echo "$rows"
