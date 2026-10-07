#!/usr/bin/env bash
# JCHAT (PLACE §2.3, §5 item 4, client half): friends talk in a room through
# `mini shell` on this journey's live Store.
#
# Five friends are enrolled and provisioned the way OPERATOR.md does it (as in
# j12): alice founds `commons`; bob, carol and the Discord bridge are invited;
# dave is an outsider until alice invites him late. Every chat line is typed
# into a friend's own `mini shell --line` session.
#
# Rows print `name<TAB>expect=…<TAB>got=…<TAB>detail`. Both poles of every verb:
# say/tail in order; an outsider's join and tail refused; carol cannot append
# to bob's stream (the author law, at the Host); concurrent says by three
# friends with no re-plan and one merge order for every reader and across a
# restart; --re and --to; topic/pin by a member shown ignored, by the founder
# effective; reactions; a late joiner sees all of it; a tampered held payload
# prints [payload unavailable]; --follow; the Discord mirror both ways with no
# loop; a cold audit re-admits every record. Latency of `say` and of a
# 200-entry `tail` is measured beside the box's load.
#
# Needs: JCHAT_DISCORD_DIR = a directory holding `mini-discord-mirror` and
# `fake-discord` built from native/discord-entrance (the mirror rows FAIL
# without it). Hook contract: journey.sh. Last stdout line: the row table.
set -u
. "$(dirname "${BASH_SOURCE[0]}")/../journey-private.sh"
umask 077
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}" "${JOURNEY_WORLD:?}"
SH=${SHELL_BIN:-}; [ -n "$SH" ] || SH=$MINI
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
WRAPPER=$(CDPATH='' cd -- "$HERE/../../../deploy/shell" && pwd)/mini-shell-ssh
SD=$JOURNEY_STEP_DIR
H=$SD/h; WS=$SD/w; L=$SD/log
mkdir -p -m 700 "$H" "$WS" "$L"
ROWS=$SD/jchat-rows.tsv
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
    echo "JCHAT: $(wc -l <"$ROWS") rows as expected" >&2; exit 0
  fi
  echo "JCHAT: $BAD of $(wc -l <"$ROWS") rows differ; first: $FIRST" >&2; exit 1
}

# ------------------------------------------------ friends: enroll, provision, init (j12's way)
mkdir -p -m 700 "$H/sponsor"
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/permit-all.json"
declare -A S
for f in alice bob carol dave bridge; do
  mkdir -p -m 700 "$H/$f"
  setup "$f" "keygen mini.key"
  operator "custody copy" install_private 0600 "$H/$f/keys/mini.key" "$H/sponsor/keys/$f.key"
  setup sponsor "enroll plan $f $f.key $(xxd -p -c 256 "$H/$f/keys/mini.key.next.pub") $(xxd -p -c 256 "$H/$f/keys/mini.key.next.cosign")"
  setup sponsor "enroll seal $f"
  setup sponsor "enroll submit $f"
  S[$f]=$(jq -r '.subject // empty' "$OUT")
  [ -n "${S[$f]}" ] || { echo "no subject for $f" >&2; finish; }
  operator "custody remove" rm -f "$H/sponsor/keys/$f.key"
  operator "provision $f" "$MINI" workspace --action provision --dir "$SPONSOR_WS" --name "$f" --holder "${S[$f]}" \
      --funding 1000 --account-predicate "$SD/permit-all.json" --factory-ref factory
  operator "deliver $f" install_private 0600 "$SPONSOR_WS/provisions/$f/birth-context.json" "$H/$f/provision/birth-context.json"
  setup "$f" "init mini.key ${S[$f]}"
done
A=${S[alice]} B=${S[bob]} C=${S[carol]} D=${S[dave]} E=${S[bridge]}
# petnames: each reader names the others (names are local to each reader)
for r in alice bob carol dave bridge; do
  for f in alice bob carol dave bridge; do
    [ "$r" = "$f" ] || setup "$r" "chat name ${S[$f]} $f"
  done
done

# ------------------------------------------------ the room
# critical NAME WHO LINE: a row that later rows depend on; stop when it fails
critical() { ok "$@"; [ "$RC" = 0 ] || { echo "critical row $1 failed" >&2; finish; }; }
critical new alice "chat new commons"
invite() { # WHO: alice invites WHO; WHO joins with the line alice printed
  critical "invite-$1" alice "chat invite commons ${S[$1]} $1"
  INV_LINE=$(grep '^chat join commons ' "$OUT" | tail -1)
  [ -n "$INV_LINE" ] || { row "invitation-$1" "a chat join line" "none" "$(head -3 "$OUT")"; finish; }
  printf '%s\n' "$INV_LINE" >"$SD/invitation-$1.txt"
  critical "join-$1" "$1" "$INV_LINE"
}
for f in bob carol bridge; do invite "$f"; done
ROOMT=$(jq -r .target "$WS/alice/refs/commons.json")
SB=$(jq -r .target "$WS/alice/refs/commons-${B: -10}.json")
CCAP=$(jq -r .observeCapability "$WS/carol/refs/commons.json")
BCAP=$(jq -r .observeCapability "$WS/bob/refs/commons.json")

# ------------------------------------------------ an outsider
fails outsider-join dave "$(cat "$SD/invitation-bob.txt")" 2 "not addressed to you"
ok outsider-import dave "import commons-x object $ROOMT $BCAP"
operator "dave crafts a room record from bob's invitation numbers" sh -c "mkdir -p -m 700 '$H/dave/chat/rooms' && printf '%s\n' '{\"type\":\"mini-chat-room-v1\",\"room\":\"commons-x\",\"grant\":\"commons-x\",\"stream\":null}' >'$H/dave/chat/rooms/commons-x.json' && printf 'commons-x\n' >'$H/dave/chat/current'"
refused outsider-tail dave "tail" "no-grant"

# ------------------------------------------------ say / tail
SAY_SECS=()
ok say-a alice "say hello, friends"; SAY_SECS+=("$SECS")
ok say-b bob "say hi alice, it's bob"; SAY_SECS+=("$SECS")
ok tail-c carol "tail"
in_order() { # FILE: alice's line then bob's, as #1 and #2
  grep -nE '^#1 h[0-9]+ alice: hello, friends$' "$1" | cut -d: -f1 >"$SD/o1" &&
  grep -nE "^#2 h[0-9]+ bob: hi alice, it's bob$" "$1" | cut -d: -f1 >"$SD/o2" &&
  [ "$(cat "$SD/o1")" -lt "$(cat "$SD/o2")" ]
}
check c-sees-in-order "carol's tail: #1 alice, then #2 bob, with their text" in_order "$OUT"
cp "$OUT" "$SD/tail-c-1.txt"

# ------------------------------------------------ the author law
ok c-own-control carol "say carol here, in my own stream"
ok c-forge-import carol "import sb-forged object $SB $CCAP $CCAP"
ok c-forge-propose carol "propose forge1 {\"type\":\"minidregg-workspace-proposal-v1\",\"action\":\"invoke\",\"targets\":[{\"name\":\"sb-forged\",\"payload\":{\"type\":\"append\",\"topic\":\"\",\"text\":\"{\\\"type\\\":\\\"say\\\",\\\"text\\\":\\\"I am bob\\\"}\"}}]}"
refused c-into-b carol "submit forge1" "law-denied"
row c-into-b-clause "names bob" "$(grep -q "$B" "$ERR" && echo 'names bob' || echo 'does not name bob')" "the refusal's clause is sb's author law: $(first_ending "$ERR")"

# ------------------------------------------------ concurrent says
for f in alice bob carol; do
  ( "$SH" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" --workspace "$WS/$f" --home "$H/$f" \
      --line "say at once, from $f" >"$L/conc-$f.out" 2>"$L/conc-$f.err"; echo $? >"$L/conc-$f.rc" ) &
done
wait
admitted=0; for f in alice bob carol; do [ "$(cat "$L/conc-$f.rc")" = 0 ] && admitted=$((admitted + 1)); done
again() { # FILES…: total re-plans (staleTarget) and re-signs (stale-root) the says reported
  cat "$@" 2>/dev/null | grep -o 're-planned [0-9]*, re-signed [0-9]*' |
    awk '{p += $2; r += $4} END {printf "%d %d", p, r}'
}
read -r REPLANS RESIGNS <<<"$(again "$L"/conc-*.out)"
row concurrent-3 "3/3,replans=0" "$admitted/3,replans=$REPLANS" "three says started together, each planned from one read of its own stream; re-signed over a fresh challenge (stale-root, another admission moved the world root mid-exchange): $RESIGNS"
feed_of() { # WHO TAG: the merged order as WHO reads it (n cell sequence height text)
  line "$1" "tail --json -n 100000"
  tail -n +2 "$OUT" | jq -c '[.n, .cell, .sequence, .height, .kind, .text]' >"$SD/feed-$1-$2.jsonl"
}
for f in alice bob carol; do feed_of "$f" before; done
same_feed() { cmp -s "$SD/feed-alice-$1.jsonl" "$SD/feed-bob-$1.jsonl" && cmp -s "$SD/feed-alice-$1.jsonl" "$SD/feed-carol-$1.jsonl"; }
row merge-identical "identical" "$(same_feed before && echo identical || echo DIFFERENT)" "alice, bob and carol: $(wc -l <"$SD/feed-alice-before.jsonl") entries in one order"

# ------------------------------------------------ --re, --to
ok re bob "say --re 1 replying to alice"
ok to alice "say --to carol psst, carol"
ok tail-c2 carol "tail -n 50"
check re-shown "bob's reply names #1" grep -qE '^#[0-9]+ h[0-9]+ bob ↪#1: replying to alice$' "$OUT"
check to-shown "alice's line is addressed to carol (me, to carol)" grep -qE '^#[0-9]+ h[0-9]+ alice →me: psst, carol$' "$OUT"

# ------------------------------------------------ topic, pin, react
ok topic-member bob "topic bob's topic"
ok topic-founder alice "topic release planning"
ok pin-member bob "pin 1"
ok pin-founder alice "pin 2"
ok react-c carol "react 2 +1"
ok react-b bob "react 2 +1"
ok react-c-again carol "react 2 +1"
ok tail-a alice "tail -n 100"
check topic-set "header: topic release planning" grep -qE '^# commons · topic: release planning \(#[0-9]+\)' "$OUT"
check pin-set "header: pinned #2 bob" grep -qE "· pinned #2 bob: hi alice, it's bob ·" "$OUT"
check topic-member-ignored "bob's topic shown ignored, with the reason" grep -qF "bob set the topic to \"bob's topic\" (ignored: only me, the founder, sets the topic in this room)" "$OUT"
check pin-member-ignored "bob's pin shown ignored" grep -qE '^#[0-9]+ h[0-9]+ bob pinned #1 \(ignored: only me, the founder, pins in this room\)$' "$OUT"
check reactions "#2 has +1 from carol and bob, once each" grep -qxF '      +1 carol bob' "$OUT"

# ------------------------------------------------ a late joiner
invite dave
ok tail-d dave "tail -n 100"
check late-topic "dave sees the topic" grep -qE '^# commons · topic: release planning' "$OUT"
check late-pin "dave sees the pin" grep -qE "· pinned #2 bob: hi alice, it's bob ·" "$OUT"
check late-react "dave sees the reactions" grep -qxF '      +1 carol bob' "$OUT"
check late-all "dave sees #1" grep -qE '^#1 h[0-9]+ alice: hello, friends$' "$OUT"
ok say-d dave "say hello, I'm late"

# ------------------------------------------------ follow
( "$SH" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" --workspace "$WS/carol" --home "$H/carol" \
    --line "tail --follow -n 1" >"$L/follow.out" 2>"$L/follow.err" ) &
FOLLOW_PID=$!
for i in $(seq 1 120); do [ -s "$L/follow.out" ] && break; sleep 0.5; done   # the first page is out
ok say-while-following alice "say this arrives while carol follows"
t0=$(now)
for i in $(seq 1 120); do
  grep -qE '^#[0-9]+ h[0-9]+ alice: this arrives while carol follows$' "$L/follow.out" && break; sleep 0.5
done
FOLLOW_LAG=$(echo "$(now) - $t0" | bc)
kill "$FOLLOW_PID" 2>/dev/null; pkill -P "$FOLLOW_PID" 2>/dev/null; wait "$FOLLOW_PID" 2>/dev/null
check follow "carol's --follow printed the new line ${FOLLOW_LAG}s after alice's say returned (poll every 3 s)" grep -qE '^#[0-9]+ h[0-9]+ alice: this arrives while carol follows$' "$L/follow.out"

# ------------------------------------------------ the held view, tampered
ok tail-c3 carol "tail -n 100"
ok held-c carol "tail --held -n 100"
check held-control "the held view prints bob's text" grep -qE "^#2 h[0-9]+ bob: hi alice, it's bob$" "$OUT"
HELD=$(ls -d "$H/carol/chat/reads/commons/s$SB-p1."* | head -1)/view.bin
operator "carol's held read of bob's stream: one byte of bob's text flipped" python3 - "$HELD" <<'EOF'
import sys
p = sys.argv[1]
b = bytearray(open(p, "rb").read())
i = b.find(b"hi alice")
assert i >= 0
b[i] ^= 0x01
open(p, "wb").write(bytes(b))
EOF
ok held-tampered carol "tail --held -n 100"
check tamper-unavailable "bob's tampered entry prints [payload unavailable]" grep -qE '^#2 h[0-9]+ bob: \[payload unavailable\]$' "$OUT"
check tamper-others "alice's untouched entry still prints" grep -qE '^#1 h[0-9]+ alice: hello, friends$' "$OUT"
check tamper-no-forgery "no altered text is printed" sh -c "! grep -q 'ii alice' '$OUT'"

# ------------------------------------------------ the Discord bridge, both ways
DD=${JCHAT_DISCORD_DIR:-}
if [ -x "$DD/mini-discord-mirror" ] && [ -x "$DD/fake-discord" ]; then
  PORT=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1])')
  mkdir -p -m 700 "$SD/discord" "$SD/spool"
  "$DD/fake-discord" api "127.0.0.1:$PORT" "$SD/discord" 2>"$SD/discord/fake.err" &
  FAKE_PID=$!
  sleep 1
  post() { curl -s -o /dev/null -w '%{http_code}' -X POST "http://127.0.0.1:$PORT/fake/channels/701/messages" -d "$1"; }
  post '{"content":"hello from discord","author":{"id":"4242","username":"zed"}}' >/dev/null
  post '{"content":"beep","author":{"id":"99","username":"somebot","bot":true}}' >/dev/null
  mirror() {
    env -i PATH=/usr/bin:/bin MINI_SHELL_WRAPPER="$WRAPPER" MINI_CLIENT="$SH" MINI_HOST="$HOST" MINI_CONFIG="$CONFIG" \
      MINI_SOCKET="$SOCKET" MINI_MIRROR_HOME="$H/bridge" MINI_MIRROR_WORKSPACE="$WS/bridge" MINI_MIRROR_ROOM=commons \
      MINI_MIRROR_WEBHOOK_URL="http://127.0.0.1:$PORT/api/webhooks/555/hooktoken" \
      MINI_MIRROR_CHANNEL_URL="http://127.0.0.1:$PORT/api/v10/channels/701/messages" \
      MINI_MIRROR_BOT_TOKEN=fake-bot-token MINI_DISCORD_SPOOL="$SD/spool" \
      "$DD/mini-discord-mirror" --once >"$SD/mirror-$1.out" 2>"$SD/mirror-$1.err"
    MRC=$?
    MLINE=$(grep -o 'posted [0-9]*, said [0-9]*' "$SD/mirror-$1.err" | tail -1)
  }
  webhook_count() { jq '[.[] | select(.webhook_id != null)] | length' "$SD/discord/channel-701.json"; }
  mirror m1
  row mirror-1 "rc0,said 1" "rc$MRC,${MLINE#*, }" "$MLINE; $(tail -1 "$SD/mirror-m1.err")"
  P1=$(webhook_count)
  check mirror-1-posts "the room's says reached the channel as webhook messages" sh -c "[ '$P1' -ge 5 ] && jq -e '[.[] | select(.webhook_id != null) | .content] | index(\"**alice**: hello, friends\") != null' '$SD/discord/channel-701.json'"
  ok tail-after-mirror carol "tail -n 100"
  check mirror-said "zed's message is in the room, said by the bridge" grep -qE '^#[0-9]+ h[0-9]+ bridge via discord zed#4242: hello from discord$' "$OUT"
  check mirror-bot-skipped "the bot's message was not said" sh -c "! grep -q 'beep' '$OUT'"
  mirror m2
  row mirror-2-no-loop "rc0,posted 0, said 0" "rc$MRC,$MLINE" "the bridge's own entry is not posted back; webhook messages are not said again"
  row mirror-2-channel "$P1" "$(webhook_count)" "webhook messages in the channel after the second poll"
  ok mirror-say alice "say back to discord?"
  mirror m3
  row mirror-3 "rc0,posted 1, said 0" "rc$MRC,$MLINE" "exactly alice's new line went up"
  check mirror-3-content "the channel has alice's line" jq -e '[.[] | select(.webhook_id != null) | .content] | index("**alice**: back to discord?") != null' "$SD/discord/channel-701.json"
  ok via-count carol "tail --json -n 1000"
  row mirror-once "1" "$(tail -n +2 "$OUT" | jq -s '[.[] | select(.via != null)] | length')" "bridged entries in the room: exactly one (no echo)"
  row mirror-signer "[\"$E\"]" "$(tail -n +2 "$OUT" | jq -s -c '[.[] | select(.via != null) | .author] | unique')" "every bridged entry is signed by the bridge's own subject, never a friend's"
  kill "$FAKE_PID" 2>/dev/null; wait "$FAKE_PID" 2>/dev/null; FAKE_PID=
else
  row mirror "built" "absent" "JCHAT_DISCORD_DIR=$DD holds no mini-discord-mirror and fake-discord"
fi

# ------------------------------------------------ latency: say, and a 200-entry tail
load() { cut -d' ' -f1-3 /proc/loadavg; }
LOAD_SAY=$(load)
for i in 1 2 3 4 5; do ok "say-latency-$i" bob "say timing line $i"; SAY_SECS+=("$SECS"); done
median() { printf '%s\n' "$@" | sort -n | awk '{a[NR]=$1} END {print a[int((NR+1)/2)]}'; }
for f in alice bob carol; do
  ( for i in $(seq 1 64); do
      "$SH" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" --workspace "$WS/$f" --home "$H/$f" \
        --line "say filler $i from $f" >>"$L/fill-$f.out" 2>>"$L/fill-$f.err" || echo "fail $i" >>"$L/fill-$f.fail"
    done ) &
done
wait
line carol "tail --json -n 100000"
TOTAL=$(tail -n +2 "$OUT" | wc -l)
LOAD_TAIL=$(load)
ok tail-200 carol "tail -n 200"
TAIL_SECS=$SECS
row tail-200-lines "200" "$(grep -cE '^#[0-9]+ ' "$OUT")" "carol's tail -n 200 of $TOTAL entries took ${TAIL_SECS}s (load $LOAD_TAIL)"
read -r FP FR <<<"$(again "$L"/fill-*.out)"
row fill-192 "0 failed" "$(cat "$L"/fill-*.fail 2>/dev/null | wc -l) failed" "192 says, three friends saying at once: re-planned $FP (staleTarget), re-signed $FR (stale-root)"
row say-latency "measured" "measured" "say median $(median "${SAY_SECS[@]}")s over ${#SAY_SECS[@]} says one at a time (load $LOAD_SAY)"

# ------------------------------------------------ restart: one order before and after; a cold audit
pidfile=$JOURNEY_WORLD/public/server.pid
restart() {
  local pid; pid=$(cat "$pidfile")
  kill -TERM "$pid"
  for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$pid" 2>/dev/null && { echo "server $pid alive after TERM" >&2; finish; }
  "$MINI" audit --host "$HOST" --config "$CONFIG" >"$SD/audit-$1.out" 2>"$SD/audit-$1.err"
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$JOURNEY_WORLD/public/serve-jchat-$1.log" 2>&1 </dev/null &
  echo $! >"$pidfile"
  for i in $(seq 1 6000); do
    [ -S "$SOCKET" ] && grep -q serving "$JOURNEY_WORLD/public/serve-jchat-$1.log" 2>/dev/null && break; sleep 0.1
  done
}
for f in alice bob carol; do feed_of "$f" pre; done
restart r1
for f in alice bob carol; do feed_of "$f" post; done
row merge-identical-pre "identical" "$(same_feed pre && echo identical || echo DIFFERENT)" "$(wc -l <"$SD/feed-alice-pre.jsonl") entries, three readers"
row merge-across-restart "identical" "$(cmp -s "$SD/feed-alice-pre.jsonl" "$SD/feed-alice-post.jsonl" && same_feed post && echo identical || echo DIFFERENT)" "every reader's order, before and after the Host restarted"
AUDITED=$(grep -o 'audited [0-9]* accepted records: every signed ingress re-admitted at its original prefix' "$SD/audit-r1.out" | head -1)
row audit-cold "re-admitted" "$([ -n "$AUDITED" ] && echo re-admitted || echo NOT)" "${AUDITED:-$(head -c 160 "$SD/audit-r1.out" "$SD/audit-r1.err" | tr '\n' ' ')} (the Host stopped; run before the restart)"

finish
