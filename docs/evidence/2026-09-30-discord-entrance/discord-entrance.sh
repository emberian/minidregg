#!/usr/bin/env bash
# The Discord entrance on a fresh private Store. A loopback fake of Discord signs
# interactions and POSTs them to `mini-discord`; `mini-discord` runs each line
# through deploy/shell/mini-shell-ssh (the ssh entrance's forced command) in the
# rostered user's session and PATCHes the answer to the fake's webhook API.
# No real Discord is involved: this is the deployable shape (interactions
# endpoint + follow-up webhook) against a stand-in for discord.com.
#
# usage: discord-entrance.sh HOST MINI STORE VERIFIER TARGET_DIR NEW_RUN_DIR [PORT]
#   HOST, MINI, STORE, VERIFIER: the Host, the client carrying `mini shell`
#     (also used for bootstrap and `mini serve`), and the two Host helpers.
#   TARGET_DIR: native/discord-entrance/target/release (mini-discord,
#     mini-discord-mirror, examples/fake-discord).
#   NEW_RUN_DIR must not exist. mini-discord listens on 127.0.0.1:PORT
#     (default 28793), the fake API on PORT+1. All are stopped on exit.
set -uo pipefail
umask 077
if [[ $# -lt 6 || $# -gt 7 ]]; then sed -n '2,16p' "$0" >&2; exit 64; fi
HOST=$1 MINI_SRC=$2 STORE=$3 VERIFIER=$4 TGT=$5 RUN=$6 PORT=${7:-28793}
API_PORT=$((PORT + 1))
for p in "$HOST" "$MINI_SRC" "$STORE" "$VERIFIER" "$TGT" "$RUN"; do
  [[ $p == /* ]] || { echo "path must be absolute: $p" >&2; exit 64; }
done
[[ ! -e $RUN ]] || { echo "run directory exists: $RUN" >&2; exit 64; }
command -v jq >/dev/null || { echo 'jq is required' >&2; exit 66; }
for port in "$PORT" "$API_PORT"; do
  if ss -ltn | awk '{print $4}' | grep -q ":$port\$"; then echo "port $port in use" >&2; exit 69; fi
done
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../../.." && pwd)

mkdir -m 700 "$RUN" "$RUN/bin" "$RUN/log" "$RUN/etc" "$RUN/sessions" "$RUN/api" "$RUN/spool"
RUN=$(CDPATH='' cd -- "$RUN" && pwd)
LOG=$RUN/log R=$RUN/store
install -m 0500 "$MINI_SRC" "$RUN/bin/mini"
install -m 0500 "$REPO/deploy/shell/mini-shell-ssh" "$RUN/bin/mini-shell-ssh"
install -m 0500 "$TGT/mini-discord" "$TGT/mini-discord-mirror" "$TGT/examples/fake-discord" "$RUN/bin/"
MINI=$RUN/bin/mini FAKE=$RUN/bin/fake-discord
CONFIG=$R/deployment/pinned-config.json SOCK=$R/public/mini.sock
sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$RUN/bin/mini-shell-ssh" "$RUN/bin/mini-discord" \
  "$RUN/bin/mini-discord-mirror" "$FAKE" >"$LOG/binaries.sha256"

APP=1400000000000000001 SPONSOR_ID=1400000000000000010 FRIEND_ID=1400000000000000020 STRANGER_ID=1400000000000000999
ENTRANCE_PID= API_PID=
TABLE=$LOG/rows.tsv
printf 'n\twho\tcommand\tline\texpect\thttp\ttype\tack_s\tfollowup_s\tverdict\tanswer\n' >"$TABLE"
N=0 FAILS=0

cleanup() {
  {
    echo "--- cleanup"
    for pid in $ENTRANCE_PID $API_PID; do
      cmd=$(tr '\0' ' ' 2>/dev/null <"/proc/$pid/cmdline") || continue
      [[ $cmd == "$RUN/bin/"* ]] && kill -TERM "$pid" && echo "stopped $pid: $cmd"
    done
    if [[ -f $R/public/server.pid ]]; then
      spid=$(cat "$R/public/server.pid")
      cmd=$(tr '\0' ' ' 2>/dev/null <"/proc/$spid/cmdline") || cmd=
      if [[ $cmd == *" serve "*"--socket $SOCK"* ]]; then
        kids=$(ps -o pid= --ppid "$spid" | tr -d ' ')
        kill -TERM "$spid"
        for _ in $(seq 1 300); do kill -0 "$spid" 2>/dev/null || break; sleep 0.1; done
        echo "stopped mini serve $spid (children: $kids)"
      fi
    fi
    sleep 1
    echo "--- processes naming the run directory after cleanup:"
    ps -eo pid,args | grep -F "$RUN" | grep -v -e grep -e discord-entrance.sh || echo none
  } >>"$LOG/cleanup.txt" 2>&1
}
trap cleanup EXIT

# row WHO USER_ID COMMAND EXPECT LINE-or-@file [--corrupt-signature] [--id ID]
#   EXPECT: 401 | now (type 4) | deferred (type 5, then a PATCH) | pong
row() {
  local who=$1 user=$2 command=$3 expect=$4 line=$5; shift 5
  local extra=() id
  N=$((N + 1)); id=$((5000 + N))
  while [[ $# -gt 0 ]]; do
    case $1 in --corrupt-signature) extra+=(--corrupt-signature) ;; --id) id=$2; shift ;; esac
    shift
  done
  local name; name=$(printf '%02d-%s' "$N" "$who")
  local token="tok-$N"
  local lineopt=()
  if [[ $line == @* ]]; then lineopt=(--line-file "${line#@}"); elif [[ -n $line ]]; then lineopt=(--line "$line"); fi
  local s e http type ack fs=- answer verdict=ok
  s=$(date +%s.%N)
  if [[ $expect == pong ]]; then
    "$FAKE" ping "127.0.0.1:$PORT" "$RUN/etc/app.secret" >"$LOG/$name.response" 2>"$LOG/$name.stderr"
  else
    "$FAKE" interact "127.0.0.1:$PORT" "$RUN/etc/app.secret" "$APP" "$user" "$id" "$token" "$command" \
      "${lineopt[@]}" "${extra[@]}" >"$LOG/$name.response" 2>"$LOG/$name.stderr"
  fi
  e=$(date +%s.%N)
  ack=$(awk -v a="$s" -v b="$e" 'BEGIN{printf "%.3f", b-a}')
  http=$(sed -n '1s/^HTTP //p' "$LOG/$name.response")
  sed -n '2,$p' "$LOG/$name.response" >"$LOG/$name.body"
  type=$(jq -r '.type // "-"' "$LOG/$name.body" 2>/dev/null || echo -)
  answer=$(head -c 300 "$LOG/$name.body" | tr '\n' ' ')
  case $expect in
    401) [[ $http == 401 ]] || verdict=FAIL ;;
    pong) [[ $http == 200 && $type == 1 ]] || verdict=FAIL ;;
    now) [[ $http == 200 && $type == 4 ]] || verdict=FAIL
         answer=$(jq -r .data.content "$LOG/$name.body") ;;
    deferred)
      [[ $http == 200 && $type == 5 ]] || verdict=FAIL
      local f=$RUN/api/followup-$token.json
      for _ in $(seq 1 1200); do [[ -s $f ]] && break; sleep 0.05; done
      if [[ -s $f ]]; then
        fs=$(awk -v a="$s" -v b="$(date +%s.%N)" 'BEGIN{printf "%.3f", b-a}')
        cp "$f" "$LOG/$name.followup.json"
        answer=$(jq -r .content "$f")
      else
        verdict=FAIL answer="no follow-up within 60 s"
      fi ;;
  esac
  printf '%s\n' "$answer" >"$LOG/$name.answer"
  [[ $verdict == ok ]] || FAILS=$((FAILS + 1))
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$who" "/$command" "$(printf '%s' "$line" | cut -c1-70)" \
    "$expect" "$http" "$type" "$ack" "$fs" "$verdict" "$(printf '%s' "$answer" | tr '\n\t' '  ' | cut -c1-240)" >>"$TABLE"
  printf '%3s %-8s /%-9s %-50.50s %-8s http=%s type=%s ack=%ss fu=%ss %s\n' "$N" "$who" "$command" "$line" "$expect" "$http" "$type" "$ack" "$fs" "$verdict"
  LAST=$LOG/$name
}

check() { # description, command...
  local desc=$1; shift
  N=$((N + 1))
  local v=ok
  "$@" >>"$LOG/checks.log" 2>&1 || { v=FAIL; FAILS=$((FAILS + 1)); }
  printf '%s\tcheck\t-\t%s\t-\t-\t-\t-\t-\t%s\t-\n' "$N" "$desc" "$v" >>"$TABLE"
  printf '%3s check    %s %s\n' "$N" "$desc" "$v"
}

# ------------------------------------------------------------------- setup
echo "run: $RUN"
sh "$REPO/native/resource-client/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$R" \
  >"$LOG/bootstrap.stdout" 2>"$LOG/bootstrap.stderr" || { echo 'bootstrap failed' >&2; exit 1; }
[[ -S $SOCK ]] || { echo 'no socket after bootstrap' >&2; exit 1; }
mkdir -m 700 "$RUN/sessions/ember" "$RUN/sessions/friend"
jq -n --arg s "$SPONSOR_ID" --arg f "$FRIEND_ID" '{version: 1, users: {($s): "ember", ($f): "friend"}}' >"$RUN/etc/discord-roster.json"
chmod 0644 "$RUN/etc/discord-roster.json"
PUB=$("$FAKE" keygen "$RUN/etc/app.secret")
cat >"$RUN/etc/discord.env" <<EOF
MINI_DISCORD_APPLICATION_ID=$APP
MINI_DISCORD_PUBLIC_KEY=$PUB
MINI_DISCORD_LISTEN=127.0.0.1:$PORT
MINI_DISCORD_ROSTER=$RUN/etc/discord-roster.json
MINI_DISCORD_ROSTER_OWNER_UID=$(id -u)
MINI_DISCORD_API_BASE=http://127.0.0.1:$API_PORT/api/v10
MINI_DISCORD_SPOOL=$RUN/spool
MINI_SHELL_WRAPPER=$RUN/bin/mini-shell-ssh
MINI_CLIENT=$MINI
MINI_HOST=$HOST
MINI_CONFIG=$CONFIG
MINI_SOCKET=$SOCK
MINI_SESSIONS=$RUN/sessions
MINI_SPONSOR=ember
MINI_SPONSOR_WORKSPACE=$R/sponsor
EOF
chmod 0600 "$RUN/etc/discord.env"
setsid "$FAKE" api "127.0.0.1:$API_PORT" "$RUN/api" >"$LOG/fake-api.log" 2>&1 </dev/null &
API_PID=$!
setsid env -i PATH=/usr/bin:/bin bash -c "set -a; . '$RUN/etc/discord.env'; exec '$RUN/bin/mini-discord'" \
  >"$LOG/mini-discord.log" 2>&1 </dev/null &
ENTRANCE_PID=$!
for _ in $(seq 1 100); do
  ss -ltn | awk '{print $4}' | grep -q "127.0.0.1:$PORT\$" && ss -ltn | awk '{print $4}' | grep -q "127.0.0.1:$API_PORT\$" && break
  sleep 0.1
done
echo "mini-discord pid $ENTRANCE_PID, fake api pid $API_PID"

# ------------------------------------------------------------------- rows
row discord PING pong pong ""
row sponsor "$SPONSOR_ID" mini 401 "refs" --corrupt-signature
row stranger "$STRANGER_ID" mini now "refs"
row friend "$FRIEND_ID" mini deferred "keygen k1"
check "k1 secret and public key exist only in the friend's session home" \
  bash -c "[[ -f '$RUN/sessions/friend/keys/k1' && -f '$RUN/sessions/friend/keys/k1.pub' && ! -e '$RUN/sessions/ember/keys/k1' ]]"
row sponsor "$SPONSOR_ID" mini deferred "refs"
REFS=$LOG/$(printf '%02d' "$N")-sponsor.followup.json
jq -r .content "$REFS" | sed '1d;$d' >"$LOG/sponsor-refs.json"
TARGET=$(jq -r '.references[] | select(.name == "factory") | .target' "$LOG/sponsor-refs.json")
CAP=$(jq -r '.references[] | select(.name == "factory") | .observeCapability' "$LOG/sponsor-refs.json")
check "sponsor refs lists factory (target $TARGET)" bash -c "[[ -n '$TARGET' && '$TARGET' != null ]]"
row sponsor "$SPONSOR_ID" mini deferred "read nope"
row friend "$FRIEND_ID" mini deferred "init k1 4242424242"
row friend "$FRIEND_ID" mini deferred "import stolen object $TARGET $CAP"
row friend "$FRIEND_ID" mini deferred "read stolen"
check "friend's read of the sponsor's cell is the Host's refusal, verbatim" \
  bash -c "grep -q '^refused: unknown-key: ' '$LAST.answer'"
printf 'read %s\n' "$(head -c 996 /dev/zero | tr '\0' x)" >"$LOG/long-line.txt"
row friend "$FRIEND_ID" mini now "@$LOG/long-line.txt"
row friend "$FRIEND_ID" mini-help deferred ""
ID_REPLAY=$((9000))
row sponsor "$SPONSOR_ID" mini deferred "whoami" --id "$ID_REPLAY"
row sponsor "$SPONSOR_ID" mini 401 "whoami" --id "$ID_REPLAY"

# stream -> channel mirror (runner), over the same door
row sponsor "$SPONSOR_ID" mini deferred 'create shared declared {"type":"all","predicates":[]}'
row sponsor "$SPONSOR_ID" mini deferred "invoke w1 shared create 2 1"
row sponsor "$SPONSOR_ID" mini deferred "submit w1"
mirror() {
  env -i PATH=/usr/bin:/bin MINI_MIRROR_REF=shared \
    MINI_MIRROR_WEBHOOK_URL="http://127.0.0.1:$API_PORT/api/webhooks/1400000000000000777/chan-secret" \
    MINI_MIRROR_HOME="$RUN/sessions/ember" MINI_MIRROR_WORKSPACE="$R/sponsor" MINI_DISCORD_SPOOL="$RUN/spool" \
    MINI_SHELL_WRAPPER="$RUN/bin/mini-shell-ssh" MINI_CLIENT="$MINI" MINI_HOST="$HOST" MINI_CONFIG="$CONFIG" MINI_SOCKET="$SOCK" \
    "$RUN/bin/mini-discord-mirror" --once
}
mirror >"$LOG/mirror-1.out" 2>&1; rc=$?
check "mirror poll 1 (exit $rc) posted field 2 = 1" bash -c "ls '$RUN/api'/channel-chan-secret-*.json | wc -l | grep -qx 1 && jq -r .content '$RUN/api'/channel-chan-secret-*.json | grep -qx 'field 2 = 1'"
row sponsor "$SPONSOR_ID" mini deferred "invoke w2 shared write 2 7 1"
row sponsor "$SPONSOR_ID" mini deferred "submit w2"
mirror >"$LOG/mirror-2.out" 2>&1; rc=$?
check "mirror poll 2 (exit $rc) posted field 2 = 7 (was 1)" bash -c "ls '$RUN/api'/channel-chan-secret-*.json | wc -l | grep -qx 2 && cat '$RUN/api'/channel-chan-secret-*.json | jq -r .content | grep -qx 'field 2 = 7 (was 1)'"
mirror >"$LOG/mirror-3.out" 2>&1; rc=$?
check "mirror poll 3 (exit $rc) posted nothing new" bash -c "ls '$RUN/api'/channel-chan-secret-*.json | wc -l | grep -qx 2 && grep -q 'posted 0 change' '$LOG/mirror-3.out'"
for f in "$RUN"/api/channel-*.json; do cp "$f" "$LOG/"; done

# ------------------------------------------------------------------- logs
check "every run line and every rostered refusal is in its session's discord.log" \
  bash -c "[[ \$(wc -l <'$RUN/sessions/friend/discord.log') == 6 && \$(wc -l <'$RUN/sessions/ember/discord.log') == 8 ]]"
check "no interaction token or channel webhook secret appears in the entrance log" \
  bash -c "! grep -q 'tok-\|chan-secret' '$LOG/mini-discord.log'"
check "the spool is empty (every follow-up body removed)" bash -c "[[ -z \$(ls -A '$RUN/spool') ]]"
cp "$RUN/sessions/friend/discord.log" "$LOG/friend-discord.log"
cp "$RUN/sessions/ember/discord.log" "$LOG/ember-discord.log"
cp "$RUN/api/requests.log" "$LOG/fake-api-requests.log"
echo "rows: $N, failed: $FAILS"
echo "$FAILS" >"$LOG/fails"
[[ $FAILS == 0 ]]
