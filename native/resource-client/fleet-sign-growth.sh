#!/bin/sh
# Fleet-turn cost as the Store grows: one `mini fleet-sign` profile commits
# TURNS turns in sequence (sends and transfers alternating) on a fresh Store.
# At each level in LEVELS the Host is stopped and served again, and the cold
# reopen is timed to the first answered request (an exact receipt lookup).
# VERBS=transfer commits transfers only (the fleet-turn cost without one
# stream's growth); the default alternates sends on ONE topic with transfers.
# After the last turn one send goes to a fresh topic, as the control for the
# stream's share of a send.
#
# usage: fleet-sign-growth.sh HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY [TURNS] [LEVELS]
set -eu
umask 077
[ "$#" -ge 5 ] || { echo "usage: $0 HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY [TURNS] [LEVELS]" >&2; exit 2; }
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 ROOT=$5 TURNS=${6:-1000} LEVELS=${7:-"10 100 1000"}
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
case "$ROOT" in /*) ;; *) echo 'path must be absolute' >&2; exit 2;; esac
[ ! -e "$ROOT" ] || { echo 'directory already exists' >&2; exit 2; }
mkdir -m 700 "$ROOT"
OUT="$ROOT/evidence"; mkdir -m 700 "$OUT" "$OUT/turns"
FIX="$ROOT/fixture"
SERVER_PID=
stop_server() {
  if [ -n "$SERVER_PID" ] && kill -0 "$SERVER_PID" 2>/dev/null; then
    kill "$SERVER_PID" 2>/dev/null || true
    i=0; while kill -0 "$SERVER_PID" 2>/dev/null && [ "$i" -lt 100 ]; do i=$((i + 1)); sleep 0.1; done
  fi
  SERVER_PID=
}
trap stop_server EXIT INT TERM
now() { date +%s.%N; }
elapsed() { awk -v a="$1" -v b="$2" 'BEGIN { printf "%.3f", b - a }'; }
serve() {
  nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" >"$1" 2>&1 </dev/null &
  SERVER_PID=$!
  i=0
  until grep -q '^mini: serving ' "$1" 2>/dev/null; do
    kill -0 "$SERVER_PID" 2>/dev/null || { echo 'Mini server exited' >&2; exit 1; }
    i=$((i + 1)); [ "$i" -lt 36000 ] || { echo 'Mini server not ready' >&2; exit 1; }
    sleep 0.1
  done
}

"$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$FIX" \
  >"$OUT/fixture.stdout" 2>"$OUT/fixture.stderr"
SERVER_PID=$(cat "$FIX/public/server.pid")
CONFIG="$FIX/deployment/pinned-config.json"
SOCKET="$FIX/public/mini.sock"
export MINI_FLEET_HOME="$ROOT/fleet-home" MINI_FLEET_SPONSOR="$FIX/sponsor"
"$MINI" fleet-sign join --profile alpha --fund 20000 >"$OUT/join-alpha.json" 2>"$OUT/join-alpha.stderr"
"$MINI" fleet-sign join --profile bravo --fund 100 >"$OUT/join-bravo.json" 2>"$OUT/join-bravo.stderr"
B=$(jq -er .cell "$OUT/join-bravo.json")

T="$OUT/turns.tsv"; R="$OUT/reopen.tsv"
printf 'n\tverb\tseconds\treplans\tchain_index\n' >"$T"
printf 'level\tchain_index\tserve_ready_s\tfirst_receipt_s\tstore_bytes\n' >"$R"
n=1
while [ "$n" -le "$TURNS" ]; do
  f="$OUT/turns/$n.json"
  t0=$(now)
  if [ "${VERBS:-mixed}" != transfer ] && [ $((n % 2)) -eq 1 ]; then verb=send
    "$MINI" fleet-sign send --profile alpha --topic growth "turn $n" >"$f" 2>"$f.stderr"
  else verb=transfer
    "$MINI" fleet-sign transfer --profile alpha --to "$B" --amount 1 >"$f" 2>"$f.stderr"
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$n" "$verb" "$(elapsed "$t0" "$(now)")" \
    "$(jq -r .replans "$f")" "$(jq -r .chain_index "$f")" >>"$T"
  for level in $LEVELS; do
    if [ "$n" -eq "$level" ]; then
      TX=$(jq -er .turn_hash "$f")
      stop_server
      t0=$(now)
      serve "$FIX/public/serve-$level.log"
      t1=$(now)
      "$MINI" fleet-sign receipt --profile alpha --turn-hash "$TX" >"$OUT/reopen-$level.json" 2>"$OUT/reopen-$level.stderr"
      t2=$(now)
      printf '%s\t%s\t%s\t%s\t%s\n' "$level" "$(jq -r .chain_index "$f")" "$(elapsed "$t0" "$t1")" \
        "$(elapsed "$t1" "$t2")" "$(du -sb "$FIX/store" | cut -f1)" >>"$R"
    fi
  done
  n=$((n + 1))
done
t0=$(now)
"$MINI" fleet-sign send --profile alpha --topic fresh "control" >"$OUT/control-fresh-topic.json" 2>"$OUT/control-fresh-topic.stderr"
printf 'control-fresh-topic\tsend\t%s\t%s\t%s\n' "$(elapsed "$t0" "$(now)")" \
  "$(jq -r .replans "$OUT/control-fresh-topic.json")" "$(jq -r .chain_index "$OUT/control-fresh-topic.json")" >>"$T"
stop_server
sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" >"$OUT/binaries.sha256"
printf '%s\n' "$OUT"
