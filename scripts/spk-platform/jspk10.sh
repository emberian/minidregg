#!/bin/sh
# J-SPK-10: WebSockets through the grain route. A socket is ONE admitted Mini
# dispatch (the open, method WEBSOCKET, a streamed dispatch); its frames are
# opaque bytes in the admitted session and write nothing; the size class caps
# open sockets per grain and bytes per minute per socket. Every row is decided
# by an artifact (a JSON field the client printed, a record count, an HTTP
# status), never by an exit status alone.
#
#   jspk10.sh run RUN_ROOT t1|t2|t3   one Store's rows, in order
#   jspk10.sh rows RUN_ROOT ROW...    named rows against RUN_ROOT (resumable)
#
# Store t1 (app 7801, sntfy, class S, api route):
#   (a) subscribe /m6grain/ws, publish by POST, the socket delivers it; the
#       open adds exactly one dispatch record, the frames none;
#   (e) one flooder is cut at the class byte cap, named in the resident's
#       journal; four bystanders still receive; burst frames/s and bytes/s;
#   (f) STOP with a socket open: the socket closes; continue; a new open is
#       one new record in the new generation.
# Store t2 (app 7901, EtherCalc, class S, web route):
#   (b) two sockets on one sheet: an edit on one appears on the other;
#   (d) 32 sockets open and joined, the 33rd refused `wsConcurrencyCap`
#       before Mini (no record), all 32 alive; memory and open latency.
# Store t3 (app 8001, Simple Todos, class M, web route):
#   (c) DDP over /websocket: `connected`, a todo inserted by the UI's DDP
#       method lands (a second socket's subscription sees it).
#
# Runs as the Store operator (the broker must be serving). Environment: BIN,
# GRAINS_ROOT, UNIT_PREFIX as grain-journey.sh; SPK_NTFY, SPK_ETHERCALC,
# SPK_TODOS name the packages.
set -eu
umask 077

usage() { sed -n '2,32p' "$0" >&2; exit 2; }
[ "$#" -ge 2 ] || usage
MODE=$1 ROOT=$2
shift 2
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
BIN=${BIN:-/usr/local/libexec/minidregg}
SPK_HOST=$BIN/spk-host
GRAINS_ROOT=${GRAINS_ROOT:-/var/lib/mini/grains}
J=$HERE/grain-journey.sh
WSC="python3 $HERE/jspk10-ws.py"
ROWS=$ROOT/rows.tsv
OUT=$ROOT/rows
export BIN GRAINS_ROOT

[ "$(id -u)" != 0 ] || { echo "jspk10: run as the Store operator, not root" >&2; exit 2; }
mkdir -p -m 700 "$ROOT" "$OUT"

now() { date +%s; }
row() {
  name=$1; shift
  t0=$(now)
  set +e
  (set -e; "$@") >"$OUT/$name.out" 2>"$OUT/$name.err"
  rc=$?
  set -e
  t1=$(now)
  detail=$(tail -n 1 "$OUT/$name.out" | tr '\t' ' ')
  verdict=PASS
  if [ "$rc" != 0 ]; then
    verdict=FAIL
    detail="exit $rc: $(tail -n 1 "$OUT/$name.err" | tr '\t' ' ') | $detail"
  fi
  printf '%s\t%s\t%ss\t%s\n' "$name" "$verdict" "$((t1 - t0))" "$detail" >>"$ROWS"
  [ "$verdict" = PASS ] || { echo "jspk10: row $name failed: $detail" >&2; exit 1; }
}

ALL='{"type":"allAccess"}'
t1() { GRAIN_A=78 CLASS_A=S KIND_A=api SPK_A=$SPK_NTFY "$J" phase "$ROOT/t1" "$@"; }
t2() { GRAIN_A=79 CLASS_A=S KIND_A=web SPK_A=$SPK_ETHERCALC GET_PATH_A=/ ROLE_BASIS_A=$ALL \
  "$J" phase "$ROOT/t2" "$@"; }
t3() { GRAIN_A=80 CLASS_A=M KIND_A=web SPK_A=$SPK_TODOS GET_PATH_A=/ ROLE_BASIS_A=$ALL \
  "$J" phase "$ROOT/t3" "$@"; }
profile_of() {
  for p in "$GRAINS_ROOT"/*/host/grain-host.json; do
    [ -r "$p" ] || continue
    if [ "$(jq -r .miniConfig "$p")" = "$ROOT/$1/store/base/workroom/deployment/pinned-config.json" ]; then
      echo "$p"; return 0
    fi
  done
  return 1
}
status() { "$SPK_HOST" grain status "$(profile_of "$1")" "$2"; }
running_gen() { status "$1" "$2" | jq -er '[.runs[] | select(.state == "running")][-1].generation'; }
running_unit() { status "$1" "$2" | jq -er '[.runs[] | select(.state == "running")][-1].unit'; }
route() { echo "$(dirname "$(profile_of "$1")")/apps/$2/routes/owner-$3"; }
journal() { echo "$(dirname "$(profile_of "$1")")/apps/$2/g$(running_gen "$1" "$2")"; }

r_get() { "$1" "$2" >/dev/null; tail -n 1 "$ROOT/$1/evidence/$2.stdout"; [ "$(tail -n 1 "$ROOT/$1/evidence/$2.stdout")" = 200 ]; }

# (f): a socket held across STOP. It must end (EOF or a close frame) while
# the STOP runs, and the STOP completes.
r_stop_close() {
  marker=$OUT/hold.open
  rm -f "$marker"
  $WSC hold "$(route t1 7801 api)" m6grain "$marker" >"$OUT/hold.json" 2>"$OUT/hold.err" &
  hold=$!
  tick=0
  until [ -s "$marker" ]; do
    tick=$((tick + 1)); [ "$tick" -lt 900 ] || { echo "hold socket never opened" >&2; kill "$hold"; exit 1; }
    sleep 1
  done
  echo "holding: $(cat "$marker")"
  started=$(date +%s.%N)
  t1 stop-a >/dev/null
  stopped=$(date +%s.%N)
  wait "$hold"
  cat "$OUT/hold.json"
  closed=$(jq -r .closedAt "$OUT/hold.json")
  jq -e '.end | test("^(eof|close frame)")' "$OUT/hold.json" >/dev/null
  echo "$started $closed $stopped" | awk '{ if (!($1 <= $2 && $2 <= $3)) exit 1 }'
  echo "STOP began $started, socket ended $closed ($(jq -r .end "$OUT/hold.json")), STOP completed $stopped; $(tail -n 1 "$ROOT/t1/evidence/stop-a.stdout" | jq -c '{generation, activeState, elapsedMs}')"
}

run_row() {
  case "$1" in
    t[123]-store) s=${1%-store}; row "$1" "$s" store services workroom profile ;;
    t[123]-birth-a|t[123]-install-a|t[123]-share-a|t[123]-start-a|t[123]-enroll-a|t[123]-stop-a|t1-start-a2|t1-enroll-a2|t1-stop-a2)
      s=${1%%-*}; row "$1" "$s" "${1#*-}" ;;
    t[123]-get-a) s=${1%%-*}; row "$1" r_get "$s" get-a ;;
    t1-ws-deliver) row "$1" $WSC ntfy "$(route t1 7801 api)" "$(journal t1 7801)" m6grain ;;
    t1-ws-flood) row "$1" $WSC flood "$(route t1 7801 api)" "$(journal t1 7801)" m6grain 4 "$(running_unit t1 7801)" ;;
    t1-ws-stop) row "$1" r_stop_close ;;
    t1-ws-deliver2) row "$1" $WSC ntfy "$(route t1 7801 api)" "$(journal t1 7801)" m6grain ;;
    t2-ws-coedit) row "$1" $WSC ethercalc "$(route t2 7901 web)" "$(journal t2 7901)" wsroom ;;
    t2-ws-caps) row "$1" $WSC caps "$(route t2 7901 web)" "$(journal t2 7901)" caproom 32 "$(running_unit t2 7901)" ;;
    t3-ws-ddp) row "$1" $WSC meteor "$(route t3 8001 web)" "$(journal t3 8001)" ;;
    *) echo "unknown row $1" >&2; exit 2 ;;
  esac
}

T1="t1-store t1-birth-a t1-install-a t1-share-a t1-start-a t1-enroll-a t1-get-a t1-ws-deliver
  t1-ws-flood t1-ws-stop t1-start-a2 t1-enroll-a2 t1-ws-deliver2 t1-stop-a2"
T2="t2-store t2-birth-a t2-install-a t2-share-a t2-start-a t2-enroll-a t2-get-a t2-ws-coedit
  t2-ws-caps t2-stop-a"
T3="t3-store t3-birth-a t3-install-a t3-share-a t3-start-a t3-enroll-a t3-get-a t3-ws-ddp t3-stop-a"

case "$MODE" in
  run)
    case "${1:-}" in t1) set -- $T1 ;; t2) set -- $T2 ;; t3) set -- $T3 ;; *) usage ;; esac
    for r in "$@"; do run_row "$r"; done
    s=${1%%-*}
    "$J" stop-services "$ROOT/$s" >/dev/null 2>&1 || : ;;
  rows)
    for r in "$@"; do run_row "$r"; done ;;
  *) usage ;;
esac
echo "$ROWS"
