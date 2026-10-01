#!/bin/sh
# J-SPK-1: robust SPK hosting on one host, as the Store operator, through the
# root broker. Every row is decided by an artifact (a JSON field, a /proc
# line, a systemd property, an HTTP body), never by an exit status alone.
#
#   jspk1.sh all RUN_ROOT          every row below, in order
#   jspk1.sh rows RUN_ROOT ROW...  named rows against RUN_ROOT (resumable)
#
# Store 1 (RUN_ROOT/s1): grain a (app 7101, class S) is installed through the
#   broker, started, checked under the floor, reached, written to; its
#   resident is killed with SIGKILL and the supervisor STOPs that generation
#   and continues the next; the message survives; a live backup is frozen;
#   STOP; export bound to the STOP receipt; a is continued again.
# Store 2 (RUN_ROOT/s2): grain a (app 7101 again) imports Store 1's export
#   into its own volume, and its START is refused by the broker because Mini's
#   resident unit name carries no Store identity (K-SPK); grain c (app 7301)
#   refuses a tampered export, imports the real one and serves Store 1's
#   message; grain b (app 7201, class M) runs beside it. All three Stores'
#   grains run side by side.
#
# Runs as the Store operator, never root (the broker must be serving).
# Environment: BIN SPK GRAINS_ROOT (as grain-journey.sh), UNIT_PREFIX (the
# broker's unit prefix, default mini). Hook contract (journey.sh): exit 0
# only when every row passes; the last stdout line is the rows file; stderr's
# last line is the first failing row.
set -eu
umask 077

usage() { sed -n '2,27p' "$0" >&2; exit 2; }
[ "$#" -ge 2 ] || usage
MODE=$1 ROOT=$2
shift 2
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
BIN=${BIN:-/usr/local/libexec/minidregg}
SPK_HOST=$BIN/spk-host
GRAINS_ROOT=${GRAINS_ROOT:-/var/lib/mini/grains}
PREFIX=${UNIT_PREFIX:-mini}
J=$HERE/grain-journey.sh
ROWS=$ROOT/rows.tsv
OUT=$ROOT/rows
export BIN GRAINS_ROOT

[ "$(id -u)" != 0 ] || { echo "jspk1: run as the Store operator, not root" >&2; exit 2; }
mkdir -p -m 700 "$ROOT" "$OUT"

now() { date +%s; }
# row NAME CMD...: run CMD, keep its output, record PASS/FAIL and the last
# stdout line (the artifact) in rows.tsv. A failing row stops the run.
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
    detail="exit $rc: $(tail -n 1 "$OUT/$name.err" | tr '\t' ' ')"
  fi
  printf '%s\t%s\t%ss\t%s\n' "$name" "$verdict" "$((t1 - t0))" "$detail" | tee -a "$ROWS"
  [ "$verdict" = PASS ] || { echo "jspk1: row $name failed: $detail" >&2; exit 1; }
}

s1() { GRAIN_A=71 CLASS_A=S "$J" phase "$ROOT/s1" "$@"; }
s2() { GRAIN_A=71 GRAIN_B=72 GRAIN_C=73 CLASS_A=S CLASS_B=M CLASS_C=S \
  IMPORT_A=${IMPORT_A:-} IMPORT_C=${IMPORT_C:-} IMPORT_KEY=${IMPORT_KEY:-} \
  "$J" phase "$ROOT/s2" "$@"; }
profile_of() { ls "$GRAINS_ROOT"/*/host/grain-host.json 2>/dev/null |
  while read -r p; do
    [ "$(jq -r .miniConfig "$p")" = "$1/store/base/workroom/deployment/pinned-config.json" ] &&
      echo "$p"
  done; }
P1() { profile_of "$ROOT/s1"; }
P2() { profile_of "$ROOT/s2"; }
status() { "$SPK_HOST" grain status "$1" "$2"; }
running_unit() { status "$1" "$2" | jq -er '[.runs[] | select(.state == "running")][-1].unit'; }
broker_raw() { python3 -c '
import socket, sys
s = socket.socket(socket.AF_UNIX); s.connect("/run/mini-spk-broker.sock")
s.sendall(sys.argv[1].encode() + b"\n"); s.shutdown(socket.SHUT_WR)
print(s.recv(65536).decode())' "$1"; }

# ---- rows -------------------------------------------------------------------

r_identity() {
  echo "client uid=$(id -u) user=$(id -un) groups=$(id -Gn)"
  [ "$(id -u)" != 0 ]
  ls -l /run/mini-spk-broker.sock
  stat -c '%U:%G %a' /run/mini-spk-broker.sock | grep -qx 'root:[^ ]* 660'
  echo "operator $(id -un) is not root; broker socket root-owned 0660"
}

r_refusals() {
  for req in '{"verb":"exec","command":"sh"}' \
      '{"verb":"install-unit","store":"0123456789abcdef","app":"7","generation":"2","unitText":"[Service]\nExecStart=/bin/sh"}' \
      '{"verb":"stop","unit":"sshd.service"}' \
      '{"verb":"place","store":"../../../../etc","app":"1"}' \
      '{"verb":"start","unit":"mini-spk-a9101-g2.service"}'; do
    reply=$(broker_raw "$req")
    echo "$req -> $reply"
    printf '%s' "$reply" | jq -e '.ok == false' >/dev/null
  done
  echo "5/5 out-of-protocol requests refused with a reason"
}

# r_floor s1|s2 X: the floor probe for instance X of that Store.
r_floor() {
  "$1" "floor-$2" >/dev/null
  cat "$ROOT/$1/evidence/floor-$2.stdout"
}

r_limits() {
  profile=$1 app=$2 class=$3
  unit=$(running_unit "$profile" "$app")
  slice=$(systemctl show "$unit" --property=Slice --value)
  cg=$(systemctl show "$unit" --property=ControlGroup --value)
  limits=$(systemctl show "$slice" --property=MemoryMax,CPUWeight,TasksMax,IOWeight | tr '\n' ' ')
  echo "unit=$unit slice=$slice cgroup=$cg"
  echo "systemctl: $limits"
  mem=$(cat "/sys/fs/cgroup${cg%/*}/memory.max")
  echo "cgroup memory.max=$mem pids.max=$(cat "/sys/fs/cgroup${cg%/*}/pids.max")"
  case "$class" in
    S) want_mem=536870912 want="MemoryMax=536870912 CPUWeight=50 TasksMax=256 IOWeight=50" ;;
    M) want_mem=1073741824 want="MemoryMax=1073741824 CPUWeight=100 TasksMax=512 IOWeight=100" ;;
  esac
  for item in $want; do printf '%s' "$limits" | grep -q "$item" || { echo "missing $item" >&2; exit 1; }; done
  [ "$mem" = "$want_mem" ]
  case "$cg" in */"$PREFIX"-grains.slice/"$slice"/"$unit") ;; *) echo "cgroup path" >&2; exit 1 ;; esac
  echo "class $class limits hold on $slice ($want)"
}

r_kill() {
  profile=$1 app=$2
  unit=$(running_unit "$profile" "$app")
  gen=$(status "$profile" "$app" | jq -er '[.runs[] | select(.state == "running")][-1].generation')
  pid=$(systemctl show "$unit" --property=MainPID --value)
  store=$(jq -r .stateRoot "$profile" | awk -F/ '{print $(NF-1)}')
  sup=$PREFIX-spk-supervisor@$store-$app.service
  echo "killing resident pid=$pid unit=$unit generation=$gen (uid $(stat -c %u /proc/$pid))"
  killed=$(date +%s.%N)
  kill -9 "$pid"
  # The supervisor starts on the unit's failure (OnFailure=).
  tick=0
  until [ "$(systemctl show "$sup" --property=ActiveState --value)" = activating ] ||
      [ "$(systemctl show "$sup" --property=ActiveState --value)" = active ] ||
      [ -n "$(systemctl show "$sup" --property=ExecMainStartTimestampMonotonic --value | grep -v '^0$')" ]; do
    tick=$((tick + 1)); [ "$tick" -lt 600 ] || { echo "supervisor never started" >&2; exit 1; }
    sleep 0.1
  done
  activated=$(date +%s.%N)
  echo "unit after kill: $(systemctl show "$unit" --property=ActiveState,Result,InvocationID | tr '\n' ' ')"
  echo "supervisor $sup activated $(echo "$activated - $killed" | bc)s after SIGKILL"
  # Wait for the supervisor to STOP the dead generation and continue the next.
  tick=0
  while :; do
    st=$(systemctl show "$sup" --property=ActiveState,Result,NRestarts --value | tr '\n' ' ')
    new=$(status "$profile" "$app" | jq -r '[.runs[] | select(.state == "running")][-1].generation // empty')
    if [ -n "$new" ] && [ "$new" -gt "$gen" ] &&
        [ "$(systemctl show "$(running_unit "$profile" "$app")" --property=ActiveState --value)" = active ]; then
      break
    fi
    case "$st" in failed*) echo "supervisor failed: $st" >&2; exit 1 ;; esac
    tick=$((tick + 1)); [ "$tick" -lt 720 ] || { echo "no new generation in 2h" >&2; exit 1; }
    sleep 10
  done
  done_at=$(date +%s.%N)
  status "$profile" "$app" | jq -c '[.runs[] | {generation, state, unit, unitActiveState}]'
  journalctl --no-pager -o cat -u "$sup" 2>/dev/null | tail -n 3 || :
  echo "generation $gen killed -> supervisor STOP + continue -> generation $new active $(echo "$done_at - $killed" | bc)s after SIGKILL (supervisor activation $(echo "$activated - $killed" | bc)s)"
}

r_poll() {
  store=$1 phase=$2 want=$3
  "$store" "$phase" >/dev/null
  body=$ROOT/$store/evidence/$phase-body.body
  head -c 400 "$body"; echo
  grep -q "\"message\":\"$want\"" "$body"
  echo "poll returned \"$want\" through $(grep -c . "$body") line(s)"
}

r_backup() {
  "$SPK_HOST" grain backup "$(P1)" >"$OUT/backup.json"
  jq -c '.grains[] | {name, state, frozenMs, sha256, e2fsck, rootListing: (.rootListing | length)}' "$OUT/backup.json"
  key1=$(jq -r .stateRoot "$(P1)" | awk -F/ '{print $(NF-1)}')
  jq -r --arg n "$key1-7101" '.grains[] | select(.name == $n) | .rootListing[]' "$OUT/backup.json"
  jq -e --arg n "$key1-7101" '.grains[] | select(.name == $n) |
    .state == "running-frozen-crash-consistent" and .e2fsck == "clean" and
    ([.rootListing[] | select(test("lost\\+found| \\.$| \\.\\.$") | not)] | length > 0)' \
    "$OUT/backup.json" >/dev/null
  echo "backup of the RUNNING grain $key1-7101: frozen copy, e2fsck clean, /var listed without mounting"
}

r_export() {
  rm -rf "$ROOT/export-a"
  "$SPK_HOST" grain export "$(P1)" 7101 "$ROOT/export-a" >"$OUT/export.json"
  jq -c . "$OUT/export.json"
  jq -e '.stopGeneration // true' "$ROOT/export-a/manifest.json" >/dev/null
  jq -c '{app, class, stopGeneration, image, stopReceiptSha256,
    stopAccepted: .stopReceipt.receipt.acceptedCount}' "$ROOT/export-a/manifest.json"
  echo "export of 7101 bound to STOP receipt $(jq -r .stopReceiptSha256 "$ROOT/export-a/manifest.json"), signed by $(cat "$ROOT/export-a/exporter.pub")"
}

r_tamper() {
  rm -rf "$ROOT/export-tampered"
  cp -a "$ROOT/export-a" "$ROOT/export-tampered"
  python3 - "$ROOT/export-tampered/var.ext4" <<'EOF'
import sys
with open(sys.argv[1], "r+b") as f:
    f.seek(1024 + 120); b = f.read(1); f.seek(1024 + 120); f.write(bytes([b[0] ^ 1]))
EOF
  set +e
  (r_install_import c "$ROOT/export-tampered") >/dev/null
  rc=$?
  set -e
  [ "$rc" != 0 ]
  cat "$ROOT/s2/evidence/install-c.stderr"
  grep -q "image bytes differ from the signed manifest" "$ROOT/s2/evidence/install-c.stderr"
  [ ! -e "$(dirname "$(P2)")/apps/7301/placement.json" ]
  mv "$ROOT/s2/evidence/install-c.stderr" "$OUT/tamper-install-c.stderr"
  echo "one flipped byte refused before any Mini or broker effect (no placement for 7301)"
}

# r_install_import LETTER EXPORT_DIR: Store 2 installs instance LETTER from
# an export, trusting Store 1's completion custodian key.
r_install_import() {
  IMPORT_KEY=$(cat "$ROOT/export-a/exporter.pub")
  upper=$(printf '%s' "$1" | tr a-c A-C)
  eval "IMPORT_$upper=\$2"
  export IMPORT_KEY "IMPORT_$upper"
  s2 "install-$1"
  jq -c '{app, store, class, imported: (.imported.manifest | {app, stopGeneration, stopReceiptSha256, image})}' \
    "$ROOT/s2/evidence/install-$1.stdout"
}

r_collision() {
  set +e
  s2 start-a >/dev/null
  rc=$?
  set -e
  [ "$rc" != 0 ]
  cat "$ROOT/s2/evidence/start-a.stderr"
  grep -q "belongs to store" "$ROOT/s2/evidence/start-a.stderr"
  key1=$(jq -r .stateRoot "$(P1)" | awk -F/ '{print $(NF-1)}')
  key2=$(jq -r .stateRoot "$(P2)" | awk -F/ '{print $(NF-1)}')
  ls -d "$GRAINS_ROOT/vars/$key1-7101" "$GRAINS_ROOT/vars/$key2-7101"
  echo "app 7101 in two Stores: distinct volumes $key1-7101 and $key2-7101; Store 2's START refused (unit name pinned by Mini without a Store id)"
}

r_side_by_side() {
  for spec in "$(P1) 7101" "$(P2) 7201" "$(P2) 7301"; do
    set -- $spec
    unit=$(running_unit "$1" "$2")
    printf '%s %s %s %s\n' "$(jq -r .stateRoot "$1" | awk -F/ '{print $(NF-1)}')" "$2" "$unit" \
      "$(systemctl show "$unit" --property=ActiveState,Slice --value | tr '\n' ' ')"
    [ "$(systemctl show "$unit" --property=ActiveState --value)" = active ]
  done | tee "$OUT/side-by-side.txt"
  [ "$(cut -d ' ' -f 3 "$OUT/side-by-side.txt" | sort -u | wc -l)" = 3 ]
  echo "three grains of two Stores active at once under three distinct units"
}

run_row() {
  case "$1" in
    identity) row identity r_identity ;;
    refusals) row refusals r_refusals ;;
    s1-store) row s1-store s1 store services workroom profile ;;
    s1-birth-a) row s1-birth-a s1 birth-a ;;
    s1-install-a) row s1-install-a s1 install-a ;;
    s1-share-a) row s1-share-a s1 share-a ;;
    s1-start-a) row s1-start-a s1 start-a ;;
    s1-floor-a) row s1-floor-a r_floor s1 a ;;
    s1-limits-a) row s1-limits-a r_limits "$(P1)" 7101 S ;;
    s1-enroll-a) row s1-enroll-a s1 enroll-a ;;
    s1-get-a) row s1-get-a s1 get-a ;;
    s1-post-a) row s1-post-a s1 post-a ;;
    s1-supervise-a) row s1-supervise-a s1 supervise-a ;;
    s1-kill-a) row s1-kill-a r_kill "$(P1)" 7101 ;;
    s1-floor-a2) row s1-floor-a2 r_floor s1 a2 ;;
    s1-enroll-a2) row s1-enroll-a2 s1 enroll-a2 ;;
    s1-poll-a2) row s1-poll-a2 r_poll s1 poll-a2 "published by a before STOP" ;;
    s1-backup) row s1-backup r_backup ;;
    s1-stop-a) row s1-stop-a s1 stop-a ;;
    s1-export-a) row s1-export-a r_export ;;
    s1-start-a3) row s1-start-a3 s1 start-a3 ;;
    s2-store) row s2-store s2 store services workroom profile ;;
    s2-birth-a) row s2-birth-a s2 birth-a ;;
    s2-install-a) row s2-install-a r_install_import a "$ROOT/export-a" ;;
    s2-share-a) row s2-share-a s2 share-a ;;
    s2-collision) row s2-collision r_collision ;;
    s2-birth-c) row s2-birth-c s2 birth-c ;;
    s2-tamper-c) row s2-tamper-c r_tamper ;;
    s2-install-c) row s2-install-c r_install_import c "$ROOT/export-a" ;;
    s2-share-c) row s2-share-c s2 share-c ;;
    s2-start-c) row s2-start-c s2 start-c ;;
    s2-enroll-c) row s2-enroll-c s2 enroll-c ;;
    s2-poll-c) row s2-poll-c r_poll s2 poll-c "published by a before STOP" ;;
    s2-birth-b) row s2-birth-b s2 birth-b ;;
    s2-install-b) row s2-install-b s2 install-b ;;
    s2-share-b) row s2-share-b s2 share-b ;;
    s2-start-b) row s2-start-b s2 start-b ;;
    s2-limits-b) row s2-limits-b r_limits "$(P2)" 7201 M ;;
    s2-enroll-b) row s2-enroll-b s2 enroll-b ;;
    s2-get-b) row s2-get-b s2 get-b ;;
    side-by-side) row side-by-side r_side_by_side ;;
    *) echo "unknown row $1" >&2; exit 2 ;;
  esac
}

ALL="identity refusals s1-store s1-birth-a s1-install-a s1-share-a s1-start-a s1-floor-a
  s1-limits-a s1-enroll-a s1-get-a s1-post-a s1-kill-a s1-floor-a2 s1-enroll-a2 s1-poll-a2
  s1-backup s1-stop-a s1-export-a s1-start-a3 s2-store s2-birth-a s2-install-a s2-share-a
  s2-collision s2-birth-c s2-tamper-c s2-install-c s2-share-c s2-start-c s2-enroll-c
  s2-poll-c s2-birth-b s2-install-b s2-share-b s2-start-b s2-limits-b s2-enroll-b s2-get-b
  side-by-side"

case "$MODE" in
  all) for r in $ALL; do run_row "$r"; done ;;
  rows)
    # Resumed rows need the Store services this journey runs as children.
    for s in s1 s2; do
      [ ! -e "$ROOT/$s/store" ] || "$s" services >/dev/null
    done
    for r in "$@"; do run_row "$r"; done ;;
  *) usage ;;
esac
echo "$ROWS"
