#!/usr/bin/env bash
# J13: a refusal that names the clause (PLACE §2.6, K-LAW-LEAF §4.6).
#
# On a fresh private Store, A (the sponsor) creates a board cell, grants B
# observe+mutate, and B creates field 2 = 1. A then installs, in the shell's
# law grammar,
#   any [ verb == read, verb == write, all [ verb in {delegate,install,revoke}, subject == A ] ];
#   any [ field 2 monotone, not (verb == write) ];
#   any [ field 2 in {0,1,2}, not (verb == write) ]
# (a cell's one law judges every verb, so each game clause is guarded to
# writes and management is its own clause; see p-templates). B moves 1 -> 2
# (admitted: its grant survives the law change), then drafts 2 -> 1 and 2 -> 5,
# whose submissions are refused with the failing clause when the Host plans
# them; A seals the board (`sealed`) and its own repair is refused.
#
# Every refusal row asserts the exit code (3), the reason AND the leaf text on
# the shell's `refused:` line, and that the Host's own decoding of the retained
# refusal frame carries the same `explain`. A row whose command exits 0, or
# refuses for another reason or clause, fails.
#
# usage: j13.sh HOST MINI STORE VERIFIER NEW_RUN_DIR [PORT]
#   HOST: the native Host built from this branch; MINI: the `mini` client
#   (bootstrap, `mini serve` and `mini shell`); STORE, VERIFIER: the Host
#   helpers. NEW_RUN_DIR must not exist; a private sshd on 127.0.0.1:PORT
#   (default 22433) and the Mini service run from it and are stopped on exit.
set -uo pipefail
umask 077

if [[ $# -lt 5 || $# -gt 6 ]]; then
  sed -n '2,27p' "$0" >&2
  exit 64
fi
HOST=$1 MINI_SRC=$2 STORE=$3 VERIFIER=$4 RUN=$5 PORT=${6:-22433}
for path in "$HOST" "$MINI_SRC" "$STORE" "$VERIFIER" "$RUN"; do
  [[ $path == /* ]] || { echo "path must be absolute: $path" >&2; exit 64; }
done
[[ ! -e $RUN ]] || { echo "run directory already exists: $RUN" >&2; exit 64; }
command -v jq >/dev/null || { echo 'jq is required' >&2; exit 66; }
SSHD=$(command -v sshd || echo /usr/sbin/sshd)
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
WRAPPER_SRC=$REPO/deploy/shell/mini-shell-ssh
RENDER=$REPO/deploy/shell/render-shell-key
[[ -x $WRAPPER_SRC && -x $RENDER ]] || { echo 'deploy/shell scripts missing' >&2; exit 66; }
if ss -ltn 2>/dev/null | awk '{print $4}' | grep -q ":$PORT\$"; then
  echo "port $PORT is in use" >&2
  exit 69
fi

mkdir -m 700 "$RUN" "$RUN/bin" "$RUN/log" "$RUN/ssh" "$RUN/sshd" "$RUN/homes"
RUN=$(CDPATH='' cd -- "$RUN" && pwd)
LOG=$RUN/log
R=$RUN/store
install -m 0500 "$MINI_SRC" "$RUN/bin/mini"
install -m 0500 "$WRAPPER_SRC" "$RUN/bin/mini-shell-ssh"
MINI=$RUN/bin/mini
CONFIG=$R/deployment/pinned-config.json
SOCK=$R/public/mini.sock
sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$RUN/bin/mini-shell-ssh" >"$LOG/binaries.sha256"

TABLE=$LOG/steps.tsv
printf 'n\tJ\twho\tline\texpect\texit\twall_s\tverdict\tnote\n' >"$TABLE"
printf 'step\treason\tleaf\tshell line\thost explain\tverdict\n' >"$LOG/refusals.tsv"
N=0
SSHD_PID=
LAST=
LAST_NAME=

row() { # J who line expect exit wall verdict note
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$@" >>"$TABLE"
  printf '%3s %-3s %-8s %-64.64s exp=%-2s got=%-3s %7ss %s %s\n' "$N" "$@"
}

ssh_base() { # who, then ssh options and arguments
  local who=$1; shift
  ssh -F /dev/null -p "$PORT" -i "$RUN/ssh/$who" -o IdentitiesOnly=yes -o BatchMode=yes \
    -o UserKnownHostsFile="$RUN/ssh/known_hosts" -o StrictHostKeyChecking=accept-new \
    -o LogLevel=ERROR "$@"
}

timed() { # name, command...; records stdout/stderr/exit/timing under $LOG
  local name=$1; shift
  local s e rc
  s=$(date +%s.%N)
  "$@" >"$LOG/$name.stdout" 2>"$LOG/$name.stderr"
  rc=$?
  e=$(date +%s.%N)
  echo "$rc" >"$LOG/$name.exit"
  WALL=$(awk -v a="$s" -v b="$e" 'BEGIN{printf "%.3f", b-a}')
  echo "start=$s end=$e wall_s=$WALL exit=$rc" >"$LOG/$name.timing"
  return "$rc"
}

refused_line() { # stderr file -> the shell's first `refused:` line
  grep -m1 '^refused: ' "$1" || true
}

step() { # J expect who line   -- one verb, one ssh session (SSH_ORIGINAL_COMMAND)
  local j=$1 expect=$2 who=$3 line=$4 rc
  N=$((N + 1)); LAST_NAME=$(printf '%02d-%s-%s' "$N" "$j" "$who")
  printf '%s\n' "$line" >"$LOG/$LAST_NAME.line"
  timed "$LAST_NAME" ssh_base "$who" -T "$USER@127.0.0.1" "$line" </dev/null
  rc=$?
  LAST=$LOG/$LAST_NAME.stdout
  local v=ok; [[ $rc == "$expect" ]] || v=FAIL
  row "$j" "$who" "$line" "$expect" "$rc" "$WALL" "$v" "$(refused_line "$LOG/$LAST_NAME.stderr" | cut -c1-90)"
}

check() { # J description, command...
  local j=$1 desc=$2; shift 2
  N=$((N + 1))
  if "$@" >>"$LOG/checks.log" 2>&1; then
    row "$j" check "$desc" - - - ok ""
  else
    row "$j" check "$desc" - - - FAIL "check failed"
  fi
}

op() { # J description, command...
  local j=$1 desc=$2 name rc; shift 2
  N=$((N + 1)); name=$(printf '%02d-%s-operator' "$N" "$j")
  printf '%s\n' "$desc" >"$LOG/$name.line"
  timed "$name" "$@"
  rc=$?
  local v=ok; [[ $rc == 0 ]] || v=FAIL
  row "$j" OPERATOR "$desc" 0 "$rc" "$WALL" "$v" ""
}

field() { # stdout-file field -> value or "absent"
  jq -r --arg f "$2" '[.cell.entries[] | select(.key.field == $f) | .value][0] // "absent"' "$1"
}
is() { [[ $1 == "$2" ]] || { echo "expected [$2], got [$1]"; return 1; }; }

newest_refusal() { # who -> the newest retained Host decoding of a refusal frame
  find "$RUN/homes/$1/refusals" -name '*.json' -printf '%T@ %p\n' 2>/dev/null | sort -n | tail -n1 | cut -d' ' -f2-
}

# A shell verb the Host must refuse with REASON, naming LEAF. The shell line
# must be exactly `refused: REASON: LEAF`, optionally followed by the shell's
# ` (Host refused …)` suffix, and the Host's own decoding of the retained frame
# must carry `explain` = LEAF and a structured `leaf`.
lstep() { # J reason leaf who line
  local j=$1 reason=$2 leaf=$3 who=$4 line=$5 before got decoded explain v
  before=$(newest_refusal "$who")
  step "$j" 3 "$who" "$line"
  got=$(refused_line "$LOG/$LAST_NAME.stderr")
  decoded=$(newest_refusal "$who")
  explain=-
  [[ -n $decoded && $decoded != "$before" ]] && explain=$(jq -r '.explain // "-"' "$decoded")
  v=ok
  case $got in
    "refused: $reason: $leaf" | "refused: $reason: $leaf (Host refused "*) ;;
    *) v=FAIL ;;
  esac
  [[ $explain == "$leaf" ]] || v=FAIL
  [[ -n $decoded && $decoded != "$before" ]] && { jq -e '.leaf.path | type == "array"' "$decoded" >/dev/null || v=FAIL; }
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$LAST_NAME" "$reason" "$leaf" "$got" "$explain" "$v" >>"$LOG/refusals.tsv"
  N=$((N + 1))
  row "$j" check "named $reason: $leaf" - - - "$v" "host explain: $explain"
}

# ------------------------------------------------------------- services

server_pid() { cat "$R/public/server.pid"; }
owned_server() { # pid -> true when its cmdline is our serve on our socket
  local cmd
  cmd=$(tr '\0' ' ' 2>/dev/null <"/proc/$1/cmdline") || return 1
  [[ $cmd == *" serve "*"--socket $SOCK"* ]]
}
stop_server() {
  local pid kids
  pid=$(server_pid) || return 1
  owned_server "$pid" || { echo "pid $pid is not our server; not signalled"; return 1; }
  kids=$(ps -o pid= --ppid "$pid" | tr -d ' ')
  echo "stopping server $pid (children: $kids)"
  kill -TERM "$pid"
  for _ in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
  for c in $pid $kids; do
    for _ in $(seq 1 100); do kill -0 "$c" 2>/dev/null || break; sleep 0.1; done
    if kill -0 "$c" 2>/dev/null; then echo "still alive: $c"; return 1; fi
  done
  echo "stopped $pid $kids"
}

setup_sshd() {
  local who workspace
  for who in sponsor newcomer; do
    ssh-keygen -q -t ed25519 -N '' -C "j13-$who" -f "$RUN/ssh/$who" || return 1
    if [[ $who == sponsor ]]; then workspace=$R/sponsor; else workspace=$RUN/homes/$who/workspace; fi
    mkdir -m 700 "$RUN/homes/$who"
    "$RENDER" "$RUN/bin/mini-shell-ssh" "$MINI" "$HOST" "$CONFIG" "$SOCK" \
      "$workspace" "$RUN/homes/$who" "$RUN/ssh/$who.pub" >>"$RUN/sshd/authorized_keys" || return 1
  done
  ssh-keygen -q -t ed25519 -N '' -f "$RUN/sshd/host_ed25519" || return 1
  cat >"$RUN/sshd/sshd_config" <<EOF
Port $PORT
ListenAddress 127.0.0.1
HostKey $RUN/sshd/host_ed25519
AuthorizedKeysFile $RUN/sshd/authorized_keys
PidFile $RUN/sshd/sshd.pid
AllowUsers $USER
PubkeyAuthentication yes
PasswordAuthentication no
KbdInteractiveAuthentication no
UsePAM no
StrictModes no
PermitTTY yes
X11Forwarding no
AllowTcpForwarding no
AllowAgentForwarding no
PermitUserEnvironment no
LogLevel VERBOSE
EOF
  setsid "$SSHD" -f "$RUN/sshd/sshd_config" -D -e >"$RUN/sshd/sshd.log" 2>&1 </dev/null &
  SSHD_PID=$!
  echo "$SSHD_PID" >"$RUN/sshd/sshd.pid.launched"
  for _ in $(seq 1 100); do
    ss -ltn | awk '{print $4}' | grep -q "127.0.0.1:$PORT\$" && { echo "sshd $SSHD_PID on $PORT"; return 0; }
    kill -0 "$SSHD_PID" 2>/dev/null || { cat "$RUN/sshd/sshd.log"; return 1; }
    sleep 0.1
  done
  return 1
}
stop_sshd() {
  [[ -n $SSHD_PID ]] || return 0
  local cmd
  cmd=$(tr '\0' ' ' 2>/dev/null <"/proc/$SSHD_PID/cmdline") || { echo "sshd $SSHD_PID already gone"; SSHD_PID=; return 0; }
  [[ $cmd == *"$RUN/sshd/sshd_config"* ]] || { echo "pid $SSHD_PID is not our sshd; not signalled"; return 1; }
  kill -TERM "$SSHD_PID"
  for _ in $(seq 1 100); do kill -0 "$SSHD_PID" 2>/dev/null || break; sleep 0.1; done
  kill -0 "$SSHD_PID" 2>/dev/null && { echo "sshd still alive"; return 1; }
  echo "stopped sshd $SSHD_PID"; SSHD_PID=
}
cleanup() {
  {
    echo "--- cleanup"
    stop_sshd
    [[ -f $R/public/server.pid ]] && owned_server "$(server_pid)" && stop_server
    echo "--- processes naming the run directory after cleanup:"
    ps -eo pid,args | grep -F "$RUN" | grep -v -e grep -e j13.sh || echo none
  } >>"$LOG/cleanup.txt" 2>&1
}
trap cleanup EXIT

# ------------------------------------------------------------- setup

echo "run: $RUN"
op S "bootstrap fresh private Store, sponsor workspace, mini serve" \
  sh "$REPO/native/resource-client/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$R"
op S "ssh keys, rendered authorized_keys, private sshd on 127.0.0.1:$PORT" setup_sshd
step S 0 newcomer "keygen mini.key"
op S "CUSTODY: copy newcomer secret into sponsor home (co-signed enrollment)" \
  bash -c "mkdir -p -m 700 '$RUN/homes/sponsor/keys' && install -m 600 '$RUN/homes/newcomer/keys/mini.key' '$RUN/homes/sponsor/keys/newcomer-1.key' && install -m 644 '$RUN/homes/newcomer/keys/mini.key.next.pub' '$RUN/homes/sponsor/keys/newcomer-1.key.next.pub'"
step S 0 sponsor "enroll plan newcomer-1 newcomer-1.key $(xxd -p -c 256 "$RUN/homes/newcomer/keys/mini.key.next.pub") $(xxd -p -c 256 "$RUN/homes/newcomer/keys/mini.key.next.cosign")"
step S 0 sponsor "enroll seal newcomer-1"
step S 0 sponsor "enroll submit newcomer-1"
B_SUBJ=$(jq -r '.subject' "$LAST")
A_SUBJ=7
# `init` binds a delivered birth context (p-shell-docs): provision the newcomer
# the way deploy/shell/OPERATOR.md step 6 does, as shell-journey.sh does.
printf '%s\n' '{"type":"all","predicates":[]}' >"$RUN/permit-all.json"
op S "PROVISION (OPERATOR step 6): factory observation + a funded account owned by newcomer" \
  "$MINI" workspace --action provision --dir "$R/sponsor" --name newcomer --holder "$B_SUBJ" \
    --funding 1000 --account-predicate "$RUN/permit-all.json" --factory-ref factory
op S "DELIVER (OPERATOR step 6): the birth context into newcomer's HOME/provision/" \
  install -D -m 0600 "$R/sponsor/provisions/newcomer/birth-context.json" "$RUN/homes/newcomer/provision/birth-context.json"
step S 0 newcomer "init mini.key $B_SUBJ"
step S 0 sponsor 'create board declared {"type":"all","predicates":[]} 2'
step S 0 sponsor "delegate grant-b board $B_SUBJ observe,mutate 50000"
step S 0 sponsor "submit grant-b"
step S 0 sponsor "publish grant-b"
step S 0 sponsor "export grant-b"
REF_JSON=$(jq -c . "$LAST")
step S 0 newcomer "import board $REF_JSON"
step S 0 newcomer "invoke first board create 2 1"
step S 0 newcomer "submit first"
step S 0 newcomer "read board"
check S "B created field 2 = 1 under the open law" is "$(field "$LAST" 2)" 1

# ------------------------------------------------------------- the law, in the grammar

LAW="any [ verb == read, verb == write, all [ verb in {delegate,install,revoke}, subject == $A_SUBJ ] ]; any [ field 2 monotone, not (verb == write) ]; any [ field 2 in {0,1,2}, not (verb == write) ]"
step L 0 sponsor "law board-law board \"$LAW\""
check L "the proposal carries the grammar rendered to Pred JSON" \
  jq -e '.predicate.type == "all" and (.predicate.predicates | length) == 3
    and .predicate.predicates[1].predicates[0] == {"type":"monotone","slot":"resource/field/2/after"}' \
  "$RUN/homes/sponsor/requests/board-law.json"
step L 0 sponsor "submit board-law"
check L "law installed (the Host parsed the grammar's JSON)" jq -e '.confirmation == "installed"' "$LAST"

# ------------------------------------------------------------- B plays under the law

step W 0 newcomer "invoke up board write 2 2 1"
check W "no refusal on the admitted move" bash -c "! grep -q '^refused:' '$LOG/$LAST_NAME.stderr'"
step W 0 newcomer "submit up"
step W 0 newcomer "read board"
check W "B's grant still writes after the law change: field 2 = 2" is "$(field "$LAST" 2)" 2

# `invoke` only drafts the intent (after a read the law admits); the Host
# plans the write at `submit`, on the read-authorized preparation path, and
# that is where the law refuses it.
step D 0 newcomer "invoke down board write 2 1 2"
lstep D law-denied "field 2 monotone (before 2, after 1)" newcomer "submit down"
step D 0 newcomer "invoke out board write 2 5 2"
lstep D law-denied "field 2 in {0,1,2} (value 5)" newcomer "submit out"
step D 0 newcomer "read board"
check D "control: the refused moves wrote nothing, field 2 = 2" is "$(field "$LAST" 2)" 2

# ------------------------------------------------------------- A seals; A's repair is refused

step E 0 sponsor "law seal board sealed --allow-unsatisfiable"
check E "sealed renders to any []" jq -e '.predicate == {"type":"any","predicates":[]}' \
  "$RUN/homes/sponsor/requests/seal.json"
step E 0 sponsor "submit seal"
check E "seal installed" jq -e '.confirmation == "installed"' "$LAST"
lstep E law-denied "sealed" sponsor "law repair board open"
lstep E law-denied "sealed" newcomer "read board"

# ------------------------------------------------------------- end

op END "stop sshd" stop_sshd
op END "stop the Mini service" stop_server
trap - EXIT
cleanup

echo
column -t -s $'\t' "$LOG/refusals.tsv" | tee "$LOG/refusals.txt"
FAILS=$(awk -F'\t' 'NR > 1 && $8 != "ok"' "$TABLE" | wc -l)
echo "failed rows: $FAILS" | tee "$LOG/verdicts.txt"
echo "step table: $TABLE"
[[ $FAILS == 0 ]]
