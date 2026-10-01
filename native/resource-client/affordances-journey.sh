#!/usr/bin/env bash
# J12A: affordances — `can NAME` (P-AFFORDANCES, DEOS §1.3; deos's project_for(held)).
#
# On a fresh private Store, A (the sponsor) and B (a newcomer) ask the kernel
# what they can do, verb by verb, without doing it. `can NAME` reads the
# capability records the reference names from the Host, and for each verb they
# cover prepares the smallest representative command and dry-runs it (Host op
# 130: plan as op 1, assemble, submit over a Store writer that never appends).
#
#   A's `can paper` lists read/write/edit/link/delegate/law admitted;
#   B, granted observe on paper, lists read only (`--all`: the rest noGrant);
#   B, granted observe+mutate on board under a monotone law, sees
#     write admitted for 1 -> 2 and law-denied, naming the clause, for 1 -> 0;
#   after A revokes B's board grant, B's `can board` lists no verb;
#   A seals paper (J8's deny-all) and every verb is law-denied: sealed;
#   a restart prints the same answers.
# Around every `can`: the world root and height (a signed read of board by A)
# and the Host's `audit` count are identical before and after — the
# differential that nothing committed.
#
# usage: affordances-journey.sh HOST MINI STORE VERIFIER NEW_RUN_DIR [PORT]
#   HOST: the native Host built from this branch (it must answer op 130);
#   MINI: the `mini` client; STORE, VERIFIER: the Host helpers. NEW_RUN_DIR
#   must not exist; a private sshd on 127.0.0.1:PORT (default 22434) and the
#   Mini service run from it and are stopped on exit.
set -uo pipefail
umask 077

if [[ $# -lt 5 || $# -gt 6 ]]; then
  sed -n '2,25p' "$0" >&2
  exit 64
fi
HOST=$1 MINI_SRC=$2 STORE=$3 VERIFIER=$4 RUN=$5 PORT=${6:-22434}
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
    ssh-keygen -q -t ed25519 -N '' -C "j12a-$who" -f "$RUN/ssh/$who" || return 1
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
    ps -eo pid,args | grep -F "$RUN" | grep -v -e grep -e affordances-journey.sh || echo none
  } >>"$LOG/cleanup.txt" 2>&1
}
trap cleanup EXIT

# ------------------------------------------------------------- the differential

# The world root and height, from a signed read of board by A (a query never
# commits); a turn appended anywhere moves the root.
world() {
  local err=$LOG/world-$N.err attempt
  "$MINI" workspace --action read --dir "$R/sponsor" --name board >/dev/null 2>"$err" || { echo "read-failed"; return 0; }
  attempt=$(sed -n 's/^workspace read attempt: //p' "$err" | tail -n1)
  jq -r '.worldRoot + "@" + .height' "$attempt/challenge.json"
}
audit_count() { "$HOST" "$CONFIG" audit 2>/dev/null | sed -n 's/^audited \([0-9]*\) .*/\1/p'; }

# cstep J who line: one `can` verb, with the root/height and audit differential.
cstep() {
  local j=$1 who=$2 line=$3 before after ab aa
  before=$(world); ab=$(audit_count)
  step "$j" 0 "$who" "$line"
  CAN=$LOG/can-$(printf '%02d' "$N")-$who.txt
  cp "$LAST" "$CAN"
  after=$(world); aa=$(audit_count)
  CANS=$((CANS + 1))
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$who" "$line" "$before" "$after" "$ab/$aa" >>"$LOG/differential.tsv"
  check "$j" "world root+height unchanged by '$line' ($before)" is "$after" "$before"
  check "$j" "audit count unchanged by '$line' ($ab)" is "$aa" "$ab"
}
has() { grep -Eq "^  $1 +$2" "$CAN" || { echo "no row [$1 $2] in $CAN"; cat "$CAN"; return 1; }; }
hasnt() { ! grep -Eq "^  $1 " "$CAN" || { echo "unexpected row [$1] in $CAN"; return 1; }; }
rows() { is "$(grep -Ec '^  [a-z]+ ' "$CAN")" "$1"; }
CANS=0
printf 'n\twho\tline\tbefore\tafter\taudit\n' >"$LOG/differential.tsv"

start_server() {
  setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCK" \
    >"$R/public/serve-restart.log" 2>&1 </dev/null &
  echo "$!" >"$R/public/server.pid"
  for _ in $(seq 1 1200); do [[ -S $SOCK ]] && break; sleep 0.1; done
  for _ in $(seq 1 300); do [[ $(world) != read-failed ]] && return 0; sleep 0.1; done
  return 1
}

# ------------------------------------------------------------- setup

echo "run: $RUN"
op S "bootstrap fresh private Store, sponsor workspace, mini serve" \
  sh "$REPO/native/resource-client/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$R"
op S "ssh keys, rendered authorized_keys, private sshd on 127.0.0.1:$PORT" setup_sshd
step S 0 newcomer "keygen mini.key"
op S "CUSTODY: copy newcomer secret into sponsor home (co-signed enrollment)" \
  bash -c "mkdir -p -m 700 '$RUN/homes/sponsor/keys' && install -m 600 '$RUN/homes/newcomer/keys/mini.key' '$RUN/homes/sponsor/keys/newcomer-1.key'"
step S 0 sponsor "enroll plan newcomer-1 newcomer-1.key"
step S 0 sponsor "enroll seal newcomer-1"
step S 0 sponsor "enroll submit newcomer-1"
B_SUBJ=$(jq -r '.subject' "$LAST")
A_SUBJ=7
printf '%s\n' '{"type":"all","predicates":[]}' >"$RUN/permit-all.json"
op S "PROVISION (OPERATOR step 6): factory observation + a funded account owned by newcomer" \
  "$MINI" workspace --action provision --dir "$R/sponsor" --name newcomer --holder "$B_SUBJ" \
    --funding 1000 --account-predicate "$RUN/permit-all.json" --factory-ref factory
op S "DELIVER (OPERATOR step 6): the birth context into newcomer's HOME/provision/" \
  install -D -m 0600 "$R/sponsor/provisions/newcomer/birth-context.json" "$RUN/homes/newcomer/provision/birth-context.json"
step S 0 newcomer "init mini.key $B_SUBJ"
step S 0 sponsor 'create board declared {"type":"all","predicates":[]}'
world_ok() { [[ $(world) != read-failed ]]; }
check S "the differential's signed read of board answers" world_ok

# ------------------------------------------------------------- A owns paper

step A 0 sponsor "doc new paper"
step A 0 sponsor "doc append p1 paper hello"
step A 0 sponsor "submit p1"
cstep A sponsor "can paper"
check A "owner: read admitted" has read admitted
check A "owner: write (append) admitted" has write admitted
check A "owner: edit (line to its own text) admitted" has edit admitted
check A "owner: link (paper -> paper) admitted" has link admitted
check A "owner: delegate (to itself) admitted" has delegate admitted
check A "owner: law (reinstall) admitted" has law admitted
check A "owner: revoke not probed (nothing delegated yet)" has revoke '\(not probed\)'

# ------------------------------------------------------------- B reads paper

step B 0 sponsor "delegate rd paper $B_SUBJ observe 50000"
step B 0 sponsor "submit rd"
step B 0 sponsor "publish rd"
step B 0 sponsor "export rd"
REF_JSON=$(jq -c . "$LAST")
step B 0 newcomer "import paper $REF_JSON"
cstep B newcomer "can paper"
check B "reader: read admitted" has read admitted
check B "reader: exactly one verb row" rows 1
cstep B newcomer "can paper --all"
for v in write edit link delegate law revoke; do
  check B "reader --all: $v noGrant" has "$v" noGrant
done
check B "reader --all: read admitted" has read admitted
for v in write edit link; do
  check B "reader --all: $v planned by op 1 yet refused by the dry run on the grant (capabilityRejected)" \
    has "$v" 'noGrant +\[no capability names mutate; Host: operation-rejected: .*capabilityRejected'
done
check B "reader --all: the Host refused every uncovered probe (no disagreement)" bash -c "! grep -q 'HOST ADMITTED' '$CAN'"
cstep B sponsor "can paper"
check B "owner: revoke now probes the grant to B, admitted" has revoke admitted

# ------------------------------------------------------------- B writes board under a monotone law

step W 0 sponsor "delegate wb board $B_SUBJ observe,mutate 50000"
step W 0 sponsor "submit wb"
step W 0 sponsor "publish wb"
step W 0 sponsor "export wb"
REF_JSON=$(jq -c . "$LAST")
step W 0 newcomer "import board $REF_JSON"
step W 0 newcomer "invoke first board create 2 1"
W0=$(world)
step W 0 newcomer "submit first"
W1=$(world)
differs() { [[ $1 != "$2" ]] || { echo "root did not move: $1"; return 1; }; }
check W "falsifier: the differential sees a real commit (root+height moved by 'submit first')" differs "$W0" "$W1"
LAW="any [ verb == read, verb == write, all [ verb in {delegate,install,revoke}, subject == $A_SUBJ ] ]; any [ field 2 monotone, not (verb == write) ]"
step W 0 sponsor "law mono board \"$LAW\""
step W 0 sponsor "submit mono"
cstep W newcomer "can board"
check W "writer: read admitted" has read admitted
check W "writer: write up (1 -> 2) admitted" has write 'admitted +\[field 2: 1 -> 2 \(up\)\]'
check W "writer: write down (1 -> 0) law-denied, naming the clause" \
  has write 'law-denied: field 2 monotone \(before 1, after 0\) +\[field 2: 1 -> 0 \(down\)\]'
check W "writer: no delegate/law/revoke rows (not granted)" bash -c "! grep -Eq '^  (delegate|law|revoke) ' '$CAN'"
step W 0 newcomer "read board"
check W "control: field 2 is still 1 after can" is "$(field "$LAST" 2)" 1

# ------------------------------------------------------------- revocation

step R 0 sponsor "revoke rvb board $B_SUBJ"
step R 0 sponsor "submit rvb"
cstep R newcomer "can board"
check R "after revocation: no verb rows" rows 0
check R "after revocation: the record's refusal is shown" grep -q '^  # capability ' "$CAN"

# ------------------------------------------------------------- locked (J8: deny-all)

step L 0 sponsor "law seal paper sealed --allow-unsatisfiable"
step L 0 sponsor "submit seal"
cstep L sponsor "can paper"
for v in read delegate law revoke; do
  check L "locked: $v law-denied: sealed" has "$v" 'law-denied: sealed'
done
check L "locked: no verb admitted" bash -c "! grep -Eq '^  [a-z]+ +admitted' '$CAN'"
LOCKED=$CAN
cstep L newcomer "can paper"
check L "locked, reader: read law-denied: sealed" has read 'law-denied: sealed'
READER_LOCKED=$CAN
cstep L newcomer "can board"
REVOKED=$CAN

# ------------------------------------------------------------- restart: same answers

op X "stop the Mini service" stop_server
op X "start the Mini service on the same Store" start_server
cstep X sponsor "can paper"
check X "restart: owner's locked answers identical" diff "$LOCKED" "$CAN"
cstep X newcomer "can paper"
check X "restart: reader's locked answers identical" diff "$READER_LOCKED" "$CAN"
cstep X newcomer "can board"
check X "restart: revoked answers identical" diff "$REVOKED" "$CAN"

# ------------------------------------------------------------- end

op END "stop sshd" stop_sshd
op END "stop the Mini service" stop_server
trap - EXIT
cleanup

FAILS=$(awk -F'\t' 'NR > 1 && $8 != "ok"' "$TABLE" | wc -l)
ROWS=$(awk 'NR > 1' "$TABLE" | wc -l)
echo "rows: $ROWS  failed: $FAILS  can invocations: $CANS (each with root+height and audit differential)" | tee "$LOG/verdicts.txt"
echo "step table: $TABLE"
[[ $FAILS == 0 ]]
