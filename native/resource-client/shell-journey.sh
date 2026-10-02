#!/usr/bin/env bash
# Bake-off journey J0-J8 with every participant step typed into `mini shell`
# over ssh. Each participant has its own ssh key, bound by a forced command
# (deploy/shell/mini-shell-ssh) to its own workspace and session home.
#
# Rows marked OPERATOR are things the service operator does outside any
# participant's shell: bootstrap, sshd, service restart, the one key-custody
# step the current enrollment contract needs (see J1), and provisioning
# (deploy/shell/OPERATOR.md step 6: the sponsor's `provision`, and delivering
# its birth context to the participant's HOME/provision/, which `init` binds). Rows marked check are
# assertions over retained shell output. A step passes when its exit code is
# the expected one (0 done, 3 refused by the Host) and its checks hold.
#
# usage: shell-journey.sh HOST PINNED_MINI SHELL_MINI STORE VERIFIER NEW_RUN_DIR [PORT]
#   HOST, PINNED_MINI, STORE, VERIFIER: the pinned Host, the pinned client used
#     for bootstrap and `mini serve`, and the two Host helpers.
#   SHELL_MINI: the client binary that carries `mini shell`.
#   NEW_RUN_DIR: must not exist; a private sshd on 127.0.0.1:PORT (default
#     22422) and the Mini service run from it and are stopped on exit.
set -uo pipefail
umask 077

if [[ $# -lt 6 || $# -gt 7 ]]; then
  sed -n '2,17p' "$0" >&2
  exit 64
fi
HOST=$1 PINNED_MINI=$2 SHELL_MINI_SRC=$3 STORE=$4 VERIFIER=$5 RUN=$6 PORT=${7:-22422}
for path in "$HOST" "$PINNED_MINI" "$SHELL_MINI_SRC" "$STORE" "$VERIFIER" "$RUN"; do
  [[ $path == /* ]] || { echo "path must be absolute: $path" >&2; exit 64; }
done
[[ ! -e $RUN ]] || { echo "run directory already exists: $RUN" >&2; exit 64; }
command -v jq >/dev/null || { echo 'jq is required' >&2; exit 66; }
SSHD=$(command -v sshd || echo /usr/sbin/sshd)
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
WRAPPER_SRC=$HERE/../../deploy/shell/mini-shell-ssh
RENDER=$HERE/../../deploy/shell/render-shell-key
[[ -x $WRAPPER_SRC && -x $RENDER ]] || { echo 'deploy/shell scripts missing' >&2; exit 66; }
if ss -ltn 2>/dev/null | awk '{print $4}' | grep -q ":$PORT\$"; then
  echo "port $PORT is in use" >&2
  exit 69
fi

mkdir -m 700 "$RUN" "$RUN/bin" "$RUN/log" "$RUN/ssh" "$RUN/sshd" "$RUN/homes"
RUN=$(CDPATH='' cd -- "$RUN" && pwd)
LOG=$RUN/log
R=$RUN/store
install -m 0500 "$SHELL_MINI_SRC" "$RUN/bin/mini-shell"
install -m 0500 "$WRAPPER_SRC" "$RUN/bin/mini-shell-ssh"
SHELL_MINI=$RUN/bin/mini-shell
CONFIG=$R/deployment/pinned-config.json
SOCK=$R/public/mini.sock
sha256sum "$HOST" "$PINNED_MINI" "$SHELL_MINI" "$STORE" "$VERIFIER" "$RUN/bin/mini-shell-ssh" \
  >"$LOG/binaries.sha256"

TABLE=$LOG/steps.tsv
printf 'n\tJ\twho\tline\texpect\texit\twall_s\tverdict\tnote\n' >"$TABLE"
declare -A JFAIL=()
N=0
SSHD_PID=
LAST=

row() { # J who line expect exit wall verdict note
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$@" >>"$TABLE"
  [[ $7 == ok ]] || JFAIL[$1]=1
  printf '%3s %-3s %-9s %-60.60s exp=%-2s got=%-3s %7ss %s %s\n' "$N" "$@"
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

verdict_note() { # first shell ending line on stderr, if any
  grep -m1 -E '^(refused|error|undecided|usage):' "$LOG/$1.stderr" | cut -c1-110 || true
}

step() { # J expect who line   -- one verb, one ssh session, SSH_ORIGINAL_COMMAND
  local j=$1 expect=$2 who=$3 line=$4 name rc
  N=$((N + 1)); name=$(printf '%02d-%s-%s' "$N" "$j" "$who")
  printf '%s\n' "$line" >"$LOG/$name.line"
  timed "$name" ssh_base "$who" -T "$USER@127.0.0.1" "$line" </dev/null
  rc=$?
  LAST=$LOG/$name.stdout
  local v=ok; [[ $rc == "$expect" ]] || v=FAIL
  row "$j" "$who" "$line" "$expect" "$rc" "$WALL" "$v" "$(verdict_note "$name")"
}

script_step() { # J expect who script-text   -- script mode over ssh stdin
  local j=$1 expect=$2 who=$3 text=$4 name rc
  N=$((N + 1)); name=$(printf '%02d-%s-%s-script' "$N" "$j" "$who")
  printf '%s' "$text" >"$LOG/$name.line"
  timed "$name" ssh_base "$who" -T "$USER@127.0.0.1" <"$LOG/$name.line"
  rc=$?
  LAST=$LOG/$name.stdout
  local v=ok; [[ $rc == "$expect" ]] || v=FAIL
  row "$j" "$who" "(script) $(tr '\n' ';' <"$LOG/$name.line")" "$expect" "$rc" "$WALL" "$v" "$(verdict_note "$name")"
}

tty_step() { # J who keystrokes   -- interactive mode on a real pty
  local j=$1 who=$2 keys=$3 name rc
  N=$((N + 1)); name=$(printf '%02d-%s-%s-tty' "$N" "$j" "$who")
  printf '%s' "$keys" >"$LOG/$name.keys"
  timed "$name" tty_run "$LOG/$name.keys" "$who"
  rc=$?
  LAST=$LOG/$name.stdout
  local v=ok; [[ $rc == 0 ]] || v=FAIL
  row "$j" "$who" "(tty) $(od -An -c "$LOG/$name.keys" | tr -s ' ' | tr -d '\n' | cut -c1-58)" 0 "$rc" "$WALL" "$v" ""
}

tty_run() { # keys-file who -- release one line of keystrokes at a time so each verb finishes first
  local keys=$1 who=$2
  {
    sleep 3
    while IFS= read -r -d $'\r' chunk; do printf '%s\r' "$chunk"; sleep 4; done <"$keys"
    sleep 1
  } | ssh_base "$who" -tt "$USER@127.0.0.1"
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
start_server() {
  setsid nohup "$PINNED_MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCK" \
    >"$R/public/serve-restart.log" 2>&1 </dev/null &
  echo "$!" >"$R/public/server.pid"
  for _ in $(seq 1 3000); do
    kill -0 "$(server_pid)" 2>/dev/null || { cat "$R/public/serve-restart.log"; return 1; }
    [[ -S $SOCK ]] && grep -q serving "$R/public/serve-restart.log" && { echo "serving pid $(server_pid)"; return 0; }
    sleep 0.1
  done
  return 1
}
restart_server() { stop_server && start_server; }

setup_sshd() {
  local who workspace
  for who in sponsor newcomer third stranger; do
    ssh-keygen -q -t ed25519 -N '' -C "m4-shell-journey-$who" -f "$RUN/ssh/$who" || return 1
    if [[ $who == sponsor ]]; then workspace=$R/sponsor; else workspace=$RUN/homes/$who/workspace; fi
    mkdir -m 700 "$RUN/homes/$who"
    "$RENDER" "$RUN/bin/mini-shell-ssh" "$SHELL_MINI" "$HOST" "$CONFIG" "$SOCK" \
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
    ps -eo pid,args | grep -F "$RUN" | grep -v -e grep -e shell-journey.sh || echo none
  } >>"$LOG/cleanup.txt" 2>&1
}
trap cleanup EXIT

# provision WHO SUBJECT: OPERATOR step 6 for one enrolled participant.
provision() {
  op "$1" "PROVISION (OPERATOR step 6): factory observation + a funded account owned by $2" \
    "$SHELL_MINI" workspace --action provision --dir "$R/sponsor" --name "$2" --holder "$3" \
      --funding 1000 --account-predicate "$RUN/permit-all.json" --factory-ref factory
  op "$1" "DELIVER (OPERATOR step 6): the birth context into $2's HOME/provision/" \
    install -D -m 0600 "$R/sponsor/provisions/$2/birth-context.json" "$RUN/homes/$2/provision/birth-context.json"
}
printf '%s\n' '{"type":"all","predicates":[]}' >"$RUN/permit-all.json"

# ------------------------------------------------------------- J0

echo "run: $RUN"
op J0 "bootstrap fresh private Store, sponsor workspace, mini serve (pinned client)" \
  sh "$HERE/newparticipant-acceptance.sh" "$HOST" "$PINNED_MINI" "$STORE" "$VERIFIER" "$R"
op J0 "ssh keys, rendered authorized_keys, private sshd on 127.0.0.1:$PORT" setup_sshd
step J0 0 sponsor "whoami"
check J0 "sponsor session is subject 7" is "$(jq -r .subject "$LAST")" 7
step J0 0 sponsor "read factory"

# ------------------------------------------------------------- J1

step J1 0 newcomer "keygen mini.key"
NEW_PUB=$(od -An -tx1 -v "$RUN/homes/newcomer/keys/mini.key.pub" | tr -d ' \n')
check J1 "newcomer public key appears in no genesis/config file" \
  bash -c "! grep -l -F '$NEW_PUB' '$R/genesis.json' '$R/operator.json' '$CONFIG' '$R/sponsor-birth-context.json'"
op J1 "CUSTODY: copy newcomer secret into sponsor home (enroll plan+seal sign with both keys in one process)" \
  bash -c "mkdir -p -m 700 '$RUN/homes/sponsor/keys' && install -m 600 '$RUN/homes/newcomer/keys/mini.key' '$RUN/homes/sponsor/keys/newcomer-1.key' && install -m 644 '$RUN/homes/newcomer/keys/mini.key.next.pub' '$RUN/homes/sponsor/keys/newcomer-1.key.next.pub'"
step J1 0 sponsor "enroll plan newcomer-1 newcomer-1.key $(xxd -p -c 256 "$RUN/homes/newcomer/keys/mini.key.next.pub") $(xxd -p -c 256 "$RUN/homes/newcomer/keys/mini.key.next.cosign")"
step J1 0 sponsor "enroll seal newcomer-1"
step J1 0 sponsor "enroll submit newcomer-1"
J1_SUBMIT=$LAST
check J1 "submit returned an admitted-key-only enrollment result" \
  jq -e '.type == "minidregg-participant-enrollment-result-v1" and .authority == "admitted-key-only"' "$J1_SUBMIT"
step J1 0 sponsor "enroll lookup newcomer-1"
J1_LOOKUP=$LAST
NEW_SUBJ=$(jq -r '.subject' "$J1_LOOKUP")
check J1 "lookup returns the same receipt as submit" \
  is "$(jq -c .receipt "$J1_SUBMIT")" "$(jq -c .receipt "$J1_LOOKUP")"
check J1 "enrolled public key is the newcomer's own" is "$(jq -r .publicKey "$J1_LOOKUP")" "$NEW_PUB"
provision J1 newcomer "$NEW_SUBJ"
step J1 0 newcomer "init mini.key $NEW_SUBJ"
step J1 0 newcomer "whoami"
check J1 "newcomer session is subject $NEW_SUBJ" is "$(jq -r .subject "$LAST")" "$NEW_SUBJ"

# ------------------------------------------------------------- J2

step J2 0 sponsor 'create shared declared {"type":"all","predicates":[]}'
step J2 0 sponsor "refs"
TARGET=$(jq -r '.references[] | select(.name == "shared") | .target' "$LAST")
OWNER_CAP=$(jq -r '.references[] | select(.name == "shared") | .observeCapability' "$LAST")
check J2 "sponsor holds reference shared (target $TARGET)" bash -c "[[ '$TARGET' =~ ^[0-9]+\$ ]]"
step J2 0 sponsor "describe shared"
check J2 "law is all[] at version 0" \
  jq -e '.version == "0" and .predicate == {"type":"all","predicates":[]}' "$LAST"

# ------------------------------------------------------------- J3

step J3 0 sponsor "delegate grant-newcomer shared $NEW_SUBJ observe,mutate 50000"
step J3 0 sponsor "submit grant-newcomer"
check J3 "delegation installed" jq -e '.type == "confirmed" and .confirmation == "installed"' "$LAST"
step J3 0 sponsor "publish grant-newcomer"
step J3 0 sponsor "export grant-newcomer"
REF_JSON=$(jq -c . "$LAST")
check J3 "exported reference is addressed to the newcomer" \
  jq -e --arg s "$NEW_SUBJ" '.recipient == $s and .authority == "hint-only"' "$LAST"
check J3 "signed child capability: holder newcomer, verbs observe+mutate only" \
  jq -e --arg s "$NEW_SUBJ" '.purpose.draft.command.child | .verbs == ["observe","mutate"] and .holder.subject == $s' \
  "$R/sponsor/proposals/grant-newcomer/intent.json"
step J3 0 newcomer "import shared $REF_JSON"
step J3 0 newcomer "refs"
CHILD_CAP=$(jq -r '.references[] | select(.name == "shared") | .observeCapability' "$LAST")

# ------------------------------------------------------------- J4

step J4 0 newcomer "read shared"
check J4 "field 2 absent before the write" is "$(field "$LAST" 2)" absent
step J4 0 newcomer "invoke first-action shared create 2 1"
step J4 0 newcomer "submit first-action"
check J4 "write installed" jq -e '.type == "confirmed" and .confirmation == "installed"' "$LAST"
J4_TX=$(jq -r .transactionId "$LAST")
J4_COUNT=$(jq -r .acceptedCount "$LAST")
script_step J4 0 newcomer $'whoami\nread shared\n'
check J4 "script-mode read back: field 2 = 1" \
  is "$(jq -s -r '[.[1].cell.entries[] | select(.key.field == "2") | .value][0]' "$LAST")" 1
tty_step J4 newcomer $'rea\tsh\t\rhis\t\rexit\r'
check J4 "tty: Tab completed 'read shared' and the Host answered field 2 = 1" \
  bash -c "grep -a -q 'read shared' '$LAST' && tr -d '\r' <'$LAST' | grep -a -A4 '\"field\": \"2\"' | grep -a -q '\"value\": \"1\"'"

# ------------------------------------------------------------- J5

step J5 0 third "keygen mini.key"
op J5 "CUSTODY: copy third secret into sponsor home for the co-signed enrollment" \
  install -m 600 "$RUN/homes/third/keys/mini.key" "$RUN/homes/sponsor/keys/third-1.key"
step J5 0 sponsor "enroll plan third-1 third-1.key $(xxd -p -c 256 "$RUN/homes/third/keys/mini.key.next.pub") $(xxd -p -c 256 "$RUN/homes/third/keys/mini.key.next.cosign")"
step J5 0 sponsor "enroll seal third-1"
step J5 0 sponsor "enroll submit third-1"
THIRD_SUBJ=$(jq -r .subject "$LAST")
provision J5 third "$THIRD_SUBJ"
# the newest accepted record is now the third's provisioned account birth
THIRD_COUNT=$(jq -r .account.birthReceipt.acceptedCount "$R/sponsor/provisions/third/provision.json")
step J5 0 third "init mini.key $THIRD_SUBJ"
step J5 0 third "import stolen object $TARGET $CHILD_CAP"
step J5 3 third "read stolen"
step J5 3 third "invoke third-write stolen create 3 1"
step J5 0 third "import owner object $TARGET $OWNER_CAP"
step J5 3 third "read owner"
step J5 0 stranger "keygen mini.key"
# A stranger is never enrolled, so never provisioned: the shell's init refuses
# it, and the operator makes the workspace the stranger's reads are refused from.
step J5 1 stranger "init mini.key 4242424242"
check J5 "the shell's init names the missing provisioning and makes no workspace" \
  bash -c "grep -q '^error: init needs your provisioning at $RUN/homes/stranger/provision/birth-context.json' '${LAST%.stdout}.stderr' && [[ ! -e '$RUN/homes/stranger/workspace' ]]"
op J5 "an unprovisioned workspace for the unenrolled stranger (plain mini workspace init)" \
  "$SHELL_MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCK" \
    --key "$RUN/homes/stranger/keys/mini.key" --subject 4242424242 --dir "$RUN/homes/stranger/workspace"
step J5 0 stranger "import stolen object $TARGET $CHILD_CAP"
step J5 3 stranger "read stolen"
step J5 3 stranger "invoke stranger-write stolen create 3 1"
step J5 0 newcomer "read shared"
check J5 "control: newcomer still reads field 2 = 1" is "$(field "$LAST" 2)" 1

# ------------------------------------------------------------- J6

op J6 "stop the service and reopen the same Store (pinned mini serve)" restart_server
step J6 0 sponsor "enroll lookup newcomer-1"
check J6 "enrollment receipt recovered unchanged" \
  is "$(jq -c .receipt "$LAST")" "$(jq -c .receipt "$J1_LOOKUP")"
step J6 0 newcomer "read shared"
check J6 "J4 value recovered: field 2 = 1" is "$(field "$LAST" 2)" 1
step J6 0 newcomer "retry first-action"
check J6 "exact retry returns the original receipt, replayed" \
  jq -e --arg tx "$J4_TX" --arg n "$J4_COUNT" \
  '.confirmation == "replayed" and .transactionId == $tx and .acceptedCount == $n' "$LAST"
step J6 0 newcomer "history"

# ------------------------------------------------------------- J7

step J7 0 sponsor 'law law-v2 shared {"type":"not","predicate":{"type":"any","predicates":[]}}'
step J7 0 sponsor "submit law-v2"
check J7 "law installed as record $((THIRD_COUNT + 1)): the J6 retry caused no second effect" \
  jq -e --arg n "$((THIRD_COUNT + 1))" '.confirmation == "installed" and .acceptedCount == $n' "$LAST"
step J7 0 sponsor "describe shared"
check J7 "law is not(any[]) at version 1" \
  jq -e '.version == "1" and .predicate.type == "not"' "$LAST"
step J7 0 newcomer "invoke after-law-v2 shared write 2 7 1"
step J7 0 newcomer "submit after-law-v2"
check J7 "newcomer's existing grant still writes" jq -e '.confirmation == "installed"' "$LAST"
step J7 0 newcomer "read shared"
check J7 "field 2 = 7" is "$(field "$LAST" 2)" 7

# ------------------------------------------------------------- J8

step J8 0 sponsor 'law lockout shared {"type":"any","predicates":[]} --allow-unsatisfiable'
step J8 0 sponsor "submit lockout"
check J8 "deny-all installed" jq -e '.confirmation == "installed"' "$LAST"
step J8 3 newcomer "read shared"
step J8 3 newcomer "invoke after-lock shared write 2 8 7"
step J8 3 sponsor "read shared"
step J8 3 sponsor 'law repair shared {"type":"all","predicates":[]}'
check J8 "each refused frame is retained with the Host's own decoding" \
  bash -c "n=\$(ls '$RUN/homes/newcomer/refusals/' | grep -c '\.json\$'); [[ \$n -ge 2 ]] && jq -e '.type == \"refused\"' '$RUN/homes/newcomer/refusals/'*.json"
step J8 0 newcomer "lookup after-law-v2"
check J8 "historical lookup still answers, replayed" jq -e '.confirmation == "replayed"' "$LAST"

# ------------------------------------------------------------- end

op END "stop sshd" stop_sshd
op END "stop the Mini service" stop_server
trap - EXIT
cleanup

echo
echo "journey verdicts:"
for j in J0 J1 J2 J3 J4 J5 J6 J7 J8; do
  if [[ -n ${JFAIL[$j]-} ]]; then echo "$j FAIL"; else echo "$j PASS"; fi
done | tee "$LOG/verdicts.txt"
echo "step table: $TABLE"
[[ ${#JFAIL[@]} == 0 ]]
