#!/usr/bin/env bash
# Every named Host refusal reason, produced on a fresh Store. Participant steps
# are typed into `mini shell` over ssh (harness taken from M4's
# shell-journey.sh). Rows marked RAW send one exact byte payload to the same
# `mini serve` socket with raw-host-op.py (evidence glue: fault injection for
# malformed bytes, a flipped signature byte and a replayed stale observation;
# no friend-facing verb sends raw bytes). Rows marked OPERATOR are service
# steps and the one hand-crafted revocation intent (the workspace has no revoke
# verb). A step passes when its exit code is the expected one (0 done,
# 3 refused) and, for a refusal, its first stderr line names the expected reason.
#
# usage: refusal-reasons.sh HOST PINNED_MINI SHELL_MINI STORE VERIFIER NEW_RUN_DIR [PORT]
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
REPO=$(CDPATH='' cd -- "$HERE/../../.." && pwd)
WRAPPER_SRC=$REPO/deploy/shell/mini-shell-ssh
RENDER=$REPO/deploy/shell/render-shell-key
RAW=$HERE/raw-host-op.py
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
  jq -r --arg f "$2" '[.page.entries[] | select(.key.field == $f) | .value][0] // "absent"' "$1"
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
    ssh-keygen -q -t ed25519 -N '' -C "mr-refusal-reasons-$who" -f "$RUN/ssh/$who" || return 1
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

reason_of() { # stderr-file -> reason named on the first `refused:` line
  sed -n 's/^refused: \([a-z-]*\): .*/\1/p' "$1" | head -n1
}

rstep() { # J expect-reason who line -- a shell verb the Host must refuse with REASON
  local j=$1 reason=$2 who=$3 line=$4
  step "$j" 3 "$who" "$line"
  local name got
  name=$(printf '%02d-%s-%s' "$N" "$j" "$who")
  got=$(reason_of "$LOG/$name.stderr")
  printf '%s\t%s\t%s\t%s\n' "$name" "$reason" "$got" shell >>"$LOG/reasons.tsv"
  check "$j" "Host named $reason (shell showed: ${got:-none})" is "$got" "$reason"
}

raw() { # J expect-exit expect-reason op input label -- exact bytes to the socket
  local j=$1 expect=$2 reason=$3 op=$4 input=$5 label=$6 name rc got
  N=$((N + 1)); name=$(printf '%02d-%s-raw' "$N" "$j")
  printf '%s (op %s, %s)\n' "$label" "$op" "$input" >"$LOG/$name.line"
  cp "$input" "$LOG/$name.request.bin"
  timed "$name" python3 "$RAW" "$SOCK" "$CONFIG" "$HOST" "$op" "$input" \
    "$LOG/$name.reply.bin" "$LOG/$name.decoded.json"
  rc=$?
  local v=ok; [[ $rc == "$expect" ]] || v=FAIL
  got=-
  [[ -f $LOG/$name.decoded.json ]] && got=$(jq -r '.reason // "none"' "$LOG/$name.decoded.json")
  [[ $expect != 3 || $got == "$reason" ]] || v=FAIL
  [[ $expect == 3 ]] && printf '%s\t%s\t%s\t%s\n' "$name" "$reason" "$got" raw >>"$LOG/reasons.tsv"
  row "$j" RAW "$label" "$expect" "$rc" "$WALL" "$v" "reason=$got"
}

newest() { # directory name -> newest file of that name below it
  find "$1" -name "$2" -printf '%T@ %p\n' | sort -n | tail -n1 | cut -d' ' -f2-
}

# ------------------------------------------------------------- setup

echo "run: $RUN"
printf 'step\texpected\tnamed\tchannel\n' >"$LOG/reasons.tsv"
op S "bootstrap fresh private Store, sponsor workspace, mini serve" \
  sh "$REPO/native/resource-client/newparticipant-acceptance.sh" "$HOST" "$PINNED_MINI" "$STORE" "$VERIFIER" "$R"
op S "ssh keys, rendered authorized_keys, private sshd on 127.0.0.1:$PORT" setup_sshd
step S 0 newcomer "keygen mini.key"
op S "CUSTODY: copy newcomer secret into sponsor home (co-signed enrollment)" \
  bash -c "mkdir -p -m 700 '$RUN/homes/sponsor/keys' && install -m 600 '$RUN/homes/newcomer/keys/mini.key' '$RUN/homes/sponsor/keys/newcomer-1.key'"
step S 0 sponsor "enroll plan newcomer-1 newcomer-1.key"
step S 0 sponsor "enroll seal newcomer-1"
step S 0 sponsor "enroll submit newcomer-1"
NEW_SUBJ=$(jq -r '.subject' "$LAST")
step S 0 newcomer "init mini.key $NEW_SUBJ"
step S 0 sponsor 'create shared declared {"type":"all","predicates":[]}'
step S 0 sponsor "refs"
TARGET=$(jq -r '.references[] | select(.name == "shared") | .target' "$LAST")
OWNER_CAP=$(jq -r '.references[] | select(.name == "shared") | .observeCapability' "$LAST")
CONTROL_CAP=$(jq -r '.references[] | select(.name == "shared") | .controlCapability' "$LAST")
step S 0 sponsor "delegate grant-newcomer shared $NEW_SUBJ observe,mutate 50000"
step S 0 sponsor "submit grant-newcomer"
step S 0 sponsor "publish grant-newcomer"
step S 0 sponsor "export grant-newcomer"
REF_JSON=$(jq -c . "$LAST")
step S 0 newcomer "import shared $REF_JSON"
step S 0 newcomer "refs"
CHILD_CAP=$(jq -r '.references[] | select(.name == "shared") | .observeCapability' "$LAST")
step S 0 newcomer "invoke first shared create 2 1"
step S 0 newcomer "submit first"
step S 0 newcomer "read shared"
check S "admitted pole: the grant holder reads field 2 = 1" is "$(field "$LAST" 2)" 1

# ------------------------------------------------------------- no-grant

step N 0 third "keygen mini.key"
op N "CUSTODY: copy third secret into sponsor home (co-signed enrollment)" \
  install -m 600 "$RUN/homes/third/keys/mini.key" "$RUN/homes/sponsor/keys/third-1.key"
step N 0 sponsor "enroll plan third-1 third-1.key"
step N 0 sponsor "enroll seal third-1"
step N 0 sponsor "enroll submit third-1"
THIRD_SUBJ=$(jq -r .subject "$LAST")
step N 0 third "init mini.key $THIRD_SUBJ"
step N 0 third "import stolen object $TARGET $CHILD_CAP"
rstep N no-grant third "read stolen"
rstep N no-grant third "invoke third-write stolen create 3 1"
cli() { # J expect-reason label, command... -- the plain mini client (no shell)
  local j=$1 reason=$2 label=$3 name rc got; shift 3
  N=$((N + 1)); name=$(printf '%02d-%s-cli' "$N" "$j")
  printf '%s\n' "$label" >"$LOG/$name.line"
  timed "$name" "$@"
  rc=$?
  got=$(reason_of "$LOG/$name.stderr")
  local v=ok; [[ $rc == 3 && $got == "$reason" ]] || v=FAIL
  printf '%s\t%s\t%s\t%s\n' "$name" "$reason" "${got:--}" cli >>"$LOG/reasons.tsv"
  row "$j" CLI "$label" 3 "$rc" "$WALL" "$v" "$(verdict_note "$name")"
}
jq -n --arg s "$THIRD_SUBJ" --arg t "$TARGET" --arg c "$CHILD_CAP" \
  --arg n "$(od -An -N8 -tu8 /dev/urandom | tr -d ' ')" \
  '{subject:$s,nonce:$n,purpose:{type:"query",kind:"object",target:$t,view:"resource"},
    grants:[{kind:"object",target:$t,capability:$c}]}' >"$RUN/third-query.json"
cli N no-grant "plain mini query by the third key with the newcomer's capability" \
  "$SHELL_MINI" query --socket "$SOCK" --host "$HOST" --config "$CONFIG" \
  --intent "$RUN/third-query.json" --key "$RUN/homes/third/keys/mini.key" --view resource \
  --dir "$RUN/third-query-attempt"
step N 0 third "import owner object $TARGET $OWNER_CAP"
rstep N no-grant third "read owner"

# ------------------------------------------------------------- unknown-key

step U 0 stranger "keygen mini.key"
step U 0 stranger "init mini.key 4242424242"
step U 0 stranger "import stolen object $TARGET $CHILD_CAP"
rstep U unknown-key stranger "read stolen"

# ------------------------------------------------------------- malformed / bad-signature / stale-root (raw)

head -c 64 /dev/urandom >"$RUN/garbage.bin"
raw M 3 malformed 5 "$RUN/garbage.bin" "query with 64 random bytes"
raw M 3 malformed 1 "$RUN/garbage.bin" "prepare with 64 random bytes"
step B 0 newcomer "read shared"
SIGNED=$(newest "$RUN/homes/newcomer/workspace" signed-observation.bin)
check B "the newcomer's read retained its signed observation" test -s "$SIGNED"
cp "$SIGNED" "$RUN/current-observation.bin"
python3 -c 'import sys; b=bytearray(open(sys.argv[1],"rb").read()); b[-1]^=1; open(sys.argv[2],"wb").write(b)' \
  "$RUN/current-observation.bin" "$RUN/flipped-observation.bin"
raw B 3 bad-signature 5 "$RUN/flipped-observation.bin" "the same observation with its last signature byte flipped"
raw B 0 - 5 "$RUN/current-observation.bin" "admitted pole: the unmodified observation, same image"
step R 0 newcomer "invoke move-on shared write 2 5 1"
step R 0 newcomer "submit move-on"
raw R 3 stale-root 5 "$RUN/current-observation.bin" "the same observation after the image moved"

# ------------------------------------------------------------- revoked

step V 0 sponsor "read shared"
SPONSOR_VIEW=$LAST
SPONSOR_CHALLENGE=$(newest "$R/sponsor" challenge.json)
op V "OPERATOR: hand-craft the revocation intent for the newcomer's grant (no revoke verb)" \
  bash -c "jq -n \
    --arg target '$TARGET' --arg owner '$OWNER_CAP' --arg control '$CONTROL_CAP' --arg child '$CHILD_CAP' \
    --arg root \"\$(jq -r '.page.root' '$SPONSOR_VIEW')\" \
    --arg auth \"\$(jq -r '.signing[0].authorityRoot' '$SPONSOR_CHALLENGE')\" \
    --arg n1 \"\$(od -An -N8 -tu8 /dev/urandom | tr -d ' ')\" --arg n2 \"\$(od -An -N8 -tu8 /dev/urandom | tr -d ' ')\" \
    '{subject:\"7\",nonce:\$n1,grants:[{kind:\"object\",target:\$target,capability:\$owner}],
      purpose:{type:\"prepare\",draft:{type:\"revoke-source\",command:{kind:\"object\",subject:\"7\",nonce:\$n2,
        target:\$target,victimKind:\"object\",capability:\$child,controlCapability:\$control,
        expectedTargetRoot:\$root,expectedAuthorityRoot:\$auth}}}}' \
    >'$RUN/revoke-intent.json'"
N=$((N + 1)); REVOKE_NAME=$(printf '%02d-V-operator' "$N")
printf 'sponsor signs and submits the revocation with mini submit\n' >"$LOG/$REVOKE_NAME.line"
timed "$REVOKE_NAME" "$PINNED_MINI" submit --socket "$SOCK" --host "$HOST" --config "$CONFIG" \
  --intent "$RUN/revoke-intent.json" --key "$R/sponsor.key" --dir "$R/sponsor/attempts/revoke-newcomer"
REVOKE_RC=$?
row V OPERATOR "sponsor signs and submits the revocation (mini submit)" 0 "$REVOKE_RC" "$WALL" \
  "$([[ $REVOKE_RC == 0 ]] && echo ok || echo FAIL)" ""
LAST=$LOG/$REVOKE_NAME.stdout
check V "revocation installed" jq -e '.type == "confirmed" and .confirmation == "installed"' "$LAST"
rstep V revoked newcomer "read shared"
rstep V revoked newcomer "invoke after-revoke shared write 2 6 5"
step V 0 sponsor "read shared"
check V "control: the sponsor still reads field 2 = 5" is "$(field "$LAST" 2)" 5

# ------------------------------------------------------------- law-denied

step L 0 sponsor 'law lockout shared {"type":"any","predicates":[]}'
step L 0 sponsor "submit lockout"
check L "deny-all installed" jq -e '.confirmation == "installed"' "$LAST"
rstep L law-denied sponsor "read shared"
rstep L law-denied sponsor 'law repair shared {"type":"all","predicates":[]}'
rstep L no-grant third "read owner"

# ------------------------------------------------------------- retained decodings

check X "every shell refusal frame is retained with the Host's own decoding, naming a reason" \
  bash -c "for f in '$RUN'/homes/*/refusals/*.json; do jq -e '.type == \"refused\" and (.reason | type == \"string\")' \"\$f\" >/dev/null || exit 1; done"

# ------------------------------------------------------------- end

op END "stop sshd" stop_sshd
op END "stop the Mini service" stop_server
trap - EXIT
cleanup

echo
column -t -s $'\t' "$LOG/reasons.tsv" | tee "$LOG/reasons.txt"
FAILS=$(awk -F'\t' 'NR > 1 && $8 != "ok"' "$TABLE" | wc -l)
echo "failed rows: $FAILS" | tee "$LOG/verdicts.txt"
echo "step table: $TABLE"
[[ $FAILS == 0 ]]
