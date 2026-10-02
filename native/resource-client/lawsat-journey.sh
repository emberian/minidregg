#!/usr/bin/env bash
# JLAWSAT: law satisfiability (C-SAT-2, Host op 150 `law-sat`).
#
# On a fresh private Store, the sponsor (subject 7) asks the Host whether laws
# can ever pass, before and after installing them:
#   the EVAL falsifier (field 1 <= 0; field 1 monotone; field 1 == 1): `law check`
#     says UNSATISFIABLE and names the two-constraint cycle; installing it is
#     refused locally; --allow-unsatisfiable installs it and the kernel then
#     refuses every write (the certificate was right);
#   three satisfiable laws (the falsifier without its `eq`, J13's board law, a
#     delta law): `can --any` prints a write to paste, and SUBMITTING THAT WRITE
#     IS ADMITTED by the kernel;
#   a law satisfiable in general but stuck from the cell's current value: the
#     certificate names the clause and the cell's value;
#   `sealed`: unsatisfiable with an empty certificate, and the override;
#   a read-only law: installed with the warning that it admits no write;
#   a law with a `ran` leaf: outside the fragment, the leaf named;
#   eleven independent disjunctions: undecided, the cap named.
# Around every query (law check, can --any): the world root and height and the
# Host's audit count are identical before and after.
#
# usage: lawsat-journey.sh HOST MINI STORE VERIFIER NEW_RUN_DIR [PORT]
#   HOST must answer op 150. NEW_RUN_DIR must not exist; a private sshd on
#   127.0.0.1:PORT (default 22436) and the Mini service run from it and are
#   stopped on exit.
set -uo pipefail
umask 077

if [[ $# -lt 5 || $# -gt 6 ]]; then
  sed -n '2,28p' "$0" >&2
  exit 64
fi
HOST=$1 MINI_SRC=$2 STORE=$3 VERIFIER=$4 RUN=$5 PORT=${6:-22436}
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
  for who in sponsor; do
    ssh-keygen -q -t ed25519 -N '' -C "jlawsat-$who" -f "$RUN/ssh/$who" || return 1
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
    ps -eo pid,args | grep -F "$RUN" | grep -v -e grep -e lawsat-journey.sh || echo none
  } >>"$LOG/cleanup.txt" 2>&1
}
trap cleanup EXIT

# ------------------------------------------------------------- the differential

world() {
  local err=$LOG/world-$N.err attempt
  "$MINI" workspace --action read --dir "$R/sponsor" --name ctl >/dev/null 2>"$err" || { echo "read-failed"; return 0; }
  attempt=$(sed -n 's/^workspace read attempt: //p' "$err" | tail -n1)
  jq -r '.worldRoot + "@" + .height' "$attempt/challenge.json"
}
audit_count() { "$HOST" "$CONFIG" audit 2>/dev/null | sed -n 's/^audited \([0-9]*\) .*/\1/p'; }

# qstep J line: one query (law check, can --any), with the differential.
qstep() {
  local j=$1 line=$2 before after ab aa
  before=$(world); ab=$(audit_count)
  step "$j" 0 sponsor "$line"
  Q=$LOG/q-$(printf '%02d' "$N").txt
  cp "$LAST" "$Q"
  after=$(world); aa=$(audit_count)
  QS=$((QS + 1))
  printf '%s\t%s\t%s\t%s\t%s\n' "$N" "$line" "$before" "$after" "$ab/$aa" >>"$LOG/differential.tsv"
  check "$j" "world root+height unchanged by the query ($before)" is "$after" "$before"
  check "$j" "audit count unchanged by the query ($ab)" is "$aa" "$ab"
}
QS=0
printf 'n\tline\tbefore\tafter\taudit\n' >"$LOG/differential.tsv"
says() { grep -Fq -- "$2" "$1" || { echo "no [$2] in $1:"; cat "$1"; return 1; }; }
saysnt() { ! grep -Fq -- "$2" "$1" || { echo "unexpected [$2] in $1"; return 1; }; }
count() { is "$(grep -Fc -- "$2" "$1")" "$3"; }
err() { echo "$LOG/$LAST_NAME.stderr"; }
# paste FILE -> the `invoke ID …` line can --any printed, without `invoke ID `
paste_of() { sed -n 's/^    invoke ID //p' "$1" | head -n1; }
nonempty() { [[ -n $1 ]] || { echo "empty"; return 1; }; }

# ------------------------------------------------------------- setup

echo "run: $RUN"
op S "bootstrap fresh private Store, sponsor workspace, mini serve" \
  sh "$REPO/native/resource-client/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$R"
op S "ssh key, rendered authorized_keys, private sshd on 127.0.0.1:$PORT" setup_sshd
OPEN='{"type":"all","predicates":[]}'
for c in ctl f adm board dl st sl ro; do
  # Closed declarations name the fields each later scenario actually uses.
  case $c in
    f|adm|st) fields=1 ;;
    board|dl) fields=2 ;;
    *) fields= ;;
  esac
  step S 0 sponsor "create $c declared $OPEN${fields:+ $fields}"
done
# These scenarios assume an existing field 1 at zero: the falsifier must fail
# its equality clause, adm must remain readable, and st later writes 0 -> 3.
for c in f adm st; do
  step S 0 sponsor "invoke seed-$c $c create 1 0"
  step S 0 sponsor "submit seed-$c"
  step S 0 sponsor "read $c"
  check S "$c: signed read confirms field 1 starts at 0" is "$(field "$LAST" 1)" 0
done
world_ok() { [[ $(world) != read-failed ]]; }
check S "the differential's signed read of ctl answers" world_ok
step S 0 sponsor "help law"
check S "help law names check and --allow-unsatisfiable" says "$LAST" "law check"
check S "help law names the override" says "$LAST" "--allow-unsatisfiable"

# ------------------------------------------------------------- F: the EVAL falsifier

FALS="field 1 <= 0; field 1 monotone; field 1 == 1"
qstep F "law check \"$FALS\""
check F "check: UNSATISFIABLE" says "$Q" "UNSATISFIABLE: this law admits no step."
check F "check: one cycle, its clauses contradict" says "$Q" "these clauses contradict:"
check F "check: constraint field 1 <= 0 from clause [0]" grep -Eq '^  field 1 <= 0 +from clause \[0\] `field 1 <= 0`$' "$Q"
check F "check: constraint field 1 >= 1 from clause [2] (the eq)" grep -Eq '^  field 1 >= 1 +from clause \[2\] `field 1 == 1`$' "$Q"
check F "check: exactly the two-constraint cycle (monotone is not in it)" count "$Q" " from clause [" 2
check F "check: the sum line" says "$Q" "0 <= -1"
step F 1 sponsor "law lf f \"$FALS\""
check F "install refused locally: law-unsatisfiable" says "$(err)" "law-unsatisfiable: this law can never pass"
check F "install refusal names the clauses" says "$(err)" 'clause [2] `field 1 == 1`'
check F "install refusal says sealed is legitimate and names the override" says "$(err)" "--allow-unsatisfiable"
check F "nothing was proposed" bash -c "[[ ! -e '$R/sponsor/proposals/lf' ]]"
step F 0 sponsor "law lf2 f \"$FALS\" --allow-unsatisfiable"
check F "override: installed anyway, and said so" says "$(err)" "installing it anyway (--allow-unsatisfiable)"
step F 0 sponsor "submit lf2"
# The law judges every verb, so the kernel refuses even the read a write is
# drafted from: no write on f can be planned, let alone admitted.
step F 3 sponsor "invoke fw0 f write 1 0 0"
check F "kernel refuses the write 1: 0 -> 0 (le holds, eq fails): law-denied" says "$(err)" "refused: law-denied: field 1 == 1"
step F 3 sponsor "invoke fw1 f write 1 1 0"
check F "kernel refuses the write 1: 0 -> 1 (eq holds): law-denied" says "$(err)" "refused: law-denied"
step F 3 sponsor "read f"
check F "kernel refuses the read too: law-denied" says "$(err)" "refused: law-denied"
check F "nothing about f was ever admitted: no attempt retained for fw0/fw1" bash -c "[[ ! -e '$R/sponsor/proposals/fw0/intent.json' && ! -e '$R/sponsor/proposals/fw1/intent.json' ]]"

# ------------------------------------------------------------- A: the falsifier without the eq

ADM="field 1 <= 0; field 1 monotone"
qstep A "law check \"$ADM\""
check A "check: satisfiable, with a witness" says "$Q" "satisfiable: admits e.g."
check A "check: writes admitted too" says "$Q" "writes: admits e.g."
step A 0 sponsor "law la adm \"$ADM\""
step A 0 sponsor "submit la"
qstep A "can --any adm"
check A "can --any: a write to paste" says "$Q" "    invoke ID adm write 1 "
PA=$(paste_of "$Q")
check A "can --any: the paste line ($PA)" nonempty "$PA"
step A 0 sponsor "invoke wa $PA"
step A 0 sponsor "submit wa"
check A "THE WITNESS IS ADMITTED: submit wa exit 0" is "$(cat "$LOG/$LAST_NAME.exit")" 0
step A 0 sponsor "read adm"
check A "field 1 is the witness value" is "$(field "$LAST" 1)" "$(echo "$PA" | awk '{print $4}')"

# ------------------------------------------------------------- B: J13's board law

step B 0 sponsor "invoke b0 board create 2 1"
step B 0 sponsor "submit b0"
BOARD="any [ verb == read, verb == write, all [ verb in {delegate,install,revoke}, subject == 7 ] ]; any [ field 2 monotone, not (verb == write) ]; any [ field 2 in {0,1,2}, not (verb == write) ]"
qstep B "law check \"$BOARD\""
check B "check: satisfiable" says "$Q" "satisfiable: admits e.g."
check B "check: writes admitted" says "$Q" "writes: admits e.g."
step B 0 sponsor "law lb board \"$BOARD\""
step B 0 sponsor "submit lb"
qstep B "can --any board"
check B "can --any: a write of field 2 (the field the law reads)" says "$Q" "    invoke ID board write 2 "
PB=$(paste_of "$Q")
step B 0 sponsor "invoke wb $PB"
step B 0 sponsor "submit wb"
check B "THE WITNESS IS ADMITTED: submit wb exit 0" is "$(cat "$LOG/$LAST_NAME.exit")" 0
step B 0 sponsor "read board"
check B "field 2 is the witness value" is "$(field "$LAST" 2)" "$(echo "$PB" | awk '{print $4}')"
step B 0 sponsor "invoke bd board write 2 0 $(field "$LAST" 2)"
step B 3 sponsor "submit bd"
check B "control: a write the law forbids is refused (monotone)" says "$(err)" "field 2 monotone"

# ------------------------------------------------------------- D: a delta law

step D 0 sponsor "invoke d0 dl create 2 5"
step D 0 sponsor "submit d0"
DL="any [ verb in {read,delegate,install,revoke}, all [ verb == write, field 2 delta == 3 ] ]"
step D 0 sponsor "law ld dl \"$DL\""
step D 0 sponsor "submit ld"
qstep D "can --any dl"
check D "can --any: field 2 from 5 to 8 (delta 3)" says "$Q" "    invoke ID dl write 2 8 5"
PD=$(paste_of "$Q")
step D 0 sponsor "invoke wd $PD"
step D 0 sponsor "submit wd"
check D "THE WITNESS IS ADMITTED: submit wd exit 0" is "$(cat "$LOG/$LAST_NAME.exit")" 0
step D 0 sponsor "read dl"
check D "field 2 = 8" is "$(field "$LAST" 2)" 8

# ------------------------------------------------------------- T: stuck from here

step T 0 sponsor "invoke t0 st write 1 3 0"
step T 0 sponsor "submit t0"
ST="any [ field 1 <= 0, not (verb == write) ]; any [ field 1 monotone, not (verb == write) ]"
step T 0 sponsor "law lt st \"$ST\""
step T 0 sponsor "submit lt"
qstep T "can --any st"
check T "can --any: writes exist in general, none from here" says "$Q" "none that changes one field from the cell as it is now"
check T "the certificate names clause [0] (field 1 <= 0)" says "$Q" 'clause [0] `any [ field 1 <= 0, not (verb == write) ]` (its part `field 1 <= 0`)'
check T "the certificate names the cell's current value" says "$Q" 'the cell now: `field 1 before == 3`'

# ------------------------------------------------------------- S: sealed

qstep S "law check sealed"
check S "sealed: UNSATISFIABLE" says "$Q" "UNSATISFIABLE"
check S "sealed: the empty certificate reads as sealed" says "$Q" 'like `sealed` (`any []`), it admits nothing'
step S 1 sponsor "law ls sl sealed"
check S "sealed install refused locally" says "$(err)" "law-unsatisfiable"
check S "the refusal says sealed is a legitimate use" says "$(err)" "a law that admits nothing is a legitimate choice"
step S 0 sponsor "law ls2 sl sealed --allow-unsatisfiable"
step S 0 sponsor "submit ls2"
step S 3 sponsor "read sl"
check S "sealed cell: read law-denied: sealed" says "$(err)" "law-denied: sealed"

# ------------------------------------------------------------- R: read-only

qstep R "law check \"verb == read\""
check R "read-only: satisfiable" says "$Q" "satisfiable: admits e.g."
check R "read-only: WARNING no write" says "$Q" "WARNING: this law admits no write."
check R "read-only: the certificate names the law's verb == read" says "$Q" 'from the law `verb == read`'
check R "read-only: and the check's own verb == write" says "$Q" "from the check's own \`verb == write\`"
step R 0 sponsor "law lr ro \"verb == read\""
check R "install proceeds with the warning" says "$(err)" "law check: WARNING: this law admits no write."
step R 0 sponsor "submit lr"

# ------------------------------------------------------------- O: outside (ran)

RAN='{"type":"all","predicates":[{"type":"le","slot":"resource/field/1/after","value":"5"},{"type":"ran","program":"7"}]}'
qstep O "law check $RAN"
check O "outside, the ran leaf named at its path" says "$Q" 'outside the decidable fragment: `ran 7` (at [1])'

# ------------------------------------------------------------- U: past the cap

U=""
for i in $(seq 1 11); do U="$U${U:+; }any [ field $i monotone, field $i == 5 ]"; done
qstep U "law check \"$U\""
check U "eleven independent disjunctions: undecided, the cap named" says "$Q" "cap of 1024 systems"
U10=""
for i in $(seq 1 10); do U10="$U10${U10:+; }any [ field $i monotone, field $i == 5 ]"; done
qstep U "law check \"$U10\""
check U "ten fit under the cap: decided" says "$Q" "satisfiable: admits e.g."

# ------------------------------------------------------------- end

op END "stop sshd" stop_sshd
op END "stop the Mini service" stop_server
trap - EXIT
cleanup

FAILS=$(awk -F'\t' 'NR > 1 && $8 != "ok"' "$TABLE" | wc -l)
ROWS=$(awk 'NR > 1' "$TABLE" | wc -l)
echo "rows: $ROWS  failed: $FAILS  queries: $QS (each with root+height and audit differential)" | tee "$LOG/verdicts.txt"
echo "step table: $TABLE"
# The journey hook reports the final stderr line on failure.
echo "JLAWSAT: $FAILS of $ROWS rows failed (see $TABLE)" >&2
[[ $FAILS == 0 ]]
