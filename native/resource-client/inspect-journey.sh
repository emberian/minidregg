#!/usr/bin/env bash
# JINSPECT: the moldable inspector's first views (K-INSPECT-VIEWS, DEOS #13).
#
# On a fresh private Store, A (the sponsor) and B (a newcomer) look at what
# they hold through `inspect` views: Lean renderers (Host `inspect
# cap-tree|law|why|turn|receipt`) over bytes the client already holds or reads
# with its own signed views. No view commits anything.
#
#   A's `inspect caps board` draws the delegation to B as an edge root -> child,
#     with its narrowing; B's draws only B's branch (its record's lineage);
#   `inspect law board` prints the installed law (P-LAW's J13 law) from the
#     Host's compiled policy, clause by clause; the printed line, parsed again by
#     the shell's law grammar, is the Host's predicate (compared as JSON);
#   B's refused writes, then `why`: the failing clause, the slot values it was
#     judged on, and the request value that passes it; `why` reveals nothing
#     beyond the Host's own refusal frame (compared field by field);
#   `inspect turn` of a write lists its legs and footprint (compared with the
#     Host's `inspect plan` of the same plan) and commits nothing (world
#     root+height and audit identical); `inspect receipt` after the submit;
#   a restart prints the same views.
#
# usage: inspect-journey.sh HOST MINI STORE VERIFIER NEW_RUN_DIR [PORT]
#   as affordances-journey.sh (default PORT 22436).
set -uo pipefail
umask 077

if [[ $# -lt 5 || $# -gt 6 ]]; then
  sed -n '2,24p' "$0" >&2
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

# The Store's socket will be $RUN/store/public/mini.sock, and a Unix socket
# path is at most 107 bytes (sun_path). Refuse a longer one here, by name,
# rather than let `mini serve` fail to bind and every later row cascade.
SOCK_WOULD_BE=$RUN/store/public/mini.sock
if (( ${#SOCK_WOULD_BE} >= 108 )); then
  echo "socket path would be ${#SOCK_WOULD_BE} bytes (>= 108, sun_path): $SOCK_WOULD_BE; use a shorter NEW_RUN_DIR" >&2
  exit 64
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
    ssh-keygen -q -t ed25519 -N '' -C "jinspect-$who" -f "$RUN/ssh/$who" || return 1
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
    ps -eo pid,args | grep -F "$RUN" | grep -v -e grep -e inspect-journey.sh || echo none
  } >>"$LOG/cleanup.txt" 2>&1
}
trap cleanup EXIT

# ------------------------------------------------------------- the differential

world() {
  local err=$LOG/world-$N.err attempt
  "$MINI" workspace --action read --dir "$R/sponsor" --name board >/dev/null 2>"$err" || { echo "read-failed"; return 0; }
  attempt=$(sed -n 's/^workspace read attempt: //p' "$err" | tail -n1)
  jq -r '.worldRoot + "@" + .height' "$attempt/challenge.json"
}
audit_count() { "$HOST" "$CONFIG" audit 2>/dev/null | sed -n 's/^audited \([0-9]*\) .*/\1/p'; }
printf 'n\twho\tline\tbefore\tafter\taudit\n' >"$LOG/differential.tsv"
VIEWS=0

# vstep J who line: one view, with the root/height and audit differential;
# its stdout is kept as $V.
vstep() {
  local j=$1 who=$2 line=$3 before after ab aa
  before=$(world); ab=$(audit_count)
  step "$j" 0 "$who" "$line"
  V=$LOG/view-$(printf '%02d' "$N")-$who.out
  cp "$LAST" "$V"
  after=$(world); aa=$(audit_count)
  VIEWS=$((VIEWS + 1))
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$N" "$who" "$line" "$before" "$after" "$ab/$aa" >>"$LOG/differential.tsv"
  check "$j" "world root+height unchanged by '$line'" is "$after" "$before"
  check "$j" "audit count unchanged by '$line' ($ab)" is "$aa" "$ab"
}
jqv() { jq -e "$@" "$V" >/dev/null || { echo "jq $* failed on $V"; cat "$V"; return 1; }; }
differs() { [[ $1 != "$2" ]] || { echo "root did not move: $1"; return 1; }; }
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
  bash -c "mkdir -p -m 700 '$RUN/homes/sponsor/keys' && install -m 600 '$RUN/homes/newcomer/keys/mini.key' '$RUN/homes/sponsor/keys/newcomer-1.key' && install -m 644 '$RUN/homes/newcomer/keys/mini.key.next.pub' '$RUN/homes/sponsor/keys/newcomer-1.key.next.pub'"
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

# ------------------------------------------------------------- C: cap trees

# The J3-shaped delegation: observe+mutate (no control) to B, maxCost 50000.
step C 0 sponsor "delegate wb board $B_SUBJ observe,mutate 50000"
step C 0 sponsor "submit wb"
step C 0 sponsor "publish wb"
step C 0 sponsor "export wb"
REF_JSON=$(jq -c . "$LAST")
CHILD=$(jq -r .capability "$LAST")
step C 0 newcomer "import board $REF_JSON"
ROOT=$(jq -r .operationCapability "$R/sponsor/refs/board.json")
CONTROL=$(jq -r .controlCapability "$R/sponsor/refs/board.json")
TARGET=$(jq -r .target "$R/sponsor/refs/board.json")
echo "root $ROOT control $CONTROL child $CHILD target $TARGET" >"$LOG/ids.txt"

vstep C sponsor "inspect caps board --json"
check C "owner: the delegation is an edge root -> child" jqv --arg c "$CHILD" --arg p "$ROOT" '[.edges[] | select(.child == $c and .parent == $p)] | length == 1'
check C "owner: the edge states its narrowing" jqv --arg c "$CHILD" '.edges[] | select(.child == $c) | .narrows | test("targets ⊆, verbs ⊆, maxCost 50000 ≤ ")'
check C "owner: the child is B's, observe+mutate, maxCost 50000, from my delegation wb (installed)" \
  jqv --arg c "$CHILD" --arg b "subject $B_SUBJ" '.nodes[] | select(.id == $c) | .holder == $b and .verbs == ["observe","mutate"] and .maxCost == "50000" and (.sources | index("my delegation wb, installed") != null)'
check C "owner: no widening drawn" jqv '.widenings == []'
check C "owner: every node id appears exactly once" jqv '[.nodes[].id] | length == (unique | length)'
check C "owner: the control capability is shown, not omitted (readable or [not readable])" jqv --arg k "$CONTROL" '[.nodes[] | select(.id == $k)] | length == 1'
OWNER_CAPS=$V
vstep C sponsor "inspect caps board"
check C "owner text: the edge is drawn with its narrowing" grep -q '└─ narrows: targets ⊆, verbs ⊆, maxCost 50000' "$V"
OWNER_CAPS_TEXT=$V

vstep C newcomer "inspect caps board --json"
check C "reader: one edge root -> child (from its record's lineage)" jqv --arg c "$CHILD" --arg p "$ROOT" '[.edges[] | {child, parent}] == [{"child":$c,"parent":$p}]'
check C "reader: only its branch: exactly the root and its own capability" jqv --arg c "$CHILD" --arg p "$ROOT" '[.nodes[].id] | sort == ([$c, $p] | sort)'
check C "reader: the root came from lineage, the child from its own record" \
  jqv --arg c "$CHILD" --arg p "$ROOT" '(.nodes[] | select(.id == $p) | .sources == ["lineage"]) and (.nodes[] | select(.id == $c) | .sources == ["record"])'
check C "reader: the owner's control capability is not in the reader's tree" jqv --arg k "$CONTROL" '[.nodes[] | select(.id == $k)] == []'
READER_CAPS=$V

# ------------------------------------------------------------- L: the law

step L 0 newcomer "invoke first board create 2 1"
step L 0 newcomer "submit first"
JLAW="any [ verb == read, verb == write, all [ verb in {delegate,install,revoke}, subject == $A_SUBJ ] ]; any [ field 2 monotone, not (verb == write) ]; any [ field 2 in {0,1,2}, not (verb == write) ]"
step L 0 sponsor "law jl board \"$JLAW\""
step L 0 sponsor "submit jl"
step L 0 newcomer "invoke up board write 2 2 1"
step L 0 newcomer "submit up"
vstep L sponsor "inspect law board --json"
check L "law: printed from the Host's compiled policy, exactly P-LAW's J13 line" jqv --arg l "$JLAW" '.law == $l'
check L "law: three clauses, indexed 0..2" jqv '[.clauses[].index] == ["0","1","2"]'
check L "law: the token round trip holds (law_print_parse, evaluated)" jqv '.roundTrip == true'
check L "law: field 2's current value from the reader's own read" jqv '.slots[] | select(.rendered == "field 2") | .now == "2 now"'
LAW_LINE=$(jq -r .law "$V")
OWNER_LAW=$V
POLICY_VIEW=$(ls -t "$R"/sponsor/attempts/*/view.json | while read -r f; do jq -e '.type == "policy"' "$f" >/dev/null 2>&1 && { echo "$f"; break; }; done)
echo "policy view: $POLICY_VIEW" >>"$LOG/ids.txt"
step L 0 sponsor "law rt board \"$LAW_LINE\""
same_predicate() { [[ -n $POLICY_VIEW ]] && diff <(jq -S .predicate "$POLICY_VIEW") <(jq -S .predicate "$R/sponsor/proposals/rt/request.json"); }
check L "law: the printed line, parsed by the shell's grammar, is the Host's compiled predicate" same_predicate
vstep L newcomer "inspect law board"
check L "reader: the law text view prints the same line" grep -qF "  $JLAW" "$V"

# ------------------------------------------------------------- W: why

newest_refusal() { find "$RUN/homes/$1/refusals" -name '*.json' -printf '%T@ %p\n' 2>/dev/null | sort -n | tail -n1 | cut -d' ' -f2-; }
same_as_frame() { # why-json frame-json: the why view carries nothing the Host's frame did not
  jq -e -n --slurpfile w "$1" --slurpfile f "$2" '$w[0].before == $f[0].leaf.before and $w[0].after == $f[0].leaf.after and $w[0].path == $f[0].leaf.path and ($f[0].explain | startswith($w[0].clause))' >/dev/null
}
step W 0 newcomer "invoke down board write 2 1 2"
step W 3 newcomer "submit down"
DOWN_FRAME=$(newest_refusal newcomer)
vstep W newcomer "why --json"
check W "why: the attempt is 'down'" jqv '.attempt == "down"'
check W "why: names the clause field 2 monotone" jqv '.reason == "law-denied" and .clause == "field 2 monotone"'
check W "why: the slot values it was judged on (before 2, after 1)" jqv '.slot == "resource/field/2/after" and .before == "2" and .after == "1"'
check W "why: the request value that passes it (2)" jqv '.suggestion.value == "2" and .suggestion.relation == ">= 2"'
check W "why reveals only the refusal frame's own values (vs the Host's decoding of the retained frame)" same_as_frame "$V" "$DOWN_FRAME"
step W 0 newcomer "invoke out board write 2 5 2"
step W 3 newcomer "submit out"
OUT_FRAME=$(newest_refusal newcomer)
vstep W newcomer "why --json"
check W "why: the out-of-set write names field 2 in {0,1,2}" jqv '.attempt == "out" and .clause == "field 2 in {0,1,2}" and .after == "5"'
check W "why: the nearest passing value (2, you asked 5)" jqv '.suggestion.value == "2" and .suggestion.relation == "in {0,1,2}"'
check W "why reveals only the refusal frame's own values (out)" same_as_frame "$V" "$OUT_FRAME"
vstep W newcomer "why down"
check W "why ATTEMPT: the text names clause, values and the fix" grep -q 'to pass it: field 2 >= 2 — e.g. 2 (you asked 1)' "$V"
WHY_DOWN_TEXT=$V

# ------------------------------------------------------------- T: turn and receipt

step T 0 newcomer "read board"
F1=$(field "$LAST" 1)
F1N=$((F1 + 5))
step T 0 newcomer "invoke t1 board write 1 $F1N $F1"
W0=$(world)
vstep T newcomer "inspect turn t1 --json"
check T "turn: the leg writes board's cell, field 1 := $F1N (expected $F1)" \
  jqv --arg t "$TARGET" --arg w "    write field 1 := $F1N (expected $F1)" '(.legs | map(select(test("writes cell object " + $t))) | length == 1) and (.legs | index($w) != null)'
check T "turn: not submitted" jqv '.outcome == null and (.text | test("nothing was submitted"))'
TURN=$V
DRY_PLAN=$(ls -td "$RUN"/homes/newcomer/workspace/attempts/*/ | while read -r d; do [[ -f $d/dry-run-plan.bin ]] && { echo "${d}dry-run-plan.bin"; break; }; done)
echo "turn plan: $DRY_PLAN" >>"$LOG/ids.txt"
"$HOST" "$CONFIG" inspect plan "$DRY_PLAN" "$LOG/turn-plan.json" >/dev/null 2>"$LOG/turn-plan.err"
same_footprint() { [[ -s $LOG/turn-plan.json ]] && diff <(jq -c '[.slots[] | [.signing.footprint[].address]]' "$LOG/turn-plan.json") <(jq -c '[.slots[] | [.reads[].canonical]]' "$TURN"); }
check T "turn_view_matches_footprint, measured: the listed reads are the Host's own decoding of the same plan" same_footprint
nonempty_footprint() { jq -e '[.slots[].reads[]] | length > 0' "$TURN" >/dev/null; }
check T "turn: the footprint is not empty (the comparison is not vacuous)" nonempty_footprint
step T 0 newcomer "submit t1"
W1=$(world)
check T "falsifier: the differential sees a real commit (submit t1 moved root+height)" differs "$W0" "$W1"
vstep T newcomer "inspect receipt t1 --json"
check T "receipt: committed, and its world root is the root the world reads right after the submit" jqv --arg r "${W1%@*}" '.outcome.worldRoot == $r'
same_legs() { diff <(jq -c .legs "$TURN") <(jq -c .legs "$V"); }
check T "receipt: the committed legs are exactly the turn's (what it said it would write)" same_legs
step T 0 newcomer "invoke td board write 2 0 2"
W2=$(world)
step T 3 newcomer "inspect turn td"
check T "a refused turn names the clause through the why view" grep -q 'failing clause \[1\]: field 2 monotone' "$LAST"
check T "a refused turn commits nothing" is "$(world)" "$W2"

# ------------------------------------------------------------- X: restart, same views

op X "stop the Mini service" stop_server
op X "start the Mini service on the same Store" start_server
vstep X sponsor "inspect caps board --json"
check X "restart: owner's cap tree identical" diff "$OWNER_CAPS" "$V"
vstep X sponsor "inspect caps board"
check X "restart: owner's cap tree text identical" diff "$OWNER_CAPS_TEXT" "$V"
vstep X newcomer "inspect caps board --json"
check X "restart: reader's cap tree identical" diff "$READER_CAPS" "$V"
vstep X sponsor "inspect law board --json"
check X "restart: law identical" diff "$OWNER_LAW" "$V"
vstep X newcomer "why down"
check X "restart: why identical" diff "$WHY_DOWN_TEXT" "$V"

# ------------------------------------------------------------- U: an undisclosed refusal

# A blind submission names no reason (MR's rule): B prepares and signs a write
# now (prepare-only, B's own client run directly; the shell has no verb for
# it), A seals board, B submits the retained call blind (`retry`). `why` says
# the refusal was undisclosed and shows what the dry run of the same command
# says now, to a requester whose signed observation op 1 accepts.
BWS=$RUN/homes/newcomer/workspace
step U 0 newcomer "invoke u1 board write 1 6 5"
op U "B prepares and signs u1 without submitting (prepare-only)" \
  "$MINI" workspace --action submit --dir "$BWS" --intent "$BWS/proposals/u1/intent.json" --attempt "$BWS/attempts/u1" --prepare-only true
step U 0 sponsor "law seal2 board sealed --allow-unsatisfiable"
step U 0 sponsor "submit seal2"
step U 3 newcomer "retry u1"
vstep U newcomer "why --json"
check U "why: the blind submission's refusal is undisclosed" jqv '.attempt == "u1" and .reason == "undisclosed" and .clause == null'
check U "why: the dry run of the same command, now, names the clause (sealed)" jqv '.dryRun.reason == "law-denied" and .dryRun.clause == "sealed"'

# ------------------------------------------------------------- end

op END "stop sshd" stop_sshd
op END "stop the Mini service" stop_server
trap - EXIT
cleanup

FAILS=$(awk -F'\t' 'NR > 1 && $8 != "ok"' "$TABLE" | wc -l)
ROWS=$(awk 'NR > 1' "$TABLE" | wc -l)
echo "rows: $ROWS  failed: $FAILS  views: $VIEWS (each with root+height and audit differential)" | tee "$LOG/verdicts.txt"
echo "step table: $TABLE"
[[ $FAILS == 0 ]]
