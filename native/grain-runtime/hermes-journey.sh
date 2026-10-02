#!/bin/bash
# Hosted Hermes as a participant on a fresh Store (goal item 5, K7/C3).
#
# A human sponsor and a human friend share one Store with a hosted Hermes
# grain. Hermes does J4 (signed read, write field 2 := 1, readback) through
# the controller's MCP tools, which call the same `mini workspace` client the
# humans use. The controller is SIGKILLed while Hermes's write is in flight;
# its systemd unit restarts it; the controller's own startup recovery
# resolves the attempt (performed / refused / uncertain) and reconciles what
# it can prove, with no operator command. Hermes then reports the attempt and
# reads back, delegates observation to the friend and exports the recipient
# reference, which the friend imports with the ordinary CLI and reads.
#
# The agent is fixture/hermes-deterministic-acp (a scripted ACP+MCP peer,
# no inference) running as /agent/hermes-acp inside the real bwrap/systemd
# worker sandbox. Verdicts come from retained artifacts, never from exit
# codes of wrappers.
set -euo pipefail
umask 077

if [ "$#" -ne 6 ]; then
  echo "usage: $0 HOST MINI STORE VERIFIER GRAIN_RUNTIME NEW_RUN_DIRECTORY" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 GRAIN=$5 RUN=$6
TASK=${HERMES_JOURNEY_TASK:-8751}
TOOL_TASK=$((TASK + 1))
UNIT=mini-grain-controller@$TASK
for item in "$HOST" "$MINI" "$STORE" "$VERIFIER" "$GRAIN" "$RUN"; do
  case "$item" in /*) ;; *) echo "paths must be absolute: $item" >&2; exit 2;; esac
done
for item in "$HOST" "$MINI" "$STORE" "$VERIFIER" "$GRAIN"; do
  [ -x "$item" ] || { echo "not executable: $item" >&2; exit 2; }
done
[ "$(uname -s)" = Linux ] || { echo 'Linux user systemd is required' >&2; exit 2; }
for tool in jq python3 rustc systemctl systemd-run sha256sum bwrap; do
  command -v "$tool" >/dev/null || { echo "missing $tool" >&2; exit 2; }
done
[ ! -e "$RUN" ] || { echo 'run directory exists' >&2; exit 2; }
state=$(systemctl --user show -p LoadState --value "$UNIT.service" 2>/dev/null || :)
[ "$state" = not-found ] || { echo "unit $UNIT is already loaded ($state)" >&2; exit 2; }

HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
mkdir -m 700 "$RUN"
RUN=$(CDPATH='' cd -- "$RUN" && pwd)
EV=$RUN/evidence
mkdir -m 700 "$EV" "$RUN/keys"
TIMELINE=$EV/timeline.tsv
: >"$TIMELINE"
mark() { printf '%s\t%s\n' "$(date +%s.%N)" "$*" | tee -a "$TIMELINE" >&2; }
fail() { mark "FAIL $*"; exit 1; }

ROOT=$RUN/store
SERVER_PID=
CONNECTOR_PID=
cleanup() {
  set +e
  if [ -n "$CONNECTOR_PID" ]; then kill "$CONNECTOR_PID" 2>/dev/null; wait "$CONNECTOR_PID" 2>/dev/null; fi
  if [ "$(systemctl --user show -p Description --value "$UNIT.service" 2>/dev/null)" = "mini-hermes-journey:$RUN" ]; then
    systemctl --user stop "$UNIT.service" >/dev/null 2>&1
  fi
  systemctl --user reset-failed "$UNIT.service" >/dev/null 2>&1
  if [ -f "$ROOT/public/server.pid" ]; then
    pid=$(cat "$ROOT/public/server.pid")
    case "$(tr '\0' ' ' </proc/"$pid"/cmdline 2>/dev/null)" in
      *" serve "*"--socket $ROOT/public/mini.sock"*) kill "$pid"; sleep 1 ;;
    esac
  fi
  mark "services stopped"
}
trap cleanup EXIT

sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$GRAIN" "$0" \
  "$HERE/fixture/hermes-deterministic-acp" "$REPO/deploy/grain-host/bwrap" \
  "$REPO/deploy/grain-host/launch-gate.rs" \
  "$REPO/native/resource-client/newparticipant-acceptance.sh" >"$EV/inputs.sha256"
confirmed() {
  jq -e '.type == "confirmed" and (.confirmation == "installed" or .confirmation == "replayed")' "$1" >/dev/null
}

# --- Store: sponsor + the hosted grain's two genesis subjects ---------------
"$MINI" keygen --secret "$RUN/keys/hermes-host.key" --public "$RUN/keys/hermes-host.pub" >/dev/null
"$MINI" keygen --secret "$RUN/keys/hermes.key" --public "$RUN/keys/hermes.pub" >/dev/null
HOST_PUB=$(od -An -tx1 -v "$RUN/keys/hermes-host.pub" | tr -d ' \n')
HERMES_PUB=$(od -An -tx1 -v "$RUN/keys/hermes.pub" | tr -d ' \n')
jq -n --arg h "$HOST_PUB" --arg w "$HERMES_PUB" '[
  {key:{keyId:"8008",keyEpoch:"2",algorithm:"1",subject:"8",publicKey:$h,
    activeFrom:"0",activeUntil:"1000000"},
   accountId:"8",spendCapabilityId:"42",controlCapabilityId:"52",
   factoryObserveCapabilityId:"55",initialBalance:"100",
   accountPredicate:{type:"all",predicates:[]}},
  {key:{keyId:"9009",keyEpoch:"2",algorithm:"1",subject:"9",publicKey:$w,
    activeFrom:"0",activeUntil:"1000000"},
   accountId:"9",spendCapabilityId:"43",controlCapabilityId:"56",
   factoryObserveCapabilityId:"57",initialBalance:"100",
   accountPredicate:{type:"all",predicates:[]}}]' >"$RUN/hermes-genesis-enrollments.json"
mark "bootstrap start"
EXTRA_GENESIS_ENROLLMENTS=$RUN/hermes-genesis-enrollments.json \
  sh "$REPO/native/resource-client/newparticipant-acceptance.sh" \
  "$HOST" "$MINI" "$STORE" "$VERIFIER" "$ROOT" >"$EV/bootstrap.stdout" 2>"$EV/bootstrap.stderr"
CONFIG=$ROOT/deployment/pinned-config.json
SOCK=$ROOT/public/mini.sock
mark "bootstrap done: sponsor workspace, public socket"

# --- The hosted grain: birth (genesis image only), witness delegation -------
jq -n --slurpfile g "$ROOT/genesis.json" --arg t "$TASK" --arg tt "$TOOL_TASK" '
  {subject:"7",nonce:"22000",birth:{genesis:$g[0],
   template:{issuer:"5",ownerBudget:"100000",lifetime:"10000"},creator:"7",nonce:"22000",
   resources:[{kind:"object",storage:"grain",target:$t,owner:"8",ownerCapability:"8761",
     controlCapability:"8762",budget:"100",workerSubject:"9",workerGeneration:"1"},
    {kind:"object",storage:"grain",target:$tt,owner:"9",ownerCapability:"8771",
     controlCapability:"8772",budget:"50"}],
   sourceCapabilities:["41"],funding:[],feePayer:"7"},
   grants:[{kind:"object",target:"10",capability:"54"},{kind:"account",target:"7",capability:"41"}]}' \
  >"$RUN/grain-birth-intent.json"
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCK" \
  --intent "$RUN/grain-birth-intent.json" --intent-kind birth-intent \
  --key "$ROOT/sponsor.key" --dir "$RUN/grain-birth" >"$EV/grain-birth.stdout" 2>&1
confirmed "$RUN/grain-birth/outcome.json" || fail "grain birth not confirmed"
cp "$RUN/grain-birth/outcome.json" "$EV/grain-birth-outcome.json"
mark "hosted grain born: parent $TASK owner 8 worker 9, tool $TOOL_TASK owner 9"

# The host subject grants the worker subject its parent-witness capability
# through the ordinary workspace client: the child lifetime and ancestry come
# from the signed parent capability head, and its ID from the namespace.
"$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCK" \
  --key "$RUN/keys/hermes-host.key" --subject 8 --namespace-root "$ROOT/namespace" \
  --dir "$RUN/host-workspace" >/dev/null
"$MINI" workspace --action import --dir "$RUN/host-workspace" --name parent --kind object \
  --target "$TASK" --observe-capability 8761 --control-capability 8762 >/dev/null
jq -n '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"parent",
  recipient:"9",verbs:["observe","mutate"],maxCost:"50000"}' >"$RUN/witness-request.json"
"$MINI" workspace --action propose --dir "$RUN/host-workspace" --request "$RUN/witness-request.json" \
  --proposal-id witness >"$EV/witness-propose.stdout" 2>"$EV/witness-propose.stderr"
"$MINI" workspace --action submit --dir "$RUN/host-workspace" \
  --intent "$RUN/host-workspace/proposals/witness/intent.json" \
  --attempt "$RUN/host-workspace/attempts/witness" >"$EV/witness-submit.stdout" 2>"$EV/witness-submit.stderr" || :
confirmed "$RUN/host-workspace/attempts/witness/outcome.json" || fail "witness delegation not confirmed"
WITNESS=$(jq -er .delegation.childCapability "$RUN/host-workspace/proposals/witness/proposal.json")
mark "parent witness capability $WITNESS delegated to worker subject 9"

# --- Human friend enrolls through the ordinary sponsor-sealed path ----------
"$MINI" enroll --action plan --sponsor-workspace "$ROOT/sponsor" --factory-ref factory \
  --name friend --new-key "$ROOT/newcomer.key" --dir "$ROOT/attempts/friend" >/dev/null
"$MINI" enroll --action seal --dir "$ROOT/attempts/friend" >/dev/null
"$MINI" enroll --action submit --dir "$ROOT/attempts/friend" >"$EV/friend-enroll.json"
FRIEND=$(jq -er .subject "$ROOT/attempts/friend/enrollment.json")
"$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCK" \
  --enrollment "$ROOT/attempts/friend/enrollment.json" --dir "$ROOT/friend" >/dev/null
mark "friend enrolled through mini enroll: subject $FRIEND"

# --- Sponsor creates the shared resource and delegates to Hermes -------------
printf '%s\n' '{"type":"all","predicates":[]}' >"$RUN/all-true.json"
"$MINI" workspace --action create --dir "$ROOT/sponsor" --name shared --storage declared \
  --predicate "$RUN/all-true.json" --fields 2 >"$EV/sponsor-create.stdout" 2>"$EV/sponsor-create.stderr"
jq -n '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"shared",
  recipient:"9",verbs:["observe","mutate","delegate"],maxCost:"50000"}' >"$RUN/grant-hermes.json"
"$MINI" workspace --action propose --dir "$ROOT/sponsor" --request "$RUN/grant-hermes.json" \
  --proposal-id grant-hermes >/dev/null 2>&1
"$MINI" workspace --action submit --dir "$ROOT/sponsor" \
  --intent "$ROOT/sponsor/proposals/grant-hermes/intent.json" \
  --attempt "$ROOT/sponsor/attempts/grant-hermes" >/dev/null 2>&1
confirmed "$ROOT/sponsor/attempts/grant-hermes/outcome.json" || fail "grant to Hermes not confirmed"
"$MINI" workspace --action publish-delegation --dir "$ROOT/sponsor" --proposal-id grant-hermes \
  --attempt "$ROOT/sponsor/attempts/grant-hermes" >/dev/null 2>&1
HERMES_REF=$ROOT/sponsor/proposals/grant-hermes/recipient-reference.json
cp "$HERMES_REF" "$EV/reference-sponsor-to-hermes.json"
mark "sponsor created 'shared' and published a recipient reference for subject 9"

# --- Hosted controller: private state, workspace, sandbox, supervised unit --
H=$RUN/hermes
mkdir -m 700 "$H" "$H/state" "$H/worker-work" "$H/worker-runtime" "$H/launcher"
"$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCK" \
  --key "$RUN/keys/hermes.key" --subject 9 --namespace-root "$ROOT/namespace" \
  --dir "$H/state/resource-workspace" >/dev/null
cp "$REPO/deploy/grain-host/bwrap" "$H/launcher/bwrap"
rustc -O --edition 2021 -o "$H/launcher/launch-gate" "$REPO/deploy/grain-host/launch-gate.rs" 2>"$EV/launch-gate-build.log"
cp "$GRAIN" "$H/worker-runtime/grain-runtime"
cp "$HERE/fixture/hermes-deterministic-acp" "$H/worker-runtime/hermes-acp"
chmod 700 "$H/launcher/bwrap" "$H/worker-runtime/hermes-acp"
mkdir -m 700 "$H/worker-work/.hermes"
printf 'timeouts:\n  mcp:\n    tool_call: 600\n' >"$H/worker-work/.hermes/config.yaml"
chmod 600 "$H/worker-work/.hermes/config.yaml"
jq -n --arg mini "$MINI" --arg host "$HOST" --arg cfg "$CONFIG" --arg sock "$SOCK" \
  --arg state "$H/state" --arg cwd "$H" --arg hk "$RUN/keys/hermes-host.key" \
  --arg wk "$RUN/keys/hermes.key" --arg t "$TASK" --arg tt "$TOOL_TASK" \
  --arg launcher "$H/launcher/bwrap" --arg work "$H/worker-work" --arg rt "$H/worker-runtime" \
  --arg witness "$WITNESS" '
  {mini:$mini,host:$host,hostConfig:$cfg,hostSocket:$sock,custodyKey:$hk,
   stateDir:$state,controlSocket:($state + "/control.sock"),cwd:$cwd,
   task:$t,subject:"8",capability:"8761",queryCapability:"8761",
   policyControlCapability:"8762",
   toolTask:{task:$tt,subject:"9",capability:"8771",queryCapability:"8771",
     custodyKey:$wk,parentCapability:$witness,parentObserveCapability:$witness,
     reserve:"2",charge:"1",allowedPublications:[],
     resourceWorkspace:($state + "/resource-workspace")},
   commands:[{name:"hermes-acp",program:$launcher,
     args:["--workspace",$work,"--runtime-root",$rt,"--network","none","--","/agent/hermes-acp"],
     systemdScope:true,wallTimeSeconds:600,reserve:"3",charge:"1"}]}' >"$H/controller.json"
chmod 600 "$H/controller.json"
CONTROL=$H/state/control.sock
JOURNAL=$H/state/journal.json
systemd-run --user --unit="$UNIT" --description="mini-hermes-journey:$RUN" \
  --property=Restart=on-failure --property=RestartSec=2s \
  --property=KillMode=control-group --property=RuntimeMaxSec=7200s \
  "$GRAIN" serve "$H/controller.json" >"$EV/unit-start.log" 2>&1
for _ in $(seq 1 300); do [ -S "$CONTROL" ] && break; sleep 0.1; done
[ -S "$CONTROL" ] || fail "controller socket absent"
mark "controller unit $UNIT active, MainPID $(systemctl --user show -p MainPID --value "$UNIT.service"), Restart=on-failure"

wait_journal() {  # EXPRESSION SECONDS
  local deadline=$(( $(date +%s) + $2 ))
  while [ "$(date +%s)" -lt "$deadline" ]; do
    if [ -f "$JOURNAL" ] && jq -e "$1" "$JOURNAL" >/dev/null 2>&1; then return 0; fi
    sleep 0.05
  done
  return 1
}

open_connector() {  # LABEL
  local fifo=$EV/$1.fifo
  mkfifo -m 600 "$fifo"
  "$GRAIN" connect "$CONTROL" <"$fifo" >"$EV/$1.connector.log" 2>&1 &
  CONNECTOR_PID=$!
  exec 3>"$fifo"
  printf 'attach soft\n' >&3
  wait_journal '.connection == "soft" and .pending == null' 300 || fail "$1: soft attach"
  mark "$1: attached soft (worker law renewed to generation $(jq -r .managedLawGeneration "$JOURNAL"))"
}
close_connector() {  # LABEL
  exec 3>&-
  wait "$CONNECTOR_PID" 2>/dev/null || true
  CONNECTOR_PID=
  rm -f "$EV/$1.fifo"
}
prompt_and_wait() {  # LABEL PROMPT
  printf 'hermes %s\n' "$2" >&3
  wait_journal '.child != null' 120 || fail "$1: worker did not start"
  mark "$1: prompt running in worker unit $(jq -r .child.unit "$JOURNAL")"
  wait_journal '.child == null and .pending == null and .settlementDue == null and .parentHold == null and .connection == "soft"' 900 ||
    fail "$1: prompt did not settle"
  mark "$1: prompt settled"
}

# --- Phase A: Hermes J4 over MCP; the controller is killed mid-write --------
REF_LINE=$(jq -c . "$HERMES_REF")
open_connector phase-a
printf 'hermes %s\n' "@tools ;; @import shared $REF_LINE ;; @read shared ;; @write shared 2 1 ;; @read shared" >&3
wait_journal '.child != null' 120 || fail "phase-a: worker did not start"
mark "phase-a: prompt running in worker unit $(jq -r .child.unit "$JOURNAL")"
WS=$H/state/resource-workspace
OP=
deadline=$(( $(date +%s) + 900 ))
while [ "$(date +%s)" -lt "$deadline" ]; do
  OP=$(jq -r '.workspaceAttempt.operationId // empty' "$JOURNAL" 2>/dev/null || :)
  if [ -n "$OP" ] && [ -f "$WS/attempts/$OP/call.bin" ]; then break; fi
  OP=
  sleep 0.02
done
[ -n "$OP" ] || fail "phase-a: write never reached its signed call"
OLD_PID=$(systemctl --user show -p MainPID --value "$UNIT.service")
mark "phase-a: write operation $OP has a retained signed call; outcome.json present: $([ -f "$WS/attempts/$OP/outcome.json" ] && echo yes || echo no)"
# HERMES_KILL_DELAY_MS lets a run land the kill after the sent frame reached
# the Host (exact lookup then confirms it) instead of right after call.bin.
if [ "${HERMES_KILL_DELAY_MS:-0}" -gt 0 ]; then
  sleep "$(awk -v ms="$HERMES_KILL_DELAY_MS" 'BEGIN{printf "%.3f", ms/1000}')"
fi
systemctl --user kill --signal=SIGKILL --kill-whom=main "$UNIT.service"
mark "KILL: SIGKILL to controller MainPID $OLD_PID during write operation $OP (delay ${HERMES_KILL_DELAY_MS:-0} ms after call.bin; outcome.json present at kill: $([ -f "$WS/attempts/$OP/outcome.json" ] && echo yes || echo no))"
cp "$JOURNAL" "$EV/journal-at-kill.json"
close_connector phase-a

# --- Automatic restart: supervisor + the controller's own recovery ----------
NEW_PID=
for _ in $(seq 1 600); do
  NEW_PID=$(systemctl --user show -p MainPID --value "$UNIT.service")
  if [ -n "$NEW_PID" ] && [ "$NEW_PID" != 0 ] && [ "$NEW_PID" != "$OLD_PID" ]; then break; fi
  NEW_PID=
  sleep 0.1
done
[ -n "$NEW_PID" ] || fail "supervisor did not restart the controller"
mark "RESTART: systemd started controller MainPID $NEW_PID (NRestarts=$(systemctl --user show -p NRestarts --value "$UNIT.service"))"
wait_journal 'any(.reconciliationLog[]; .action == "startup-recovery")' 600 ||
  fail "startup recovery did not run"
cp "$JOURNAL" "$EV/journal-after-restart.json"
jq '[.reconciliationLog[] | select(.action == "startup-recovery")][-1]' "$JOURNAL" >"$EV/startup-recovery.json"
jq -e '.result == "recovered"' "$EV/startup-recovery.json" >/dev/null ||
  fail "startup recovery left the task fenced: $(jq -c . "$EV/startup-recovery.json")"
jq --arg op "$OP" '.workspaceResolutions[] | select((.operationId | tostring) == $op)' "$JOURNAL" \
  >"$EV/write-resolution.json"
RESOLUTION=$(jq -er .resolution "$EV/write-resolution.json")
mark "RESOLVED: operation $OP $RESOLUTION ($(jq -r .basis "$EV/write-resolution.json"); $(jq -r .resolvedBy "$EV/write-resolution.json")); connection $(jq -r .connection "$JOURNAL"); unresolved external $(jq -c .unresolvedExternal "$JOURNAL")"
jq -e '.connection == "detached" and .parentHold == null and .toolHold == null and
  .workspaceAttempt == null and (.unresolvedExternal | length) == 0' "$JOURNAL" >/dev/null ||
  fail "task is not attachable after automatic recovery"

# --- Phase B: reattach (no operator step), report, read back ----------------
PHASE_B="@attempts ;; @read shared"
if [ "$RESOLUTION" != performed ]; then
  PHASE_B="$PHASE_B ;; @write shared 2 1 ;; @read shared ;; @attempts"
fi
open_connector phase-b
prompt_and_wait phase-b "$PHASE_B"
close_connector phase-b

# --- Phase C: Hermes delegates to the friend and exports the reference ------
open_connector phase-c
prompt_and_wait phase-c "@delegate shared $FRIEND observe 50000 ;; @export friend-shared-ref.json ;; @attempts"
close_connector phase-c
[ -f "$H/worker-work/friend-shared-ref.json" ] || fail "Hermes exported no reference"
cp "$H/worker-work/friend-shared-ref.json" "$EV/reference-hermes-to-friend.json"
"$MINI" workspace --action import --dir "$ROOT/friend" --name from-hermes \
  --from-ref "$H/worker-work/friend-shared-ref.json" >"$EV/friend-import.stdout" 2>&1
"$MINI" workspace --action read --dir "$ROOT/friend" --name from-hermes >"$EV/friend-read.json" 2>"$EV/friend-read.stderr"
mark "friend imported Hermes's reference with the CLI and read: field 2 = $(jq -r '.cell.entries[] | select(.key.field == "2") | .value' "$EV/friend-read.json")"
"$MINI" workspace --action read --dir "$ROOT/sponsor" --name shared >"$EV/sponsor-read.json" 2>"$EV/sponsor-read.stderr"
mark "sponsor read of 'shared': field 2 = $(jq -r '.cell.entries[] | select(.key.field == "2") | .value' "$EV/sponsor-read.json")"

# --- Phase D: hard attachment loss is a circuit breaker ---------------------
AGENT_LOG=$H/worker-work/agent-log.jsonl
fifo=$EV/phase-d.fifo
mkfifo -m 600 "$fifo"
"$GRAIN" connect "$CONTROL" <"$fifo" >"$EV/phase-d.connector.log" 2>&1 &
CONNECTOR_PID=$!
exec 3>"$fifo"
printf 'attach hard\n' >&3
wait_journal '.connection == "hard" and .pending == null' 300 || fail "phase-d: hard attach"
mark "phase-d: attached hard"
BEFORE_D=$(grep -c '"kind": "step"' "$AGENT_LOG")
printf 'hermes %s\n' "@read shared ;; @read shared ;; @read shared ;; @read shared ;; @read shared" >&3
wait_journal '.child != null' 120 || fail "phase-d: worker did not start"
for _ in $(seq 1 1200); do
  [ "$(grep -c '"kind": "step"' "$AGENT_LOG")" -gt "$BEFORE_D" ] && break
  sleep 0.05
done
exec 3>&-
kill "$CONNECTOR_PID" 2>/dev/null || true
wait "$CONNECTOR_PID" 2>/dev/null || true
CONNECTOR_PID=
rm -f "$fifo"
mark "phase-d: hard connector dropped while the prompt ran"
wait_journal '.child == null and .connection == "detached" and .parentHold == null and (.unresolvedExternal | length) == 0' 600 ||
  fail "phase-d: breaker did not fence and reconcile ($(jq -c '{connection,parentHold,unresolvedExternal}' "$JOURNAL"))"
sleep 2
D_STEPS=$(( $(grep -c '"kind": "step"' "$AGENT_LOG") - BEFORE_D ))
mark "phase-d: prompt interrupted after $D_STEPS of 5 directives; parent settled automatically; task detached"
[ "$D_STEPS" -lt 5 ] || fail "phase-d: hard loss did not interrupt the prompt"

# --- Phase E: a soft detach keeps the prompt running within its reserve -----
open_connector phase-e
BEFORE_E=$(grep -c '"kind": "step"' "$AGENT_LOG")
printf 'hermes %s\n' "@read shared ;; @read shared ;; @attempts" >&3
wait_journal '.child != null' 120 || fail "phase-e: worker did not start"
close_connector phase-e
mark "phase-e: soft connector closed while the prompt ran"
wait_journal '.child == null and .pending == null and .settlementDue == null and .parentHold == null' 900 ||
  fail "phase-e: soft prompt did not settle"
E_STEPS=$(( $(grep -c '"kind": "step"' "$AGENT_LOG") - BEFORE_E ))
[ "$E_STEPS" -eq 3 ] || fail "phase-e: soft prompt ran $E_STEPS of 3 directives"
mark "phase-e: soft prompt completed all 3 directives after detach and settled"

# --- Evidence ---------------------------------------------------------------
cp "$JOURNAL" "$EV/journal-final.json"
cp "$H/worker-work/agent-log.jsonl" "$EV/agent-log.jsonl"
journalctl --user -u "$UNIT.service" --no-pager -o short-iso >"$EV/unit-journal.log" 2>&1 || :
for dir in "$WS"/attempts/*; do
  name=$(basename "$dir")
  for file in outcome.json attempt.json; do
    [ -f "$dir/$file" ] && cp "$dir/$file" "$EV/ws-attempt-$name-$file"
  done
  for file in "$dir"/retry-*.json; do
    [ -f "$file" ] && cp "$file" "$EV/ws-attempt-$name-$(basename "$file")"
  done
done
jq -n --slurpfile final "$EV/journal-final.json" --slurpfile friend "$EV/friend-read.json" \
  --slurpfile sponsor "$EV/sponsor-read.json" --arg op "$OP" --arg friendSubject "$FRIEND" '
  {type:"mini-hermes-journey-v1",killedOperation:$op,friendSubject:$friendSubject,
   resolutions:$final[0].workspaceResolutions,
   managedLawGeneration:$final[0].managedLawGeneration,
   automaticDecisions:[$final[0].reconciliationLog[] | select(.automatic == true or .action == "startup-recovery" or .action == "recover-gated-worker")],
   friendField2:([$friend[0].cell.entries[] | select(.key.field == "2") | .value][0]),
   sponsorField2:([$sponsor[0].cell.entries[] | select(.key.field == "2") | .value][0])}' \
  >"$EV/summary.json"
jq -e '.friendField2 == "1" and .sponsorField2 == "1" and
  (.resolutions | map(.resolution) | all(. == "performed" or . == "refused" or . == "uncertain"))' \
  "$EV/summary.json" >/dev/null || fail "final readback or resolutions differ"
mark "PASS: Hermes J4 on the humans' Store through MCP, killed mid-write, restarted by its unit, attempt $OP $RESOLUTION, readback 1, delegation reached the friend, hard loss interrupted, soft detach continued"
