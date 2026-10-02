#!/usr/bin/env bash
# Run after jworld-method on a source-matched fresh fixture. Reuses its real
# immutable close program and member payer; no fixed task/user capacity.
set -euo pipefail
umask 077
RUN_DIR=${RUN_DIR:-${JOURNEY_STEP_DIR:?}/jworld-board}
: "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}" "${NEWCOMER_WS:?}" "${NEWCOMER_SUBJECT:?}" "${RUN_DIR:?}"
test ! -e "$RUN_DIR" || exit 2
mkdir -p "$RUN_DIR/home/requests" "$RUN_DIR/log"
N=0
say() { local ws=$1 line=$2; N=$((N+1)); printf '%s\n' "$line" >"$RUN_DIR/log/$N.line"; "$MINI" shell --host "$HOST" --config "$CONFIG" --socket "$SOCKET" --workspace "$ws" --home "$RUN_DIR/home" --line "$line" >"$RUN_DIR/log/$N.out" 2>"$RUN_DIR/log/$N.err" || { cat "$RUN_DIR/log/$N.err" >&2; return 1; }; }
PROGRAM_ID=$(jq -er '.programId' "$SPONSOR_WS/programs/wm-close.json")
jq -n --arg program "$PROGRAM_ID" '{descriptor:{revision:"1",fields:[
 {id:"1",name:"title",meaning:"task title keyed by task identity",codec:"bytes",discipline:"ram"},
 {id:"2",name:"open",meaning:"board accepts task changes",codec:"nat",discipline:"ram"},
 {id:"3",name:"status",meaning:"task state keyed by task identity",codec:"nat",discipline:"ram"},
 {id:"4",name:"tally",meaning:"number of tasks at board closure",codec:"nat",discipline:"ram"},
 {id:"5",name:"methods",meaning:"dregg/world/method-table/v1",codec:"bytes",discipline:"rom"},
 {id:"6",name:"assignee",meaning:"task assignee subject keyed by task identity",codec:"nat",discipline:"ram"}]},
 defaults:[{field:"2",key:"0",value:"1"},{field:"4",key:"0",value:"0"},
 {field:"5",key:"0",value:[{name:"close",program:$program,outputs:[{output:"90",field:"2",key:"0"},{output:"91",field:"4",key:"0"}]}]}]}' >"$RUN_DIR/home/requests/board-kind.json"
say "$SPONSOR_WS" 'kind create bstep-board-kind @board-kind.json open'
cat >"$RUN_DIR/home/requests/board-law.json" <<'BOARDLAW'
{"selector":{"physicalKinds":["18"],"verbs":["2"]},"parents":[],"predicate":{"type":"any","predicates":[{"type":"all","predicates":[{"type":"eq","slot":"world/request/birth","value":"1"},{"type":"eq","slot":"world/resource/field/2/0/after","value":"1"},{"type":"eq","slot":"world/resource/field/3/count/after","value":"0"}]},{"type":"all","predicates":[{"type":"eq","slot":"world/request/birth","value":"0"},{"type":"eq","slot":"world/resource/field/2/0/before","value":"1"}]}]}}
BOARDLAW
say "$SPONSOR_WS" 'law export bstep-board-law bstep-board-kind @board-law.json'
say "$SPONSOR_WS" 'submit bstep-board-law'
say "$SPONSOR_WS" 'create bstep-board --from bstep-board-kind open'
say "$SPONSOR_WS" 'instance show bstep-board'
# Arbitrary task keys, including a key unrelated to field count or population.
python3 - "$RUN_DIR/home/requests/board-tasks.json" <<'TASKS'
import json,sys
keys=list(range(11))+[100000000000]
actions=[]
for key in keys:
    actions += [{"type":"set","field":"title","key":str(key),"value":f"Task {key}"},
                {"type":"set","field":"status","key":str(key),"value":"0"}]
json.dump({"type":"minidregg-workspace-proposal-v1","action":"invoke",
           "targets":[{"name":"bstep-board","payload":{"type":"worldNamed","actions":actions}}]},open(sys.argv[1],"w"))
TASKS
say "$SPONSOR_WS" 'propose bstep-fill @board-tasks.json'
say "$SPONSOR_WS" 'submit bstep-fill'
say "$SPONSOR_WS" 'instance show bstep-board'
jq -e '([.value.entries[]|select(.field=="1")]|length)==12 and ([.value.entries[]|select(.field=="3")]|length)==12' "$RUN_DIR/log/$N.out" >/dev/null
cp "$RUN_DIR/log/$N.out" "$RUN_DIR/twelve-task-board.json"
say "$SPONSOR_WS" "delegate bstep-board-edit bstep-board $NEWCOMER_SUBJECT observe,mutate 50000"
say "$SPONSOR_WS" 'submit bstep-board-edit'
say "$SPONSOR_WS" 'publish bstep-board-edit'
say "$SPONSOR_WS" 'export bstep-board-edit'
REF=$(cat "$RUN_DIR/log/$N.out")
say "$NEWCOMER_WS" "import bstep-board $REF"
say "$NEWCOMER_WS" 'instance show bstep-board'
say "$NEWCOMER_WS" 'instance set bstep-progress bstep-board status 100000000000 1'
say "$NEWCOMER_WS" 'submit bstep-progress'
say "$NEWCOMER_WS" 'instance show bstep-board'
jq -e '.value.entries|any(.field=="3" and .key=="100000000000" and .value=="1")' "$RUN_DIR/log/$N.out" >/dev/null
cp "$RUN_DIR/log/$N.out" "$RUN_DIR/member-progress.json"
# Reuse the exact poll close program in another member-defined kind.
say "$NEWCOMER_WS" 'instance call bstep-close bstep-board close --fund wm-payer --max-compute-credits 1000'
say "$NEWCOMER_WS" 'submit bstep-close'
say "$NEWCOMER_WS" 'instance show bstep-board'
jq -e '(.value.entries|any(.field=="2" and .key=="0" and .value=="0")) and (.value.entries|any(.field=="4" and .key=="0" and .value=="12"))' "$RUN_DIR/log/$N.out" >/dev/null
cp "$RUN_DIR/log/$N.out" "$RUN_DIR/closed-board.json"
set +e
"$MINI" shell --host "$HOST" --config "$CONFIG" --socket "$SOCKET" --workspace "$NEWCOMER_WS" --home "$RUN_DIR/home" --line 'instance set bstep-closed-edit bstep-board status 100000000000 2' >"$RUN_DIR/closed-edit.out" 2>"$RUN_DIR/closed-edit.err"
RC=$?
if [ "$RC" = 0 ]; then
  "$MINI" shell --host "$HOST" --config "$CONFIG" --socket "$SOCKET" --workspace "$NEWCOMER_WS" --home "$RUN_DIR/home" --line 'submit bstep-closed-edit' >>"$RUN_DIR/closed-edit.out" 2>>"$RUN_DIR/closed-edit.err"
  RC=$?
fi
set -e
test "$RC" = 3 && grep -q '^refused:' "$RUN_DIR/closed-edit.err"
printf '%s\n' 'WORLD-BOARD PASS:12 keyed tasks; shared member edits; poll program reused for board close/tally; current kind law refuses closed-board mutation. Status-monotonicity remains next work.' >&2
printf '%s\n' "$RUN_DIR"
