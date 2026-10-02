#!/usr/bin/env bash
# Real Mini shell journey for member-defined poll kinds. Uses journey.sh's
# existing live Store and two provisioned workspaces; no simulated Host/network.
# Run this hook with JOURNEY_STEP_DIR, MINI, HOST, CONFIG, SOCKET, SPONSOR_WS,
# NEWCOMER_WS and NEWCOMER_SUBJECT from a source-matched v6 candidate.
# Exit zero requires both descriptor behavior AND current exported-law admission.
set -euo pipefail
umask 077
: "${JOURNEY_STEP_DIR:?}" "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}"
: "${SPONSOR_WS:?}" "${NEWCOMER_WS:?}" "${NEWCOMER_SUBJECT:?}"
D=$JOURNEY_STEP_DIR/jworld-kind
[ ! -e "$D" ] || { echo "refusing to reuse $D" >&2; exit 2; }
mkdir -p -m 700 "$D/alice/requests" "$D/dan/requests" "$D/log"
ROWS=$D/rows.tsv
printf 'step\texpect\trc\tresult\n' >"$ROWS"
N=0
FOREIGN_KEY=0; [ "$NEWCOMER_SUBJECT" != 0 ] || FOREIGN_KEY=1
SHELL_BIN=${SHELL_BIN:-$MINI}
finish() { local rc=$?; printf '%s\n' "$ROWS"; [ "$rc" = 0 ] || echo "JWORLD-KIND: stopped at the first failed row; see $D/log" >&2; }
trap finish EXIT
say() {
  local who=$1 line=$2 ws
  if [ "$who" = alice ]; then ws=$SPONSOR_WS; else ws=$NEWCOMER_WS; fi
  N=$((N+1)); OUT=$D/log/$N.out; ERR=$D/log/$N.err
  printf '%s\n' "$line" >"$D/log/$N.line"
  if "$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
      --workspace "$ws" --home "$D/$who" --line "$line" >"$OUT" 2>"$ERR"; then RC=0; else RC=$?; fi
}
ok() {
  local step=$1 who=$2 line=$3
  say "$who" "$line"
  printf '%s\t0\t%s\t%s\n' "$step" "$RC" "$([ "$RC" = 0 ] && echo PASS || echo FAIL)" >>"$ROWS"
  if [ "$RC" != 0 ]; then cat "$ERR" >&2; return 1; fi
}
check() {
  local step=$1; shift
  if "$@"; then printf '%s\ttrue\t0\tPASS\n' "$step" >>"$ROWS";
  else printf '%s\ttrue\t1\tFAIL\n' "$step" >>"$ROWS"; return 1; fi
}
turn() { local step=$1 who=$2 id=$3 line=$4; ok "$step-prepare" "$who" "$line"; ok "$step-submit" "$who" "submit $id"; }
refused_turn() {
  local step=$1 who=$2 id=$3 line=$4 reason=${5:-}
  ok "$step-prepare" "$who" "$line"
  say "$who" "submit $id"
  if [ "$RC" != 3 ] || ! grep -q '^refused:' "$ERR" || { [ -n "$reason" ] && ! grep -q "$reason" "$ERR"; }; then
    printf '%s\trefused%s\t%s\tFAIL\n' "$step" "$reason" "$RC" >>"$ROWS"; cat "$ERR" >&2; return 1
  fi
  printf '%s\trefused%s\t%s\tPASS\n' "$step" "$reason" "$RC" >>"$ROWS"
}
export_ref() {
  local id=$1 name=$2
  ok "$id-publish" alice "publish $id"
  ok "$id-export" alice "export $id"
  local value; value=$(cat "$OUT")
  ok "$id-import" dan "import $name $value"
}
check newcomer-provisioned jq -e '.birthContext != null' "$NEWCOMER_WS/workspace.json" >/dev/null
cat >"$D/alice/requests/poll-v1.json" <<'JSON'
{"descriptor":{"revision":"1","fields":[
 {"id":"1","name":"question","meaning":"the poll question","codec":"bytes","discipline":"rom"},
 {"id":"2","name":"open","meaning":"whether the poll accepts votes","codec":"nat","discipline":"ram"},
 {"id":"3","name":"votes","meaning":"one immutable vote keyed by member subject","codec":"nat","discipline":"append"}]},
 "defaults":[{"field":"1","key":"0","value":"4c756e63683f"},{"field":"2","key":"0","value":"1"}]}
JSON
jq '.descriptor.revision="2" | .descriptor.fields += [{id:"4",name:"title",meaning:"display title",codec:"bytes",discipline:"ram"}] | .defaults += [{field:"4",key:"0",value:"506f6c6c"}]' \
  "$D/alice/requests/poll-v1.json" >"$D/alice/requests/poll-v2.json"
# The management law stays open. This separate descendants facet applies to
# actual world-instance mutate legs. Only Dan can close/reopen; that branch
# permits only the open field, never a vote under an owner bypass.
jq -n --arg dan "$NEWCOMER_SUBJECT" '{selector:{physicalKinds:["18"],requestKinds:null,verbs:["2"]},parents:[],
 predicate:{type:"all",predicates:[
  {type:"eq",slot:"world/changed/count",value:"1"},
  {type:"any",predicates:[
   {type:"all",predicates:[
    {type:"eq",slot:"request/subject",value:$dan},
    {type:"eq",slot:"world/resource/field/2/changed",value:"1"}]},
   {type:"all",predicates:[
    {type:"eq",slot:"world/resource/field/2/0/before",value:"1"},
    {type:"eq",slot:"world/resource/field/3/changed",value:"1"},
    {type:"eq",slot:"world/changed/subject-keys-only",value:"1"}]}]}]}}' >"$D/alice/requests/poll-export.json"
# Allocation is also subject to the current export. Its distinct source-owned
# birth marker allows only open, empty-vote defaults. Ordinary writes must use
# the mutation branch; missing source slots never count as zero.
jq '.predicate={type:"any",predicates:[
 {type:"all",predicates:[
  {type:"eq",slot:"world/request/birth",value:"1"},
  {type:"eq",slot:"world/resource/field/2/0/after",value:"1"},
  {type:"eq",slot:"world/resource/field/3/count/after",value:"0"}]},
 {type:"all",predicates:[{type:"eq",slot:"world/request/birth",value:"0"},.predicate]}]}' \
  "$D/alice/requests/poll-export.json" >"$D/poll-with-birth.json"
mv "$D/poll-with-birth.json" "$D/alice/requests/poll-export.json"
# A current export that refuses every instance mutation, while definition
# management and observation remain separately authorized.
printf '%s\n' '{"selector":{"physicalKinds":["18"],"verbs":["2"]},"parents":[],"predicate":{"type":"any","predicates":[]}}' >"$D/alice/requests/poll-sealed.json"

ok kind-create alice 'kind create wk-poll @poll-v1.json open'
ok kind-read alice 'kind show wk-poll'
check kind-revision jq -e '.value.descriptor.revision == "1" and (.value.descriptor.fields|length)==3' "$OUT" >/dev/null
turn kind-delegate alice wk-kind-read "delegate wk-kind-read wk-poll $NEWCOMER_SUBJECT observe 50000"
export_ref wk-kind-read wk-poll
# Dan imports a reference only. No poll definition source is copied into his home.
check no-author-file test ! -e "$D/dan/requests/poll-v1.json"
ok shared-kind-read dan 'kind show wk-poll'
ok first-instance dan 'create wk-one --from wk-poll open'
ok second-instance dan 'create wk-two --from wk-poll open'
ok first-read dan 'instance show wk-one'
check first-defaults jq -e '.value.descriptor.revision=="1" and any(.value.entries[]; .field=="2" and .key=="0" and .value=="1")' "$OUT" >/dev/null

turn export-install alice wk-export 'law export wk-export wk-poll @poll-export.json'
ok export-readback alice 'law export show wk-poll'
check exported-facet jq -e '.policy.descendants.selector.physicalKinds==["18"] and .policy.predicate=={"type":"all","predicates":[]}' "$OUT" >/dev/null
# Repeating the proposal reuses source bytes pinned before installation.
EXPORT_INTENT=$SPONSOR_WS/proposals/wk-export/intent.json
BEFORE=$(sha256sum "$EXPORT_INTENT" | cut -d' ' -f1)
ok export-exact-reprepare alice 'law export wk-export wk-poll @poll-export.json'
check export-same-source test "$BEFORE" = "$(sha256sum "$EXPORT_INTENT" | cut -d' ' -f1)"

ok first-show dan 'instance show wk-one'
refused_turn foreign-vote dan wk-foreign "instance set wk-foreign wk-one votes $FOREIGN_KEY 1" law-denied
turn first-vote dan wk-vote "instance set wk-vote wk-one votes $NEWCOMER_SUBJECT 1"
ok first-vote-read dan 'instance show wk-one'
check vote-present jq -e --arg subject "$NEWCOMER_SUBJECT" 'any(.value.entries[]; .field=="3" and .key==$subject and .value=="1")' "$OUT" >/dev/null
refused_turn append-rewrite dan wk-revote "instance set wk-revote wk-one votes $NEWCOMER_SUBJECT 2"
refused_turn rom-rewrite dan wk-question 'instance set wk-question wk-one question 0 Changed'

ok second-show dan 'instance show wk-two'
turn close-second dan wk-close 'instance set wk-close wk-two open 0 0'
ok closed-read dan 'instance show wk-two'
refused_turn closed-vote dan wk-closed-vote "instance set wk-closed-vote wk-two votes $NEWCOMER_SUBJECT 1" law-denied
turn reopen-second dan wk-reopen 'instance set wk-reopen wk-two open 0 1'
ok second-open-read dan 'instance show wk-two'
ok stale-prepare dan "instance set wk-stale wk-two votes $NEWCOMER_SUBJECT 1"
# Capture an actual Host-prepared, signed call before the export changes.
# The shell's preceding proposal only authored source; prepare-only exercises
# the real observation/prepare/assemble boundary and retains exact call bytes.
if "$MINI" workspace --socket "$SOCKET" --action submit --dir "$NEWCOMER_WS" \
    --intent "$NEWCOMER_WS/proposals/wk-stale/intent.json" \
    --attempt "$NEWCOMER_WS/attempts/wk-stale" --prepare-only true \
    >"$D/log/stale-prepare.out" 2>"$D/log/stale-prepare.err"; then
  printf 'stale-real-prepare\t0\t0\tPASS\n' >>"$ROWS"
else
  printf 'stale-real-prepare\t0\t1\tFAIL\n' >>"$ROWS"; cat "$D/log/stale-prepare.err" >&2; exit 1
fi
check stale-call-retained test -s "$NEWCOMER_WS/attempts/wk-stale/call.bin"
STALE_CALL=$(sha256sum "$NEWCOMER_WS/attempts/wk-stale/call.bin" | cut -d' ' -f1)
# Change the exported law after preparing a valid vote. Existing target local
# laws and both instance descriptors remain unchanged.
turn seal-export alice wk-seal 'law export wk-seal wk-poll @poll-sealed.json'
say dan 'retry wk-stale'
if [ "$RC" != 3 ] && [ "$RC" != 4 ]; then printf 'stale-export\trefused/contention\t%s\tFAIL\n' "$RC" >>"$ROWS"; exit 1; fi
check stale-call-unchanged test "$STALE_CALL" = "$(sha256sum "$NEWCOMER_WS/attempts/wk-stale/call.bin" | cut -d' ' -f1)"
# Require a decoded native decision, not a transport failure with the same exit.
check stale-native-decision jq -e '.type=="refused" or .type=="contention"' "$NEWCOMER_WS/attempts/wk-stale/retry-0001.json" >/dev/null
printf 'stale-export\trefused/contention\t%s\tPASS\n' "$RC" >>"$ROWS"
ok still-no-second-vote dan 'instance show wk-two'
check refused-vote-absent jq -e --arg subject "$NEWCOMER_SUBJECT" 'all(.value.entries[]; .field!="3" or .key!=$subject)' "$OUT" >/dev/null
ok first-current-read dan 'instance show wk-one'
refused_turn both-instance-current-export dan wk-block-open 'instance set wk-block-open wk-one open 0 0' law-denied
turn restore-export alice wk-restore 'law export wk-restore wk-poll @poll-export.json'

turn revise-kind alice wk-revision 'kind revise wk-revision wk-poll @poll-v2.json'
ok old-instance-layout dan 'instance show wk-one'
check old-layout-preserved jq -e '.value.descriptor.revision=="1" and all(.value.descriptor.fields[]; .id!="4")' "$OUT" >/dev/null
ok new-instance-layout dan 'create wk-three --from wk-poll open'
ok new-instance-read dan 'instance show wk-three'
check new-layout-visible jq -e '.value.descriptor.revision=="2" and any(.value.entries[]; .field=="4" and .key=="0" and .value=="506f6c6c")' "$OUT" >/dev/null
turn revised-instance-vote dan wk-newvote "instance set wk-newvote wk-three votes $NEWCOMER_SUBJECT 1"
ok old-instance-vote-preserved dan 'instance show wk-one'
check old-vote-preserved jq -e --arg subject "$NEWCOMER_SUBJECT" 'any(.value.entries[]; .field=="3" and .key==$subject and .value=="1")' "$OUT" >/dev/null
printf 'JWORLD-KIND: all shell, descriptor and exported-law rows passed\n' >&2
