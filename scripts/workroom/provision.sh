#!/bin/sh
# Fresh Mini grain and kernel content workroom provisioner. It stops before
# launching a controller or provider; the caller supplies their own fixture.
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: $0 MINIDREGG_HOST NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi

HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
HOST=$1
EVIDENCE=$2
MINI=${MINI:-"$REPO/native/resource-client/target/debug/mini"}
STORE_BINARY=${STORE_BINARY:-"$REPO/native/hyperdocument-link-sqlite-store/target/debug/minidregg-link-sqlite-store"}
SIGNATURE_BINARY=${SIGNATURE_BINARY:-"$REPO/native/credential-signature-verifier/target/debug/minidregg-credential-signature-verifier"}
WORKROOM_PARENT_TASK=${WORKROOM_PARENT_TASK-7101}
WORKROOM_TOOL_TASK=${WORKROOM_TOOL_TASK-7102}

canonical_task() {
  case "$1" in
    ''|0*|*[!0-9]*) echo "task ID must be a canonical positive decimal: $1" >&2; exit 2 ;;
  esac
  case "$1" in
    7|8|10|11|12|7003|8001) echo "task ID collides with a provisioned resource: $1" >&2; exit 2 ;;
  esac
}
canonical_task "$WORKROOM_PARENT_TASK"
canonical_task "$WORKROOM_TOOL_TASK"
[ "$WORKROOM_PARENT_TASK" != "$WORKROOM_TOOL_TASK" ] || {
  echo "parent and tool task IDs must differ" >&2; exit 2;
}

absolute_executable() {
  item=$1
  [ -x "$item" ] || { echo "not executable: $item" >&2; exit 2; }
  directory=$(CDPATH='' cd -- "$(dirname -- "$item")" && pwd)
  printf '%s/%s\n' "$directory" "$(basename -- "$item")"
}
HOST=$(absolute_executable "$HOST")
MINI=$(absolute_executable "$MINI")
STORE_BINARY=$(absolute_executable "$STORE_BINARY")
SIGNATURE_BINARY=$(absolute_executable "$SIGNATURE_BINARY")
command -v jq >/dev/null 2>&1 || { echo "jq is required" >&2; exit 2; }
if [ -e "$EVIDENCE" ]; then
  echo "refusing to replace evidence directory: $EVIDENCE" >&2
  exit 2
fi
mkdir -m 700 "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
SERVICE_PID=
cleanup() {
  if [ -n "$SERVICE_PID" ]; then kill "$SERVICE_PID" 2>/dev/null || :; wait "$SERVICE_PID" 2>/dev/null || :; fi
}
trap cleanup EXIT HUP INT TERM

decimal() {
  jq -er --arg key "$2" '.[$key] | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$1"
}
confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (.acceptedCount | type == "string" and test("^[1-9][0-9]*$"))' "$1" >/dev/null
}
query_task() (
  name=$1 subject=$2 task=$3 capability=$4 key=$5 nonce=$6
  jq -n --arg s "$subject" --arg t "$task" --arg c "$capability" --arg n "$nonce" \
    '{subject:$s,nonce:$n,purpose:{type:"query",kind:"object",target:$t,view:"resource"},
      grants:[{kind:"object",target:$t,capability:$c}]}' >"$EVIDENCE/$name-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --key "$key" --view resource \
    --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
)
query_policy() (
  name=$1 subject=$2 task=$3 capability=$4 key=$5 nonce=$6
  jq -n --arg s "$subject" --arg t "$task" --arg c "$capability" --arg n "$nonce" \
    '{subject:$s,nonce:$n,purpose:{type:"query",kind:"object",target:$t,view:"policy"},
      grants:[{kind:"object",target:$t,capability:$c}]}' >"$EVIDENCE/$name-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --key "$key" --view policy \
    --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
)
"$MINI" keygen --secret "$EVIDENCE/controller.key" --public "$EVIDENCE/controller.pub" >"$EVIDENCE/controller-public.txt"
"$MINI" keygen --secret "$EVIDENCE/tool.key" --public "$EVIDENCE/tool.pub" >"$EVIDENCE/tool-public.txt"
CONTROLLER_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/controller.pub" | tr -d ' \n')
TOOL_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/tool.pub" | tr -d ' \n')
test "$CONTROLLER_PUBLIC" != "$TOOL_PUBLIC"

cat >"$EVIDENCE/operator.json" <<EOF
{"domain":8501,"federation":9,"factoryId":10,"resourceBookId":11,
 "authorityCatalogueId":12,"issuer":5,"ownerBudget":100000,"lifetime":10000,
 "tariffBase":3,"tariffPerBirth":2,"tariffPerGrant":1,
 "tariffPerInitialPayloadByte":0,"collector":99,"asset":0,
 "genesisHeight":10,"expectedSeed":0,"storageBinary":"$STORE_BINARY",
 "storageRoot":"$EVIDENCE/store","signatureBinary":"$SIGNATURE_BINARY"}
EOF
"$HOST" "$EVIDENCE/operator.json" profile >"$EVIDENCE/operator-profile.json"
SEMANTICS=$(decimal "$EVIDENCE/operator-profile.json" semantics)
cat >"$EVIDENCE/genesis.json" <<EOF
{"domain":"8501","factoryId":"10","resourceBookId":"11",
 "authorityCatalogueId":"12","federation":"9","tariffBase":"3",
 "tariffPerBirth":"2","tariffPerGrant":"1","tariffPerInitialPayloadByte":"0",
 "collector":"99","asset":"0","expectedSemantics":"$SEMANTICS",
 "issuerEpoch":"2","genesisHeight":"10",
 "factoryPredicate":{"type":"all","predicates":[]},
 "enrollments":[
  {"key":{"keyId":"7007","keyEpoch":"2","algorithm":"1","subject":"7",
    "publicKey":"$CONTROLLER_PUBLIC","activeFrom":"0","activeUntil":"1000000","revoked":false},
   "accountId":"7","spendCapabilityId":"41","controlCapabilityId":"51",
   "factoryObserveCapabilityId":"54","initialBalance":"100",
   "accountPredicate":{"type":"all","predicates":[]}},
  {"key":{"keyId":"8008","keyEpoch":"2","algorithm":"1","subject":"8",
    "publicKey":"$TOOL_PUBLIC","activeFrom":"0","activeUntil":"1000000","revoked":false},
   "accountId":"8","spendCapabilityId":"42","controlCapabilityId":"52",
   "factoryObserveCapabilityId":"55","initialBalance":"100",
   "accountPredicate":{"type":"all","predicates":[]}}],
 "factoryControllerSubject":"7","factoryControllerCapability":"53",
 "meterAllowance":{"incidences":"10000000","turnBytes":"10000000",
   "memoryTouches":"10000000","witnessBytes":"10000000",
   "proofWork":"10000000","storageBytes":"10000000",
   "networkBytes":"10000000","sideEffectCount":"10000000",
   "feeDebit":"10000000","leaseByteBlocks":"10000000"}}
EOF
"$MINI" bootstrap --host "$HOST" --config "$EVIDENCE/operator.json" \
  --source "$EVIDENCE/genesis.json" --dir "$EVIDENCE/deployment" >"$EVIDENCE/bootstrap.stdout"
CONFIG="$EVIDENCE/deployment/pinned-config.json"

mkdir -m 700 "$EVIDENCE/session"
SOCKET="$EVIDENCE/session/host.sock"
"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$EVIDENCE/session.stdout" 2>"$EVIDENCE/session.stderr" &
SERVICE_PID=$!
tick=0
until [ -S "$SOCKET" ]; do
  kill -0 "$SERVICE_PID" 2>/dev/null || { echo "Mini session failed to start" >&2; exit 1; }
  tick=$((tick + 1))
  [ "$tick" -lt 120 ] || { echo "Mini session socket timeout" >&2; exit 1; }
  sleep 1
done

# The Lean birth author constructs both four-field pages and their real
# AgentGrain policies atomically. Budget is an explicit operator allocation,
# not a worker-provided balance or metered provider claim.
cat >"$EVIDENCE/birth-intent.json" <<EOF
{"subject":"7","nonce":"22000",
 "birth":{"genesis":$(cat "$EVIDENCE/genesis.json"),
  "template":{"issuer":"5","ownerBudget":"100000","lifetime":"10000"},
  "creator":"7","nonce":"22000","resources":[
   {"kind":"object","storage":"grain","target":"$WORKROOM_PARENT_TASK","owner":"7",
    "ownerCapability":"71","controlCapability":"72","budget":"100",
    "workerSubject":"8","workerGeneration":"1"},
   {"kind":"object","storage":"grain","target":"$WORKROOM_TOOL_TASK","owner":"8",
    "ownerCapability":"81","controlCapability":"82","budget":"50"},
   {"kind":"object","storage":"declared","target":"7003","owner":"7",
    "ownerCapability":"91","controlCapability":"92",
    "predicate":{"type":"all","predicates":[]}},
   {"kind":"object","storage":"content","target":"8001","owner":"7",
    "ownerCapability":"89","controlCapability":"90",
    "predicate":{"type":"all","predicates":[]}}],
  "sourceCapabilities":["41"],"funding":[],"feePayer":"7"},
 "grants":[{"kind":"object","target":"10","capability":"54"},
   {"kind":"account","target":"7","capability":"41"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/birth-intent.json" --intent-kind birth-intent \
  --key "$EVIDENCE/controller.key" --dir "$EVIDENCE/birth-attempt" >"$EVIDENCE/birth.stdout"
confirmed "$EVIDENCE/birth-attempt/outcome.json"
query_task controller-born 7 "$WORKROOM_PARENT_TASK" 71 "$EVIDENCE/controller.key" 30001
query_task tool-born 8 "$WORKROOM_TOOL_TASK" 81 "$EVIDENCE/tool.key" 30002
query_task publication-born 7 7003 91 "$EVIDENCE/controller.key" 30009
query_task workroom-born 7 8001 89 "$EVIDENCE/controller.key" 30010
jq -e --arg task "$WORKROOM_PARENT_TASK" '.page.grain == {task:$task,generation:"0",status:"0",remaining:"100",reserved:"0"}' \
  "$EVIDENCE/controller-born/view.json" >/dev/null
jq -e --arg task "$WORKROOM_TOOL_TASK" '.page.grain == {task:$task,generation:"0",status:"0",remaining:"50",reserved:"0"}' \
  "$EVIDENCE/tool-born/view.json" >/dev/null

for name in controller tool; do
  if [ "$name" = controller ]; then
    owner=7 task=$WORKROOM_PARENT_TASK capability=71 key=controller.key nonce=30003
  else
    owner=8 task=$WORKROOM_TOOL_TASK capability=81 key=tool.key nonce=30004
  fi
  query_policy "$name-policy" "$owner" "$task" "$capability" "$EVIDENCE/$key" "$nonce"
  if [ "$name" = controller ]; then
    jq -n --arg owner "$owner" \
      '{owner:$owner,workerSubject:"8",workerGeneration:"1"}' \
      >"$EVIDENCE/$name-policy-source.json"
  else
    jq -n --arg owner "$owner" '{owner:$owner}' >"$EVIDENCE/$name-policy-source.json"
  fi
  "$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --kind grain-policy --input "$EVIDENCE/$name-policy-source.json" \
    --output "$EVIDENCE/$name-policy.bin"
  authored=$(od -An -tx1 -v "$EVIDENCE/$name-policy.bin" | tr -d ' \n')
  jq -e --arg owner "$owner" '.predicate != null and .version == "0"' \
    "$EVIDENCE/$name-policy/view.json" >/dev/null
  jq -n --slurpfile view "$EVIDENCE/$name-policy/view.json" '$view[0].predicate' \
    >"$EVIDENCE/$name-predicate.json"
  "$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --kind predicate --input "$EVIDENCE/$name-predicate.json" \
    --output "$EVIDENCE/$name-view-predicate.bin"
  viewed=$(od -An -tx1 -v "$EVIDENCE/$name-view-predicate.bin" | tr -d ' \n')
  test "$authored" = "$viewed"
done

# Parent witness authority is a distinct delegated child grant held by the
# tool identity. The source-authored parent rule permits that subject only the
# pinned-generation witness no-op; the tool owns its own spendable task.
PARENT_ROOT=$(jq -er '.page.root' "$EVIDENCE/controller-born/view.json")
PARENT_AUTHORITY=$(jq -er '.signing[0].authorityRoot' "$EVIDENCE/controller-born/challenge.json")
cat >"$EVIDENCE/parent-witness-delegation.json" <<EOF
{"subject":"7","nonce":"31000","purpose":{"type":"prepare","draft":{
 "type":"delegate-source","command":{"kind":"object","domain":"8501",
 "semantics":"$SEMANTICS","subject":"7","nonce":"31001",
 "expectedTargetRoot":"$PARENT_ROOT","parentId":"71","target":"$WORKROOM_PARENT_TASK",
 "expectedPreRoot":"$PARENT_AUTHORITY",
 "child":{"id":"73","root":"71","parent":"71","issuer":"5",
  "holder":{"type":"subject","subject":"8"},"targets":["$WORKROOM_PARENT_TASK"],
  "verbs":["observe","mutate"],"maxCost":"50000",
  "notBefore":"10","notAfter":"1000","issuerEpoch":"2",
  "policyId":"$WORKROOM_PARENT_TASK","policyEpoch":"0","ancestors":["71"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"$WORKROOM_PARENT_TASK","capability":"71"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/parent-witness-delegation.json" --key "$EVIDENCE/controller.key" \
  --dir "$EVIDENCE/delegation-attempt" >"$EVIDENCE/delegation.stdout"
confirmed "$EVIDENCE/delegation-attempt/outcome.json"
query_task delegated-parent 8 "$WORKROOM_PARENT_TASK" 73 "$EVIDENCE/tool.key" 31002
test "$(jq -er '.page.root' "$EVIDENCE/delegated-parent/view.json")" = "$PARENT_ROOT"

PUBLICATION_ROOT=$(jq -er '.page.root' "$EVIDENCE/publication-born/view.json")
PUBLICATION_AUTHORITY=$(jq -er '.signing[0].authorityRoot' "$EVIDENCE/delegated-parent/challenge.json")
cat >"$EVIDENCE/publication-delegation.json" <<EOF
{"subject":"7","nonce":"31010","purpose":{"type":"prepare","draft":{
 "type":"delegate-source","command":{"kind":"object","domain":"8501",
 "semantics":"$SEMANTICS","subject":"7","nonce":"31011",
 "expectedTargetRoot":"$PUBLICATION_ROOT","parentId":"91","target":"7003",
 "expectedPreRoot":"$PUBLICATION_AUTHORITY",
 "child":{"id":"93","root":"91","parent":"91","issuer":"5",
  "holder":{"type":"subject","subject":"8"},"targets":["7003"],
  "verbs":["observe","mutate"],"maxCost":"50000",
  "notBefore":"10","notAfter":"1000","issuerEpoch":"2",
  "policyId":"7003","policyEpoch":"0","ancestors":["91"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"7003","capability":"91"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/publication-delegation.json" --key "$EVIDENCE/controller.key" \
  --dir "$EVIDENCE/publication-delegation-attempt" >"$EVIDENCE/publication-delegation.stdout"
confirmed "$EVIDENCE/publication-delegation-attempt/outcome.json"
query_task delegated-publication 8 7003 93 "$EVIDENCE/tool.key" 31012
test "$(jq -er '.page.root' "$EVIDENCE/delegated-publication/view.json")" = "$PUBLICATION_ROOT"

# Reads use a separate observe-only sibling grant. The MCP reader cannot use
# the publication mutation authority or select an arbitrary target.
PUBLICATION_AUTHORITY=$(jq -er '.signing[0].authorityRoot' \
  "$EVIDENCE/delegated-publication/challenge.json")
cat >"$EVIDENCE/publication-read-delegation.json" <<EOF
{"subject":"7","nonce":"31020","purpose":{"type":"prepare","draft":{
 "type":"delegate-source","command":{"kind":"object","domain":"8501",
 "semantics":"$SEMANTICS","subject":"7","nonce":"31021",
 "expectedTargetRoot":"$PUBLICATION_ROOT","parentId":"91","target":"7003",
 "expectedPreRoot":"$PUBLICATION_AUTHORITY",
 "child":{"id":"94","root":"91","parent":"91","issuer":"5",
  "holder":{"type":"subject","subject":"8"},"targets":["7003"],
  "verbs":["observe"],"maxCost":"50000",
  "notBefore":"10","notAfter":"1000","issuerEpoch":"2",
  "policyId":"7003","policyEpoch":"0","ancestors":["91"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"7003","capability":"91"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/publication-read-delegation.json" --key "$EVIDENCE/controller.key" \
  --dir "$EVIDENCE/publication-read-delegation-attempt" \
  >"$EVIDENCE/publication-read-delegation.stdout"
confirmed "$EVIDENCE/publication-read-delegation-attempt/outcome.json"
query_task delegated-read 8 7003 94 "$EVIDENCE/tool.key" 31022
test "$(jq -er '.page.root' "$EVIDENCE/delegated-read/view.json")" = "$PUBLICATION_ROOT"

# The workroom is a real empty content page. A tool mutation grant and a
# separate observe-only read grant are delegated from its owner capability.
WORKROOM_ROOT=$(jq -er '.page.root' "$EVIDENCE/workroom-born/view.json")
WORKROOM_AUTHORITY=$(jq -er '.signing[0].authorityRoot' \
  "$EVIDENCE/delegated-read/challenge.json")
cat >"$EVIDENCE/workroom-delegation.json" <<EOF
{"subject":"7","nonce":"31030","purpose":{"type":"prepare","draft":{
 "type":"delegate-source","command":{"kind":"object","domain":"8501",
 "semantics":"$SEMANTICS","subject":"7","nonce":"31031",
 "expectedTargetRoot":"$WORKROOM_ROOT","parentId":"89","target":"8001",
 "expectedPreRoot":"$WORKROOM_AUTHORITY",
 "child":{"id":"95","root":"89","parent":"89","issuer":"5",
  "holder":{"type":"subject","subject":"8"},"targets":["8001"],
  "verbs":["observe","mutate"],"maxCost":"50000",
  "notBefore":"10","notAfter":"1000","issuerEpoch":"2",
  "policyId":"8001","policyEpoch":"0","ancestors":["89"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"8001","capability":"89"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/workroom-delegation.json" --key "$EVIDENCE/controller.key" \
  --dir "$EVIDENCE/workroom-delegation-attempt" \
  >"$EVIDENCE/workroom-delegation.stdout"
confirmed "$EVIDENCE/workroom-delegation-attempt/outcome.json"
query_task delegated-workroom 8 8001 95 "$EVIDENCE/tool.key" 31032
test "$(jq -er '.page.root' "$EVIDENCE/delegated-workroom/view.json")" = "$WORKROOM_ROOT"

WORKROOM_AUTHORITY=$(jq -er '.signing[0].authorityRoot' \
  "$EVIDENCE/delegated-workroom/challenge.json")
cat >"$EVIDENCE/workroom-read-delegation.json" <<EOF
{"subject":"7","nonce":"31040","purpose":{"type":"prepare","draft":{
 "type":"delegate-source","command":{"kind":"object","domain":"8501",
 "semantics":"$SEMANTICS","subject":"7","nonce":"31041",
 "expectedTargetRoot":"$WORKROOM_ROOT","parentId":"89","target":"8001",
 "expectedPreRoot":"$WORKROOM_AUTHORITY",
 "child":{"id":"96","root":"89","parent":"89","issuer":"5",
  "holder":{"type":"subject","subject":"8"},"targets":["8001"],
  "verbs":["observe"],"maxCost":"50000",
  "notBefore":"10","notAfter":"1000","issuerEpoch":"2",
  "policyId":"8001","policyEpoch":"0","ancestors":["89"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"8001","capability":"89"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/workroom-read-delegation.json" --key "$EVIDENCE/controller.key" \
  --dir "$EVIDENCE/workroom-read-delegation-attempt" \
  >"$EVIDENCE/workroom-read-delegation.stdout"
confirmed "$EVIDENCE/workroom-read-delegation-attempt/outcome.json"
query_task workroom-read 8 8001 96 "$EVIDENCE/tool.key" 31042
test "$(jq -er '.page.root' "$EVIDENCE/workroom-read/view.json")" = "$WORKROOM_ROOT"

# The provider lane fills `commands` and starts its own Hermes runtime. No
# application database is provisioned: notes live in the Mini content cell.
mkdir -m 700 "$EVIDENCE/runtime-state"
jq -n --arg mini "$MINI" --arg host "$HOST" --arg cfg "$CONFIG" \
  --arg controller "$EVIDENCE/controller.key" --arg tool "$EVIDENCE/tool.key" \
  --arg state "$EVIDENCE/runtime-state" --arg cwd "$EVIDENCE" \
  --arg control "$EVIDENCE/runtime-state/control.sock" \
  --arg parent_task "$WORKROOM_PARENT_TASK" --arg tool_task "$WORKROOM_TOOL_TASK" \
  '{mini:$mini,host:$host,hostConfig:$cfg,custodyKey:$controller,
    stateDir:$state,controlSocket:$control,cwd:$cwd,
    task:$parent_task,subject:"7",capability:"71",queryCapability:"71",
    policyControlCapability:"72",
    toolTask:{task:$tool_task,subject:"8",capability:"81",queryCapability:"81",
      custodyKey:$tool,parentCapability:"73",parentObserveCapability:"73",
      reserve:"2",charge:"1",
      allowedPublications:[
        {kind:"object",target:"7003",capability:"93",observeCapability:"93"},
        {kind:"object",target:"8001",capability:"95",observeCapability:"95"}],
      allowedReads:[
        {name:"publication",kind:"object",target:"7003",observeCapability:"94",maxResultBytes:65536},
        {name:"workroom",kind:"object",target:"8001",observeCapability:"96",maxResultBytes:262144}]},
    commands:[]}' >"$EVIDENCE/runtime-config.base.json"
printf '%s\n' "$EVIDENCE/runtime-config.base.json"
