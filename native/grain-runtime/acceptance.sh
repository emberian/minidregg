#!/bin/sh
# Fresh, source-authored Mini grain deployment and local runtime journey.
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
GRAIN=${GRAIN:-"$HERE/target/debug/grain-runtime"}
STORE_BINARY=${STORE_BINARY:-"$REPO/native/hyperdocument-link-sqlite-store/target/debug/minidregg-link-sqlite-store"}
SIGNATURE_BINARY=${SIGNATURE_BINARY:-"$REPO/native/credential-signature-verifier/target/debug/minidregg-credential-signature-verifier"}

absolute_executable() {
  item=$1
  [ -x "$item" ] || { echo "not executable: $item" >&2; exit 2; }
  directory=$(CDPATH='' cd -- "$(dirname -- "$item")" && pwd)
  printf '%s/%s\n' "$directory" "$(basename -- "$item")"
}
HOST=$(absolute_executable "$HOST")
MINI=$(absolute_executable "$MINI")
GRAIN=$(absolute_executable "$GRAIN")
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
GRAIN_SERVICE_PID=
RUNTIME_PID=
CONTROLLER_UNIT=
CONTROLLER_MARKER=
CONTROLLER_INVOCATION=
cleanup() {
  if [ -n "$RUNTIME_PID" ]; then kill "$RUNTIME_PID" 2>/dev/null || :; wait "$RUNTIME_PID" 2>/dev/null || :; fi
  if [ -n "$CONTROLLER_UNIT" ] && [ -n "$CONTROLLER_MARKER" ]; then
    current_description=$(systemctl --user show -p Description --value "$CONTROLLER_UNIT" 2>/dev/null || :)
    current_invocation=$(systemctl --user show -p InvocationID --value "$CONTROLLER_UNIT" 2>/dev/null || :)
    if [ "$current_description" = "$CONTROLLER_MARKER" ] &&
        { [ -z "$CONTROLLER_INVOCATION" ] ||
          [ "$current_invocation" = "$CONTROLLER_INVOCATION" ]; }; then
      systemctl --user stop "$CONTROLLER_UNIT" >/dev/null 2>&1 || :
    fi
  fi
  if [ -n "$GRAIN_SERVICE_PID" ]; then kill "$GRAIN_SERVICE_PID" 2>/dev/null || :; wait "$GRAIN_SERVICE_PID" 2>/dev/null || :; fi
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
wait_for_journal() {
  expression=$1
  tick=0
  while [ "$tick" -lt 600 ]; do
    if [ -f "$EVIDENCE/runtime-state/journal.json" ] &&
        jq -e "$expression" "$EVIDENCE/runtime-state/journal.json" >/dev/null 2>&1; then
      return 0
    fi
    if ! kill -0 "$GRAIN_SERVICE_PID" 2>/dev/null; then
      echo "grain service exited before journal reached: $expression" >&2
      return 1
    fi
    tick=$((tick + 1))
    sleep 1
  done
  echo "timed out waiting for grain journal: $expression" >&2
  return 1
}

"$MINI" keygen --secret "$EVIDENCE/controller.key" --public "$EVIDENCE/controller.pub" >"$EVIDENCE/controller-public.txt"
"$MINI" keygen --secret "$EVIDENCE/tool.key" --public "$EVIDENCE/tool.pub" >"$EVIDENCE/tool-public.txt"
if [ "${PROVIDER_BOOTSTRAP:-0}" = 1 ]; then
  "$MINI" keygen --secret "$EVIDENCE/provider.key" --public "$EVIDENCE/provider.pub" \
    >"$EVIDENCE/provider-public.txt"
  PROVIDER_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/provider.pub" | tr -d ' \n')
fi
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
if [ "${PROVIDER_BOOTSTRAP:-0}" = 1 ]; then
  jq --arg public "$PROVIDER_PUBLIC" '.enrollments += [{
    key:{keyId:"9009",keyEpoch:"2",algorithm:"1",subject:"9",
      publicKey:$public,activeFrom:"0",activeUntil:"1000000",revoked:false},
    accountId:"9",spendCapabilityId:"43",controlCapabilityId:"56",
    factoryObserveCapabilityId:"57",initialBalance:"100",
    accountPredicate:{type:"all",predicates:[]}}]' \
    "$EVIDENCE/genesis.json" >"$EVIDENCE/genesis-provider.json"
  mv "$EVIDENCE/genesis-provider.json" "$EVIDENCE/genesis.json"
fi
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
   {"kind":"object","storage":"grain","target":"7001","owner":"7",
    "ownerCapability":"71","controlCapability":"72","budget":"100",
    "workerSubject":"8","workerGeneration":"1"},
   {"kind":"object","storage":"grain","target":"7002","owner":"8",
    "ownerCapability":"81","controlCapability":"82","budget":"50"},
   {"kind":"object","storage":"declared","target":"7003","owner":"7",
    "ownerCapability":"91","controlCapability":"92",
    "predicate":{"type":"all","predicates":[]}}],
  "sourceCapabilities":["41"],"funding":[],"feePayer":"7"},
 "grants":[{"kind":"object","target":"10","capability":"54"},
   {"kind":"account","target":"7","capability":"41"}]}
EOF
if [ "${PROVIDER_BOOTSTRAP:-0}" = 1 ]; then
  jq '(.birth.resources[0] |= (del(.workerSubject) +
       {workerSubjects:["8","9"]})) |
      .birth.resources += [{kind:"object",storage:"grain",target:"7004",
        owner:"9",ownerCapability:"101",controlCapability:"102",budget:"50"}]' \
    "$EVIDENCE/birth-intent.json" >"$EVIDENCE/birth-provider-intent.json"
  mv "$EVIDENCE/birth-provider-intent.json" "$EVIDENCE/birth-intent.json"
fi
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/birth-intent.json" --intent-kind birth-intent \
  --key "$EVIDENCE/controller.key" --dir "$EVIDENCE/birth-attempt" >"$EVIDENCE/birth.stdout"
confirmed "$EVIDENCE/birth-attempt/outcome.json"
query_task controller-born 7 7001 71 "$EVIDENCE/controller.key" 30001
query_task tool-born 8 7002 81 "$EVIDENCE/tool.key" 30002
query_task publication-born 7 7003 91 "$EVIDENCE/controller.key" 30009
if [ "${PROVIDER_BOOTSTRAP:-0}" = 1 ]; then
  query_task provider-born 9 7004 101 "$EVIDENCE/provider.key" 30010
  jq -e '.page.grain == {task:"7004",generation:"0",status:"0",
    remaining:"50",reserved:"0"}' "$EVIDENCE/provider-born/view.json" >/dev/null
fi
jq -e '.page.grain == {task:"7001",generation:"0",status:"0",remaining:"100",reserved:"0"}' \
  "$EVIDENCE/controller-born/view.json" >/dev/null
jq -e '.page.grain == {task:"7002",generation:"0",status:"0",remaining:"50",reserved:"0"}' \
  "$EVIDENCE/tool-born/view.json" >/dev/null

grain_names='controller tool'
if [ "${PROVIDER_BOOTSTRAP:-0}" = 1 ]; then grain_names="$grain_names provider"; fi
for name in $grain_names; do
  if [ "$name" = controller ]; then
    owner=7 task=7001 capability=71 key=controller.key nonce=30003
  elif [ "$name" = tool ]; then
    owner=8 task=7002 capability=81 key=tool.key nonce=30004
  else
    owner=9 task=7004 capability=101 key=provider.key nonce=30011
  fi
  query_policy "$name-policy" "$owner" "$task" "$capability" "$EVIDENCE/$key" "$nonce"
  if [ "$name" = controller ]; then
    if [ "${PROVIDER_BOOTSTRAP:-0}" = 1 ]; then
      jq -n --arg owner "$owner" \
        '{owner:$owner,workerSubjects:["8","9"],workerGeneration:"1"}' \
        >"$EVIDENCE/$name-policy-source.json"
    else
      jq -n --arg owner "$owner" \
        '{owner:$owner,workerSubject:"8",workerGeneration:"1"}' \
        >"$EVIDENCE/$name-policy-source.json"
    fi
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
 "expectedTargetRoot":"$PARENT_ROOT","parentId":"71","target":"7001",
 "expectedPreRoot":"$PARENT_AUTHORITY",
 "child":{"id":"73","root":"71","parent":"71","issuer":"5",
  "holder":{"type":"subject","subject":"8"},"targets":["7001"],
  "verbs":["observe","mutate"],"maxCost":"50000",
  "notBefore":"10","notAfter":"1000","issuerEpoch":"2",
  "policyId":"7001","policyEpoch":"0","ancestors":["71"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"7001","capability":"71"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/parent-witness-delegation.json" --key "$EVIDENCE/controller.key" \
  --dir "$EVIDENCE/delegation-attempt" >"$EVIDENCE/delegation.stdout"
confirmed "$EVIDENCE/delegation-attempt/outcome.json"
query_task delegated-parent 8 7001 73 "$EVIDENCE/tool.key" 31002
test "$(jq -er '.page.root' "$EVIDENCE/delegated-parent/view.json")" = "$PARENT_ROOT"
if [ "${PROVIDER_BOOTSTRAP:-0}" = 1 ]; then
  query_task parent-for-provider 7 7001 71 "$EVIDENCE/controller.key" 31003
  PROVIDER_PARENT_AUTHORITY=$(jq -er '.signing[0].authorityRoot' \
    "$EVIDENCE/parent-for-provider/challenge.json")
  cat >"$EVIDENCE/provider-parent-delegation.json" <<EOF
{"subject":"7","nonce":"31004","purpose":{"type":"prepare","draft":{
 "type":"delegate-source","command":{"kind":"object","domain":"8501",
 "semantics":"$SEMANTICS","subject":"7","nonce":"31005",
 "expectedTargetRoot":"$PARENT_ROOT","parentId":"71","target":"7001",
 "expectedPreRoot":"$PROVIDER_PARENT_AUTHORITY",
 "child":{"id":"75","root":"71","parent":"71","issuer":"5",
  "holder":{"type":"subject","subject":"9"},"targets":["7001"],
  "verbs":["observe","mutate"],"maxCost":"50000",
  "notBefore":"10","notAfter":"1000","issuerEpoch":"2",
  "policyId":"7001","policyEpoch":"0","ancestors":["71"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"7001","capability":"71"}]}
EOF
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/provider-parent-delegation.json" \
    --key "$EVIDENCE/controller.key" --dir "$EVIDENCE/provider-parent-delegation-attempt" \
    >"$EVIDENCE/provider-parent-delegation.stdout"
  confirmed "$EVIDENCE/provider-parent-delegation-attempt/outcome.json"
  query_task delegated-provider-parent 9 7001 75 "$EVIDENCE/provider.key" 31006
  test "$(jq -er '.page.root' "$EVIDENCE/delegated-provider-parent/view.json")" = "$PARENT_ROOT"
fi

PUBLICATION_ROOT=$(jq -er '.page.root' "$EVIDENCE/publication-born/view.json")
if [ "${PROVIDER_BOOTSTRAP:-0}" = 1 ]; then
  query_task publication-for-delegation 7 7003 91 "$EVIDENCE/controller.key" 31007
  PUBLICATION_AUTHORITY=$(jq -er '.signing[0].authorityRoot' \
    "$EVIDENCE/publication-for-delegation/challenge.json")
else
  PUBLICATION_AUTHORITY=$(jq -er '.signing[0].authorityRoot' \
    "$EVIDENCE/delegated-parent/challenge.json")
fi
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

if [ "${BOOTSTRAP_ONLY:-0}" = 1 ]; then
  printf 'signed grain bootstrap ready: %s\n' "$EVIDENCE"
  exit 0
fi

mkdir -m 700 "$EVIDENCE/runtime-state"
case $(uname -s) in
  Darwin)
    HERMES_PROGRAM=/usr/bin/sandbox-exec
    WORKER_PROGRAM=/bin/sleep
    WORKER_SHORT_ARGS='["5"]'
    WORKER_HOLD_ARGS='["3600"]'
    WORKER_SYSTEMD=false
    HERMES_ARGS=$(jq -nc --arg peer "$HERE/fixture/hermes-acp" \
      --arg ready "$EVIDENCE/acp-prompt-ready" \
      --arg release "$EVIDENCE/acp-prompt-release" \
      '["-p","(version 1)(allow default)",$peer,$ready,$release]')
    HERMES_SYSTEMD=false
    ACP_READY="$EVIDENCE/acp-prompt-ready"
    ACP_RELEASE="$EVIDENCE/acp-prompt-release"
    ;;
  Linux)
    HERMES_PROGRAM=$(absolute_executable "$REPO/deploy/grain-host/bwrap")
    CONTROLLER_UNIT=mini-grain-controller@7001.service
    CONTROLLER_MARKER="mini-grain-acceptance:$EVIDENCE"
    mkdir -m 700 "$EVIDENCE/worker-work" "$EVIDENCE/worker-runtime"
    cp "$GRAIN" "$EVIDENCE/worker-runtime/grain-runtime"
    cp "$HERE/fixture/hermes-acp" "$EVIDENCE/worker-runtime/hermes-acp"
    cp "$HERE/fixture/sleep-fixed" "$EVIDENCE/worker-runtime/sleep-fixed"
    WORKER_PROGRAM=$HERMES_PROGRAM
    WORKER_SHORT_ARGS=$(jq -nc --arg work "$EVIDENCE/worker-work" \
      --arg runtime "$EVIDENCE/worker-runtime" \
      '["--workspace",$work,"--runtime-root",$runtime,"--network","none",
        "--","/agent/sleep-fixed","5"]')
    WORKER_HOLD_ARGS=$(jq -nc --arg work "$EVIDENCE/worker-work" \
      --arg runtime "$EVIDENCE/worker-runtime" \
      '["--workspace",$work,"--runtime-root",$runtime,"--network","none",
        "--","/agent/sleep-fixed","3600"]')
    WORKER_SYSTEMD=true
    ACP_READY="$EVIDENCE/worker-work/acp-prompt-ready"
    ACP_RELEASE="$EVIDENCE/worker-work/acp-prompt-release"
    HERMES_ARGS=$(jq -nc --arg work "$EVIDENCE/worker-work" \
      --arg runtime "$EVIDENCE/worker-runtime" \
      '["--workspace",$work,"--runtime-root",$runtime,"--network","none",
        "--","/agent/hermes-acp","/workspace/acp-prompt-ready",
        "/workspace/acp-prompt-release"]')
    HERMES_SYSTEMD=true
    ;;
  *) echo "unsupported acceptance host platform" >&2; exit 2 ;;
esac
jq -n --arg mini "$MINI" --arg host "$HOST" --arg cfg "$CONFIG" \
  --arg socket "$SOCKET" --arg controller "$EVIDENCE/controller.key" \
  --arg tool "$EVIDENCE/tool.key" --arg state "$EVIDENCE/runtime-state" \
  --arg cwd "$EVIDENCE" --arg control "$EVIDENCE/runtime-state/control.sock" \
  --arg hermesProgram "$HERMES_PROGRAM" --argjson hermesArgs "$HERMES_ARGS" \
  --argjson hermesSystemd "$HERMES_SYSTEMD" \
  --arg workerProgram "$WORKER_PROGRAM" \
  --argjson workerShortArgs "$WORKER_SHORT_ARGS" \
  --argjson workerHoldArgs "$WORKER_HOLD_ARGS" \
  --argjson workerSystemd "$WORKER_SYSTEMD" \
  '{mini:$mini,host:$host,hostConfig:$cfg,hostSocket:$socket,custodyKey:$controller,
    stateDir:$state,controlSocket:$control,cwd:$cwd,
    task:"7001",subject:"7",capability:"71",queryCapability:"71",
    policyControlCapability:"72",
    toolTask:{task:"7002",subject:"8",capability:"81",queryCapability:"81",
      custodyKey:$tool,parentCapability:"73",parentObserveCapability:"73",
      reserve:"2",charge:"1",
      allowedPublications:[{kind:"object",target:"7003",capability:"93",observeCapability:"93"}],
      allowedReads:[{name:"publication",kind:"object",target:"7003",
        observeCapability:"94",maxResultBytes:65536}]},
    commands:[{name:"short",program:$workerProgram,args:$workerShortArgs,
        systemdScope:$workerSystemd,reserve:"3",charge:"1"},
      {name:"hold",program:$workerProgram,args:$workerHoldArgs,
        systemdScope:$workerSystemd,reserve:"3",charge:"0"},
      {name:"hermes-acp",program:$hermesProgram,args:$hermesArgs,
        systemdScope:$hermesSystemd,reserve:"3",charge:"1"}]}' \
  >"$EVIDENCE/runtime-config.json"

CONTROL_SOCKET="$EVIDENCE/runtime-state/control.sock"
if [ -n "$CONTROLLER_UNIT" ]; then
  current_state=$(systemctl --user show -p ActiveState --value "$CONTROLLER_UNIT" 2>/dev/null || :)
  case $current_state in
    active|activating|deactivating|reloading)
      echo "controller unit is already in use: $CONTROLLER_UNIT ($current_state)" >&2
      exit 1 ;;
  esac
  systemd-run --user --wait --pipe --collect --unit="${CONTROLLER_UNIT%.service}" \
    --description="$CONTROLLER_MARKER" \
    --property=KillMode=control-group --property=RuntimeMaxSec=1800s \
    "$GRAIN" serve "$EVIDENCE/runtime-config.json" \
    >"$EVIDENCE/grain-service.stdout" 2>"$EVIDENCE/grain-service.stderr" &
else
  "$GRAIN" serve "$EVIDENCE/runtime-config.json" \
    >"$EVIDENCE/grain-service.stdout" 2>"$EVIDENCE/grain-service.stderr" &
fi
GRAIN_SERVICE_PID=$!
tick=0
until [ -S "$CONTROL_SOCKET" ]; do
  kill -0 "$GRAIN_SERVICE_PID" 2>/dev/null || { echo "grain service failed to start" >&2; exit 1; }
  tick=$((tick + 1))
  [ "$tick" -lt 120 ] || { echo "grain control socket timeout" >&2; exit 1; }
  sleep 1
done
if [ -n "$CONTROLLER_UNIT" ]; then
  current_description=$(systemctl --user show -p Description --value "$CONTROLLER_UNIT")
  [ "$current_description" = "$CONTROLLER_MARKER" ] || {
    echo "controller unit ownership marker mismatch" >&2; exit 1;
  }
  CONTROLLER_INVOCATION=$(systemctl --user show -p InvocationID --value "$CONTROLLER_UNIT")
  [ -n "$CONTROLLER_INVOCATION" ] || {
    echo "controller unit has no invocation identity" >&2; exit 1;
  }
fi

# A soft EOF allows the allowlisted local command to finish and settle.
mkfifo "$EVIDENCE/soft-input.fifo"
"$GRAIN" connect "$CONTROL_SOCKET" <"$EVIDENCE/soft-input.fifo" \
  >"$EVIDENCE/soft-runtime.stdout" 2>"$EVIDENCE/soft-runtime.stderr" &
RUNTIME_PID=$!
exec 3>"$EVIDENCE/soft-input.fifo"
printf 'attach soft\n' >&3
wait_for_journal '.connection == "soft" and .pending == null'
printf 'run short\n' >&3
wait_for_journal '.child != null and .child.pid > 0'
exec 3>&-
wait "$RUNTIME_PID"
RUNTIME_PID=
wait_for_journal '.connection == "soft" and .pending == null and .child == null and .settlementDue == null'
query_task after-soft 7 7001 71 "$EVIDENCE/controller.key" 30005
jq -e '.page.grain.status == "2" and .page.grain.remaining == "99" and
  .page.grain.reserved == "0"' "$EVIDENCE/after-soft/view.json" >/dev/null

# Switch to hard mode, hold a local process, then disconnect while reserved.
# The runtime stops its process group before submitting the generation fence.
mkfifo "$EVIDENCE/runtime-input.fifo"
"$GRAIN" connect "$CONTROL_SOCKET" <"$EVIDENCE/runtime-input.fifo" \
  >"$EVIDENCE/hard-runtime.stdout" 2>"$EVIDENCE/hard-runtime.stderr" &
RUNTIME_PID=$!
exec 3>"$EVIDENCE/runtime-input.fifo"
printf 'attach hard\n' >&3
wait_for_journal '.connection == "hard" and .pending == null'
printf 'run hold\n' >&3
wait_for_journal '.child != null and .child.pid > 0'
HOLD_PID=$(jq -er '.child.pid' "$EVIDENCE/runtime-state/journal.json")
HOLD_UNIT=$(jq -r '.child.unit // ""' "$EVIDENCE/runtime-state/journal.json")

# The separate tool task writes alongside an unchanged parent grain witness
# under one signed native command. Both target read grants are authenticated.
tool_witness_source() {
  name=$1 operation=$2 nonce=$3
  query_task "$name-tool" 8 7002 81 "$EVIDENCE/tool.key" "$((nonce + 1))"
  query_task "$name-parent" 8 7001 73 "$EVIDENCE/tool.key" "$((nonce + 2))"
  jq -e '.page.grain.status == "3" and .page.grain.generation == "1"' \
    "$EVIDENCE/$name-parent/view.json" >/dev/null
  jq -n --argjson op "$operation" --arg nonce "$nonce" \
    --slurpfile tool "$EVIDENCE/$name-tool/view.json" \
    --slurpfile toolChallenge "$EVIDENCE/$name-tool/challenge.json" \
    --slurpfile parent "$EVIDENCE/$name-parent/view.json" \
    '{grain:{task:"7002",subject:"8",capability:"81",observeCapability:"81",
      schemaVersion:"1",expectedAuthorityRoot:$toolChallenge[0].signing[0].authorityRoot,
      expectedTargetRoot:$tool[0].page.root,
      context:{operationId:$nonce,payload:"separate tool task with parent witness"},
      before:{generation:$tool[0].page.grain.generation,status:$tool[0].page.grain.status,
        remaining:$tool[0].page.grain.remaining,reserved:$tool[0].page.grain.reserved},
      operation:$op,
      parentWitness:{task:"7001",capability:"73",observeCapability:"73",
        expectedTargetRoot:$parent[0].page.root,
        before:{generation:$parent[0].page.grain.generation,
          status:$parent[0].page.grain.status,remaining:$parent[0].page.grain.remaining,
          reserved:$parent[0].page.grain.reserved}},publications:[]},
      grants:[{kind:"object",target:"7002",capability:"81"},
        {kind:"object",target:"7001",capability:"73"}],intentNonce:$nonce}' \
    >"$EVIDENCE/$name-intent.json"
}
tool_witness_source tool-attach '{"type":"attach","soft":false}' 32000
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/tool-attach-intent.json" --intent-kind grain-intent \
  --key "$EVIDENCE/tool.key" --dir "$EVIDENCE/tool-attach-attempt" \
  >"$EVIDENCE/tool-attach.stdout"
confirmed "$EVIDENCE/tool-attach-attempt/outcome.json"
tool_witness_source stale-tool-input '{"type":"input"}' 32010
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/stale-tool-input-intent.json" --intent-kind grain-intent \
  --key "$EVIDENCE/tool.key" --prepare-only true \
  --dir "$EVIDENCE/stale-tool-input-attempt" >"$EVIDENCE/stale-tool-input.stdout"
test -s "$EVIDENCE/stale-tool-input-attempt/call.bin"

printf 'disconnect\n' >&3
exec 3>&-
wait "$RUNTIME_PID"
RUNTIME_PID=
wait_for_journal '.connection == "detached" and .pending == null and .child == null'
if kill -0 "$HOLD_PID" 2>/dev/null; then
  echo "hard-stopped worker PID is still live: $HOLD_PID" >&2
  exit 1
fi
if [ -n "$HOLD_UNIT" ]; then
  unit_state=$(systemctl --user show -p ActiveState --value "$HOLD_UNIT.service")
  case $unit_state in
    active|activating|deactivating)
      echo "hard-stopped worker unit is still active: $HOLD_UNIT ($unit_state)" >&2
      exit 1 ;;
  esac
fi
query_task after-hard 7 7001 71 "$EVIDENCE/controller.key" 30006
jq -e '.page.grain.generation == "2" and .page.grain.status == "5" and
  .page.grain.reserved == "3"' "$EVIDENCE/after-hard/view.json" >/dev/null
if "$MINI" retry --attempt "$EVIDENCE/stale-tool-input-attempt" --socket "$SOCKET" \
    --mode submit >"$EVIDENCE/stale-tool-input-retry.stdout" \
    2>"$EVIDENCE/stale-tool-input-retry.stderr"; then
  echo "stale parent witness unexpectedly published" >&2
  exit 1
fi
jq -e '.type == "refused"' "$EVIDENCE/stale-tool-input-attempt/retry-0001.json" >/dev/null

# Recovery is operator-directed through the separate private admin socket.
# The operator audited the stopped local process group. The runtime checks
# the signed reserved amount, settles the configured zero charge, records that
# audit and an explicit external-effect acknowledgement, then reattaches.
"$GRAIN" admin "$EVIDENCE/runtime-state/admin.sock" 'reconcile parent audited' \
  >"$EVIDENCE/reconcile-parent.stdout" 2>"$EVIDENCE/reconcile-parent.stderr"
wait_for_journal '.parentHold == null and
  (.reconciliationLog | any(.authority == "parent" and .stage == "signed-settlement-confirmed"))'
query_task reconciled-parent 7 7001 71 "$EVIDENCE/controller.key" 30010
jq -e '.page.grain.generation == "2" and .page.grain.status == "0" and
  .page.grain.remaining == "99" and .page.grain.reserved == "0"' \
  "$EVIDENCE/reconciled-parent/view.json" >/dev/null
"$GRAIN" admin "$EVIDENCE/runtime-state/admin.sock" 'reconcile effects' \
  >"$EVIDENCE/reconcile-effects.stdout" 2>"$EVIDENCE/reconcile-effects.stderr"
wait_for_journal '(.unresolvedExternal | length) == 0 and
  (.reconciliationLog | any(.action == "acknowledge-external-effects" and
    .externalEffectsAcknowledged == true))'

mkfifo "$EVIDENCE/recovered-input.fifo"
"$GRAIN" connect "$CONTROL_SOCKET" <"$EVIDENCE/recovered-input.fifo" \
  >"$EVIDENCE/recovered-runtime.stdout" 2>"$EVIDENCE/recovered-runtime.stderr" &
RUNTIME_PID=$!
exec 3>"$EVIDENCE/recovered-input.fifo"
printf 'attach soft\n' >&3
wait_for_journal '.connection == "soft" and .pending == null'
printf 'recover\nrun short\n' >&3
wait_for_journal '.child != null and .child.pid > 0'
wait_for_journal '.connection == "soft" and .pending == null and .child == null and .settlementDue == null'
printf 'hermes acceptance-publication\n' >&3
tick=0
until [ -f "$ACP_READY" ]; do
  kill -0 "$GRAIN_SERVICE_PID" 2>/dev/null || { echo "grain service exited before ACP prompt" >&2; exit 1; }
  if [ -f "$EVIDENCE/runtime-state/journal.json" ] &&
      jq -e '.connection == "fenced" and .pending == null and .child == null' \
        "$EVIDENCE/runtime-state/journal.json" >/dev/null; then
    echo "grain fenced before ACP prompt" >&2
    exit 1
  fi
  tick=$((tick + 1))
  [ "$tick" -lt 600 ] || { echo "ACP protocol peer did not reach prompt" >&2; exit 1; }
  sleep 1
done
broker=
for candidate in "$EVIDENCE"/runtime-state/mcp-*.sock; do
  if [ -S "$candidate" ]; then broker=$candidate; break; fi
done
test -n "$broker" || { echo "MCP broker socket absent during ACP prompt" >&2; exit 1; }

# The fixture only holds the ACP prompt open. This call traverses the real
# stdio MCP edge, controller broker, signed tool grain and native publication.
jq -nc --arg root "$PUBLICATION_ROOT" \
  '{jsonrpc:"2.0",id:3,method:"tools/call",params:{name:"mini_publish",
    arguments:{publications:[{kind:"object",target:"7003",expectedTargetRoot:$root,
      payload:{type:"scalar",actions:[{type:"create",
        key:{type:"object",resource:"7003",field:"0"},value:"1"}]}}]}}}' \
  >"$EVIDENCE/mcp-publication-request.json"
{
  printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18"}}'
  printf '%s\n' '{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}'
  cat "$EVIDENCE/mcp-publication-request.json"
  printf '%s\n' '{"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"mini_read_resource","arguments":{"name":"publication"}}}'
} | "$GRAIN" mcp-stdio "$broker" >"$EVIDENCE/mcp-responses.jsonl"
jq -es 'length == 4 and .[0].result.serverInfo.name == "mini-grain" and
  (.[1].result.tools | any(.name == "mini_publish")) and
  (.[1].result.tools | any(.name == "mini_read_resource")) and
  .[2].result.isError == false and .[3].result.isError == false and
  (.[3].result.content[0].text | fromjson |
    .kind == "object" and .target == "7003" and .view.type == "resource")' \
  "$EVIDENCE/mcp-responses.jsonl" >/dev/null
query_task after-mcp-publication 8 7003 93 "$EVIDENCE/tool.key" 33005
POST_PUBLICATION_ROOT=$(jq -er '.page.root' "$EVIDENCE/after-mcp-publication/view.json")
test "$POST_PUBLICATION_ROOT" != "$PUBLICATION_ROOT"
jq -es --arg root "$POST_PUBLICATION_ROOT" \
  '(.[3].result.content[0].text | fromjson | .view.page.root) == $root' \
  "$EVIDENCE/mcp-responses.jsonl" >/dev/null
: >"$ACP_RELEASE"
wait_for_journal '.connection == "soft" and .pending == null and .child == null and .settlementDue == null'
exec 3>&-
wait "$RUNTIME_PID"
RUNTIME_PID=
query_task final-controller 7 7001 71 "$EVIDENCE/controller.key" 30007
query_task final-tool 8 7002 81 "$EVIDENCE/tool.key" 30008
jq -e '.page.grain.generation == "3" and .page.grain.status == "2" and
  .page.grain.remaining == "97" and .page.grain.reserved == "0"' \
  "$EVIDENCE/final-controller/view.json" >/dev/null
jq -e '.page.grain == {task:"7002",generation:"4",status:"0",remaining:"49",reserved:"0"}' \
  "$EVIDENCE/final-tool/view.json" >/dev/null

# The runtime itself renews the source-authored witness rule after each
# attachment and before admitting a tool call. Reattachment advanced the
# parent generation to three; inspect that live installed rule directly.
query_policy renewed 7 7001 71 "$EVIDENCE/controller.key" 33003
test "$(jq -er '.version | tonumber' "$EVIDENCE/renewed/view.json")" -ge 3
jq -e '.previous != null' "$EVIDENCE/renewed/view.json" >/dev/null
jq -n '{owner:"7",workerSubject:"8",workerGeneration:"3"}' \
  >"$EVIDENCE/renewed-policy-source.json"
"$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --kind grain-policy --input "$EVIDENCE/renewed-policy-source.json" \
  --output "$EVIDENCE/renewed-policy.bin"
jq '.predicate' "$EVIDENCE/renewed/view.json" >"$EVIDENCE/renewed-predicate.json"
"$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --kind predicate --input "$EVIDENCE/renewed-predicate.json" \
  --output "$EVIDENCE/renewed-view-predicate.bin"
cmp "$EVIDENCE/renewed-policy.bin" "$EVIDENCE/renewed-view-predicate.bin"
query_task renewed-worker-read 8 7001 73 "$EVIDENCE/tool.key" 33004

jq -n --slurpfile birth "$EVIDENCE/birth-attempt/outcome.json" \
  --slurpfile reconciliation "$EVIDENCE/runtime-state/journal.json" \
  --slurpfile controller "$EVIDENCE/final-controller/view.json" \
  --slurpfile tool "$EVIDENCE/final-tool/view.json" \
  --slurpfile publication "$EVIDENCE/after-mcp-publication/view.json" \
  '{type:"grain-native-acceptance",birth:$birth[0],
    reconciliation:$reconciliation[0].reconciliationLog,
    controller:$controller[0].page.grain,tool:$tool[0].page.grain,
    publicationRoot:$publication[0].page.root}' \
  >"$EVIDENCE/acceptance.json"
cat >"$EVIDENCE/OPERATE.txt" <<EOF
This directory is a native Mini deployment with two distinct grain resources.
The exact source, signed attempts, pinned config and runtime journal are retained.

Start the local verified host session:
  $MINI serve --host $HOST --config $CONFIG --socket $SOCKET

Start the persistent grain controller in another terminal:
  $GRAIN serve $EVIDENCE/runtime-config.json

Attach over its private control socket from a third terminal:
  $GRAIN connect $CONTROL_SOCKET
  attach hard

Only the allowlisted short and hold commands can be selected by this config.
The tool task is resource 7002, owned by subject 8 with its own custody key.
Resource 7003 was published through the runtime's MCP broker while a local
deterministic ACP protocol peer held a prompt. The peer performs no model work;
this check exercises the native tool and publication path.
The delegated parent witness is capability 73; native policy pins its no-op
mutation to the current generation. The runtime must renew that policy through
the signed grain-policy-install-intent route after a later generation change.
EOF
echo "PASS native grain bootstrap, persistent socket, soft completion, hard stop, signed reconciliation, recovery, worker policy renewal and MCP publication: $EVIDENCE"
