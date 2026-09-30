#!/bin/sh
# Four independently enrolled signers, two parent/tool grains, one content room.
# Signed Mini bootstrap only: controller launch and Hermes prompts are separate.
set -eu
umask 077

if [ "$#" -ne 2 ]; then
  echo "usage: $0 MINIDREGG_HOST NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
BASE=$HERE/provision.sh
EXPECTED=4648f7222897de69e3454c8b7abad7022719697594c0b987fe24a0bb000ba9c8
[ "$(sha256sum "$BASE" | cut -d' ' -f1)" = "$EXPECTED" ] || {
  echo "reviewed provisioner changed; inspect hosted overlay" >&2; exit 2;
}
WORKROOM_PARENT_TASK=7801
WORKROOM_TOOL_TASK=7802
export WORKROOM_PARENT_TASK WORKROOM_TOOL_TASK
STAGE=$(mktemp -d)
trap 'rm -rf "$STAGE"' EXIT HUP INT TERM
cat >"$STAGE/preboot" <<'EOF'
"$MINI" keygen --secret "$EVIDENCE/controller-b.key" --public "$EVIDENCE/controller-b.pub" >"$EVIDENCE/controller-b-public.txt"
"$MINI" keygen --secret "$EVIDENCE/tool-b.key" --public "$EVIDENCE/tool-b.pub" >"$EVIDENCE/tool-b-public.txt"
CONTROLLER_B_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/controller-b.pub" | tr -d ' \n')
TOOL_B_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/tool-b.pub" | tr -d ' \n')
test "$CONTROLLER_B_PUBLIC" != "$TOOL_B_PUBLIC"
test "$CONTROLLER_B_PUBLIC" != "$CONTROLLER_PUBLIC"
test "$CONTROLLER_B_PUBLIC" != "$TOOL_PUBLIC"
test "$TOOL_B_PUBLIC" != "$TOOL_PUBLIC"
test "$TOOL_B_PUBLIC" != "$CONTROLLER_PUBLIC"
jq --arg controller "$CONTROLLER_B_PUBLIC" --arg tool "$TOOL_B_PUBLIC" \
  '.enrollments += [
    {key:{keyId:"9009",keyEpoch:"2",algorithm:"1",subject:"9",
      publicKey:$controller,activeFrom:"0",activeUntil:"1000000"},
      accountId:"9",spendCapabilityId:"43",controlCapabilityId:"56",
      factoryObserveCapabilityId:"57",initialBalance:"100",
      accountPredicate:{type:"all",predicates:[]}},
    {key:{keyId:"1010",keyEpoch:"2",algorithm:"1",subject:"10",
      publicKey:$tool,activeFrom:"0",activeUntil:"1000000"},
      accountId:"13",spendCapabilityId:"44",controlCapabilityId:"58",
      factoryObserveCapabilityId:"59",initialBalance:"100",
      accountPredicate:{type:"all",predicates:[]}}]' \
  "$EVIDENCE/genesis.json" >"$EVIDENCE/genesis-hosted.json"
mv "$EVIDENCE/genesis-hosted.json" "$EVIDENCE/genesis.json"
EOF
cat >"$STAGE/prebirth" <<'EOF'
jq '.birth.resources += [
  {kind:"object",storage:"grain",target:"7803",owner:"9",
    ownerCapability:"111",controlCapability:"112",budget:"100",
    workerSubject:"10",workerGeneration:"1"},
  {kind:"object",storage:"grain",target:"7804",owner:"10",
    ownerCapability:"121",controlCapability:"122",budget:"50"}]' \
  "$EVIDENCE/birth-intent.json" >"$EVIDENCE/birth-hosted.json"
mv "$EVIDENCE/birth-hosted.json" "$EVIDENCE/birth-intent.json"
EOF
awk -v preboot="$STAGE/preboot" -v prebirth="$STAGE/prebirth" '
  /^"\$MINI" bootstrap --host / {
    while ((getline inserted < preboot) > 0) print inserted
    close(preboot); boot++
  }
  /cat >"\$EVIDENCE\/birth-intent.json" <<EOF/ { seen_birth=1 }
  seen_birth && /^"\$MINI" submit --host / && !birth_inserted {
    while ((getline inserted < prebirth) > 0) print inserted
    close(prebirth); birth_inserted++
  }
  { print }
  END { if (boot != 1 || birth_inserted != 1) exit 2 }
' "$BASE" >"$STAGE/provision.sh"
chmod 700 "$STAGE/provision.sh"
"$STAGE/provision.sh" "$1" "$2"

EVIDENCE=$(CDPATH='' cd -- "$2" && pwd)
HOST=$1
MINI=${MINI:?set MINI to the source-matched native client}
CONFIG=$EVIDENCE/deployment/pinned-config.json
mkdir -m 700 "$EVIDENCE/hosted-session"
SOCKET=$EVIDENCE/hosted-session/host.sock
"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$EVIDENCE/hosted-session.stdout" 2>"$EVIDENCE/hosted-session.stderr" &
SERVICE_PID=$!
cleanup_service() { kill "$SERVICE_PID" 2>/dev/null || :; wait "$SERVICE_PID" 2>/dev/null || :; }
trap 'cleanup_service; rm -rf "$STAGE"' EXIT HUP INT TERM
tick=0
until [ -S "$SOCKET" ]; do
  kill -0 "$SERVICE_PID" 2>/dev/null || exit 1
  tick=$((tick + 1)); [ "$tick" -lt 120 ] || exit 1; sleep 1
done

confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (.acceptedCount | type == "string" and test("^[1-9][0-9]*$"))' "$1" >/dev/null
}
query() {
  label=$1 subject=$2 task=$3 cap=$4 key=$5 nonce=$6 view=$7
  jq -n --arg subject "$subject" --arg task "$task" --arg cap "$cap" \
    --arg nonce "$nonce" --arg view "$view" \
    '{subject:$subject,nonce:$nonce,purpose:{type:"query",kind:"object",target:$task,
      view:$view},grants:[{kind:"object",target:$task,capability:$cap}]}' \
    >"$EVIDENCE/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" --view "$view" \
    --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout"
}
submit() {
  label=$1 key=$2
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" \
    --dir "$EVIDENCE/$label-attempt" >"$EVIDENCE/$label.stdout"
  confirmed "$EVIDENCE/$label-attempt/outcome.json"
}
query b-parent-born 9 7803 111 "$EVIDENCE/controller-b.key" 64001 resource
query b-tool-born 10 7804 121 "$EVIDENCE/tool-b.key" 64002 resource
jq -e '.page.grain == {task:"7803",generation:"0",status:"0",remaining:"100",reserved:"0"}' \
  "$EVIDENCE/b-parent-born/view.json" >/dev/null
jq -e '.page.grain == {task:"7804",generation:"0",status:"0",remaining:"50",reserved:"0"}' \
  "$EVIDENCE/b-tool-born/view.json" >/dev/null

# Prove the actual born policies match source-authored owner/worker profiles.
for role in parent tool; do
  if [ "$role" = parent ]; then
    subject=9 task=7803 cap=111 key=controller-b.key nonce=64003
    jq -n '{owner:"9",workerSubject:"10",workerGeneration:"1"}' \
      >"$EVIDENCE/b-parent-policy-source.json"
  else
    subject=10 task=7804 cap=121 key=tool-b.key nonce=64004
    jq -n '{owner:"10"}' >"$EVIDENCE/b-tool-policy-source.json"
  fi
  query "b-$role-policy" "$subject" "$task" "$cap" "$EVIDENCE/$key" "$nonce" policy
  "$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --kind grain-policy --input "$EVIDENCE/b-$role-policy-source.json" \
    --output "$EVIDENCE/b-$role-policy.bin"
  jq -n --slurpfile view "$EVIDENCE/b-$role-policy/view.json" '$view[0].predicate' \
    >"$EVIDENCE/b-$role-view-predicate.json"
  "$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --kind predicate --input "$EVIDENCE/b-$role-view-predicate.json" \
    --output "$EVIDENCE/b-$role-view-predicate.bin"
  cmp "$EVIDENCE/b-$role-policy.bin" "$EVIDENCE/b-$role-view-predicate.bin"
done

SEMANTICS=$(jq -er '.semantics' "$EVIDENCE/operator-profile.json")
root=$(jq -er '.page.root' "$EVIDENCE/b-parent-born/view.json")
authority=$(jq -er '.signing[0].authorityRoot' "$EVIDENCE/b-parent-born/challenge.json")
jq -n --arg semantics "$SEMANTICS" --arg root "$root" --arg authority "$authority" \
  '{subject:"9",nonce:"64100",purpose:{type:"prepare",draft:{type:"delegate-source",
    command:{kind:"object",domain:"8501",semantics:$semantics,subject:"9",
      nonce:"64101",expectedTargetRoot:$root,parentId:"111",target:"7803",
      expectedPreRoot:$authority,
      child:{id:"113",root:"111",parent:"111",issuer:"5",
        holder:{type:"subject",subject:"10"},targets:["7803"],
        verbs:["observe","mutate"],maxCost:"50000",notBefore:"10",notAfter:"1000",
        issuerEpoch:"2",policyId:"7803",policyEpoch:"0",ancestors:["111"],channels:[]}}}},
    grants:[{kind:"object",target:"7803",capability:"111"}]}' \
  >"$EVIDENCE/b-parent-witness-intent.json"
submit b-parent-witness "$EVIDENCE/controller-b.key"
query b-parent-delegated 10 7803 113 "$EVIDENCE/tool-b.key" 64102 resource
test "$(jq -er '.page.root' "$EVIDENCE/b-parent-delegated/view.json")" = "$root"

# Owner 7 gives tool 10 two children on exactly the same content cell.
for grant in write read; do
  if [ "$grant" = write ]; then child=97 nonce=64200 verbs='["observe","mutate"]'; else
    child=98 nonce=64210 verbs='["observe"]'; fi
  query "owner-before-b-$grant" 7 8001 89 "$EVIDENCE/controller.key" "$nonce" resource
  root=$(jq -er '.page.root' "$EVIDENCE/owner-before-b-$grant/view.json")
  authority=$(jq -er '.signing[0].authorityRoot' "$EVIDENCE/owner-before-b-$grant/challenge.json")
  jq -n --arg semantics "$SEMANTICS" --arg root "$root" --arg authority "$authority" \
    --arg child "$child" --arg nonce "$nonce" --argjson verbs "$verbs" \
    '{subject:"7",nonce:($nonce+"1"),purpose:{type:"prepare",draft:{type:"delegate-source",
      command:{kind:"object",domain:"8501",semantics:$semantics,subject:"7",
        nonce:($nonce+"2"),expectedTargetRoot:$root,parentId:"89",target:"8001",
        expectedPreRoot:$authority,
        child:{id:$child,root:"89",parent:"89",issuer:"5",
          holder:{type:"subject",subject:"10"},targets:["8001"],
          verbs:$verbs,maxCost:"50000",notBefore:"10",notAfter:"1000",
          issuerEpoch:"2",policyId:"8001",policyEpoch:"0",ancestors:["89"],channels:[]}}}},
      grants:[{kind:"object",target:"8001",capability:"89"}]}' \
    >"$EVIDENCE/b-content-$grant-intent.json"
  submit "b-content-$grant" "$EVIDENCE/controller.key"
done
query b-content-read 10 8001 98 "$EVIDENCE/tool-b.key" 64220 resource
jq -e '.page.document == "8001" and .page.entries == []' \
  "$EVIDENCE/b-content-read/view.json" >/dev/null

# Both controllers will use one persistent Mini host started by the deployment
# lane after this script stops its temporary socket. Workspaces stay separate.
mkdir -m 700 "$EVIDENCE/runtime-state-a" "$EVIDENCE/runtime-state-b"
HOST_SOCKET=$EVIDENCE/runtime-host/host.sock
jq --arg socket "$HOST_SOCKET" --arg state "$EVIDENCE/runtime-state-a" \
  --arg control "$EVIDENCE/runtime-state-a/control.sock" \
  '.hostSocket=$socket | .stateDir=$state | .controlSocket=$control |
   .toolTask.allowedPublications=[{kind:"object",target:"8001",capability:"95",observeCapability:"95"}] |
   .toolTask.allowedReads=[{name:"workroom",kind:"object",target:"8001",
     observeCapability:"96",maxResultBytes:262144}]' \
  "$EVIDENCE/runtime-config.base.json" >"$EVIDENCE/runtime-config-a.base.json"
jq -n --arg mini "$MINI" --arg host "$HOST" --arg cfg "$CONFIG" \
  --arg socket "$HOST_SOCKET" --arg state "$EVIDENCE/runtime-state-b" \
  --arg control "$EVIDENCE/runtime-state-b/control.sock" --arg cwd "$EVIDENCE" \
  --arg parentKey "$EVIDENCE/controller-b.key" --arg toolKey "$EVIDENCE/tool-b.key" \
  '{mini:$mini,host:$host,hostConfig:$cfg,hostSocket:$socket,
    custodyKey:$parentKey,stateDir:$state,controlSocket:$control,cwd:$cwd,
    task:"7803",subject:"9",capability:"111",queryCapability:"111",
    policyControlCapability:"112",
    toolTask:{task:"7804",subject:"10",capability:"121",queryCapability:"121",
      custodyKey:$toolKey,parentCapability:"113",parentObserveCapability:"113",
      reserve:"2",charge:"1",
      allowedPublications:[{kind:"object",target:"8001",capability:"97",observeCapability:"97"}],
      allowedReads:[{name:"workroom",kind:"object",target:"8001",
        observeCapability:"98",maxResultBytes:262144}]},commands:[]}' \
  >"$EVIDENCE/runtime-config-b.base.json"
printf '%s\n' "$EVIDENCE/runtime-config-a.base.json" "$EVIDENCE/runtime-config-b.base.json"
