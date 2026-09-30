#!/bin/sh
# Add the integrated agents to the reviewed fresh genesis and first grain birth.
# This only writes an exact private provision source. It does not run Mini.
set -eu
umask 077

if [ "$#" -ne 3 ]; then
  echo "usage: $0 CHECKED_PROVISION ALLOCATION_JSON NEW_OUTPUT_SOURCE" >&2
  exit 2
fi
SOURCE=$1 ALLOCATION=$2 OUTPUT=$3
[ -f "$SOURCE" ] && [ -f "$ALLOCATION" ] || exit 2
[ ! -e "$OUTPUT" ] && [ ! -L "$OUTPUT" ] || {
  echo "agent provision output already exists" >&2; exit 2;
}
command -v jq >/dev/null 2>&1 || exit 2

# All resource and capability coordinates are distinct from the existing
# genesis 7/8/9, deployment 10/11/12 and initial workroom resources.
jq -e '
  .protocol == "mini-spk-integrated-allocation-v1" and
  .status == "reserved-coordinates-only" and
  ([.agents[].route] == ["hermes-a","hermes-b"]) and
  ([.agents[] | [.controller,.tool,.dispatch,.provider][]] | length == 8) and
  ([.agents[] | [.controller,.tool,.dispatch,.provider][] |
      .subject,.keyId,.account,.factoryObserveCapability,.task] |
      all(.[]; type == "string" and test("^[1-9][0-9]*$"))) and
  ([.agents[] | [.controller,.tool,.dispatch,.provider][] | .subject] +
    ["7","8","9"] | unique | length == 11) and
  ([.agents[] | [.controller,.tool,.dispatch,.provider][] | .keyId] +
    ["7007","8008","9009"] | unique | length == 11) and
  ([.humans[].plannedCaps[],.agents[].plannedCaps[],
      (.agents[] | [.controller,.tool,.dispatch,.provider][] |
        .factoryObserveCapability)] |
    all(.[]; type == "string" and test("^[1-9][0-9]*$"))) and
  (["0","7","8","9","10","11","12","99","7003","7503",
      "7901","7902","8001","8301",.app,.packageManifest,.snapshotManifest] +
    [.humans[] | .session,.descriptor,.ticket] +
    [.agents[] | .session,.descriptor,.ticket,.persistentGrant] +
    [.agents[] | [.controller,.tool,.dispatch,.provider][] | .account,.task]) as $resources |
  ($resources | all(.[]; type == "string" and
    test("^(0|[1-9][0-9]*)$"))) and
  ($resources | unique | length) == ($resources | length) and
  (["41","42","43","51","52","53","54","55","56","57",
      "71","72","73","81","82","83","84","85","86",
      "89","90","91","92","93","94","95","96",
      "141","142","143","144","145","146"] +
    [.humans[].plannedCaps[]] + [.agents[].plannedCaps[]] +
    [.agents[] | [.controller,.tool,.dispatch,.provider][] |
      .factoryObserveCapability]) as $capabilities |
  ($capabilities | unique | length) == ($capabilities | length)
' "$ALLOCATION" >/dev/null || {
  echo "agent allocation conflicts with fresh genesis or birth resources" >&2; exit 2;
}

STAGE=$OUTPUT.stage
[ ! -e "$STAGE" ] && [ ! -L "$STAGE" ] || exit 2
mkdir -m 700 "$STAGE"
trap 'rm -rf -- "$STAGE"' EXIT HUP INT TERM

cat >"$STAGE/preboot" <<'EOF'
# Agent signing keys are generated only in this private fresh fixture. Each
# genesis enrollment has its own account and cannot borrow another signer.
mkdir -m 700 "$EVIDENCE/agents"
for route in hermes-a hermes-b; do
  mkdir -m 700 "$EVIDENCE/agents/$route"
  for role in controller tool dispatch provider; do
    spec=$(jq -c --arg route "$route" --arg role "$role" '
      .agents[] | select(.route == $route) |
      .[$role] + {spendCapability:
        (if $role == "controller" then .plannedCaps.controllerSpend
         elif $role == "tool" then .plannedCaps.toolSpend
         elif $role == "dispatch" then .plannedCaps.dispatchSpend
         else .plannedCaps.providerSpend end),
        controlCapability:
        (if $role == "controller" then .plannedCaps.controllerControl
         elif $role == "tool" then .plannedCaps.toolControl
         elif $role == "dispatch" then .plannedCaps.dispatchControl
         else .plannedCaps.providerControl end)}' "$SPK_AGENT_ALLOCATION")
    [ -n "$spec" ] && [ "$spec" != null ] || exit 2
    key="$EVIDENCE/agents/$route/$role.key"
    pub="$EVIDENCE/agents/$route/$role.pub"
    "$MINI" keygen --secret "$key" --public "$pub" \
      >"$EVIDENCE/agents/$route/$role-keygen.txt"
    public=$(od -An -tx1 -v "$pub" | tr -d ' \n')
    test "${#public}" = 64
    printf '%s\n' "$spec" | jq -c --arg public "$public" '
      {key:{keyId:.keyId,keyEpoch:"2",algorithm:"1",subject:.subject,
        publicKey:$public,activeFrom:"0",activeUntil:"1000000"},
       accountId:.account,
       spendCapabilityId:.spendCapability,
       controlCapabilityId:.controlCapability,
       factoryObserveCapabilityId:.factoryObserveCapability,
       initialBalance:"1000000",accountPredicate:{type:"all",predicates:[]}}' \
      >>"$EVIDENCE/agents/enrollments.jsonl"
  done
done
EOF

cat >>"$STAGE/preboot" <<'EOF'
jq -s '.' "$EVIDENCE/agents/enrollments.jsonl" \
  >"$EVIDENCE/agents/enrollments.json"
jq --slurpfile extra "$EVIDENCE/agents/enrollments.json" \
  '.enrollments += $extra[0]' "$EVIDENCE/genesis.json" \
  >"$EVIDENCE/agents/genesis-with-agents.json"
mv "$EVIDENCE/agents/genesis-with-agents.json" "$EVIDENCE/genesis.json"
jq -e '([.enrollments[].key.publicKey] | unique | length) ==
  (.enrollments | length)' "$EVIDENCE/genesis.json" >/dev/null
EOF

cat >"$STAGE/prebirth" <<'EOF'
jq --slurpfile allocation "$SPK_AGENT_ALLOCATION" '
  .birth.resources += [ $allocation[0].agents[] as $agent |
    {kind:"object",storage:"grain",target:$agent.controller.task,
      owner:$agent.controller.subject,ownerCapability:$agent.plannedCaps.parentOwner,
      controlCapability:$agent.plannedCaps.parentControl,budget:"100",
      workerSubjects:[$agent.tool.subject,$agent.dispatch.subject,
        $agent.provider.subject],workerGeneration:"1"},
    {kind:"object",storage:"grain",target:$agent.tool.task,
      owner:$agent.tool.subject,ownerCapability:$agent.plannedCaps.toolOwner,
      controlCapability:$agent.plannedCaps.toolTaskControl,budget:"50"},
    {kind:"object",storage:"grain",target:$agent.dispatch.task,
      owner:$agent.dispatch.subject,ownerCapability:$agent.plannedCaps.dispatchOwner,
      controlCapability:$agent.plannedCaps.dispatchTaskControl,budget:"50"},
    {kind:"object",storage:"grain",target:$agent.provider.task,
      owner:$agent.provider.subject,ownerCapability:$agent.plannedCaps.providerOwner,
      controlCapability:$agent.plannedCaps.providerTaskControl,budget:"50"}
  ]' "$EVIDENCE/birth-intent.json" >"$EVIDENCE/agents/birth-with-agents.json"
mv "$EVIDENCE/agents/birth-with-agents.json" "$EVIDENCE/birth-intent.json"
EOF

cat >"$STAGE/postbirth" <<'EOF'
# The one signed birth receipt covers all eight added grains. Verify each
# owner can separately observe its exact born resource and record that view.
mkdir -m 700 "$EVIDENCE/agents/verified"
for route in hermes-a hermes-b; do
  for role in controller tool dispatch provider; do
    spec=$(jq -c --arg route "$route" --arg role "$role" \
      '.agents[] | select(.route == $route) | .[$role]' "$SPK_AGENT_ALLOCATION")
    subject=$(printf '%s\n' "$spec" | jq -er .subject)
    task=$(printf '%s\n' "$spec" | jq -er .task)
    case "$role" in
      controller) cap=$(jq -er --arg route "$route" \
        '.agents[] | select(.route == $route) | .plannedCaps.parentOwner' \
        "$SPK_AGENT_ALLOCATION"); budget=100 ;;
      tool) cap=$(jq -er --arg route "$route" \
        '.agents[] | select(.route == $route) | .plannedCaps.toolOwner' \
        "$SPK_AGENT_ALLOCATION"); budget=50 ;;
      dispatch) cap=$(jq -er --arg route "$route" \
        '.agents[] | select(.route == $route) | .plannedCaps.dispatchOwner' \
        "$SPK_AGENT_ALLOCATION"); budget=50 ;;
      provider) cap=$(jq -er --arg route "$route" \
        '.agents[] | select(.route == $route) | .plannedCaps.providerOwner' \
        "$SPK_AGENT_ALLOCATION"); budget=50 ;;
    esac
    label="$route-$role"
    jq -n --arg s "$subject" --arg t "$task" --arg c "$cap" \
      --arg n "$((50000 + task))" '
      {subject:$s,nonce:$n,purpose:{type:"query",kind:"object",
        target:$t,view:"resource"},
       grants:[{kind:"object",target:$t,capability:$c}]}' \
      >"$EVIDENCE/agents/verified/$label-intent.json"
    "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
      --intent "$EVIDENCE/agents/verified/$label-intent.json" \
      --key "$EVIDENCE/agents/$route/$role.key" --view resource \
      --dir "$EVIDENCE/agents/verified/$label" \
      >"$EVIDENCE/agents/verified/$label.stdout"
    jq -e --arg t "$task" --arg b "$budget" '
      .cell.grain == {task:$t,generation:"0",status:"0",
        remaining:$b,reserved:"0"}' \
      "$EVIDENCE/agents/verified/$label/view.json" >/dev/null
    jq -cn --arg route "$route" --arg role "$role" --arg task "$task" \
      --arg subject "$subject" --arg capability "$cap" \
      --arg viewSha "$(sha256sum \
        "$EVIDENCE/agents/verified/$label/view.json" | cut -d ' ' -f 1)" \
      --slurpfile view "$EVIDENCE/agents/verified/$label/view.json" '
      {route:$route,role:$role,task:$task,subject:$subject,
       capability:$capability,root:$view[0].cell.root,viewSha256:$viewSha}' \
      >>"$EVIDENCE/agents/verified/born-views.jsonl"
  done
done
# Check each parent's actual installed grain policy against the source-owned
# owner/tool-worker rule; the separate parent child grants are added below.
for route in hermes-a hermes-b; do
  controller=$(jq -c --arg route "$route" \
    '.agents[] | select(.route == $route) | .controller' \
    "$SPK_AGENT_ALLOCATION")
  parent_task=$(printf '%s\n' "$controller" | jq -er .task)
  controller_subject=$(printf '%s\n' "$controller" | jq -er .subject)
  tool_subject=$(jq -er --arg route "$route" \
    '.agents[] | select(.route == $route) | .tool.subject' \
    "$SPK_AGENT_ALLOCATION")
  dispatch_subject=$(jq -er --arg route "$route" \
    '.agents[] | select(.route == $route) | .dispatch.subject' \
    "$SPK_AGENT_ALLOCATION")
  provider_subject=$(jq -er --arg route "$route" \
    '.agents[] | select(.route == $route) | .provider.subject' \
    "$SPK_AGENT_ALLOCATION")
  parent_owner=$(jq -er --arg route "$route" \
    '.agents[] | select(.route == $route) | .plannedCaps.parentOwner' \
    "$SPK_AGENT_ALLOCATION")
  jq -n --arg s "$controller_subject" --arg t "$parent_task" \
    --arg c "$parent_owner" --arg n "$((55000 + parent_task))" '
    {subject:$s,nonce:$n,purpose:{type:"query",kind:"object",
      target:$t,view:"policy"},
     grants:[{kind:"object",target:$t,capability:$c}]}' \
    >"$EVIDENCE/agents/verified/$route-parent-policy-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/agents/verified/$route-parent-policy-intent.json" \
    --key "$EVIDENCE/agents/$route/controller.key" --view policy \
    --dir "$EVIDENCE/agents/verified/$route-parent-policy" \
    >"$EVIDENCE/agents/verified/$route-parent-policy.stdout"
  jq -e '.version == "0" and .predicate != null' \
    "$EVIDENCE/agents/verified/$route-parent-policy/view.json" >/dev/null
  jq -n --arg owner "$controller_subject" --arg tool "$tool_subject" \
    --arg dispatch "$dispatch_subject" --arg provider "$provider_subject" \
    '{owner:$owner,workerSubjects:[$tool,$dispatch,$provider],
      workerGeneration:"1"}' \
    >"$EVIDENCE/agents/verified/$route-parent-policy-source.json"
  "$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --kind grain-policy \
    --input "$EVIDENCE/agents/verified/$route-parent-policy-source.json" \
    --output "$EVIDENCE/agents/verified/$route-parent-policy-authored.bin"
  jq -n --slurpfile view \
    "$EVIDENCE/agents/verified/$route-parent-policy/view.json" \
    '$view[0].predicate' \
    >"$EVIDENCE/agents/verified/$route-parent-policy-predicate.json"
  "$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --kind predicate \
    --input "$EVIDENCE/agents/verified/$route-parent-policy-predicate.json" \
    --output "$EVIDENCE/agents/verified/$route-parent-policy-view.bin"
  cmp "$EVIDENCE/agents/verified/$route-parent-policy-authored.bin" \
    "$EVIDENCE/agents/verified/$route-parent-policy-view.bin"
done
# Three separately held parent witnesses per controller. Each delegation is
# prepared from a fresh signed owner observation, then the named holder signs
# its own readback. The initial workerSubject is not used as a grant shortcut.
for route in hermes-a hermes-b; do
  controller=$(jq -c --arg route "$route" \
    '.agents[] | select(.route == $route) | .controller' \
    "$SPK_AGENT_ALLOCATION")
  parent_task=$(printf '%s\n' "$controller" | jq -er .task)
  controller_subject=$(printf '%s\n' "$controller" | jq -er .subject)
  parent_owner=$(jq -er --arg route "$route" \
    '.agents[] | select(.route == $route) | .plannedCaps.parentOwner' \
    "$SPK_AGENT_ALLOCATION")
  for role in tool dispatch provider; do
    holder=$(jq -c --arg route "$route" --arg role "$role" \
      '.agents[] | select(.route == $route) | .[$role]' \
      "$SPK_AGENT_ALLOCATION")
    holder_subject=$(printf '%s\n' "$holder" | jq -er .subject)
    case "$role" in
      tool) child_name=parentToolWitness; offset=1 ;;
      dispatch) child_name=parentDispatchWitness; offset=2 ;;
      provider) child_name=parentProviderWitness; offset=3 ;;
    esac
    child=$(jq -er --arg route "$route" --arg child "$child_name" \
      '.agents[] | select(.route == $route) | .plannedCaps[$child]' \
      "$SPK_AGENT_ALLOCATION")
    label="$route-parent-$role"
    nonce=$((60000 + parent_task * 10 + offset * 4))
    jq -n --arg s "$controller_subject" --arg t "$parent_task" \
      --arg c "$parent_owner" --arg n "$nonce" '
      {subject:$s,nonce:$n,purpose:{type:"query",kind:"object",
        target:$t,view:"resource"},
       grants:[{kind:"object",target:$t,capability:$c}]}' \
      >"$EVIDENCE/agents/verified/$label-owner-intent.json"
    "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
      --intent "$EVIDENCE/agents/verified/$label-owner-intent.json" \
      --key "$EVIDENCE/agents/$route/controller.key" --view resource \
      --dir "$EVIDENCE/agents/verified/$label-owner" \
      >"$EVIDENCE/agents/verified/$label-owner.stdout"
    parent_root=$(jq -er '.cell.root' \
      "$EVIDENCE/agents/verified/$label-owner/view.json")
    authority=$(jq -er '.signing[0].authorityRoot' \
      "$EVIDENCE/agents/verified/$label-owner/challenge.json")
    jq -n --arg s "$controller_subject" --arg t "$parent_task" \
      --arg p "$parent_owner" --arg child "$child" \
      --arg holder "$holder_subject" --arg root "$parent_root" \
      --arg authority "$authority" --arg semantics "$SEMANTICS" \
      --arg n "$((nonce + 1))" --arg commandNonce "$((nonce + 2))" '
      {subject:$s,nonce:$n,purpose:{type:"prepare",draft:{
        type:"delegate-source",command:{kind:"object",domain:"8501",
          semantics:$semantics,subject:$s,nonce:$commandNonce,
          expectedTargetRoot:$root,parentId:$p,target:$t,
          expectedPreRoot:$authority,
          child:{id:$child,root:$p,parent:$p,issuer:"5",
            holder:{type:"subject",subject:$holder},targets:[$t],
            verbs:["observe","mutate"],maxCost:"50000",
            notBefore:"10",notAfter:"10000",issuerEpoch:"2",
            policyId:$t,policyEpoch:"0",ancestors:[$p],channels:[]}}}},
       grants:[{kind:"object",target:$t,capability:$p}]}' \
      >"$EVIDENCE/agents/verified/$label-delegation-intent.json"
    "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
      --intent "$EVIDENCE/agents/verified/$label-delegation-intent.json" \
      --key "$EVIDENCE/agents/$route/controller.key" \
      --dir "$EVIDENCE/agents/verified/$label-delegation-attempt" \
      >"$EVIDENCE/agents/verified/$label-delegation.stdout"
    confirmed "$EVIDENCE/agents/verified/$label-delegation-attempt/outcome.json"
    jq -n --arg s "$holder_subject" --arg t "$parent_task" \
      --arg c "$child" --arg n "$((nonce + 3))" '
      {subject:$s,nonce:$n,purpose:{type:"query",kind:"object",
        target:$t,view:"resource"},
       grants:[{kind:"object",target:$t,capability:$c}]}' \
      >"$EVIDENCE/agents/verified/$label-holder-intent.json"
    "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
      --intent "$EVIDENCE/agents/verified/$label-holder-intent.json" \
      --key "$EVIDENCE/agents/$route/$role.key" --view resource \
      --dir "$EVIDENCE/agents/verified/$label-holder" \
      >"$EVIDENCE/agents/verified/$label-holder.stdout"
    test "$(jq -er '.cell.root' \
      "$EVIDENCE/agents/verified/$label-holder/view.json")" = "$parent_root"
    jq -cn --arg route "$route" --arg role "$role" \
      --arg task "$parent_task" --arg holder "$holder_subject" \
      --arg capability "$child" --arg root "$parent_root" \
      --slurpfile receipt \
        "$EVIDENCE/agents/verified/$label-delegation-attempt/outcome.json" '
      {route:$route,role:$role,parentTask:$task,holder:$holder,
       capability:$capability,parentRoot:$root,
       receipt:($receipt[0] | {acceptedCount,transactionId,eventId,worldRoot})}' \
      >>"$EVIDENCE/agents/verified/parent-delegations.jsonl"
  done
done
jq -n --slurpfile receipt "$EVIDENCE/birth-attempt/outcome.json" \
  --slurpfile allocation "$SPK_AGENT_ALLOCATION" \
  --slurpfile born "$EVIDENCE/agents/verified/born-views.jsonl" \
  --slurpfile delegated "$EVIDENCE/agents/verified/parent-delegations.jsonl" '
  {type:"mini-spk-agent-genesis-birth-evidence-v1",
   birthReceipt:($receipt[0] | {acceptedCount,transactionId,eventId,worldRoot}),
   resources:[$allocation[0].agents[] as $agent |
     {route:$agent.route,controller:$agent.controller.task,
      tool:$agent.tool.task,dispatch:$agent.dispatch.task,
      provider:$agent.provider.task}],
   bornViews:$born,parentDelegations:$delegated}' \
  >"$EVIDENCE/agents/verified/birth-evidence.json"
EOF

awk -v preboot="$STAGE/preboot" -v prebirth="$STAGE/prebirth" \
  -v postbirth="$STAGE/postbirth" '
  /^"\$MINI" bootstrap --host / {
    while ((getline line < preboot) > 0) print line
    close(preboot); boot++
  }
  /cat >"\$EVIDENCE\/birth-intent.json" <<EOF/ { seen_birth=1 }
  seen_birth && /^"\$MINI" submit --host / && !birth_inserted {
    while ((getline line < prebirth) > 0) print line
    close(prebirth); birth_inserted++
  }
  /^confirmed "\$EVIDENCE\/birth-attempt\/outcome.json"/ {
    print
    while ((getline line < postbirth) > 0) print line
    close(postbirth); post++
    next
  }
  { print }
  END { if (boot != 1 || birth_inserted != 1 || post != 1) exit 2 }
' "$SOURCE" >"$OUTPUT"
chmod 700 "$OUTPUT"
sh -n "$OUTPUT"
