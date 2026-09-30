#!/bin/sh
# Propose A/B event22 tickets from retained app/session evidence. The current
# Mini op56 plan and op54 receiver, not this proposal, establish authority.
set -eu
umask 077

fail() { echo "agent ticket: $*" >&2; exit 2; }
absolute() { case "$1" in /*) ;; *) fail "absolute path required" ;; esac; }
chain() {
  node=$1
  while :; do
    [ -d "$node" ] && [ ! -L "$node" ] || fail "protected directory absent"
    meta=$(stat -c '%u:%a' "$node")
    owner=${meta%%:*}; mode=${meta#*:}
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory owner"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor"
    [ "$node" = / ] && break
    node=${node%/*}; [ -n "$node" ] || node=/
  done
}
private() {
  absolute "$1"; chain "${1%/*}"
  [ -f "$1" ] && [ ! -L "$1" ] || fail "private file unavailable: $1"
  meta=$(stat -c '%u:%a:%h:%s' "$1")
  case "$meta" in "$(id -u):600:1:"*) ;; *) fail "private file custody drift: $1" ;; esac
  size=${meta##*:}; [ "$size" -gt 0 ] && [ "$size" -le "${2:-65536}" ] ||
    fail "private file size refused: $1"
}
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
pin_binary() {
  absolute "$1"; chain "${1%/*}"
  [ -f "$1" ] && [ -x "$1" ] && [ ! -L "$1" ] || fail "executable unavailable"
  printf '%s' "$2" | grep -Eq '^[0-9a-f]{64}$' || fail "bad executable digest"
  [ "$(sha "$1")" = "$2" ] || fail "executable pin differs"
}
allocation() {
  absolute "$1"; chain "${1%/*}"
  [ -f "$1" ] && [ ! -L "$1" ] || fail "allocation absent"
  [ "$(sha "$1")" = ce11093ce0e3e0500ece3962d2f4cf600bdf1b9e326255d7abd04741a0abd222 ] ||
    fail "fixed A/B allocation changed"
}
load_stage() {
  DIR=$1; absolute "$DIR"; chain "$DIR"
  [ "$(stat -c '%u:%a' "$DIR")" = "$(id -u):700" ] || fail "stage custody drift"
  private "$DIR/stage.json" 4096
  MINI=$(jq -er .mini "$DIR/stage.json")
  HOST=$(jq -er .host "$DIR/stage.json")
  CONFIG=$(jq -er .config "$DIR/stage.json")
  SOCKET=$(jq -er .socket "$DIR/stage.json")
  pin_binary "$MINI" "$(jq -er .miniSha256 "$DIR/stage.json")"
  pin_binary "$HOST" "$(jq -er .hostSha256 "$DIR/stage.json")"
  private "$CONFIG"; private "$DIR/request.json"; private "$DIR/request.bin" 262144
  private "$DIR/request-inspected.json" 1048576
  private "$DIR/preview-plan.bin" 12102759
  private "$DIR/preview-plan.json" 1048576
  private "$DIR/preview-native/plan.bin" 12102759
  private "$DIR/preview-native/plan-pin.json" 4096
  cmp -s "$DIR/preview-plan.bin" "$DIR/preview-native/plan.bin" ||
    fail "retained typed preview plan changed"
  private "$DIR/selected-role.json" 65536
  SCOPE=$(jq -er .scope "$DIR/stage.json")
  POLICY=$(jq -er .policy "$DIR/stage.json")
  ALLOCATION=$(jq -er .allocation "$DIR/stage.json")
  APP_OUTCOME=$(jq -er .appBirthOutcome "$DIR/stage.json")
  SESSION_OUTCOME=$(jq -er .sessionBirthOutcome "$DIR/stage.json")
  QUALIFICATION=$(jq -er .launchQualification "$DIR/stage.json")
  PACKAGE_ATTEMPT=$(jq -er .signedPackageAttempt "$DIR/stage.json")
  private "$SCOPE"; private "$POLICY"; allocation "$ALLOCATION"
  private "$APP_OUTCOME"; private "$SESSION_OUTCOME"; private "$QUALIFICATION"
  private "$PACKAGE_ATTEMPT/descriptor.bin" 12102759
  private "$PACKAGE_ATTEMPT/schema.bin" 12102759
  private "$PACKAGE_ATTEMPT/descriptor-inspection.json" 1048576
  private "$PACKAGE_ATTEMPT/schema-inspection.json" 1048576
  jq -e --arg config "$(sha "$CONFIG")" --arg request "$(sha "$DIR/request.bin")" \
    --arg requestJson "$(sha "$DIR/request.json")" \
    --arg requestInspection "$(sha "$DIR/request-inspected.json")" \
    --arg plan "$(sha "$DIR/preview-plan.bin")" \
    --arg planInspection "$(sha "$DIR/preview-plan.json")" \
    --arg previewPin "$(sha "$DIR/preview-native/plan-pin.json")" \
    --arg selectedRole "$(sha "$DIR/selected-role.json")" \
    --arg scope "$(sha "$SCOPE")" --arg policy "$(sha "$POLICY")" \
    --arg allocation "$(sha "$ALLOCATION")" \
    --arg app "$(sha "$APP_OUTCOME")" --arg session "$(sha "$SESSION_OUTCOME")" \
    --arg qualification "$(sha "$QUALIFICATION")" \
    --arg package "$(sha "$PACKAGE_ATTEMPT/descriptor.bin")" \
    --arg schema "$(sha "$PACKAGE_ATTEMPT/schema.bin")" \
    --arg packageInspection "$(sha "$PACKAGE_ATTEMPT/descriptor-inspection.json")" \
    --arg schemaInspection "$(sha "$PACKAGE_ATTEMPT/schema-inspection.json")" \
    '.type == "mini-spk-agent-ticket-stage-v1" and
     .configSha256 == $config and .requestSha256 == $request and
     .requestJsonSha256 == $requestJson and
     .requestInspectionSha256 == $requestInspection and
     .previewPlanSha256 == $plan and
     .previewInspectionSha256 == $planInspection and
     .previewPinSha256 == $previewPin and
     .selectedRoleSha256 == $selectedRole and
     .scopeSha256 == $scope and .policySha256 == $policy and
     .allocationSha256 == $allocation and .appBirthOutcomeSha256 == $app and
     .sessionBirthOutcomeSha256 == $session and
     .launchQualificationSha256 == $qualification and
     .packageCanonicalSha256 == $package and .schemaCanonicalSha256 == $schema and
     .packageInspectionSha256 == $packageInspection and
     .schemaInspectionSha256 == $schemaInspection' \
    "$DIR/stage.json" >/dev/null || fail "staged source request changed"
}

if [ "$#" -eq 12 ] && [ "$1" = prepare ]; then
  MINI=$2 HOST=$3 CONFIG=$4 SOCKET=$5 ALLOCATION=$6 ROUTE=$7
  SCOPE=$8 POLICY=$9 DIR=${10} MINI_SHA=${11} HOST_SHA=${12}
  pin_binary "$MINI" "$MINI_SHA"; pin_binary "$HOST" "$HOST_SHA"
  private "$CONFIG"; private "$SCOPE"; private "$POLICY"
  allocation "$ALLOCATION"
  absolute "$SOCKET"; chain "${SOCKET%/*}"
  [ -S "$SOCKET" ] && [ ! -L "$SOCKET" ] || fail "operator socket unavailable"
  absolute "$DIR"; chain "${DIR%/*}"
  [ ! -e "$DIR" ] && [ ! -L "$DIR" ] || fail "stage exists"
  case "$ROUTE" in hermes-a|hermes-b) ;; *) fail "route is not an allocated agent" ;; esac
  # SCOPE is a retained *candidate* from accepted app/session readbacks. Mini
  # replays current Store history at op56 and op54; this file is not a receipt.
  jq -e --arg route "$ROUTE" --slurpfile allocation "$ALLOCATION" '
    .type == "mini-spk-agent-ticket-scope-v1" and .route == $route and
    .app == $allocation[0].app and
    .session == ($allocation[0].agents[] | select(.route == $route) | .session) and
    .descriptor == ($allocation[0].agents[] | select(.route == $route) | .descriptor) and
    (.signedPackageAttempt | type == "string" and startswith("/")) and
    (.launchQualification | type == "string" and startswith("/")) and
    (.originGeneration | type == "string" and test("^(0|[1-9][0-9]*)$")) and
    (.appBirthOutcome | type == "string" and startswith("/")) and
    (.sessionBirthOutcome | type == "string" and startswith("/")) and
    (.appBirthReceipt | type == "object" and
      has("transactionId") and has("eventId") and
      has("acceptedCount") and has("worldRoot")) and
    (.sessionBirthReceipt | type == "object" and
      has("transactionId") and has("eventId") and
      has("acceptedCount") and has("worldRoot"))
    ' "$SCOPE" >/dev/null || fail "candidate scope differs from A/B allocation"
  APP_OUTCOME=$(jq -er .appBirthOutcome "$SCOPE")
  SESSION_OUTCOME=$(jq -er .sessionBirthOutcome "$SCOPE")
  PACKAGE_ATTEMPT=$(jq -er .signedPackageAttempt "$SCOPE")
  QUALIFICATION=$(jq -er .launchQualification "$SCOPE")
  private "$APP_OUTCOME"; private "$SESSION_OUTCOME"
  private "$QUALIFICATION"
  private "$PACKAGE_ATTEMPT/descriptor.bin" 12102759
  private "$PACKAGE_ATTEMPT/schema.bin" 12102759
  private "$PACKAGE_ATTEMPT/descriptor-inspection.json" 1048576
  private "$PACKAGE_ATTEMPT/schema-inspection.json" 1048576
  PACKAGE_SOURCE_SHA=$(jq -er .canonical "$PACKAGE_ATTEMPT/descriptor-inspection.json" |
    xxd -r -p | sha256sum | cut -d ' ' -f 1)
  [ "$PACKAGE_SOURCE_SHA" = "$(sha "$PACKAGE_ATTEMPT/descriptor.bin")" ] ||
    fail "signed package source bytes differ"
  SCHEMA_SOURCE_SHA=$(jq -er .canonical "$PACKAGE_ATTEMPT/schema-inspection.json" |
    xxd -r -p | sha256sum | cut -d ' ' -f 1)
  [ "$SCHEMA_SOURCE_SHA" = "$(sha "$PACKAGE_ATTEMPT/schema.bin")" ] ||
    fail "signed schema source bytes differ"
  jq -e --slurpfile package "$PACKAGE_ATTEMPT/descriptor-inspection.json" \
    --slurpfile schema "$PACKAGE_ATTEMPT/schema-inspection.json" '
    .protocol == "mini-spk-launch-qualified-v2" and
    .packageRoot == $package[0].root and
    .rawSha256 == $package[0].rawSha256 and
    $package[0].type == "application-spk-package-identity-v1" and
    $schema[0].type == "minidregg-application-permission-schema-v1" and
    ([ $package[0].interfaces[] | select(.kind == "api") ] | length) == 1 and
    ([ $package[0].interfaces[] | select(.kind == "api") ][0].schemaRoot ==
      $schema[0].root)
    ' "$QUALIFICATION" >/dev/null || fail "signed API interface projection differs"
  jq -e --slurpfile scope "$SCOPE" '
    .type == "confirmed" and
    (.confirmation == "installed" or .confirmation == "replayed") and
    {transactionId,eventId,acceptedCount,worldRoot} ==
      $scope[0].appBirthReceipt' "$APP_OUTCOME" >/dev/null ||
    fail "accepted app birth receipt absent or changed"
  jq -e --slurpfile scope "$SCOPE" '
    .type == "confirmed" and
    (.confirmation == "installed" or .confirmation == "replayed") and
    {transactionId,eventId,acceptedCount,worldRoot} ==
      $scope[0].sessionBirthReceipt' "$SESSION_OUTCOME" >/dev/null ||
    fail "accepted session birth receipt absent or changed"
  jq -e '
    .type == "mini-spk-agent-ticket-policy-v1" and
    ([.issuer,.appDelegateCapability,.payer,.issueNonce] |
      all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$"))) and
    (.ceilingRoleId | type == "string" and test("^(0|[1-9][0-9]{0,2})$")) and
    (.expectedRolePermissions | type == "array" and length > 0) and
    (.funding | type == "array" and length <= 16) and
    (.sourceCapabilities | type == "array" and length > 0 and length <= 16 and
      all(.[]; type == "string" and test("^[1-9][0-9]*$"))) and
    ([.tool.task,.tool.capability,.tool.observeCapability,
      .parent.task,.parent.capability,.parent.observeCapability] |
      all(.[]; type == "string" and test("^[1-9][0-9]*$")))
    ' "$POLICY" >/dev/null || fail "operator policy refused"
  ROLE_ID=$(jq -er .ceilingRoleId "$POLICY")
  jq -e --argjson role "$ROLE_ID" --slurpfile policy "$POLICY" '
    (.roles | type == "array" and length > $role) and
    .roles[$role].obsolete == false and
    .roles[$role].permissions == $policy[0].expectedRolePermissions
    ' "$PACKAGE_ATTEMPT/schema-inspection.json" >/dev/null ||
    fail "selected signed role missing, obsolete, or permissions changed"
  mkdir -m 700 "$DIR"
  jq -c --argjson role "$ROLE_ID" \
    '{roleId:($role | tostring),role:.roles[$role]}' \
    "$PACKAGE_ATTEMPT/schema-inspection.json" >"$DIR/selected-role.json"
  jq -n --arg route "$ROUTE" --slurpfile allocation "$ALLOCATION" \
    --slurpfile scope "$SCOPE" --slurpfile policy "$POLICY" \
    --slurpfile package "$PACKAGE_ATTEMPT/descriptor-inspection.json" \
    --slurpfile schema "$PACKAGE_ATTEMPT/schema-inspection.json" '
    ($allocation[0].agents[] | select(.route == $route)) as $a |
    $scope[0] as $s | $policy[0] as $p |
    $package[0] as $pkg | $schema[0] as $schema |
    ([ $pkg.interfaces[] | select(.kind == "api") ][0]) as $api |
    {spec:{ticket:{resource:$a.ticket,
       scope:{app:$s.app,packageVersion:$pkg.signedAppVersion,
         packageRoot:$pkg.root,interfaceId:$api.id,
         interfaceVersion:$api.version,interfaceRoot:$api.root,
         schemaRoot:$schema.root,schemaVersion:$schema.version},
       participant:{session:$a.session,descriptorResource:$a.descriptor,
         kind:"api",subject:$a.controller.subject,
         origin:{type:"agent",task:$a.controller.task,
           generation:$s.originGeneration},
         sessionCapability:$a.plannedCaps.sessionOwner,
         appObserveCapability:$a.plannedCaps.appObserve,
         ticketObserveCapability:$a.plannedCaps.ticketObserve},
       ceiling:{basis:{type:"role",id:$p.ceilingRoleId},added:[],removed:[],
         roleSchemaRoot:$schema.root,roleVersion:$schema.version},
       issueNonce:$p.issueNonce},issuer:$p.issuer,
       appDelegateCapability:$p.appDelegateCapability,
       ticketOwnerCapability:$a.plannedCaps.ticketOwner,
       ticketControlCapability:$a.plannedCaps.ticketControl},
     payer:$p.payer,funding:$p.funding,
     sourceCapabilities:$p.sourceCapabilities,tool:$p.tool,parent:$p.parent}
    ' >"$DIR/request.json"
  chmod 600 "$DIR/request.json"
  "$HOST" "$CONFIG" author application-share-issue-grain-request \
    "$DIR/request.json" "$DIR/request.bin" || fail "source request refused"
  "$HOST" "$CONFIG" inspect application-share-issue-grain-request \
    "$DIR/request.bin" "$DIR/request-inspected.json" || fail "source request inspection refused"
  "$MINI" grain-share-issue-plan --host "$HOST" --config "$CONFIG" \
    --socket "$SOCKET" --request "$DIR/request.json" \
    --dir "$DIR/preview-native" >"$DIR/preview.stdout" \
    2>"$DIR/preview.stderr" || fail "typed current source plan refused"
  chmod 600 "$DIR/preview.stdout" "$DIR/preview.stderr"
  private "$DIR/preview-native/request.json" 12102759
  private "$DIR/preview-native/config.json" 65536
  private "$DIR/preview-native/request.bin" 12102759
  private "$DIR/preview-native/request-inspected.json" 1048576
  private "$DIR/preview-native/plan.frame" 12102759
  private "$DIR/preview-native/plan.bin" 12102759
  private "$DIR/preview-native/plan-inspected.json" 1048576
  private "$DIR/preview-native/plan-pin.json" 4096
  cmp -s "$DIR/request.json" "$DIR/preview-native/request.json" &&
    cmp -s "$CONFIG" "$DIR/preview-native/config.json" &&
    cmp -s "$DIR/request.bin" "$DIR/preview-native/request.bin" &&
    cmp -s "$DIR/request-inspected.json" \
      "$DIR/preview-native/request-inspected.json" ||
    fail "typed preview request differs from reviewed source bytes"
  jq -e --arg host "$HOST" --arg hostSha "$HOST_SHA" \
    --arg config "$CONFIG" --arg configSha "$(sha "$CONFIG")" \
    --arg socket "$SOCKET" --arg request "$(sha "$DIR/request.bin")" \
    --arg plan "$(sha "$DIR/preview-native/plan.bin")" '
    .format == "minidregg-grain-share-issue-plan-only-v1" and
    .host == $host and .hostSha256 == $hostSha and
    .config == $config and .configSha256 == $configSha and
    .operatorSocket == $socket and .requestSha256 == $request and
    .planSha256 == $plan' "$DIR/preview-native/plan-pin.json" >/dev/null ||
    fail "typed preview pin differs"
  cp "$DIR/preview-native/plan.bin" "$DIR/preview-plan.bin"
  cp "$DIR/preview-native/plan-inspected.json" "$DIR/preview-plan.json"
  chmod 600 "$DIR/preview-plan.bin" "$DIR/preview-plan.json"
  jq -e --arg route "$ROUTE" --slurpfile allocation "$ALLOCATION" \
    --slurpfile scope "$SCOPE" --slurpfile policy "$POLICY" \
    --slurpfile request "$DIR/request-inspected.json" '
    .type == "application-grain-share-issue-plan-v1" and
    .canonicalRequest == $request[0].canonicalRequest and
    .request.canonicalSpec == $request[0].canonicalSpec and
    .request.spec.ticket.resource ==
      ($allocation[0].agents[] | select(.route == $route) | .ticket) and
    .request.spec.ticket.participant.origin.type == "agent" and
    .request.spec.ticket.participant.origin.task ==
      ($allocation[0].agents[] | select(.route == $route) | .controller.task) and
    .request.spec.ticket.participant.origin.generation ==
      $scope[0].originGeneration and
    .request.parent == $policy[0].parent and
    .finalizedGrainBirth.parent.task ==
      .request.parent.task and
    .finalizedGrainBirth.parent.capability == .request.parent.capability and
    .finalizedGrainBirth.parent.observeCapability ==
      .request.parent.observeCapability and
    (.slots | type == "array" and length > 0) and
    .finalizedGrainBirth.tool.before.reserved != null
    ' "$DIR/preview-plan.json" >/dev/null || fail "preview differs from source request"
  jq -n --arg mini "$MINI" --arg miniSha "$MINI_SHA" \
    --arg host "$HOST" --arg hostSha "$HOST_SHA" --arg config "$CONFIG" \
    --arg configSha "$(sha "$CONFIG")" --arg socket "$SOCKET" \
    --arg request "$(sha "$DIR/request.bin")" \
    --arg requestJson "$(sha "$DIR/request.json")" \
    --arg requestInspection "$(sha "$DIR/request-inspected.json")" \
    --arg plan "$(sha "$DIR/preview-plan.bin")" \
    --arg planInspection "$(sha "$DIR/preview-plan.json")" \
    --arg previewPin "$(sha "$DIR/preview-native/plan-pin.json")" \
    --arg selectedRole "$(sha "$DIR/selected-role.json")" \
    --arg scope "$(sha "$SCOPE")" --arg policy "$(sha "$POLICY")" \
    --arg allocation "$(sha "$ALLOCATION")" \
    --arg scopePath "$SCOPE" --arg policyPath "$POLICY" \
    --arg allocationPath "$ALLOCATION" \
    --arg appOutcome "$APP_OUTCOME" --arg sessionOutcome "$SESSION_OUTCOME" \
    --arg appOutcomeSha "$(sha "$APP_OUTCOME")" \
    --arg sessionOutcomeSha "$(sha "$SESSION_OUTCOME")" \
    --arg qualification "$QUALIFICATION" \
    --arg qualificationSha "$(sha "$QUALIFICATION")" \
    --arg packageAttempt "$PACKAGE_ATTEMPT" \
    --arg packageSha "$(sha "$PACKAGE_ATTEMPT/descriptor.bin")" \
    --arg schemaSha "$(sha "$PACKAGE_ATTEMPT/schema.bin")" \
    --arg packageInspectionSha "$(sha "$PACKAGE_ATTEMPT/descriptor-inspection.json")" \
    --arg schemaInspectionSha "$(sha "$PACKAGE_ATTEMPT/schema-inspection.json")" '
    {type:"mini-spk-agent-ticket-stage-v1",mini:$mini,miniSha256:$miniSha,
     host:$host,hostSha256:$hostSha,config:$config,configSha256:$configSha,
     socket:$socket,requestSha256:$request,requestJsonSha256:$requestJson,
     requestInspectionSha256:$requestInspection,
     previewPlanSha256:$plan,previewInspectionSha256:$planInspection,
     previewPinSha256:$previewPin,
     selectedRoleSha256:$selectedRole,scopeSha256:$scope,
     policySha256:$policy,allocationSha256:$allocation,
     scope:$scopePath,policy:$policyPath,allocation:$allocationPath,
     appBirthOutcome:$appOutcome,sessionBirthOutcome:$sessionOutcome,
     appBirthOutcomeSha256:$appOutcomeSha,
     sessionBirthOutcomeSha256:$sessionOutcomeSha,
     launchQualification:$qualification,
     launchQualificationSha256:$qualificationSha,
     signedPackageAttempt:$packageAttempt,
     packageCanonicalSha256:$packageSha,schemaCanonicalSha256:$schemaSha,
     packageInspectionSha256:$packageInspectionSha,
     schemaInspectionSha256:$schemaInspectionSha}
    ' >"$DIR/stage.json"
  chmod 600 "$DIR"/*.json "$DIR"/*.bin
  echo "event22 candidate staged at $DIR; review preview before approval"
  exit 0
fi

if [ "$#" -eq 4 ] && [ "$1" = approve ]; then
  load_stage "$2"
  SIGNERS=$3 APPROVAL=$4; private "$SIGNERS"
  absolute "$APPROVAL"; chain "${APPROVAL%/*}"
  [ ! -e "$APPROVAL" ] && [ ! -L "$APPROVAL" ] || fail "approval exists"
  private "$DIR/preview-plan.json" 1048576
  private "$DIR/request-inspected.json" 1048576
  jq -e 'type == "array" and length > 0 and length <= 16 and
    all(.[]; (keys | sort) == (["keyId","keyEpoch","publicKey","keyPath"] | sort) and
      (.publicKey | type == "string" and test("^[0-9a-f]{64}$")) and
      (.keyPath | type == "string" and startswith("/"))) and
    ([.[] | [.keyId,.keyEpoch] | join(":")] | unique | length) == length' \
    "$SIGNERS" >/dev/null || fail "protected signer map refused"
  jq -c '.slots' "$DIR/preview-plan.json" >"$DIR/slots.json"
  chmod 600 "$DIR/slots.json"
  count=$(jq 'length' "$DIR/slots.json")
  : >"$DIR/signers.jsonl"
  index=0
  while [ "$index" -lt "$count" ]; do
    slot=$(jq -c --argjson i "$index" '.[$i]' "$DIR/slots.json")
    key_id=$(printf '%s' "$slot" | jq -er .signing.keyId)
    key_epoch=$(printf '%s' "$slot" | jq -er .signing.keyEpoch)
    signer=$(jq -cer --arg id "$key_id" --arg epoch "$key_epoch" \
      '[.[] | select(.keyId == $id and .keyEpoch == $epoch)] |
       if length == 1 then .[0] else error("missing signer") end' "$SIGNERS") ||
      fail "source signer absent"
    key_path=$(printf '%s' "$signer" | jq -er .keyPath)
    private "$key_path" 32
    [ "$(stat -c %s "$key_path")" -eq 32 ] || fail "signer seed is not raw32"
    header_sha=$(printf '%s' "$slot" | jq -er .header |
      xxd -r -p | sha256sum | cut -d ' ' -f 1)
    printf '%s' "$slot" | jq -c --argjson signer "$signer" --arg header "$header_sha" '
      {role,index,keyId:.signing.keyId,keyEpoch:.signing.keyEpoch,
       publicKey:$signer.publicKey,headerSha256:$header,keyPath:$signer.keyPath}
      ' >>"$DIR/signers.jsonl"
    index=$((index + 1))
  done
  jq -s --arg request "$(sha "$DIR/request.bin")" \
    --slurpfile inspected "$DIR/request-inspected.json" '
    $inspected[0] as $r |
    {type:"minidregg-grain-share-issue-approval-v1",
     requestSha256:$request,canonicalSpec:$r.canonicalSpec,
     issuer:$r.spec.issuer,participantSubject:$r.spec.ticket.participant.subject,
     appDelegateCapability:$r.spec.appDelegateCapability,
     ticketResource:$r.spec.ticket.resource,payer:$r.payer,
     funding:$r.funding,sourceCapabilities:$r.sourceCapabilities,
     tool:$r.tool,parent:$r.parent,signers:.}
    ' "$DIR/signers.jsonl" >"$APPROVAL"
  chmod 600 "$APPROVAL" "$DIR/signers.jsonl"
  echo "event22 exact-slot approval staged at $APPROVAL"
  exit 0
fi

if [ "$#" -eq 3 ] && [ "$1" = seal ]; then
  load_stage "$2"; APPROVAL=$3; private "$APPROVAL"
  [ ! -e "$DIR/issue" ] && [ ! -L "$DIR/issue" ] || fail "issue already prepared"
  "$MINI" grain-share-issue-prepare --host "$HOST" --config "$CONFIG" \
    --socket "$SOCKET" --request "$DIR/request.json" \
    --approval "$APPROVAL" --dir "$DIR/issue" ||
    fail "op56/57 refused; do not submit"
  cmp -s "$DIR/request.bin" "$DIR/issue/request.bin" ||
    fail "prepared request differs from reviewed source bytes"
  cmp -s "$DIR/preview-plan.bin" "$DIR/issue/plan.bin" ||
    fail "current Mini plan changed since review; do not submit"
  echo "event22 signed ingress prepared at $DIR/issue; no submit yet"
  exit 0
fi

if [ "$#" -eq 2 ] && [ "$1" = finish ]; then
  load_stage "$2"
  ISSUE=$DIR/issue; chain "$ISSUE"
  private "$ISSUE/ingress.bin" 12102759
  if [ ! -e "$ISSUE/submit-marker.json" ]; then
    "$MINI" grain-share-issue-submit --socket "$SOCKET" --attempt "$ISSUE" ||
      echo "event22 submit uncertain; exact lookup follows" >&2
  fi
  [ -e "$ISSUE/submit-marker.json" ] || fail "no durable submit marker"
  "$MINI" grain-share-issue-lookup --socket "$SOCKET" --attempt "$ISSUE" ||
    fail "exact event22 lookup refused; never resubmit"
  private "$ISSUE/receipt-anchor.json" 4096
  echo "event22 accepted with exact retained receipt at $ISSUE/receipt-anchor.json"
  exit 0
fi

echo "usage: $0 prepare MINI HOST CONFIG SOCKET ALLOCATION hermes-a|hermes-b SCOPE.json POLICY.json NEW_DIR MINI_SHA HOST_SHA" >&2
echo "       $0 approve STAGED_DIR SIGNER_MAP.json NEW_APPROVAL.json" >&2
echo "       $0 seal STAGED_DIR APPROVAL.json" >&2
echo "       $0 finish STAGED_DIR" >&2
exit 2
