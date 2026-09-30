#!/bin/sh
# Stage one event27 candidate from a retained event22 grain share issue. Mini
# alone verifies current ticket history and admits the signed grant. No caller
# field or historical lookup is a dispatch permit.
set -eu
umask 077

fail() { echo "lifetime grant: $*" >&2; exit 2; }
absolute() {
  case "$1" in /*) ;; *) fail "absolute path required" ;; esac
  case "$1" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/') fail "noncanonical path" ;; esac
}
protected_chain() {
  chain=$1
  while :; do
    [ -d "$chain" ] && [ ! -L "$chain" ] || fail "protected directory absent or linked: $chain"
    meta=$(stat -c '%u:%a' "$chain")
    owner=${meta%%:*}; mode=${meta#*:}
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory owner: $chain"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor: $chain"
    [ "$chain" = / ] && break
    chain=${chain%/*}; [ -n "$chain" ] || chain=/
  done
}
private_file() {
  absolute "$1"; protected_chain "${1%/*}"
  [ -f "$1" ] && [ ! -L "$1" ] || fail "private file absent or linked: $1"
  meta=$(stat -c '%u:%a:%h:%s' "$1")
  case "$meta" in "$(id -u):600:1:"*) ;; *) fail "private file custody drift: $1" ;; esac
  size=${meta##*:}
  [ "$size" -gt 0 ] && [ "$size" -le "${2:-16777216}" ] || fail "private file size refused: $1"
}
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
fixed_allocation() {
  absolute "$1"; protected_chain "${1%/*}"
  [ -f "$1" ] && [ ! -L "$1" ] || fail "fixed allocation unavailable"
  meta=$(stat -c '%u:%a:%h:%s' "$1")
  owner=${meta%%:*}; rest=${meta#*:}; mode=${rest%%:*}
  rest=${rest#*:}; links=${rest%%:*}
  { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } ||
    fail "fixed allocation owner drift"
  [ $((0$mode & 022)) -eq 0 ] || fail "fixed allocation is writable by another principal"
  [ "$links" = 1 ] || fail "fixed allocation has extra links"
  [ "$(sha "$1")" = ce11093ce0e3e0500ece3962d2f4cf600bdf1b9e326255d7abd04741a0abd222 ] ||
    fail "fixed A/B allocation differs from reviewed source"
}
executable_pin() {
  absolute "$1"; protected_chain "${1%/*}"
  [ -f "$1" ] && [ -x "$1" ] && [ ! -L "$1" ] || fail "qualified executable unavailable"
  printf '%s' "$2" | grep -Eq '^[0-9a-f]{64}$' || fail "executable SHA invalid"
  [ "$(sha "$1")" = "$2" ] || fail "qualified executable differs"
}
read_staging() {
  DIR=$1; absolute "$DIR"; protected_chain "$DIR"
  [ "$(stat -c '%u:%a' "$DIR")" = "$(id -u):700" ] || fail "stage directory custody drift"
  private_file "$DIR/staging.json" 4096
  private_file "$DIR/request.json" 65536
  MINI=$(jq -er .mini "$DIR/staging.json")
  MINI_SHA=$(jq -er .miniSha256 "$DIR/staging.json")
  executable_pin "$MINI" "$MINI_SHA"
  HOST=$(jq -er .host "$DIR/staging.json")
  HOST_SHA=$(jq -er .hostSha256 "$DIR/staging.json")
  executable_pin "$HOST" "$HOST_SHA"
  ISSUE=$(jq -er .event22Attempt "$DIR/staging.json")
  private_file "$ISSUE/ingress.bin" 12102759
  private_file "$ISSUE/plan.bin" 12102759
  jq -e --arg issueSha "$(sha "$ISSUE/ingress.bin")" \
    --arg planSha "$(sha "$ISSUE/plan.bin")" \
    '.event22IngressSha256 == $issueSha and .event22PlanSha256 == $planSha' \
    "$DIR/staging.json" >/dev/null || fail "original event22 attempt changed"
  ATTEMPT=$DIR/grant-attempt
  protected_chain "$ATTEMPT"
  [ "$(stat -c '%u:%a' "$ATTEMPT")" = "$(id -u):700" ] || fail "grant attempt custody drift"
  private_file "$ATTEMPT/pin.json" 4096
  private_file "$ATTEMPT/request.bin" 12102759
  jq -e --arg sha "$(sha "$DIR/request.json")" \
    '.type == "mini-spk-lifetime-grant-stage-v1" and .requestSha256 == $sha' \
    "$DIR/staging.json" >/dev/null || fail "staged source request differs"
}

if [ "$#" -eq 12 ] && [ "$1" = prepare ]; then
  MINI=$2 HOST=$3 CONFIG=$4 SOCKET=$5 ALLOCATION=$6 ISSUE=$7
  ROUTE=$8 POLICY=$9 DIR=${10} MINI_SHA=${11} HOST_SHA=${12}
  for path in "$CONFIG" "$SOCKET" "$ALLOCATION" "$ISSUE" "$POLICY" "$DIR"; do absolute "$path"; done
  executable_pin "$MINI" "$MINI_SHA"; executable_pin "$HOST" "$HOST_SHA"
  private_file "$CONFIG" 65536; private_file "$POLICY" 65536
  fixed_allocation "$ALLOCATION"
  protected_chain "$ISSUE"
  [ "$(stat -c '%u:%a' "$ISSUE")" = "$(id -u):700" ] || fail "event22 attempt custody drift"
  protected_chain "${SOCKET%/*}"
  [ -S "$SOCKET" ] && [ ! -L "$SOCKET" ] || fail "private operator socket unavailable"
  [ ! -e "$DIR" ] && [ ! -L "$DIR" ] || fail "stage already exists"
  protected_chain "${DIR%/*}"
  for name in pin.json request.json request.bin plan.bin ingress.bin \
      submit-marker.json receipt-anchor.json; do private_file "$ISSUE/$name"; done
  ISSUE_HOST=$(jq -er .host "$ISSUE/pin.json")
  ISSUE_HOST_SHA=$(jq -er .hostSha256 "$ISSUE/pin.json")
  executable_pin "$ISSUE_HOST" "$ISSUE_HOST_SHA"
  jq -e --arg configSha "$(sha "$CONFIG")" \
    --arg planSha "$(sha "$ISSUE/plan.bin")" \
    --arg ingressSha "$(sha "$ISSUE/ingress.bin")" \
    '.format == "minidregg-application-grain-share-issue-custody-v1" and
     .configSha256 == $configSha and .planSha256 == $planSha and
     .ingressSha256 == $ingressSha' "$ISSUE/pin.json" >/dev/null ||
    fail "retained event22 custody differs"
  jq -e --arg ingressSha "$(sha "$ISSUE/ingress.bin")" \
    '.type == "minidregg-grain-share-issue-submit-v1" and
     .ingressSha256 == $ingressSha' "$ISSUE/submit-marker.json" >/dev/null ||
    fail "event22 was not submitted once"
  case "$ROUTE" in hermes-a|hermes-b) ;; *) fail "unknown agent route" ;; esac
  jq -e '
    .protocol == "mini-spk-integrated-allocation-v1" and
    ([.agents[].route] == ["hermes-a","hermes-b"]) and
    [.agents[] | .session,.descriptor,.ticket,.persistentGrant] ==
      ["8420","8421","8520","8530","8422","8423","8521","8531"]
    ' "$ALLOCATION" >/dev/null || fail "fixed agent allocation differs"
  jq -e '
    (keys | sort) == (["type","nonce","payer","funding","sourceCapabilities"] | sort) and
    .type == "mini-spk-agent-lifetime-grant-policy-v1" and
    (.nonce | type == "string" and test("^[1-9][0-9]*$")) and
    (.payer | type == "string" and test("^[1-9][0-9]*$")) and
    (.funding | type == "array" and length <= 16 and all(.[];
      (keys | sort) == (["source","destination","asset","amount"] | sort) and
      ([.source,.destination,.asset,.amount] |
        all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$"))))) and
    (.sourceCapabilities | type == "array" and length >= 1 and length <= 16 and
      all(.[]; type == "string" and test("^[1-9][0-9]*$")))
    ' "$POLICY" >/dev/null || fail "grant funding/capability policy refused"
  mkdir -m 700 "$DIR"
  # op55 only looks up the exact retained event22 ingress. It does not issue it.
  "$MINI" grain-share-issue-lookup --socket "$SOCKET" --attempt "$ISSUE" \
    >"$DIR/event22-lookup.json" 2>"$DIR/event22-lookup.stderr" ||
    fail "event22 lookup refused; no event27 plan attempted"
  jq -e --slurpfile anchor "$ISSUE/receipt-anchor.json" '
    .type == "confirmed" and .confirmation == "replayed" and
    {transactionId,eventId,acceptedCount,worldRoot} == $anchor[0].receipt
    ' "$DIR/event22-lookup.json" >/dev/null || fail "event22 receipt differs"
  COUNT=$(jq -er .receipt.acceptedCount "$ISSUE/receipt-anchor.json")
  printf '%s' "$COUNT" | grep -Eq '^[1-9][0-9]{0,14}$' ||
    fail "event22 index exceeds bounded operator selector"
  ISSUE_INDEX=$((COUNT - 1))
  "$HOST" "$CONFIG" inspect application-share-issue-grain-plan \
    "$ISSUE/plan.bin" "$DIR/event22-plan.json" \
    >"$DIR/inspect.stdout" 2>"$DIR/inspect.stderr" ||
    fail "source event22 plan inspection refused"
  jq -er .canonicalPlanHex "$DIR/event22-plan.json" |
    xxd -r -p >"$DIR/event22-plan-source.bin"
  cmp -s "$ISSUE/plan.bin" "$DIR/event22-plan-source.bin" ||
    fail "source event22 plan bytes differ"
  jq -er .canonicalRequest "$DIR/event22-plan.json" |
    xxd -r -p >"$DIR/event22-request-source.bin"
  cmp -s "$ISSUE/request.bin" "$DIR/event22-request-source.bin" ||
    fail "source event22 request bytes differ"
  "$HOST" "$CONFIG" author application-share-issue-grain-request \
    "$ISSUE/request.json" "$DIR/event22-request-reauthored.bin" ||
    fail "original event22 request cannot be source-reauthored"
  cmp -s "$ISSUE/request.bin" "$DIR/event22-request-reauthored.bin" ||
    fail "event22 structured ceiling differs from retained request"
  jq -e --arg route "$ROUTE" --argjson issueIndex "$ISSUE_INDEX" \
      --slurpfile allocation "$ALLOCATION" '
    .type == "application-grain-share-issue-plan-v1" and
    .request.spec.ticket.resource ==
      ($allocation[0].agents[] | select(.route == $route) | .ticket) and
    .request.spec.ticket.scope.app == "8401" and
    .request.spec.ticket.participant.session ==
      ($allocation[0].agents[] | select(.route == $route) | .session) and
    .request.spec.ticket.participant.subject ==
      ($allocation[0].agents[] | select(.route == $route) | .controller.subject) and
    .request.spec.ticket.participant.origin.type == "agent" and
    .request.spec.ticket.participant.origin.task ==
      ($allocation[0].agents[] | select(.route == $route) | .controller.task) and
    (.request.spec.ticket.participant.origin.generation |
      type == "string" and test("^(0|[1-9][0-9]*)$")) and
    (.request.spec.ticket.ticketDigest |
      type == "string" and test("^(0|[1-9][0-9]*)$")) and
    (.request.spec.issuer | type == "string" and test("^[1-9][0-9]*$")) and
    (.request.spec.appDelegateCapability |
      type == "string" and test("^[1-9][0-9]*$")) and
    $issueIndex >= 0
    ' "$DIR/event22-plan.json" >/dev/null || fail "event22 source ticket differs from fixed agent"
  jq -n --arg route "$ROUTE" --arg issueIndex "$ISSUE_INDEX" \
    --slurpfile allocation "$ALLOCATION" --slurpfile plan "$DIR/event22-plan.json" \
    --slurpfile issue "$ISSUE/receipt-anchor.json" \
    --slurpfile original "$ISSUE/request.json" --slurpfile policy "$POLICY" '
    ($allocation[0].agents[] | select(.route == $route)) as $a |
    $plan[0].request.spec as $spec |
    {grant:{source:{resource:$a.persistentGrant,issueIndex:$issueIndex,
       issueReceipt:$issue[0].receipt,ticketResource:$a.ticket,
       ticketDigest:$spec.ticket.ticketDigest},
      participant:{app:"8401",session:$a.session,subject:$a.controller.subject,
       parentTask:$a.controller.task,
       originalGeneration:$spec.ticket.participant.origin.generation,
       grantObserveCapability:$a.plannedCaps.grantObserve},
      approval:{issuer:$spec.issuer,delegateCapability:$spec.appDelegateCapability,
       ceiling:$original[0].spec.ticket.ceiling,nonce:$policy[0].nonce}},
     grantOwnerCapability:$a.plannedCaps.grantOwner,
     grantControlCapability:$a.plannedCaps.grantControl,
     payer:$policy[0].payer,funding:$policy[0].funding,
     sourceCapabilities:$policy[0].sourceCapabilities}
    ' >"$DIR/request.json"
  chmod 600 "$DIR"/*.json "$DIR"/*.bin "$DIR"/*.stdout "$DIR"/*.stderr
  "$MINI" agent-lifetime-grant-plan --host "$HOST" --config "$CONFIG" \
    --operator-socket "$SOCKET" --request "$DIR/request.json" \
    --dir "$DIR/grant-attempt" >"$DIR/plan.stdout" 2>"$DIR/plan.stderr" ||
    fail "source op74 grant plan refused; no event27 submitted"
  jq -n --arg mini "$MINI" --arg miniSha "$MINI_SHA" \
    --arg host "$HOST" --arg hostSha "$HOST_SHA" --arg issue "$ISSUE" \
    --arg issueSha "$(sha "$ISSUE/ingress.bin")" \
    --arg issuePlanSha "$(sha "$ISSUE/plan.bin")" \
    --arg allocationSha "$(sha "$ALLOCATION")" \
    --arg policySha "$(sha "$POLICY")" \
    --arg requestSha "$(sha "$DIR/request.json")" \
    '{type:"mini-spk-lifetime-grant-stage-v1",mini:$mini,miniSha256:$miniSha,
      host:$host,hostSha256:$hostSha,event22Attempt:$issue,
      event22IngressSha256:$issueSha,event22PlanSha256:$issuePlanSha,
      allocationSha256:$allocationSha,policySha256:$policySha,
      requestSha256:$requestSha}' \
    >"$DIR/staging.json"
  executable_pin "$MINI" "$MINI_SHA"; executable_pin "$HOST" "$HOST_SHA"
  chmod 600 "$DIR/staging.json" "$DIR/plan.stdout" "$DIR/plan.stderr"
  echo "grant plan staged at $DIR/grant-attempt; review source plan and approval before seal"
  exit 0
fi

if [ "$#" -eq 3 ] && [ "$1" = seal ]; then
  read_staging "$2"
  APPROVAL=$3; private_file "$APPROVAL" 65536
  [ ! -e "$ATTEMPT/seal.json" ] && [ ! -L "$ATTEMPT/seal.json" ] ||
    fail "grant already sealed"
  "$MINI" agent-lifetime-grant-seal --attempt "$ATTEMPT" --approval "$APPROVAL" \
    >"$DIR/seal.stdout" 2>"$DIR/seal.stderr" ||
    fail "source op75 seal refused; retained attempt needs review"
  chmod 600 "$DIR/seal.stdout" "$DIR/seal.stderr"
  echo "grant sealed at $ATTEMPT; no event27 submitted"
  exit 0
fi

if [ "$#" -eq 4 ] && [ "$1" = approve ]; then
  read_staging "$2"
  SIGNERS=$3 APPROVAL=$4
  private_file "$SIGNERS" 65536
  absolute "$APPROVAL"; protected_chain "${APPROVAL%/*}"
  [ ! -e "$APPROVAL" ] && [ ! -L "$APPROVAL" ] || fail "approval already exists"
  private_file "$ATTEMPT/plan-inspected.json" 100000000
  private_file "$ATTEMPT/plan.bin" 12102759
  jq -e '
    type == "array" and length > 0 and length <= 16 and
    all(.[]; (keys | sort) == (["keyId","keyEpoch","publicKey","keyPath"] | sort) and
      ([.keyId,.keyEpoch] | all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$"))) and
      (.publicKey | type == "string" and test("^[0-9a-f]{64}$")) and
      (.keyPath | type == "string" and startswith("/"))) and
    ([.[] | [.keyId,.keyEpoch] | join(":")] | unique | length) == length
    ' "$SIGNERS" >/dev/null || fail "ordered signer custody map refused"
  jq -e '
    .type == "application-agent-lifetime-grant-plan-v1" and
    (.canonicalPlanHex | type == "string" and test("^[0-9a-f]+$")) and
    (.birthSlots | type == "array" and length > 0) and
    (.appSlot | type == "object")
    ' "$ATTEMPT/plan-inspected.json" >/dev/null || fail "source grant plan inspection refused"
  jq -er .canonicalPlanHex "$ATTEMPT/plan-inspected.json" |
    xxd -r -p >"$DIR/approval-plan-source.bin"
  chmod 600 "$DIR/approval-plan-source.bin"
  cmp -s "$ATTEMPT/plan.bin" "$DIR/approval-plan-source.bin" ||
    fail "source approval plan differs from retained plan bytes"
  SLOTS=$DIR/approval-slots.json
  jq -c '[.birthSlots[],.appSlot]' "$ATTEMPT/plan-inspected.json" >"$SLOTS"
  chmod 600 "$SLOTS"
  : >"$DIR/approval-signers.jsonl"
  count=$(jq 'length' "$SLOTS")
  index=0
  while [ "$index" -lt "$count" ]; do
    slot=$(jq -c --argjson i "$index" '.[$i]' "$SLOTS")
    key_id=$(printf '%s' "$slot" | jq -er .signing.keyId)
    key_epoch=$(printf '%s' "$slot" | jq -er .signing.keyEpoch)
    printf '%s' "$slot" | jq -e \
      '.signing.decoded == true and .signing.algorithm == "1" and
       (.headerHex | type == "string" and length > 0 and length % 2 == 0 and
         test("^[0-9a-f]+$"))' >/dev/null || fail "source signing slot refused"
    signer=$(jq -cer --arg id "$key_id" --arg epoch "$key_epoch" \
      '[.[] | select(.keyId == $id and .keyEpoch == $epoch)] |
       if length == 1 then .[0] else error("signer absent or duplicate") end' \
      "$SIGNERS") || fail "source slot has no exact protected signer"
    key_path=$(printf '%s' "$signer" | jq -er .keyPath)
    private_file "$key_path" 32
    [ "$(stat -c %s "$key_path")" -eq 32 ] || fail "signer seed is not raw32"
    header_sha=$(printf '%s' "$slot" | jq -er .headerHex | xxd -r -p | sha256sum | cut -d ' ' -f 1)
    printf '%s' "$slot" | jq -c --argjson signer "$signer" --arg sha "$header_sha" '
      {role,index,keyId:.signing.keyId,keyEpoch:.signing.keyEpoch,
       publicKey:$signer.publicKey,headerSha256:$sha,keyPath:$signer.keyPath}' \
      >>"$DIR/approval-signers.jsonl"
    index=$((index + 1))
  done
  jq -s --slurpfile plan "$ATTEMPT/plan-inspected.json" \
    --arg requestSha "$(sha "$ATTEMPT/request.bin")" \
    --arg planSha "$(sha "$ATTEMPT/plan.bin")" '
    {type:"minidregg-agent-lifetime-grant-approval-v1",
     requestSha256:$requestSha,planSha256:$planSha,
     request:$plan[0].request,birthBoundary:$plan[0].birthBoundary,
     finalizedDraftHex:$plan[0].finalizedDraftHex,signers:.}
    ' "$DIR/approval-signers.jsonl" >"$APPROVAL"
  chmod 600 "$APPROVAL" "$DIR/approval-signers.jsonl"
  echo "source-slot approval prepared at $APPROVAL; review before seal"
  exit 0
fi

if [ "$#" -eq 2 ] && [ "$1" = finish ]; then
  read_staging "$2"
  private_file "$ATTEMPT/seal.json" 4096
  private_file "$ATTEMPT/call.bin" 12102759
  if [ ! -e "$ATTEMPT/submit-marker.json" ]; then
    if ! "$MINI" agent-lifetime-grant-submit --attempt "$ATTEMPT" \
        >"$DIR/submit.stdout" 2>"$DIR/submit.stderr"; then
      echo "grant submit uncertain; exact op73 lookup follows" >&2
    fi
  fi
  [ -e "$ATTEMPT/submit-marker.json" ] || fail "no durable submit marker; no lookup authority"
  "$MINI" agent-lifetime-grant-lookup --attempt "$ATTEMPT" \
    >"$DIR/lookup.stdout" 2>"$DIR/lookup.stderr" ||
    fail "exact event27 lookup refused; do not resubmit"
  jq -e '.type == "confirmed" and .confirmation == "replayed"' \
    "$DIR/lookup.stdout" >/dev/null || fail "event27 not confirmed by exact lookup"
  chmod 600 "$DIR"/*.stdout "$DIR"/*.stderr
  echo "event27 accepted; use exact $ATTEMPT/lookup-NNNN.outcome.json with route renderer"
  exit 0
fi

echo "usage: $0 prepare MINI HOST CONFIG SOCKET ALLOCATION EVENT22_ATTEMPT hermes-a|hermes-b POLICY NEW_DIR MINI_SHA256 HOST_SHA256" >&2
echo "       $0 seal STAGED_DIR APPROVAL.json" >&2
echo "       $0 approve STAGED_DIR PRIVATE_SIGNER_MAP.json NEW_APPROVAL.json" >&2
echo "       $0 finish STAGED_DIR" >&2
exit 2
