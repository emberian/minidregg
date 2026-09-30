#!/bin/sh
# Bind an accepted human event22 ticket to one private SPK HTTP entrance.
# Native Mini rechecks ticket/session/current authority on every dispatch.
set -eu
umask 077

fail() { echo "human entrance: $*" >&2; exit 2; }
absolute() {
  case "$1" in /*) ;; *) fail "absolute path required" ;; esac
  case "$1" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/') fail "noncanonical path" ;; esac
}
chain() {
  node=$1
  while :; do
    [ -d "$node" ] && [ ! -L "$node" ] || fail "protected directory absent"
    meta=$(stat -c '%u:%a' "$node")
    owner=${meta%%:*}; mode=${meta#*:}
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign ancestor"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable ancestor"
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
binary() {
  absolute "$1"; chain "${1%/*}"
  [ -f "$1" ] && [ -x "$1" ] && [ ! -L "$1" ] || fail "binary absent"
  printf '%s' "$2" | grep -Eq '^[0-9a-f]{64}$' || fail "binary SHA malformed"
  [ "$(sha "$1")" = "$2" ] || fail "binary identity changed"
}

if [ "$#" -ne 14 ]; then
  echo "usage: $0 SPK_HOST SPK_SHA MINI MINI_SHA HOST HOST_SHA CONFIG SOCKET ALLOCATION ROUTE ISSUE_ATTEMPT SIGNERS.json POLICY.json NEW_DIRECTORY" >&2
  exit 2
fi
SPK=$1 SPK_SHA=$2 MINI=$3 MINI_SHA=$4 HOST=$5 HOST_SHA=$6
CONFIG=$7 SOCKET=$8 ALLOCATION=$9 ROUTE=${10} ISSUE=${11}
SIGNERS=${12} POLICY=${13} DIR=${14}
binary "$SPK" "$SPK_SHA"; binary "$MINI" "$MINI_SHA"; binary "$HOST" "$HOST_SHA"
private "$CONFIG"; private "$SIGNERS"; private "$POLICY"
absolute "$ALLOCATION"; chain "${ALLOCATION%/*}"
[ "$(sha "$ALLOCATION")" = ce11093ce0e3e0500ece3962d2f4cf600bdf1b9e326255d7abd04741a0abd222 ] ||
  fail "fixed allocation changed"
case "$ROUTE" in alice-web|bob-web|alice-api) ;; *) fail "unknown human route" ;; esac
absolute "$SOCKET"; chain "${SOCKET%/*}"
[ -S "$SOCKET" ] && [ ! -L "$SOCKET" ] || fail "operator socket unavailable"
absolute "$ISSUE"; chain "$ISSUE"
[ "$(stat -c '%u:%a' "$ISSUE")" = "$(id -u):700" ] || fail "issue custody drift"
STAGE=${ISSUE%/*}
[ "$ISSUE" = "$STAGE/issue" ] || fail "ticket is not the staged one-shot issue"
private "$STAGE/stage.json" 8192
private "$STAGE/request.bin" 262144
private "$STAGE/preview-plan.bin" 12102759
private "$STAGE/selected-role.json" 65536
PACKAGE_ATTEMPT=$(jq -er .signedPackageAttempt "$STAGE/stage.json")
QUALIFICATION=$(jq -er .launchQualification "$STAGE/stage.json")
TICKET_POLICY=$(jq -er .policy "$STAGE/stage.json")
private "$TICKET_POLICY"
private "$QUALIFICATION"
private "$PACKAGE_ATTEMPT/descriptor-inspection.json" 1048576
private "$PACKAGE_ATTEMPT/schema-inspection.json" 1048576
private "$PACKAGE_ATTEMPT/descriptor.bin" 12102759
private "$PACKAGE_ATTEMPT/schema.bin" 12102759
jq -e --arg package "$(sha "$PACKAGE_ATTEMPT/descriptor-inspection.json")" \
  --arg schema "$(sha "$PACKAGE_ATTEMPT/schema-inspection.json")" \
  --arg packageBytes "$(sha "$PACKAGE_ATTEMPT/descriptor.bin")" \
  --arg schemaBytes "$(sha "$PACKAGE_ATTEMPT/schema.bin")" \
  --arg qualification "$(sha "$QUALIFICATION")" \
  --arg policy "$(sha "$TICKET_POLICY")" \
  --arg role "$(sha "$STAGE/selected-role.json")" '
  .type == "mini-spk-human-ticket-stage-v1" and
  .packageInspectionSha256 == $package and
  .schemaInspectionSha256 == $schema and
  .packageCanonicalSha256 == $packageBytes and
  .schemaCanonicalSha256 == $schemaBytes and
  .launchQualificationSha256 == $qualification and
  .policySha256 == $policy and .selectedRoleSha256 == $role
  ' "$STAGE/stage.json" >/dev/null || fail "signed ticket scope staging changed"
for name in pin.json request.json request.bin plan.bin ingress.bin \
    submit-marker.json receipt-anchor.json; do private "$ISSUE/$name" 12102759; done
cmp -s "$STAGE/request.bin" "$ISSUE/request.bin" ||
  fail "accepted ticket request differs from signed scope stage"
cmp -s "$STAGE/preview-plan.bin" "$ISSUE/plan.bin" ||
  fail "accepted ticket plan differs from reviewed scope stage"
jq -e --arg config "$(sha "$CONFIG")" --arg plan "$(sha "$ISSUE/plan.bin")" \
  --arg ingress "$(sha "$ISSUE/ingress.bin")" '
  .format == "minidregg-application-grain-share-issue-custody-v1" and
  .configSha256 == $config and .planSha256 == $plan and
  .ingressSha256 == $ingress' "$ISSUE/pin.json" >/dev/null ||
  fail "retained issue custody differs"
jq -e --arg ingress "$(sha "$ISSUE/ingress.bin")" '
  .type == "minidregg-grain-share-issue-submit-v1" and
  .ingressSha256 == $ingress' "$ISSUE/submit-marker.json" >/dev/null ||
  fail "issue lacks one-shot submit marker"
absolute "$DIR"; chain "${DIR%/*}"
[ "$(stat -c '%u:%a' "${DIR%/*}")" = "$(id -u):700" ] ||
  fail "native custodian parent is not owner-private"
[ ! -e "$DIR" ] && [ ! -L "$DIR" ] || fail "entrance already exists"
jq -e '
  .type == "mini-spk-human-entrance-policy-v1" and
  (.expectedHost | type == "string" and length > 0 and length <= 255) and
  ([.sessionObserveCapability,.manifestObserveCapability,
    .enrollmentObserveCapability] |
    all(.[]; type == "string" and test("^[1-9][0-9]*$")))
  ' "$POLICY" >/dev/null || fail "human entrance policy refused"
jq -e 'type == "array" and length > 0 and length <= 64 and
  all(.[]; (keys | sort) == (["role","index","keyId","keyEpoch",
      "publicKeyHex","seedPath"] | sort) and
    ([.role,.index,.keyId,.keyEpoch] |
      all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$"))) and
    (.publicKeyHex | type == "string" and test("^[0-9a-f]{64}$")) and
    (.seedPath | type == "string" and startswith("/"))) and
  ([.[] | [.role,.index] | join(":")] | unique | length) == length' \
  "$SIGNERS" >/dev/null || fail "fixed dispatch signer map refused"
jq -r '.[].seedPath' "$SIGNERS" | while IFS= read -r seed; do
  private "$seed" 32
  [ "$(stat -c %s "$seed")" -eq 32 ] || fail "dispatch seed is not raw32"
done

# Exact op55 only replays the retained event22 ingress, never issues a ticket.
index=0
while :; do
  [ "$index" -lt 10000 ] || fail "read-only ticket probe names exhausted"
  PROBE=${DIR}-ticket-probe-$(printf '%04d' "$index")
  absolute "$PROBE"
  if [ ! -e "$PROBE" ] && [ ! -L "$PROBE" ]; then break; fi
  index=$((index + 1))
done
mkdir -m 700 "$PROBE"
"$MINI" grain-share-issue-lookup --socket "$SOCKET" --attempt "$ISSUE" \
  >"$PROBE/lookup.json" 2>"$PROBE/lookup.stderr" ||
  fail "exact event22 lookup refused"
jq -e --slurpfile anchor "$ISSUE/receipt-anchor.json" '
  .type == "confirmed" and .confirmation == "replayed" and
  {transactionId,eventId,acceptedCount,worldRoot} == $anchor[0].receipt
  ' "$PROBE/lookup.json" >/dev/null || fail "event22 receipt changed"
COUNT=$(jq -er .receipt.acceptedCount "$ISSUE/receipt-anchor.json")
printf '%s' "$COUNT" | grep -Eq '^[1-9][0-9]{0,14}$' || fail "issue index out of bound"
ISSUE_INDEX=$((COUNT - 1))
"$HOST" "$CONFIG" inspect application-share-issue-grain-plan \
  "$ISSUE/plan.bin" "$PROBE/plan.json" || fail "source ticket plan inspection refused"
jq -er .canonicalPlanHex "$PROBE/plan.json" | xxd -r -p |
  sha256sum | cut -d ' ' -f 1 >"$PROBE/plan-source.sha"
[ "$(cat "$PROBE/plan-source.sha")" = "$(sha "$ISSUE/plan.bin")" ] ||
  fail "source plan differs from retained plan bytes"
jq -er .canonicalRequest "$PROBE/plan.json" | xxd -r -p |
  sha256sum | cut -d ' ' -f 1 >"$PROBE/request-source.sha"
[ "$(cat "$PROBE/request-source.sha")" = "$(sha "$ISSUE/request.bin")" ] ||
  fail "source plan differs from retained request bytes"
"$HOST" "$CONFIG" author application-share-issue-grain-request \
  "$ISSUE/request.json" "$PROBE/request-reauthored.bin" ||
  fail "retained event22 request cannot be source-reauthored"
cmp -s "$ISSUE/request.bin" "$PROBE/request-reauthored.bin" ||
  fail "source ticket request differs"
jq -e --arg route "$ROUTE" \
  --slurpfile allocation "$ALLOCATION" \
  --slurpfile package "$PACKAGE_ATTEMPT/descriptor-inspection.json" \
  --slurpfile schema "$PACKAGE_ATTEMPT/schema-inspection.json" \
  --slurpfile role "$STAGE/selected-role.json" \
  --slurpfile policy "$TICKET_POLICY" '
  ($allocation[0].humans[] | select(.route == $route)) as $human |
  $package[0] as $pkg | $schema[0] as $schema |
  ([ $pkg.interfaces[] | select(.kind == $human.sessionKind) ][0]) as $interface |
  .request.spec.ticket as $ticket |
  .type == "application-grain-share-issue-plan-v1" and
  $ticket.resource == $human.ticket and
  $ticket.participant.session == $human.session and
  $ticket.participant.descriptorResource == $human.descriptor and
  $ticket.participant.subject == $human.subject and
  $ticket.participant.kind == $human.sessionKind and
  $ticket.participant.origin == {type:"human"} and
  $ticket.participant.sessionCapability == $human.plannedCaps.sessionOwner and
  $ticket.participant.ticketObserveCapability == $human.plannedCaps.ticketObserve and
  $ticket.participant.appObserveCapability == $policy[0].appObserveCapability and
  $ticket.scope == {app:$allocation[0].app,
    packageVersion:$pkg.signedAppVersion,packageRoot:$pkg.root,
    interfaceId:$interface.id,interfaceVersion:$interface.version,
    interfaceRoot:$interface.root,schemaRoot:$schema.root,
    schemaVersion:$schema.version} and
  $ticket.ceiling == {basis:{type:"role",id:$role[0].roleId},
    added:[],removed:[],roleSchemaRoot:$schema.root,roleVersion:$schema.version} and
  $schema.roles[($role[0].roleId | tonumber)] == $role[0].role and
  $role[0].role.obsolete == false and
  $role[0].role.permissions == $policy[0].expectedRolePermissions
  ' "$PROBE/plan.json" >/dev/null ||
  fail "source ticket differs from human allocation"

SUBJECT=$(jq -er --arg route "$ROUTE" \
  '.humans[] | select(.route == $route) | .subject' "$ALLOCATION")
SESSION=$(jq -er --arg route "$ROUTE" \
  '.humans[] | select(.route == $route) | .session' "$ALLOCATION")
TICKET=$(jq -er --arg route "$ROUTE" \
  '.humans[] | select(.route == $route) | .ticket' "$ALLOCATION")
KIND=$(jq -er --arg route "$ROUTE" \
  '.humans[] | select(.route == $route) | .sessionKind' "$ALLOCATION")
HOSTNAME=$(jq -er .expectedHost "$POLICY")
CUSTODY_STAGE=${DIR}-custody-staging
absolute "$CUSTODY_STAGE"
[ ! -e "$CUSTODY_STAGE" ] && [ ! -L "$CUSTODY_STAGE" ] ||
  fail "native custody staging already exists"
"$SPK" human-custodian-init "$CUSTODY_STAGE" "$HOSTNAME" 8401 "$SUBJECT" \
  "$SESSION" "$TICKET" "$KIND" || fail "native private custodian initialization refused"
jq -n --arg app 8401 --arg subject "$SUBJECT" --arg session "$SESSION" \
  --arg kind "$KIND" --arg issue "$ISSUE_INDEX" --arg ticket "$TICKET" \
  --slurpfile policy "$POLICY" --slurpfile signers "$SIGNERS" '
  {protocol:"mini-spk-human-dispatch-custody-v1",app:$app,
   subject:$subject,session:$session,sessionKind:$kind,
   issueIndex:$issue,ticketResource:$ticket,
   packageManifest:"8402",snapshotManifest:"8403",
   sessionObserveCapability:$policy[0].sessionObserveCapability,
   manifestObserveCapability:$policy[0].manifestObserveCapability,
   enrollmentObserveCapability:$policy[0].enrollmentObserveCapability,
   signers:$signers[0]}' >"$PROBE/dispatch.json"
install -m 600 "$PROBE/dispatch.json" "$CUSTODY_STAGE/dispatch.json"
sync -f "$CUSTODY_STAGE/dispatch.json"
sync -f "$CUSTODY_STAGE"
mv -T -- "$CUSTODY_STAGE" "$DIR"
sync -f "${DIR%/*}"
echo "human entrance staged at $DIR; private tokens remain in native files"
