#!/bin/sh
# Render both v3 route pin sets from a verifier-selected, currently accepted
# event27 grant. This does not issue a grant, start an app or authorize HTTP.
set -eu
umask 077

fail() { echo "lifetime route: $*" >&2; exit 2; }
absolute() {
  case "$1" in /*) ;; *) fail "absolute path required: $1" ;; esac
  case "$1" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/') fail "noncanonical path: $1" ;; esac
  case "$1" in *[![:print:]]*) fail "path contains control bytes" ;; esac
}
protected_chain() {
  chain=$1
  while :; do
    [ -d "$chain" ] && [ ! -L "$chain" ] || fail "directory absent or linked: $chain"
    meta=$(stat -c '%u:%a' "$chain")
    owner=${meta%%:*}; mode=${meta#*:}
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory owner: $chain"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor: $chain"
    [ "$chain" = / ] && break
    chain=${chain%/*}; [ -n "$chain" ] || chain=/
  done
}
private_file() {
  absolute "$1"
  protected_chain "${1%/*}"
  [ -f "$1" ] && [ ! -L "$1" ] || fail "private file absent or linked: $1"
  meta=$(stat -c '%u:%a:%h:%s' "$1")
  case "$meta" in "$(id -u):600:1:"*) ;; *) fail "private file custody drift: $1" ;; esac
  size=${meta##*:}
  [ "$size" -gt 0 ] && [ "$size" -le "${2:-16777216}" ] || fail "private file size refused: $1"
}
sha() { sha256sum "$1" | cut -d ' ' -f 1; }

[ "$#" -eq 7 ] || {
  echo "usage: $0 QUALIFIED_HOST CONFIG.json GRANT_ATTEMPT LOOKUP_OUTCOME.json OPERATOR_PINS.json NEW_OUTPUT_DIR EXPECTED_HOST_SHA256" >&2
  exit 2
}
HOST=$1 CONFIG=$2 GRANT=$3 LOOKUP=$4 PINS=$5 OUTPUT=$6 HOST_SHA=$7
for path in "$HOST" "$CONFIG" "$GRANT" "$LOOKUP" "$PINS" "$OUTPUT"; do absolute "$path"; done
case "$LOOKUP" in "$GRANT"/lookup-[0-9][0-9][0-9][0-9].outcome.json) ;; *) fail "lookup must belong to exact grant attempt" ;; esac
LOOKUP_STEM=${LOOKUP%.outcome.json}
[ ! -e "$OUTPUT" ] && [ ! -L "$OUTPUT" ] || fail "output attempt already exists"
protected_chain "${OUTPUT%/*}"
protected_chain "$GRANT"
[ "$(stat -c '%u:%a' "$GRANT")" = "$(id -u):700" ] || fail "grant attempt directory custody drift"
protected_chain "${HOST%/*}"
[ -f "$HOST" ] && [ -x "$HOST" ] && [ ! -L "$HOST" ] || fail "qualified Host image unavailable"
private_file "$CONFIG" 65536
private_file "$PINS" 65536
private_file "$LOOKUP" 4096
private_file "$LOOKUP_STEM.marker.json" 4096
private_file "$LOOKUP_STEM.outcome.bin" 4096
private_file "$GRANT/call.bin" 12102759
private_file "$GRANT/receipt.json" 4096
private_file "$GRANT/pin.json" 4096
private_file "$GRANT/seal.json" 4096
private_file "$GRANT/submit-marker.json" 4096
printf '%s' "$HOST_SHA" | grep -Eq '^[0-9a-f]{64}$' || fail "Host SHA pin refused"
[ "$(sha "$HOST")" = "$HOST_SHA" ] || fail "qualified Host image differs"
CONFIG_SHA=$(sha "$CONFIG")
CALL_SHA=$(sha "$GRANT/call.bin")
jq -e --arg configSha "$CONFIG_SHA" \
  '.format == "minidregg-agent-lifetime-grant-custody-v1" and
   .configSha256 == $configSha' \
  "$GRANT/pin.json" >/dev/null || fail "grant plan pin differs"
ORIGINAL_HOST=$(jq -er .host "$GRANT/pin.json")
ORIGINAL_HOST_SHA=$(jq -er .hostSha256 "$GRANT/pin.json")
absolute "$ORIGINAL_HOST"
protected_chain "${ORIGINAL_HOST%/*}"
[ -f "$ORIGINAL_HOST" ] && [ -x "$ORIGINAL_HOST" ] && [ ! -L "$ORIGINAL_HOST" ] ||
  fail "original grant Host unavailable"
printf '%s' "$ORIGINAL_HOST_SHA" | grep -Eq '^[0-9a-f]{64}$' || fail "original Host SHA pin refused"
[ "$(sha "$ORIGINAL_HOST")" = "$ORIGINAL_HOST_SHA" ] || fail "original grant Host changed"
jq -e --arg callSha "$CALL_SHA" \
  '.format == "minidregg-agent-lifetime-grant-custody-v1" and .callSha256 == $callSha' \
  "$GRANT/seal.json" >/dev/null || fail "sealed grant call differs"
jq -e --arg callSha "$CALL_SHA" \
  '.type == "minidregg-agent-lifetime-grant-submit-attempt-v1" and .callSha256 == $callSha' \
  "$GRANT/submit-marker.json" >/dev/null || fail "grant was not submitted once"
jq -e --arg callSha "$CALL_SHA" \
  '.type == "minidregg-agent-lifetime-grant-lookup-v1" and .callSha256 == $callSha' \
  "$LOOKUP_STEM.marker.json" >/dev/null || fail "lookup does not name exact sealed grant"
jq -e --slurpfile receipt "$GRANT/receipt.json" '
  .type == "confirmed" and .confirmation == "replayed" and
  {transactionId,eventId,acceptedCount,worldRoot} ==
    ($receipt[0] | {transactionId,eventId,acceptedCount,worldRoot})
  ' "$LOOKUP" >/dev/null || fail "exact event27 lookup receipt differs"
jq -e '
  def decimal: type == "string" and test("^(0|[1-9][0-9]*)$");
  (keys | sort) == (["appSigners","controllerRouteName","enrollmentObserveCapability",
    "grantSigner","hostUid","hostUnit","manifestObserveCapability","maximumCharge",
    "packageManifest","parentCapability","parentObserve","payerPins","payerSubject",
    "purseCapability","purseObserve","purseResource","reserveAmount",
    "sessionObserveCapability","signedApiPath","snapshotManifest","socketPath"] | sort) and
  .signedApiPath == "/repo.git/" and
  (.controllerRouteName | type == "string" and test("^[A-Za-z0-9-]+-app$")) and
  (.hostUid | type == "number" and . > 0 and floor == .) and
  (.hostUnit | type == "string" and length > 0 and length <= 256) and
  (.socketPath | type == "string" and startswith("/")) and
  (.appSigners | type == "array" and length > 0 and length <= 64) and
  (.grantSigner | type == "object") and
  (.payerPins | type == "array" and length == 3) and
  ([.packageManifest,.snapshotManifest,.sessionObserveCapability,
    .manifestObserveCapability,.enrollmentObserveCapability,.parentCapability,
    .parentObserve,.purseCapability,.purseObserve,.purseResource,
    .payerSubject,.reserveAmount,.maximumCharge] | all(.[]; decimal)) and
  .packageManifest == "8402" and .snapshotManifest == "8403" and
  ((.controllerRouteName == "workroom-app" and .purseResource == "7940" and
    .payerSubject == "10") or
   (.controllerRouteName == "coding-app" and .purseResource == "7941" and
    .payerSubject == "20"))
  ' "$PINS" >/dev/null || fail "operator route/key pin shape refused"

mkdir -m 700 "$OUTPUT"
# Reinspect the retained read-only op73 outcome bytes with the same qualified
# successor Host that verifies the currently accepted event27 below.
"$HOST" "$CONFIG" inspect outcome "$LOOKUP_STEM.outcome.bin" \
  "$OUTPUT/reinspected-lookup.json" \
  >"$OUTPUT/lookup.stdout" 2>"$OUTPUT/lookup.stderr" || fail "retained lookup outcome refused"
jq -e --slurpfile original "$LOOKUP" '. == $original[0]' \
  "$OUTPUT/reinspected-lookup.json" >/dev/null || fail "retained lookup outcome changed"
# This new source route performs lookupCurrent against the pinned CONFIG Store
# and returns only verifier-selected event27, never a caller-authored plan.
"$HOST" "$CONFIG" inspect-accepted-agent-lifetime-grant \
  "$GRANT/call.bin" "$OUTPUT/accepted-grant.json" \
  >"$OUTPUT/host.stdout" 2>"$OUTPUT/host.stderr" || fail "source grant inspection refused; output retained"
chmod 600 "$OUTPUT"/*
jq -e --slurpfile receipt "$GRANT/receipt.json" '
  def decimal: type == "string" and test("^(0|[1-9][0-9]*)$");
  .type == "application-agent-lifetime-grant-accepted-v1" and
  (.canonicalIngressHex | type == "string" and length > 0 and length % 2 == 0 and
    test("^[0-9a-f]+$")) and
  .grantIssueReceipt == ($receipt[0] | {transactionId,eventId,acceptedCount,worldRoot}) and
  .grantIssueIndex == $receipt[0].grantIndex and
  (.originalDescriptorHex | type == "string" and length > 0 and length % 2 == 0 and
    test("^[0-9a-f]+$")) and
  ([.grantDigest,.grantInitializedRoot,.grantResource,.ticketResource,.app,.session,
    .subject,.parentTask,.originalGeneration,.grantObserveCapability,.originalEvent22Index,
    .grantIssueIndex] | all(.[]; decimal)) and
  ([.originalEvent22Receipt,.grantIssueReceipt] |
    all(.[]; (keys | sort) == (["transactionId","eventId","acceptedCount","worldRoot"] | sort) and
      ([.transactionId,.eventId,.acceptedCount,.worldRoot] | all(.[]; decimal)))) and
  .app == "8401" and
  ((.session == "8420" and .ticketResource == "8520" and .grantResource == "8530" and
    .subject == "10" and .parentTask == "7920") or
   (.session == "8422" and .ticketResource == "8521" and .grantResource == "8531" and
    .subject == "20" and .parentTask == "7921"))
  ' "$OUTPUT/accepted-grant.json" >/dev/null || fail "source accepted grant projection differs from retained event27"
# Decode the source-projected canonical ingress to a protected file and compare
# bytes. A full ingress can exceed Linux's per-argument MAX_ARG_STRLEN.
jq -er .canonicalIngressHex "$OUTPUT/accepted-grant.json" |
  xxd -r -p >"$OUTPUT/source-grant-ingress.bin"
chmod 600 "$OUTPUT/source-grant-ingress.bin"
cmp -s "$GRANT/call.bin" "$OUTPUT/source-grant-ingress.bin" ||
  fail "source-selected ingress differs from retained sealed call"
jq -e --slurpfile pins "$PINS" '
  ($pins[0].controllerRouteName == "workroom-app" and
    .session == "8420" and .ticketResource == "8520" and
    .grantResource == "8530" and .parentTask == "7920" and .subject == "10") or
  ($pins[0].controllerRouteName == "coding-app" and
    .session == "8422" and .ticketResource == "8521" and
    .grantResource == "8531" and .parentTask == "7921" and .subject == "20")
  ' "$OUTPUT/accepted-grant.json" >/dev/null || fail "operator route differs from source-selected grant"
jq -er .originalDescriptorHex "$OUTPUT/accepted-grant.json" |
  xxd -r -p >"$OUTPUT/original-descriptor.bin"
chmod 600 "$OUTPUT/original-descriptor.bin"
DESCRIPTOR_SHA=$(sha "$OUTPUT/original-descriptor.bin")

jq -n --slurpfile a "$OUTPUT/accepted-grant.json" --slurpfile p "$PINS" \
  --arg grantAttempt "$GRANT" --arg descriptorSha "$DESCRIPTOR_SHA" '
  $a[0] as $a | $p[0] as $p |
  {name:$p.controllerRouteName,socketPath:$p.socketPath,hostUid:$p.hostUid,
   hostUnit:$p.hostUnit,appResource:$a.app,sessionResource:$a.session,
   ticketResource:$a.ticketResource,participantSubject:$a.subject,
   parentTask:$a.parentTask,originalParentGeneration:$a.originalGeneration,
   originalDescriptorSha256:$descriptorSha,purseResource:$p.purseResource,
   signedApiPath:$p.signedApiPath,
   dispatchSelectors:{issueIndex:$a.originalEvent22Index,
     packageManifest:$p.packageManifest,snapshotManifest:$p.snapshotManifest,
     sessionObserve:$p.sessionObserveCapability,
     manifestObserve:$p.manifestObserveCapability,
     enrollmentObserve:$p.enrollmentObserveCapability},
   grantIssueIndex:$a.grantIssueIndex,grantResource:$a.grantResource,
   grantObserveCapability:$a.grantObserveCapability,grantAttemptDir:$grantAttempt,
   grantDigest:$a.grantDigest,grantInitializedRoot:$a.grantInitializedRoot,
   originalIssueReceipt:$a.originalEvent22Receipt,grantIssueReceipt:$a.grantIssueReceipt}
  ' >"$OUTPUT/controller-route-v3.json"
jq -n --slurpfile a "$OUTPUT/accepted-grant.json" --slurpfile p "$PINS" \
  --arg descriptorSha "$DESCRIPTOR_SHA" '
  $a[0] as $a | $p[0] as $p |
  {protocol:"mini-spk-agent-lifetime-custody-v3",
   lineage:{appResource:$a.app,sessionResource:$a.session,participantSubject:$a.subject,
     ticketResource:$a.ticketResource,originalParentTask:$a.parentTask,
     originalParentGeneration:$a.originalGeneration,
     originalIssueIndex:$a.originalEvent22Index,
     originalIssueReceipt:$a.originalEvent22Receipt,
     originalDescriptorSha256:$descriptorSha,
     grantResource:$a.grantResource,grantIssueIndex:$a.grantIssueIndex,
     grantDigest:$a.grantDigest,grantInitializedRoot:$a.grantInitializedRoot,
     grantIssueReceipt:$a.grantIssueReceipt,parentTask:$a.parentTask,
     purseTask:$p.purseResource},
   packageManifest:$p.packageManifest,snapshotManifest:$p.snapshotManifest,
   sessionObserveCapability:$p.sessionObserveCapability,
   manifestObserveCapability:$p.manifestObserveCapability,
   enrollmentObserveCapability:$p.enrollmentObserveCapability,
   parentCapability:$p.parentCapability,parentObserve:$p.parentObserve,
   purseCapability:$p.purseCapability,purseObserve:$p.purseObserve,
   grantObserveCapability:$a.grantObserveCapability,payerSubject:$p.payerSubject,
   reserveAmount:$p.reserveAmount,maximumCharge:$p.maximumCharge,
   appSigners:$p.appSigners,grantSigner:$p.grantSigner,payerPins:$p.payerPins}
  ' >"$OUTPUT/resident-custody-v3.json"
chmod 600 "$OUTPUT"/*.json
[ "$(sha "$HOST")" = "$HOST_SHA" ] &&
  [ "$(sha "$ORIGINAL_HOST")" = "$ORIGINAL_HOST_SHA" ] &&
  [ "$(sha "$CONFIG")" = "$CONFIG_SHA" ] &&
  [ "$(sha "$GRANT/call.bin")" = "$CALL_SHA" ] ||
  fail "Host, config or grant changed during source inspection"
sha256sum "$HOST" "$ORIGINAL_HOST" "$CONFIG" "$GRANT/pin.json" \
  "$GRANT/seal.json" "$GRANT/submit-marker.json" \
  "$GRANT/call.bin" "$GRANT/receipt.json" \
  "$LOOKUP" "$LOOKUP_STEM.marker.json" "$LOOKUP_STEM.outcome.bin" \
  "$OUTPUT/reinspected-lookup.json" "$PINS" "$OUTPUT/accepted-grant.json" \
  "$OUTPUT/source-grant-ingress.bin" \
  "$OUTPUT/original-descriptor.bin" \
  "$OUTPUT/controller-route-v3.json" "$OUTPUT/resident-custody-v3.json" \
  >"$OUTPUT/SHA256SUMS"
chmod 600 "$OUTPUT/SHA256SUMS"
echo "source-bound lifetime route prepared at $OUTPUT; no API or app started"
