#!/bin/sh
# Materialize only a private resident START config from an accepted v3 INSTALL.
# The chosen action and unit are candidates; fresh Mini op66/26 must select
# their exact source identity before the resident may spawn anything.
set -eu
umask 077

fail() { echo "resident config: $*" >&2; exit 2; }
absolute() {
  case "$1" in /*) ;; *) fail "path is not absolute: $1" ;; esac
  case "$1" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/') fail "path is not canonical: $1" ;; esac
  case "$1" in *[![:print:]]*) fail "path has control bytes" ;; esac
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
  absolute "$1"
  protected_chain "${1%/*}"
  [ -f "$1" ] && [ ! -L "$1" ] || fail "private file absent or linked: $1"
  meta=$(stat -c '%u:%a:%h:%s' "$1")
  [ "${meta%%:*}" = "$(id -u)" ] || fail "private file owner drift: $1"
  case "$meta" in "$(id -u):600:1:"*) ;; *) fail "private file mode/link drift: $1" ;; esac
  size=${meta##*:}
  [ "$size" -gt 0 ] && [ "$size" -le "${2:-20000000}" ] || fail "private file size refused: $1"
}
hex64() { printf '%s' "$1" | LC_ALL=C grep -Eq '^[0-9a-f]{64}$'; }
decimal() { printf '%s' "$1" | LC_ALL=C grep -Eq '^(0|[1-9][0-9]*)$'; }
sha() { sha256sum "$1" | cut -d ' ' -f 1; }

# This is the exact parser used by the real path. The schema-only mode below
# exercises it without claiming any custody, Store state or native authority.
validate_request_schema() {
jq -e '
  .protocol == "mini-spk-resident-config-request-v1" and
  ((keys | sort) == (["agents","appGid","bwrap","bwrapSha256","entrances","protocol","spkHost","spkHostSha256","startAction","unit"] | sort) or
   (keys | sort) == (["agents","appGid","bwrap","bwrapSha256","createdJournal","entrances","protocol","spkHost","spkHostSha256","startAction","unit"] | sort)) and
  (.appGid | type == "number" and . > 0 and floor == .) and
  (.unit | type == "string" and test("^mini-spk-s[0-9a-f]{16}-a8401-g[1-9][0-9]*[.]service$")) and
  (.spkHostSha256 | type == "string" and test("^[0-9a-f]{64}$")) and
  (.bwrapSha256 | type == "string" and test("^[0-9a-f]{64}$")) and
  (((.startAction | keys | sort) == ["index","kind"] and
    .startAction.kind == "create" and .startAction.index == 0 and
    .createdJournal == null) or
   ((.startAction | keys | sort) == ["createdIndex","kind"] and
    .startAction.kind == "continue" and
    (.startAction.createdIndex | type == "string" and test("^(0|[1-9][0-9]*)$")) and
    (.createdJournal | type == "string"))) and
  (.entrances | type == "array" and length >= 1 and length <= 8) and
  (.agents | type == "array" and length <= 8) and
  all(.entrances[];
    (keys | sort) == (["directory","dispatchCustody","displayName","preferredHandle"] | sort) and
    (.directory|type == "string") and (.dispatchCustody|type == "string") and
    (.displayName|type == "string" and length > 0 and length <= 256) and
    (.preferredHandle|type == "string" and length > 0 and length <= 256)) and
  all(.agents[];
    ((keys | sort) == (["attemptDir","controllerUid","custody","displayName","preferredHandle","reverseSocket","routeName","socket"] | sort) or
     ((keys | sort) == (["attemptDir","controllerUid","controllerWorkerWallSeconds","custody","displayName","preferredHandle","protocol","reverseSocket","reverseTimeoutSeconds","routeName","socket"] | sort) and
      .protocol == "mini-spk-agent-api-v3" and
      (.controllerWorkerWallSeconds | type == "number" and floor == . and . >= 120 and . <= 1800) and
      (.reverseTimeoutSeconds | type == "number" and floor == . and . >= 60 and . <= 1740) and
      .reverseTimeoutSeconds <= .controllerWorkerWallSeconds - 60)) and
    (.controllerUid|type == "number" and . > 0 and floor == .) and
    ([.socket,.custody,.reverseSocket,.routeName,.attemptDir,.displayName,.preferredHandle] | all(type == "string" and length > 0)))
  ' "$1" >/dev/null || fail "resident request shape refused"
}

if [ "$#" -eq 2 ] && [ "$1" = --check-request ]; then
  validate_request_schema "$2"
  exit 0
fi
if [ "$#" -ne 4 ]; then
  echo "usage: $0 PREPARED_ROOT INSTALL_JOURNAL NEW_RESIDENT_JOURNAL PRIVATE_REQUEST.json" >&2
  exit 2
fi
ROOT=$1 INSTALL=$2 JOURNAL=$3 REQUEST=$4

for path in "$ROOT" "$INSTALL" "$JOURNAL" "$REQUEST"; do absolute "$path"; done
case "$ROOT" in /var/lib/minidregg/spk/fixtures/*) ;; *) fail "unexpected prepared root" ;; esac
case "$INSTALL" in /var/lib/minidregg/spk/install-ops/*) ;; *) fail "unexpected INSTALL journal" ;; esac
case "$JOURNAL" in /var/lib/minidregg/spk/resident-ops/*) ;; *) fail "unexpected resident journal" ;; esac
[ ! -e "$JOURNAL" ] && [ ! -L "$JOURNAL" ] || fail "resident journal already exists"
protected_chain "$ROOT"; protected_chain "$INSTALL"; protected_chain "${JOURNAL%/*}"
private_file "$REQUEST" 16384
REQUEST_SHA=$(sha "$REQUEST")
if ! command -v jq >/dev/null 2>&1 || ! command -v sha256sum >/dev/null 2>&1; then
  fail "jq and sha256sum required"
fi

INSTALL_CONFIG="$INSTALL/install.json"
PREPARED="$INSTALL/install-prepared-v2.json"
COMPLETED="$INSTALL/install-completed-v2.json"
INGRESS="$INSTALL/completion-v2-author/completion-v2.bin"
SUBMIT_MARKER="$INSTALL/completion-v2-author/op38-requested.json"
QUALIFICATION="$ROOT/source-stage/launch-qualified/qualification.json"
SPK="$ROOT/packages/gitweb.spk"
LAUNCH_DESCRIPTOR="$ROOT/source-stage/launch-qualified/launch-descriptor.bin"
for file in "$INSTALL_CONFIG" "$PREPARED" "$COMPLETED" "$INGRESS" "$SUBMIT_MARKER" "$QUALIFICATION" "$LAUNCH_DESCRIPTOR" "$SPK"; do
  private_file "$file"
done
PREPARED_SHA=$(sha "$PREPARED")
COMPLETED_SHA=$(sha "$COMPLETED")
INGRESS_SHA=$(sha "$INGRESS")
INSTALL_SHA=$(sha "$INSTALL_CONFIG")
SUBMIT_SHA=$(sha "$SUBMIT_MARKER")
QUALIFICATION_SHA=$(sha "$QUALIFICATION")
SPK_SHA=$(sha "$SPK")
jq -e --slurpfile prepared "$PREPARED" --slurpfile completed "$COMPLETED" \
  --slurpfile qualification "$QUALIFICATION" --arg root "$ROOT" \
  --arg launch "$QUALIFICATION" '
  def dec: type == "string" and test("^(0|[1-9][0-9]*)$");
  .protocol == "mini-spk-resident-install-v2" and
  .expectedRawSha256 == $prepared[0].rawSha256 and
  .expectedRawSha256 == $completed[0].rawSha256 and
  .expectedRawSha256 == $qualification[0].rawSha256 and
  .sourceSpk == ($root + "/packages/gitweb.spk") and
  .launchQualification == $launch and
  .miniConfig == ($root + "/base/workroom/deployment/pinned-config.json") and
  $prepared[0].protocol == "mini-spk-install-prepared-v2" and
  $completed[0].protocol == "mini-spk-install-completed-v2" and
  $prepared[0].launchRoot == $completed[0].launchRoot and
  $prepared[0].launchRoot == $qualification[0].launchRoot and
  $completed[0].originalBeginSha256 == $prepared[0].beginSha256 and
  $completed[0].committedClaimSha256 == $prepared[0].committedClaimSha256 and
  ($prepared[0].begin.volumeIdHex | type == "string" and test("^[0-9a-f]{64}$")) and
  ($prepared[0].begin.acceptedCount | dec) and
  ($prepared[0].claim.acceptedCount | dec) and
  ($completed[0].completionReceipt | [.transactionId,.eventId,.acceptedCount,.worldRoot] | all(dec))
  ' "$INSTALL_CONFIG" >/dev/null || fail "INSTALL evidence differs from retained source"
jq -e --arg digest "$(sha "$INGRESS")" '
  .protocol == "mini-spk-launch-completion-submit-requested-v1" and
  .ingressSha256 == $digest and
  (.claimSha256 | type == "string" and test("^[0-9a-f]{64}$"))
  ' "$SUBMIT_MARKER" >/dev/null || fail "original op38 marker differs from ingress"
test "$(jq -er .claimSha256 "$SUBMIT_MARKER")" = \
  "$(jq -er .committedClaimSha256 "$PREPARED")" || fail "op38 marker claim differs"
test "$(sha "$SPK")" = "$(jq -er .expectedRawSha256 "$INSTALL_CONFIG")" || fail "signed SPK changed"
test "$(sha "$LAUNCH_DESCRIPTOR")" = \
  "$(jq -er .launchCanonicalSha256 "$QUALIFICATION")" || fail "launch descriptor changed"

HOST=$(jq -er .miniHost "$INSTALL_CONFIG")
CONFIG=$(jq -er .miniConfig "$INSTALL_CONFIG")
SOCKET=$(jq -er .miniOperatorSocket "$INSTALL_CONFIG")
HOST_SHA=$(jq -er .miniHostSha256 "$INSTALL_CONFIG")
CONFIG_SHA=$(jq -er .miniConfigSha256 "$INSTALL_CONFIG")
IMAGE=$(jq -er .imageDir "$INSTALL_CONFIG")
APP_UID=$(jq -er .appUid "$INSTALL_CONFIG")
DEPLOYMENT=$(jq -er .deploymentId "$INSTALL_CONFIG")
HOST_ID=$(jq -er .hostId "$INSTALL_CONFIG")
VOLUME_ID=$(jq -er .begin.volumeIdHex "$PREPARED")
for path in "$HOST" "$CONFIG" "$SOCKET" "$IMAGE"; do absolute "$path"; done
case "$IMAGE" in
  /var/lib/minidregg/spk/packages/sha256-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa) ;;
  *) fail "materialized signed image path differs from INSTALL profile" ;;
esac
[ -d "$IMAGE" ] && [ ! -L "$IMAGE" ] || fail "materialized signed image absent"
protected_chain "$IMAGE"
for value in "$HOST_SHA" "$CONFIG_SHA" "$DEPLOYMENT" "$HOST_ID" "$VOLUME_ID"; do
  hex64 "$value" || fail "binary, host or source volume pin invalid"
done
decimal "$APP_UID" && [ "$APP_UID" -ne 0 ] || fail "app UID invalid"
protected_chain "${HOST%/*}"; protected_chain "${CONFIG%/*}"; protected_chain "${SOCKET%/*}"
[ -x "$HOST" ] && [ ! -L "$HOST" ] && [ -S "$SOCKET" ] || fail "Host/operator socket unavailable"
private_file "$CONFIG"
[ "$(sha "$HOST")" = "$HOST_SHA" ] && [ "$(sha "$CONFIG")" = "$CONFIG_SHA" ] || fail "Host/config pin drift"
WITNESS_BEFORE=''

validate_request_schema "$REQUEST"
SPK_HOST=$(jq -er .spkHost "$REQUEST")
SPK_HOST_SHA=$(jq -er .spkHostSha256 "$REQUEST")
BWRAP=$(jq -er .bwrap "$REQUEST")
BWRAP_SHA=$(jq -er .bwrapSha256 "$REQUEST")
for binary in "$SPK_HOST" "$BWRAP"; do
  absolute "$binary"; protected_chain "${binary%/*}"
  [ -x "$binary" ] && [ ! -L "$binary" ] || fail "qualified executable unavailable: $binary"
done
[ "$(sha "$SPK_HOST")" = "$SPK_HOST_SHA" ] && [ "$(sha "$BWRAP")" = "$BWRAP_SHA" ] || fail "SPK host/bwrap pin drift"

# Continue requires the retained completed create attempt and an explicit
# source selector. Mini's current verified op66 must reselect that index.
if [ "$(jq -er .startAction.kind "$REQUEST")" = continue ]; then
  CREATED_JOURNAL=$(jq -er .createdJournal "$REQUEST")
  absolute "$CREATED_JOURNAL"; protected_chain "$CREATED_JOURNAL"
  private_file "$CREATED_JOURNAL/start-admitted-v3.json"
  private_file "$CREATED_JOURNAL/start-completed-v3.json"
  CREATED_INGRESS="$CREATED_JOURNAL/completion-sign-attempt/completion-v2.bin"
  CREATED_SUBMIT="$CREATED_JOURNAL/completion-sign-attempt/op38-requested.json"
  private_file "$CREATED_INGRESS"; private_file "$CREATED_SUBMIT"
  CREATED_ADMITTED_SHA=$(sha "$CREATED_JOURNAL/start-admitted-v3.json")
  CREATED_COMPLETED_SHA=$(sha "$CREATED_JOURNAL/start-completed-v3.json")
  CREATED_INGRESS_SHA=$(sha "$CREATED_INGRESS")
  CREATED_SUBMIT_SHA=$(sha "$CREATED_SUBMIT")
  jq -e --arg volume "$VOLUME_ID" --arg raw "$(jq -er .expectedRawSha256 "$INSTALL_CONFIG")" '
    .protocol == "mini-spk-resident-start-admitted-v3" and
    .rawSha256 == $raw and .startAction == {kind:"create",index:0} and
    .begin.volumeIdHex == $volume and .begin.priorCreate == null
    ' "$CREATED_JOURNAL/start-admitted-v3.json" >/dev/null || fail "prior create attempt differs"
  jq -e --arg admitted "$(sha "$CREATED_JOURNAL/start-admitted-v3.json")" '
    .protocol == "mini-spk-resident-start-completed-v3" and
    .admittedSha256 == $admitted and
    (.completionReceipt | [.transactionId,.eventId,.acceptedCount,.worldRoot] |
      all(type == "string" and test("^(0|[1-9][0-9]*)$")))
    ' "$CREATED_JOURNAL/start-completed-v3.json" >/dev/null || fail "prior create completion absent"
  jq -e --arg ingress "$(sha "$CREATED_INGRESS")" \
    --arg claim "$(jq -er .committedClaimSha256 "$CREATED_JOURNAL/start-admitted-v3.json")" '
    .protocol == "mini-spk-launch-completion-submit-requested-v1" and
    .ingressSha256 == $ingress and .claimSha256 == $claim
    ' "$CREATED_SUBMIT" >/dev/null || fail "prior create op38 marker differs"
fi

# Root-owned attestation is a physical fact, never a substitute for fresh
# source BEGIN/claim. Rust reopens/rechecks it immediately before spawn.
WITNESS=/run/minidregg/spk/volume-attest/8401.witness
protected_chain "${WITNESS%/*}"
[ -f "$WITNESS" ] && [ ! -L "$WITNESS" ] && \
  [ "$(stat -c '%u:%a:%h' "$WITNESS")" = '0:644:1' ] || fail "root volume witness unavailable"
WITNESS_BEFORE=$(stat -c '%d:%i:%s:%Y:%Z' "$WITNESS")
WITNESS_SHA=$(sha "$WITNESS")
[ "$(sed -n '1p' "$WITNESS")" = 'DREGG/SPK-VAR-CUSTODY/v1' ] && \
  [ "$(wc -l < "$WITNESS")" -eq 13 ] || fail "root volume witness shape refused"
for pair in "deployment_id=$DEPLOYMENT" "host_id=$HOST_ID" "resource=8401" \
    "volume_id=$VOLUME_ID" "app_uid=$APP_UID"; do
  grep -Fx "$pair" "$WITNESS" >/dev/null || fail "root volume witness differs: $pair"
done
QUOTA=$(sed -n 's/^quota_bytes=//p' "$WITNESS")
MOUNT=$(sed -n 's/^mount=//p' "$WITNESS")
decimal "$QUOTA" && [ "$QUOTA" -gt 0 ] || fail "volume quota invalid"
absolute "$MOUNT"
[ "$MOUNT" = /var/lib/minidregg/spk/vars/8401 ] || fail "volume mount identity drift"

# Private route files must already exist. Their source-selected subjects,
# sessions and ticket receipts are checked again by resident dispatch.
# validate_request_schema above is also the real route-manifest parser.
jq -r '.entrances[] | [.directory,.dispatchCustody] | @tsv' "$REQUEST" | while IFS="$(printf '\t')" read -r directory custody; do
  absolute "$directory"; absolute "$custody"
  protected_chain "$directory"; private_file "$custody"; private_file "$directory/custodian.json"
  [ "${custody%/*}" = "$directory" ] || fail "dispatch custody outside entrance"
  jq -e --arg path "$custody" --slurpfile policy "$directory/custodian.json" '
    .protocol == "mini-spk-human-dispatch-custody-v1" and .app == "8401" and
    .packageManifest == "8402" and .snapshotManifest == "8403" and
    .app == $policy[0].fixedApp and .subject == $policy[0].fixedSubject and
    .session == $policy[0].fixedSession and .ticketResource == $policy[0].fixedTicket and
    ((.sessionKind == "web" and $policy[0].fixedSessionKind == "web") or
     (.sessionKind == "api" and $policy[0].fixedSessionKind == "api")) and
    ((.session == "8404" and .ticketResource == "8500" and .subject == "8" and .sessionKind == "web") or
     (.session == "8406" and .ticketResource == "8501" and .subject == "9" and .sessionKind == "web") or
     (.session == "8410" and .ticketResource == "8510" and .subject == "8" and .sessionKind == "api"))
    ' "$custody" >/dev/null || fail "participant custody differs from fixed source allocation: $custody"
done
jq -r '.agents[] | [.socket,.custody,.reverseSocket,.attemptDir,(.protocol // "mini-spk-agent-api-v2")] | @tsv' "$REQUEST" | while IFS="$(printf '\t')" read -r socket custody reverse attempt protocol; do
  for path in "$socket" "$custody" "$reverse" "$attempt"; do absolute "$path"; done
  private_file "$custody"; protected_chain "${socket%/*}"; protected_chain "${reverse%/*}"
  [ ! -e "$attempt" ] && [ ! -L "$attempt" ] || fail "agent attempt already exists"
  [ "${attempt%/*}" = "$JOURNAL" ] || fail "agent attempt outside resident journal"
  if [ "$protocol" = mini-spk-agent-api-v3 ]; then
  jq -e '
      .protocol == "mini-spk-agent-lifetime-custody-v3" and
      .lineage.appResource == "8401" and
      .packageManifest == "8402" and .snapshotManifest == "8403" and
      ((.lineage.sessionResource == "8420" and
        .lineage.ticketResource == "8520" and .lineage.grantResource == "8530" and
        .lineage.participantSubject == "10" and .lineage.parentTask == "7920" and
        .lineage.purseTask == "7940") or
       (.lineage.sessionResource == "8422" and
        .lineage.ticketResource == "8521" and .lineage.grantResource == "8531" and
        .lineage.participantSubject == "20" and .lineage.parentTask == "7921" and
        .lineage.purseTask == "7941")) and
      (.lineage.originalIssueReceipt | type == "object") and
      (.lineage.grantIssueReceipt | type == "object") and
      (.appSigners | type == "array" and length > 0) and
      (.grantSigner | type == "object") and
      (.payerPins | type == "array" and length == 3)
      ' "$custody" >/dev/null || fail "v3 agent lineage/custody differs from fixed source allocation"
  else
    [ "$protocol" = mini-spk-agent-api-v2 ] || fail "unknown agent API protocol"
    jq -e '.protocol == "mini-spk-agent-dispatch-custody-v2" and .app == "8401" and
      .packageManifest == "8402" and .snapshotManifest == "8403" and
      ((.session == "8420" and .ticketResource == "8520" and .subject == "10") or
       (.session == "8422" and .ticketResource == "8521" and .subject == "20"))' \
      "$custody" >/dev/null || fail "v2 agent custody differs from fixed source allocation"
    generation=$(jq -er .unit "$REQUEST" | sed -n 's/^mini-spk-s[0-9a-f]\{16\}-a8401-g\([1-9][0-9]*\)[.]service$/\1/p')
    jq -e --arg generation "$generation" '.appGeneration == $generation' \
      "$custody" >/dev/null || fail "v2 agent custody generation differs from candidate unit"
  fi
done
route_pins() {
  jq -r '.entrances[] | .dispatchCustody, (.directory + "/custodian.json")' "$REQUEST" |
    while IFS= read -r path; do sha256sum "$path"; done
  jq -r '.agents[] | .custody' "$REQUEST" |
    while IFS= read -r path; do sha256sum "$path"; done
}
ROUTE_PINS=$(route_pins)

mkdir -m 700 "$JOURNAL"
protected_chain "$JOURNAL"
# Receipt-only op39 reads the exact original ingress and current verified
# Store. No Mini mutation, START authoring or physical launch occurs here.
"$HOST" "$CONFIG" application-lifecycle-completion-lookup "$INGRESS" "$JOURNAL/install-lookup.bin" \
  >"$JOURNAL/install-lookup.stdout" 2>"$JOURNAL/install-lookup.stderr" || fail "INSTALL lookup refused; journal retained"
"$HOST" "$CONFIG" inspect outcome "$JOURNAL/install-lookup.bin" "$JOURNAL/install-lookup.json" \
  >"$JOURNAL/install-inspect.stdout" 2>"$JOURNAL/install-inspect.stderr" || fail "INSTALL outcome inspect refused; journal retained"
jq -e --slurpfile completed "$COMPLETED" '
  .type == "confirmed" and .confirmation == "replayed" and
  {transactionId,eventId,acceptedCount,worldRoot} == $completed[0].completionReceipt
  ' "$JOURNAL/install-lookup.json" >/dev/null || fail "INSTALL historical receipt differs"
if [ "$(jq -er .startAction.kind "$REQUEST")" = continue ]; then
  "$HOST" "$CONFIG" application-lifecycle-completion-lookup "$CREATED_INGRESS" \
    "$JOURNAL/created-lookup.bin" >"$JOURNAL/created-lookup.stdout" \
    2>"$JOURNAL/created-lookup.stderr" || fail "create lookup refused; journal retained"
  "$HOST" "$CONFIG" inspect outcome "$JOURNAL/created-lookup.bin" \
    "$JOURNAL/created-lookup.json" >"$JOURNAL/created-inspect.stdout" \
    2>"$JOURNAL/created-inspect.stderr" || fail "create inspect refused; journal retained"
  jq -e --slurpfile completed "$CREATED_JOURNAL/start-completed-v3.json" '
    .type == "confirmed" and .confirmation == "replayed" and
    {transactionId,eventId,acceptedCount,worldRoot} == $completed[0].completionReceipt
    ' "$JOURNAL/created-lookup.json" >/dev/null || fail "create historical receipt differs"
fi

jq -n --slurpfile request "$REQUEST" --slurpfile install "$INSTALL_CONFIG" \
  --arg journal "$JOURNAL" --arg volume "$VOLUME_ID" --arg mount "$MOUNT" \
  --argjson quota "$QUOTA" --arg raw "$(jq -er .expectedRawSha256 "$INSTALL_CONFIG")" \
  --arg spkHost "$SPK_HOST" --arg spkHostSha "$SPK_HOST_SHA" '
  $request[0] as $r | $install[0] as $i |
  {protocol:"mini-spk-resident-start-v3",journalDir:$journal,
   imageDir:$i.imageDir,expectedRawSha256:$raw,
   launchQualification:$i.launchQualification,startAction:$r.startAction,
   volumeResource:8401,expectedVolumeId:$volume,
   persistentVar:$mount,persistentVarMaxBytes:$quota,
   deploymentId:$i.deploymentId,hostId:$i.hostId,
   bwrap:$r.bwrap,bwrapSha256:$r.bwrapSha256,
   appUid:$i.appUid,appGid:$r.appGid,unit:$r.unit,
   miniHost:$i.miniHost,miniHostSha256:$i.miniHostSha256,
   miniConfig:$i.miniConfig,miniConfigSha256:$i.miniConfigSha256,
   miniOperatorSocket:$i.miniOperatorSocket,
   beginManagementCustody:$i.beginManagementCustody,
   claimManagementCustody:$i.claimManagementCustody,
   beginOperationLedger:($journal+"/begin-operation-ledger"),
   claimNonceLedger:($journal+"/claim-nonce-ledger"),
   descriptorAttemptDir:($journal+"/descriptor-attempt"),
   beginAttemptDir:($journal+"/begin-attempt"),
   claimAuthorAttemptDir:($journal+"/claim-author-attempt"),
   claimAttemptDir:($journal+"/claim-attempt"),
   completionAttemptDir:($journal+"/completion-attempt"),
   completionSignAttemptDir:($journal+"/completion-sign-attempt"),
   completionSubmitAttemptDir:($journal+"/completion-submit-attempt"),
   completionCustodianSeed:$i.completionCustodianSeed,
   completionManagementCustody:$i.completionManagementCustody,
   completionSemantics:$i.completionSemantics,
   entrances:$r.entrances,agents:$r.agents}
  ' >"$JOURNAL/resident.json"

jq -n --slurpfile prepared "$PREPARED" --slurpfile completed "$COMPLETED" \
  --slurpfile request "$REQUEST" --arg install "$INSTALL" \
  --arg spkHost "$SPK_HOST" --arg spkHostSha "$SPK_HOST_SHA" \
  --arg volume "$VOLUME_ID" --arg witnessSha "$WITNESS_SHA" '
  {protocol:"mini-spk-resident-config-provenance-v1",
   installJournal:$install,installedBeginSha256:$prepared[0].beginSha256,
   installedClaimSha256:$prepared[0].committedClaimSha256,
   installedCompletionReceipt:$completed[0].completionReceipt,
   sourceVolumeIdHex:$volume,rootVolumeWitnessSha256:$witnessSha,
   spkHost:$spkHost,spkHostSha256:$spkHostSha,
   candidateUnit:$request[0].unit,candidateAction:$request[0].startAction,
   priorCreateJournal:($request[0].createdJournal // null)}
  ' >"$JOURNAL/provenance.json"
chmod 600 "$JOURNAL"/*
test "$(sha "$REQUEST")" = "$REQUEST_SHA" && \
  test "$(sha "$INSTALL_CONFIG")" = "$INSTALL_SHA" && \
  test "$(sha "$SUBMIT_MARKER")" = "$SUBMIT_SHA" && \
  test "$(sha "$QUALIFICATION")" = "$QUALIFICATION_SHA" && \
  test "$(sha "$SPK")" = "$SPK_SHA" && \
  test "$(sha "$SPK_HOST")" = "$SPK_HOST_SHA" && \
  test "$(sha "$BWRAP")" = "$BWRAP_SHA" && \
  test "$(sha "$HOST")" = "$HOST_SHA" && test "$(sha "$CONFIG")" = "$CONFIG_SHA" && \
  test "$(sha "$PREPARED")" = "$PREPARED_SHA" && \
  test "$(sha "$COMPLETED")" = "$COMPLETED_SHA" && \
  test "$(sha "$INGRESS")" = "$INGRESS_SHA" && \
  test "$(sha "$WITNESS")" = "$WITNESS_SHA" && \
  test "$(stat -c '%d:%i:%s:%Y:%Z' "$WITNESS")" = "$WITNESS_BEFORE" || \
  fail "source input or root attestation changed during config preparation"
test "$(route_pins)" = "$ROUTE_PINS" || fail "participant custody changed during config preparation"
if [ "$(jq -er .startAction.kind "$REQUEST")" = continue ]; then
  test "$(sha "$CREATED_JOURNAL/start-admitted-v3.json")" = "$CREATED_ADMITTED_SHA" && \
    test "$(sha "$CREATED_JOURNAL/start-completed-v3.json")" = "$CREATED_COMPLETED_SHA" && \
    test "$(sha "$CREATED_INGRESS")" = "$CREATED_INGRESS_SHA" && \
    test "$(sha "$CREATED_SUBMIT")" = "$CREATED_SUBMIT_SHA" || \
    fail "original create evidence changed during config preparation"
fi
sha256sum "$REQUEST" "$INSTALL_CONFIG" "$PREPARED" "$COMPLETED" "$INGRESS" \
  "$SUBMIT_MARKER" "$QUALIFICATION" "$LAUNCH_DESCRIPTOR" "$SPK" "$HOST" "$CONFIG" \
  "$SPK_HOST" "$BWRAP" "$WITNESS" "$JOURNAL/install-lookup.bin" \
  "$JOURNAL/install-lookup.json" "$JOURNAL/resident.json" \
  "$JOURNAL/provenance.json" \
  >"$JOURNAL/input-sha256.txt"
printf '%s\n' "$ROUTE_PINS" >>"$JOURNAL/input-sha256.txt"
if [ "$(jq -er .startAction.kind "$REQUEST")" = continue ]; then
  sha256sum "$CREATED_JOURNAL/start-admitted-v3.json" \
    "$CREATED_JOURNAL/start-completed-v3.json" "$CREATED_INGRESS" \
    "$CREATED_SUBMIT" "$JOURNAL/created-lookup.bin" \
    "$JOURNAL/created-lookup.json" >>"$JOURNAL/input-sha256.txt"
fi
echo "private START candidate prepared at $JOURNAL/resident.json; no START event or process launched"
