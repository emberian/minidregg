#!/bin/sh
# Execute only the reviewed fresh birth chain with a source-qualified Host.
# This ends at app8401/package8402/snapshot8403 and five source-born sessions;
# INSTALL/START, enrollment and share tickets are separate later operations.
set -eu
umask 077

if [ "$#" -ne 6 ]; then
  echo "usage: $0 PREPARED_ROOT QUALIFIED_HOST MINI_CLIENT SQLITE_HELPER SIGNATURE_HELPER QUALIFIED_SPK_HOST" >&2
  exit 2
fi
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
ROOT=$1 HOST=$2 MINI=$3 STORE_BINARY=$4 SIGNATURE_BINARY=$5 SPK_HOST=$6
canonical_absolute() {
  case "$1" in /*) ;; *) echo "path must be absolute: $1" >&2; exit 2 ;; esac
  case "$1" in
    *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/')
      echo "noncanonical path: $1" >&2; exit 2 ;;
  esac
}
protected_dir_chain() {
  path=$1
  operator_uid=$(id -u)
  while :; do
    [ -d "$path" ] && [ ! -L "$path" ] || {
      echo "protected directory absent or symlink: $path" >&2; exit 2;
    }
    metadata=$(stat -c '%u:%a' "$path" 2>/dev/null || stat -f '%u:%Lp' "$path")
    owner=${metadata%%:*}
    mode=${metadata#*:}
    case "$mode" in ''|*[!0-7]*) exit 2 ;; esac
    [ "$owner" = 0 ] || [ "$owner" = "$operator_uid" ] || {
      echo "directory has foreign owner: $path" >&2; exit 2;
    }
    [ $((0$mode & 022)) -eq 0 ] || {
      echo "group/world writable directory: $path" >&2; exit 2;
    }
    [ "$path" = / ] && break
    path=${path%/*}
    [ -n "$path" ] || path=/
  done
}
for input in "$ROOT" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
    "$SPK_HOST"; do
  canonical_absolute "$input"
done
case "$ROOT" in /var/lib/minidregg/spk/fixtures/*) ;; *) exit 2 ;; esac
for directory in "$ROOT" "$ROOT/custody" "$ROOT/packages" "$ROOT/source-stage"; do
  protected_dir_chain "$directory"
done
for executable in "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
    "$SPK_HOST"; do
  [ -x "$executable" ] || { echo "required executable unavailable" >&2; exit 2; }
  case "$executable" in /tmp/*|/var/tmp/*) echo "PrivateTmp hides helper path" >&2; exit 2 ;; esac
done
: "${QUALIFIED_HOST_SHA256:?set source-qualified v2-launch Host binary SHA-256}"
: "${QUALIFIED_SPK_HOST_SHA256:?set reviewed physical SPK Host SHA-256}"
case "$QUALIFIED_HOST_SHA256" in
  *[!0-9a-f]*|'') echo "Host SHA must be lowercase hex" >&2; exit 2 ;;
esac
case "$QUALIFIED_SPK_HOST_SHA256" in
  *[!0-9a-f]*|'') echo "SPK Host SHA must be lowercase hex" >&2; exit 2 ;;
esac
[ "${#QUALIFIED_HOST_SHA256}" = 64 ] || exit 2
[ "${#QUALIFIED_SPK_HOST_SHA256}" = 64 ] || exit 2
test "$(sha256sum "$HOST" | cut -d ' ' -f 1)" = "$QUALIFIED_HOST_SHA256" || {
  echo "Host differs from qualified binary" >&2; exit 2;
}
test "$(sha256sum "$SPK_HOST" | cut -d ' ' -f 1)" = \
  "$QUALIFIED_SPK_HOST_SHA256" || {
  echo "SPK Host differs from qualified binary" >&2; exit 2;
}
[ -f "$ROOT/source-stage/fixture-public.json" ] || exit 2
[ ! -e "$ROOT/base" ] && [ ! -L "$ROOT/base" ] &&
  [ ! -e "$ROOT/base.source-stage" ] && [ ! -L "$ROOT/base.source-stage" ] || {
  echo "base Store or private source stage already exists" >&2; exit 2;
}
test "$(sha256sum "$ROOT/packages/gitweb.spk" | cut -d ' ' -f 1)" = \
  2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa
sha256sum -c "$ROOT/source-stage/input-sha256.txt" >/dev/null
PREPARED_MINI_SHA=$(awk -v path="$MINI" '$2 == path {print $1}' \
  "$ROOT/source-stage/input-sha256.txt")
[ -n "$PREPARED_MINI_SHA" ] &&
  [ "$(sha256sum "$MINI" | cut -d ' ' -f 1)" = "$PREPARED_MINI_SHA" ] || {
  echo "Mini client differs from prepared fixture" >&2; exit 2;
}

SPK_COMPLETION_PUBLIC=$(od -An -tx1 -v "$ROOT/custody/completion.pub" | tr -d ' \n')
test "${#SPK_COMPLETION_PUBLIC}" = 64
test "$(jq -er .completionCustodianKey "$ROOT/source-stage/fixture-public.json")" = \
  "$SPK_COMPLETION_PUBLIC"

# Physical qualify-launch reuses one signature-verified SPK parse and the
# source Host's pure author/inspect codec before this fresh Store exists. Its
# offline config exactly matches the later operator.json settings. A missing
# CLI, unsupported descriptor version, changed signed command or mismatched
# source inspection aborts here, before native-positive-base creates a Store.
OFFLINE_CONFIG="$ROOT/source-stage/offline-operator.json"
QUALIFY_CONFIG="$ROOT/source-stage/qualify-launch.json"
QUALIFY_RESULT="$ROOT/source-stage/qualify-launch-result.json"
QUALIFY_ATTEMPT="$ROOT/source-stage/launch-qualified"
for output in "$OFFLINE_CONFIG" "$QUALIFY_CONFIG" "$QUALIFY_RESULT" \
    "$QUALIFY_ATTEMPT"; do
  [ ! -e "$output" ] && [ ! -L "$output" ] || {
    echo "pre-Store qualification output already exists" >&2; exit 2;
  }
done
jq -n --arg store "$STORE_BINARY" \
  --arg storeRoot "$ROOT/base/workroom/store" \
  --arg signature "$SIGNATURE_BINARY" \
  --arg completion "$SPK_COMPLETION_PUBLIC" '
  {domain:8501,federation:9,factoryId:10,resourceBookId:11,
    authorityCatalogueId:12,issuer:5,ownerBudget:100000,lifetime:10000,
    tariffBase:3,tariffPerBirth:2,tariffPerGrant:1,
    tariffPerInitialPayloadByte:1,collector:99,asset:0,
    genesisHeight:10,expectedSeed:0,storageBinary:$store,
    storageRoot:$storeRoot,signatureBinary:$signature,
    grainBirthTariff:{base:2,perBirth:1},completionCustodianKey:$completion,
    completionManagement:{app:8401,packageManifest:8402,
      managementSubject:8,managementKeyId:8008,appCapability:141,
      appObserveCapability:141,packageCapability:143,packageObserveCapability:143},
    residentBeginManagement:{app:8401,packageManifest:8402,
      snapshotManifest:8403,managementSubject:8,managementKeyId:8008,
      appCapability:141,packageObserveCapability:143},
    residentClaimManagement:{app:8401,packageManifest:8402,
      managementSubject:8,managementKeyId:8008,appCapability:141,
      appObserveCapability:141,packageObserveCapability:143}}' >"$OFFLINE_CONFIG"
chmod 600 "$OFFLINE_CONFIG"
OFFLINE_SHA=$(sha256sum "$OFFLINE_CONFIG" | cut -d ' ' -f 1)
jq -n --arg spk "$ROOT/packages/gitweb.spk" --arg host "$HOST" \
  --arg hostSha "$QUALIFIED_HOST_SHA256" --arg config "$OFFLINE_CONFIG" \
  --arg configSha "$OFFLINE_SHA" --arg attempt "$QUALIFY_ATTEMPT" '
  {protocol:"mini-spk-launch-qualification-v1",sourceSpk:$spk,
    miniHost:$host,miniHostSha256:$hostSha,miniConfig:$config,
    miniConfigSha256:$configSha,attemptDir:$attempt}' >"$QUALIFY_CONFIG"
chmod 600 "$QUALIFY_CONFIG"
"$SPK_HOST" qualify-launch "$QUALIFY_CONFIG" >"$QUALIFY_RESULT" || {
  echo "source-backed SPK qualify-launch unavailable or refused" >&2; exit 2;
}
jq -S . "$QUALIFY_RESULT" >"$ROOT/source-stage/qualification-stdout.sorted.json"
jq -S . "$QUALIFY_ATTEMPT/qualification.json" \
  >"$ROOT/source-stage/qualification-retained.sorted.json"
cmp "$ROOT/source-stage/qualification-stdout.sorted.json" \
  "$ROOT/source-stage/qualification-retained.sorted.json"
jq -e --arg spk \
    2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa \
  --arg packageRoot \
    "$(jq -er .packageRoot "$REPO/scripts/application-share-issue/gitweb-roots.json")" '
  (keys | sort) == (["protocol","rawSha256","packageRoot","launchRoot",
    "launchCanonicalSha256","createCount","createDigests","continueDigest"] | sort) and
  .protocol == "mini-spk-launch-qualified-v2" and .rawSha256 == $spk and
  .packageRoot == $packageRoot and
  (.launchRoot | type == "string" and test("^(0|[1-9][0-9]*)$")) and
  (.launchCanonicalSha256 | type == "string" and test("^[0-9a-f]{64}$")) and
  .createCount == "1" and (.createDigests | length == 1 and
    all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$"))) and
  (.continueDigest | type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$QUALIFY_RESULT" >/dev/null
test "$(sha256sum "$QUALIFY_ATTEMPT/launch-descriptor.bin" | cut -d ' ' -f 1)" = \
  "$(jq -er .launchCanonicalSha256 "$QUALIFY_RESULT")"
LAUNCH_CANONICAL_HEX=$(od -An -tx1 -v \
  "$QUALIFY_ATTEMPT/launch-descriptor.bin" | tr -d ' \n')
jq -e --slurpfile result "$QUALIFY_RESULT" \
  --slurpfile source "$QUALIFY_ATTEMPT/launch-source.json" \
  --arg canonical "$LAUNCH_CANONICAL_HEX" '
  (.type == "application-spk-launch-descriptor-v2") and
  (.canonical == $canonical) and
  (.root == $result[0].launchRoot) and
  (.packageRoot == $result[0].packageRoot) and
  (.packageCanonicalHex == $source[0].packageCanonicalHex) and
  ([.createCommands[] | {argvHex,environHex}] ==
    $source[0].createCommands) and
  ({argvHex:.continueCommand.argvHex,environHex:.continueCommand.environHex} ==
    $source[0].continueCommand) and
  ([.createCommands[].digest] == $result[0].createDigests) and
  (.continueCommand.digest == $result[0].continueDigest)' \
  "$QUALIFY_ATTEMPT/launch-inspection.json" >/dev/null

export SPK_COMPLETION_PUBLIC
export MINI STORE_BINARY SIGNATURE_BINARY
SPK_OFFLINE_CONFIG=$OFFLINE_CONFIG
export SPK_OFFLINE_CONFIG
PROVISION_SOURCE="$ROOT/source-stage/provision-checked.sh"
[ ! -e "$PROVISION_SOURCE" ] && [ ! -L "$PROVISION_SOURCE" ] || {
  echo "checked provision source already exists" >&2; exit 2;
}
# The original workroom source still authors operator.json. Compare its entire
# canonical Settings object with the pre-Store Host config before profile or
# bootstrap, after the positive-fee and grain-tariff overlays have run.
awk '
  index($0, "\"$HOST\" \"$EVIDENCE/operator.json\" profile") {
    print "test -s \"$SPK_OFFLINE_CONFIG\""
    print "jq -S . \"$SPK_OFFLINE_CONFIG\" >\"$EVIDENCE/offline-operator-canonical.json\""
    print "jq -S . \"$EVIDENCE/operator.json\" >\"$EVIDENCE/generated-operator-canonical.json\""
    print "cmp \"$EVIDENCE/offline-operator-canonical.json\" \"$EVIDENCE/generated-operator-canonical.json\""
    matches++
  }
  { print }
  END { if (matches != 1) exit 2 }
' "$ROOT/source-stage/provision-spk.sh" >"$PROVISION_SOURCE"
chmod 700 "$PROVISION_SOURCE"
ALLOCATION_SOURCE="$REPO/scripts/spk-platform/allocation-v1.json"
AGENT_OVERLAY="$REPO/scripts/spk-platform/agent-genesis-overlay.sh"
SPK_AGENT_ALLOCATION="$ROOT/source-stage/agent-allocation.json"
AGENT_SOURCE="$ROOT/source-stage/provision-agents.sh"
for input in "$ALLOCATION_SOURCE" "$AGENT_OVERLAY"; do
  [ -f "$input" ] || { echo "agent source input unavailable" >&2; exit 2; }
done
[ ! -e "$SPK_AGENT_ALLOCATION" ] && [ ! -L "$SPK_AGENT_ALLOCATION" ] || exit 2
install -m 600 "$ALLOCATION_SOURCE" "$SPK_AGENT_ALLOCATION"
"$AGENT_OVERLAY" "$PROVISION_SOURCE" "$SPK_AGENT_ALLOCATION" "$AGENT_SOURCE"
sha256sum "$ALLOCATION_SOURCE" "$AGENT_OVERLAY" "$SPK_AGENT_ALLOCATION" \
  "$PROVISION_SOURCE" "$AGENT_SOURCE" \
  >"$ROOT/source-stage/provision-agent-input-sha256.txt"
sha256sum -c "$ROOT/source-stage/provision-agent-input-sha256.txt" >/dev/null
PROVISION_SOURCE=$AGENT_SOURCE
export SPK_AGENT_ALLOCATION
MEMBER_SOURCE="$REPO/scripts/grain-birth/native-share-member.sh"
APP_BASE_SOURCE="$REPO/scripts/application-current-birth/native-share-base.sh"
APP_OVERLAY="$REPO/scripts/spk-platform/agent-session-overlay.sh"
APP_SOURCE="$ROOT/source-stage/application-sessions.sh"
[ -f "$APP_OVERLAY" ] || { echo "agent session overlay unavailable" >&2; exit 2; }
"$APP_OVERLAY" "$APP_BASE_SOURCE" "$SPK_AGENT_ALLOCATION" "$APP_SOURCE"
sha256sum "$APP_BASE_SOURCE" "$APP_OVERLAY" "$APP_SOURCE" \
  >"$ROOT/source-stage/application-session-input-sha256.txt"
sha256sum -c "$ROOT/source-stage/application-session-input-sha256.txt" >/dev/null
export PROVISION_SOURCE MEMBER_SOURCE APP_SOURCE

/bin/sh "$REPO/scripts/application-share-issue/native-positive-base.sh" \
  "$HOST" "$ROOT/base" >"$ROOT/source-stage/base-run.stdout" \
  2>"$ROOT/source-stage/base-run.stderr"

CONFIG="$ROOT/base/workroom/deployment/pinned-config.json"
test -s "$CONFIG"
AGENT_BIRTH="$ROOT/base/workroom/agents/verified/birth-evidence.json"
jq -e --slurpfile allocation "$SPK_AGENT_ALLOCATION" '
  .type == "mini-spk-agent-genesis-birth-evidence-v1" and
  (.birthReceipt | [.acceptedCount,.transactionId,.eventId,.imageBoundary] |
    all(.[]; type == "string" and test("^[1-9][0-9]*$"))) and
  ([.resources[].route] == [$allocation[0].agents[].route]) and
  ([.resources[] | .controller,.tool,.dispatch,.provider] ==
    [$allocation[0].agents[] | .controller.task,.tool.task,
      .dispatch.task,.provider.task]) and
  (.bornViews | length == 8) and
  (.parentDelegations | length == 6) and
  ([.bornViews[].task] ==
    [$allocation[0].agents[] | .controller.task,.tool.task,
      .dispatch.task,.provider.task]) and
  ([.parentDelegations[].capability] ==
    [$allocation[0].agents[] | .plannedCaps.parentToolWitness,
      .plannedCaps.parentDispatchWitness,
      .plannedCaps.parentProviderWitness]) and
  ([.parentDelegations[].receipt |
      .acceptedCount,.transactionId,.eventId,.imageBoundary] |
    all(.[]; type == "string" and test("^[1-9][0-9]*$")))' \
  "$AGENT_BIRTH" >/dev/null
ADDITIONAL_SESSIONS="$ROOT/base/additional-sessions.json"
jq -e --slurpfile allocation "$SPK_AGENT_ALLOCATION" '
  .type == "mini-spk-additional-session-births-v1" and
  ([.sessions[].route] == ["bob-web","alice-api","hermes-a","hermes-b"]) and
  ([.sessions[].session] ==
    [$allocation[0].humans[1].session,$allocation[0].humans[2].session,
      $allocation[0].agents[0].session,$allocation[0].agents[1].session]) and
  ([.sessions[].descriptor] ==
    [$allocation[0].humans[1].descriptor,$allocation[0].humans[2].descriptor,
      $allocation[0].agents[0].descriptor,$allocation[0].agents[1].descriptor]) and
  ([.sessions[].participant] == ["9","8","10","20"]) and
  ([.sessions[].birthReceipt |
      .acceptedCount,.transactionId,.eventId,.imageBoundary] |
    all(.[]; type == "string" and test("^[1-9][0-9]*$")))' \
  "$ADDITIONAL_SESSIONS" >/dev/null
jq -e --arg key "$SPK_COMPLETION_PUBLIC" '
  .completionCustodianKey == $key and
  .completionManagement == {app:8401,packageManifest:8402,
    managementSubject:8,managementKeyId:8008,appCapability:141,
    appObserveCapability:141,packageCapability:143,packageObserveCapability:143} and
  .residentBeginManagement == {app:8401,packageManifest:8402,
    snapshotManifest:8403,managementSubject:8,managementKeyId:8008,
    appCapability:141,packageObserveCapability:143} and
  .residentClaimManagement == {app:8401,packageManifest:8402,
    managementSubject:8,managementKeyId:8008,appCapability:141,
    appObserveCapability:141,packageObserveCapability:143}' "$CONFIG" >/dev/null
# This is a source-qualified lifecycle handoff, not an installed manifest.
# The app birth leaves package/snapshot pages empty; BEGIN-v3 and completion
# must bind the retained v2 launchRoot and canonical descriptor later.
jq -n --slurpfile qualified "$QUALIFY_RESULT" \
  --slurpfile birth "$ROOT/base/app-attempt/outcome.json" \
  --slurpfile package "$ROOT/base/package-born/view.json" \
  --slurpfile snapshot "$ROOT/base/snapshot-born/view.json" '
  {type:"mini-spk-v2-install-handoff-v1",
   rawSha256:$qualified[0].rawSha256,
   embeddedPackageRoot:$qualified[0].packageRoot,
   launchRoot:$qualified[0].launchRoot,
   launchCanonicalSha256:$qualified[0].launchCanonicalSha256,
   appBirth:($birth[0] | {acceptedCount,transactionId,eventId,imageBoundary}),
   packageBornRoot:$package[0].page.root,
   snapshotBornRoot:$snapshot[0].page.root,
   packageEmpty:($package[0].page.entries == []),
   snapshotEmpty:($snapshot[0].page.entries == [])}' \
  >"$ROOT/source-stage/install-v2-handoff.json"
jq -e '.packageEmpty and .snapshotEmpty and
  (.launchRoot | type == "string" and test("^[1-9][0-9]*$"))' \
  "$ROOT/source-stage/install-v2-handoff.json" >/dev/null
sha256sum "$HOST" "$SPK_HOST" "$MINI" "$STORE_BINARY" \
  "$SIGNATURE_BINARY" "$CONFIG" \
  >"$ROOT/source-stage/base-executable-sha256.txt"
echo "fresh Store/base births prepared; lifecycle INSTALL and START not submitted"
