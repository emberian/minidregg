#!/bin/sh
# After run-base.sh and operator socket setup, verify a separately qualified
# v3 Host against the existing Store, then construct private INSTALL custody.
# This does not invoke SPK ingestion or submit Mini events.
set -eu
umask 077

if [ "$#" -ne 11 ]; then
  echo "usage: $0 PREPARED_ROOT QUALIFIED_HOST OPERATOR_SOCKET APP_UID IMAGE_DIR NEW_INSTALL_JOURNAL OPERATOR_CONFIG OPERATOR_CONFIG_SHA256 BASE_REBOUND_CONFIG BASE_REBOUND_SHA256 NEW_PREPARE_STEP" >&2
  exit 2
fi
ROOT=$1 HOST=$2 SOCKET=$3 APP_UID=$4 IMAGE_DIR=$5 JOURNAL=$6
CONFIG=$7 EXPECTED_CONFIG_SHA=$8
BASE_REBOUND_CONFIG=$9 BASE_REBOUND_SHA=${10}
PREPARE_STEP=${11}
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
protected_root_executable() {
  executable=$1
  canonical_absolute "$executable"
  protected_dir_chain "${executable%/*}"
  [ -f "$executable" ] && [ ! -L "$executable" ] && [ -x "$executable" ] &&
    [ "$(stat -c '%u:%h' "$executable")" = '0:1' ] || {
    echo "protected helper leaf is not a root-owned single-link executable" >&2; exit 2;
  }
  leaf_mode=$(stat -c '%a' "$executable")
  case "$leaf_mode" in ''|*[!0-7]*) exit 2 ;; esac
  [ $((0$leaf_mode & 022)) -eq 0 ] || {
    echo "protected helper leaf is group/world writable" >&2; exit 2;
  }
}
for input in "$ROOT" "$HOST" "$SOCKET" "$IMAGE_DIR" "$JOURNAL" "$CONFIG" "$BASE_REBOUND_CONFIG" \
    "$PREPARE_STEP"; do
  canonical_absolute "$input"
done
case "$ROOT" in /var/lib/minidregg/spk/fixtures/*) ;; *) exit 2 ;; esac
case "$JOURNAL" in /var/lib/minidregg/spk/install-ops/*) ;; *) exit 2 ;; esac
case "$SOCKET" in /run/*) ;; *) echo "operator socket must be under /run" >&2; exit 2 ;; esac
case "$IMAGE_DIR" in
  /var/lib/minidregg/spk/packages/sha256-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa) ;;
  *) echo "image identity/path mismatch" >&2; exit 2 ;;
esac
case "$APP_UID" in ''|0*|*[!0-9]*) echo "app UID must be canonical nonzero decimal" >&2; exit 2 ;; esac
[ "$APP_UID" != "$(id -u)" ] || { echo "app UID must differ from operator" >&2; exit 2; }
[ -x "$HOST" ] && [ -S "$SOCKET" ] || {
  echo "qualified Host or protected operator socket absent" >&2; exit 2;
}
case "$HOST" in /*) ;; *) exit 2 ;; esac
case "$HOST" in /tmp/*|/var/tmp/*) exit 2 ;; esac
BASE_MANIFEST="$ROOT/source-stage/base-executable-sha256.txt"
[ -s "$BASE_MANIFEST" ] && [ ! -L "$BASE_MANIFEST" ] || {
  echo "base executable manifest absent" >&2; exit 2;
}
BASE_HOST=$(awk 'NR == 1 && NF == 2 {print $2}' "$BASE_MANIFEST")
BASE_HOST_SHA=$(awk 'NR == 1 && NF == 2 {print $1}' "$BASE_MANIFEST")
canonical_absolute "$BASE_HOST"
case "$BASE_HOST_SHA" in *[!0-9a-f]*|'') exit 2 ;; esac
[ "${#BASE_HOST_SHA}" = 64 ] || exit 2
protected_dir_chain "${BASE_HOST%/*}"
[ -x "$BASE_HOST" ] && [ ! -L "$BASE_HOST" ] &&
  [ "$(sha256sum "$BASE_HOST" | cut -d ' ' -f 1)" = "$BASE_HOST_SHA" ] || {
  echo "fresh base Host differs from retained binary pin" >&2; exit 2;
}
: "${QUALIFIED_INSTALL_HOST_SHA256:?set the separately source-qualified v3 Host SHA-256}"
case "$QUALIFIED_INSTALL_HOST_SHA256" in
  *[!0-9a-f]*|'') echo "v3 Host SHA must be lowercase hex" >&2; exit 2 ;;
esac
[ "${#QUALIFIED_INSTALL_HOST_SHA256}" = 64 ] && [ ! -L "$HOST" ] &&
  [ "$(sha256sum "$HOST" | cut -d ' ' -f 1)" = "$QUALIFIED_INSTALL_HOST_SHA256" ] || {
  echo "v3 Host differs from its exact source-qualified pin" >&2; exit 2;
}
protected_dir_chain "${HOST%/*}"
[ ! -e "$JOURNAL" ] && [ ! -L "$JOURNAL" ] || {
  echo "INSTALL journal already exists" >&2; exit 2;
}
protected_dir_chain "${JOURNAL%/*}"
[ -d "$PREPARE_STEP" ] && [ ! -L "$PREPARE_STEP" ] || exit 2
protected_dir_chain "$PREPARE_STEP"
case "$PREPARE_STEP" in "$ROOT"/continuations/gitweb-journey/prepare-install-????) ;;
  *) echo "preparation step path differs from journey" >&2; exit 2 ;;
esac
for directory in "$ROOT" "$ROOT/custody" "$ROOT/packages" \
    "$ROOT/base" "$ROOT/base/workroom"; do
  protected_dir_chain "$directory"
done
BASE_CONFIG="$ROOT/base/workroom/deployment/pinned-config.json"
PROFILE="$ROOT/base/workroom/operator-profile.json"
SETTINGS="$ROOT/base/workroom/operator.json"
QUALIFICATION="$ROOT/source-stage/launch-qualified/qualification.json"
HANDOFF="$ROOT/source-stage/install-v2-handoff.json"
BASE_CALL="$ROOT/base/app-attempt/call.bin"
BASE_OUTCOME="$ROOT/base/app-attempt/outcome.json"
SEED="$ROOT/base/workroom/tool.key"
PUBLIC="$ROOT/base/workroom/tool.pub"
COMPLETION="$ROOT/custody/completion.seed"
SPK="$ROOT/packages/gitweb.spk"
for file in "$BASE_CONFIG" "$BASE_REBOUND_CONFIG" "$CONFIG" "$PROFILE" "$SETTINGS" "$QUALIFICATION" "$HANDOFF" \
    "$BASE_CALL" "$BASE_OUTCOME" "$SEED" "$PUBLIC" "$COMPLETION" "$SPK"; do
  [ -s "$file" ] && [ ! -L "$file" ] || {
    echo "missing fresh protected fixture input" >&2; exit 2;
  }
done
protected_dir_chain "${CONFIG%/*}"
protected_dir_chain "${BASE_REBOUND_CONFIG%/*}"
case "$EXPECTED_CONFIG_SHA" in *[!0-9a-f]*|'') exit 2 ;; esac
[ "${#EXPECTED_CONFIG_SHA}" = 64 ] &&
  [ "$(sha256sum "$CONFIG" | cut -d ' ' -f 1)" = "$EXPECTED_CONFIG_SHA" ] || {
  echo "operator config differs from its explicit pin" >&2; exit 2;
}
case "$BASE_REBOUND_SHA" in *[!0-9a-f]*|'') exit 2 ;; esac
[ "${#BASE_REBOUND_SHA}" = 64 ] &&
  [ "$(sha256sum "$BASE_REBOUND_CONFIG" | cut -d ' ' -f 1)" = "$BASE_REBOUND_SHA" ] || {
  echo "base helper rebind differs from its explicit pin" >&2; exit 2;
}
STORE_PROTECTED=/opt/minidregg-gitweb-r3-20260927/bin/minidregg-link-sqlite-store-9746c47
SIGNATURE_PROTECTED=/opt/minidregg-gitweb-r3-20260927/bin/minidregg-credential-signature-verifier-9746c47
# The base config remains immutable. This first cb55 selection allows only
# two exact provider services, omission of three historical null fields, and
# two hash-identical helpers promoted into protected root-owned ancestry.
jq -e --slurpfile base "$BASE_CONFIG" \
  --arg storeHelper "$STORE_PROTECTED" --arg signatureHelper "$SIGNATURE_PROTECTED" \
  -f "$(dirname -- "$0")/base-helper-rebind-scope.jq" "$BASE_REBOUND_CONFIG" >/dev/null || {
  echo "base config differs beyond exact helper relocation" >&2; exit 2;
}
jq -e --slurpfile base "$BASE_CONFIG" \
  --arg storeHelper "$STORE_PROTECTED" --arg signatureHelper "$SIGNATURE_PROTECTED" \
  -f "$(dirname -- "$0")/install-config-scope.jq" "$CONFIG" >/dev/null || {
  echo "operator config differs beyond approved provider services" >&2; exit 2;
}
protected_dir_chain "$ROOT/source-stage/launch-qualified"
jq -e --slurpfile handoff "$HANDOFF" '
  .protocol == "mini-spk-launch-qualified-v2" and
  .rawSha256 == $handoff[0].rawSha256 and
  .packageRoot == $handoff[0].embeddedPackageRoot and
  .launchRoot == $handoff[0].launchRoot and
  .launchCanonicalSha256 == $handoff[0].launchCanonicalSha256 and
  $handoff[0].packageEmpty == true and
  $handoff[0].snapshotEmpty == true' "$QUALIFICATION" >/dev/null
test "$(sha256sum "$ROOT/source-stage/launch-qualified/launch-descriptor.bin" | cut -d ' ' -f 1)" = \
  "$(jq -er .launchCanonicalSha256 "$QUALIFICATION")"
CONFIG_SHA=$(sha256sum "$CONFIG" | cut -d ' ' -f 1)
PINNED_CONFIG_SHA=$(awk -v path="$BASE_CONFIG" '$2 == path {print $1}' "$BASE_MANIFEST")
[ "$(sha256sum "$BASE_CONFIG" | cut -d ' ' -f 1)" = "$PINNED_CONFIG_SHA" ] &&
  [ "${#PINNED_CONFIG_SHA}" = 64 ] || {
  echo "Store Settings differ from base pin" >&2; exit 2;
}
ORIGINAL_STORE_BINARY=$(jq -er '.storageBinary | select(type == "string")' "$SETTINGS")
STORE_BINARY=$(jq -er '.storageBinary | select(type == "string")' "$CONFIG")
STORE_ROOT=$(jq -er '.storageRoot | select(type == "string")' "$SETTINGS")
canonical_absolute "$ORIGINAL_STORE_BINARY"
canonical_absolute "$STORE_BINARY"
canonical_absolute "$STORE_ROOT"
[ "$STORE_ROOT" = "$ROOT/base/workroom/store" ] && [ -x "$STORE_BINARY" ] || {
  echo "base Store helper/root changed" >&2; exit 2;
}
STORE_SHA=$(awk -v path="$ORIGINAL_STORE_BINARY" '$2 == path {print $1}' "$BASE_MANIFEST")
[ "${#STORE_SHA}" = 64 ] &&
  [ "$(sha256sum "$ORIGINAL_STORE_BINARY" | cut -d ' ' -f 1)" = "$STORE_SHA" ] &&
  [ "$(sha256sum "$STORE_BINARY" | cut -d ' ' -f 1)" = "$STORE_SHA" ] || {
  echo "base Store helper differs from retained pin" >&2; exit 2;
}
protected_root_executable "$STORE_BINARY"
ORIGINAL_SIGNATURE_BINARY=$(jq -er '.signatureBinary | select(type == "string")' "$BASE_CONFIG")
SIGNATURE_SHA=$(awk -v path="$ORIGINAL_SIGNATURE_BINARY" '$2 == path {print $1}' "$BASE_MANIFEST")
[ "${#SIGNATURE_SHA}" = 64 ] &&
  [ "$(sha256sum "$ORIGINAL_SIGNATURE_BINARY" | cut -d ' ' -f 1)" = "$SIGNATURE_SHA" ] &&
  [ "$(sha256sum "$SIGNATURE_PROTECTED" | cut -d ' ' -f 1)" = "$SIGNATURE_SHA" ] || {
  echo "signature helper differs from retained original" >&2; exit 2;
}
protected_root_executable "$SIGNATURE_PROTECTED"
test "$(sha256sum "$SPK" | cut -d ' ' -f 1)" = \
  2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa
test "$(od -An -tx1 -v "$ROOT/custody/completion.pub" | tr -d ' \n')" = \
  "$(jq -er .completionCustodianKey "$CONFIG")"
jq -e '.completionManagement.app == 8401 and
  .residentBeginManagement.app == 8401 and
  .residentClaimManagement.app == 8401 and
  .grainBirthTariff == {base:2,perBirth:1}' "$CONFIG" >/dev/null
SEMANTICS=$(jq -er '.semantics | tostring | select(test("^[1-9][0-9]*$"))' \
  "$PROFILE")
MANAGEMENT_PUBLIC=$(od -An -tx1 -v "$PUBLIC" | tr -d ' \n')
test "${#MANAGEMENT_PUBLIC}" = 64

# This fixed root-published projection contains nonsecret IDs only. The
# canonical /etc registration remains root:0600 and is never opened by the
# hbox-account preparer. Check the projection before cold Mini replay.
HOST_IDENTITY=/run/minidregg/spk/host-identity.public
protected_dir_chain "${HOST_IDENTITY%/*}"
[ -f "$HOST_IDENTITY" ] && [ ! -L "$HOST_IDENTITY" ] &&
  [ "$(stat -c '%u:%a:%h' "$HOST_IDENTITY")" = '0:644:1' ] || {
  echo "root-published host identity absent or changed" >&2; exit 2;
}
HOST_IDENTITY_BEFORE=$(stat -c '%d:%i:%s:%Y:%Z' "$HOST_IDENTITY")
HOST_IDENTITY_SHA=$(sha256sum "$HOST_IDENTITY" | cut -d ' ' -f 1)
[ "$(wc -l <"$HOST_IDENTITY" | tr -d ' ')" = 2 ] || exit 2
DEPLOYMENT_ID=$(sed -n '1s/^deployment_id=//p' "$HOST_IDENTITY")
HOST_ID=$(sed -n '2s/^host_id=//p' "$HOST_IDENTITY")
case "$DEPLOYMENT_ID" in *[!0-9a-f]*|'') exit 2 ;; esac
case "$HOST_ID" in *[!0-9a-f]*|'') exit 2 ;; esac
[ "${#DEPLOYMENT_ID}" = 64 ] && [ "${#HOST_ID}" = 64 ] &&
  [ "$DEPLOYMENT_ID" != "$HOST_ID" ] &&
  [ "$(sha256sum "$HOST_IDENTITY" | cut -d ' ' -f 1)" = "$HOST_IDENTITY_SHA" ] &&
  [ "$(stat -c '%d:%i:%s:%Y:%Z' "$HOST_IDENTITY")" = "$HOST_IDENTITY_BEFORE" ] ||
  exit 2

# Both immutable Host binaries reopen and replay the exact same protected
# Settings/Store. A read-only lookup of the original base call under the new
# image must yield its original four-field receipt; no successor can mint a
# fresh base Store or silently replace its executable pin.
UPGRADE="$PREPARE_STEP/host-upgrade"
[ ! -e "$UPGRADE" ] && [ ! -L "$UPGRADE" ] || {
  echo "Host upgrade attempt already exists" >&2; exit 2;
}
mkdir -m 700 "$UPGRADE"
"$STORE_BINARY" read-to "$STORE_ROOT" "$UPGRADE/store-before.bin"
"$BASE_HOST" "$BASE_REBOUND_CONFIG" describe >"$UPGRADE/base-description.json"
"$HOST" "$CONFIG" describe >"$UPGRADE/successor-description.json"
for description in "$UPGRADE/base-description.json" \
    "$UPGRADE/successor-description.json"; do
  jq -e --arg semantics "$SEMANTICS" '
    .runtime == "minidregg-native" and .semantics == $semantics and
    .nativeChecked == true and .succinctProofDeployment == false and
    (.domain | type == "string" and test("^[1-9][0-9]*$"))' \
    "$description" >/dev/null
done
jq -S '{runtime,semantics,domain,fieldModulus,orderDifferenceWidth,
  nativeChecked,succinctProofDeployment}' "$UPGRADE/base-description.json" \
  >"$UPGRADE/base-identity.json"
jq -S '{runtime,semantics,domain,fieldModulus,orderDifferenceWidth,
  nativeChecked,succinctProofDeployment}' "$UPGRADE/successor-description.json" \
  >"$UPGRADE/successor-identity.json"
cmp "$UPGRADE/base-identity.json" "$UPGRADE/successor-identity.json"
"$BASE_HOST" "$BASE_REBOUND_CONFIG" lookup "$BASE_CALL" "$UPGRADE/base-outcome.bin"
"$BASE_HOST" "$BASE_REBOUND_CONFIG" inspect outcome "$UPGRADE/base-outcome.bin" \
  "$UPGRADE/base-outcome.json"
"$HOST" "$CONFIG" lookup "$BASE_CALL" "$UPGRADE/successor-outcome.bin"
"$HOST" "$CONFIG" inspect outcome "$UPGRADE/successor-outcome.bin" \
  "$UPGRADE/successor-outcome.json"
for outcome in "$BASE_OUTCOME" "$UPGRADE/base-outcome.json" \
    "$UPGRADE/successor-outcome.json"; do
  jq -e '.type == "confirmed" and
    (.transactionId|type == "string" and test("^(0|[1-9][0-9]*)$")) and
    (.eventId|type == "string" and test("^(0|[1-9][0-9]*)$")) and
    (.acceptedCount|type == "string" and test("^[1-9][0-9]*$")) and
    (.imageBoundary|type == "string" and test("^(0|[1-9][0-9]*)$"))' \
    "$outcome" >/dev/null
done
jq -e '.confirmation == "replayed"' "$UPGRADE/base-outcome.json" >/dev/null
jq -e '.confirmation == "replayed"' "$UPGRADE/successor-outcome.json" >/dev/null
jq -S '{transactionId,eventId,acceptedCount,imageBoundary}' "$BASE_OUTCOME" \
  >"$UPGRADE/original-receipt.json"
jq -S '{transactionId,eventId,acceptedCount,imageBoundary}' \
  "$UPGRADE/base-outcome.json" >"$UPGRADE/base-receipt.json"
jq -S '{transactionId,eventId,acceptedCount,imageBoundary}' \
  "$UPGRADE/successor-outcome.json" >"$UPGRADE/successor-receipt.json"
cmp "$UPGRADE/original-receipt.json" "$UPGRADE/base-receipt.json"
cmp "$UPGRADE/original-receipt.json" "$UPGRADE/successor-receipt.json"
"$STORE_BINARY" read-to "$STORE_ROOT" "$UPGRADE/store-after.bin"
cmp "$UPGRADE/store-before.bin" "$UPGRADE/store-after.bin"
UPGRADE_STORE_SHA=$(sha256sum "$UPGRADE/store-before.bin" | cut -d ' ' -f 1)
jq -n --arg base "$BASE_HOST" --arg baseSha "$BASE_HOST_SHA" \
  --arg successor "$HOST" --arg successorSha "$QUALIFIED_INSTALL_HOST_SHA256" \
  --arg baseConfig "$BASE_CONFIG" --arg baseConfigSha "$PINNED_CONFIG_SHA" \
  --arg baseRebound "$BASE_REBOUND_CONFIG" --arg baseReboundSha "$BASE_REBOUND_SHA" \
  --arg config "$CONFIG" --arg configSha "$CONFIG_SHA" \
  --arg profile "$PROFILE" --arg profileSha "$(sha256sum "$PROFILE" | cut -d ' ' -f 1)" \
  --argjson reusedHost "$([ "$BASE_HOST_SHA" = "$QUALIFIED_INSTALL_HOST_SHA256" ] && echo true || echo false)" \
  --arg storeSha "$UPGRADE_STORE_SHA" \
  --slurpfile receipt "$UPGRADE/successor-receipt.json" '
  {protocol:"mini-spk-install-host-upgrade-v1",reusedHost:$reusedHost,
   baseHost:$base,baseHostSha256:$baseSha,
   successorHost:$successor,successorHostSha256:$successorSha,
   baseMiniConfig:$baseConfig,baseMiniConfigSha256:$baseConfigSha,
   baseReboundMiniConfig:$baseRebound,baseReboundMiniConfigSha256:$baseReboundSha,
   miniConfig:$config,miniConfigSha256:$configSha,profile:$profile,
   profileSha256:$profileSha,storeImageSha256:$storeSha,
   originalAppReceipt:$receipt[0]}' >"$UPGRADE/host-upgrade.json"
chmod 600 "$UPGRADE"/*

DEPLOYMENT_ID_FILE="$ROOT/custody/deployment-id.hex"
HOST_ID_FILE="$ROOT/custody/host-id.hex"
install_or_match() {
  source_file=$1 destination=$2
  source_sha=$(sha256sum "$source_file" | cut -d ' ' -f 1)
  if [ -e "$destination" ] || [ -L "$destination" ]; then
    if [ -f "$destination" ] && [ ! -L "$destination" ] &&
      [ "$(stat -c '%u:%a:%h' "$destination")" = "$(id -u):600:1" ] &&
      [ "$(sha256sum "$destination" | cut -d ' ' -f 1)" = "$source_sha" ] &&
      cmp "$source_file" "$destination"; then
      :
    else
      echo "previous pure custody output differs: $destination" >&2; exit 2;
    fi
    rm -- "$source_file"
  else
    chmod 600 "$source_file"
    sync -f "$source_file"
    mv -nT -- "$source_file" "$destination"
    [ ! -e "$source_file" ] && [ -f "$destination" ] &&
      [ "$(stat -c '%u:%a:%h' "$destination")" = "$(id -u):600:1" ] &&
      [ "$(sha256sum "$destination" | cut -d ' ' -f 1)" = "$source_sha" ] || {
      echo "pure custody publication refused: $destination" >&2; exit 2;
    }
    sync -f "${destination%/*}"
  fi
}
[ "$(sha256sum "$HOST_IDENTITY" | cut -d ' ' -f 1)" = "$HOST_IDENTITY_SHA" ] &&
  [ "$(stat -c '%d:%i:%s:%Y:%Z' "$HOST_IDENTITY")" = "$HOST_IDENTITY_BEFORE" ] || {
  echo "root-published host identity changed during cold replay" >&2; exit 2;
}
printf '%s' "$DEPLOYMENT_ID" >"$PREPARE_STEP/deployment-id.candidate"
printf '%s' "$HOST_ID" >"$PREPARE_STEP/host-id.candidate"
install_or_match "$PREPARE_STEP/deployment-id.candidate" "$DEPLOYMENT_ID_FILE"
install_or_match "$PREPARE_STEP/host-id.candidate" "$HOST_ID_FILE"
DEPLOYMENT_ID=$(cat "$DEPLOYMENT_ID_FILE")
HOST_ID=$(cat "$HOST_ID_FILE")

BEGIN="$ROOT/custody/begin-management.json"
CLAIM="$ROOT/custody/claim-management.json"
INSTALL_COMPLETION="$ROOT/custody/install-completion-management.json"
# Source slot order: NativeHost.prepareLoaded invocation slots, then the
# lifecycle operator's independent observations. Exact Mini plan inspection
# remains decisive; a shape change fails before any signature is emitted.
jq -n --arg public "$MANAGEMENT_PUBLIC" --arg seed "$SEED" '
  def pin($role;$index): {role:$role,index:$index,keyId:"8008",keyEpoch:"2",
    publicKeyHex:$public,seedPath:$seed};
  {protocol:"mini-spk-resident-begin-management-v1",app:"8401",
    packageManifest:"8402",snapshotManifest:"8403",managementSubject:"8",
    signers:[pin("4";"0"),pin("1";"0"),pin("9";"0")]}'>"$PREPARE_STEP/begin-management.candidate"
jq -n --arg public "$MANAGEMENT_PUBLIC" --arg seed "$SEED" '
  def pin($role;$index): {role:$role,index:$index,keyId:"8008",keyEpoch:"2",
    publicKeyHex:$public,seedPath:$seed};
  {protocol:"mini-spk-resident-claim-management-v1",app:"8401",
    packageManifest:"8402",managementSubject:"8",
    signers:[pin("4";"0"),pin("1";"0"),pin("9";"0"),pin("10";"0")]}'>"$PREPARE_STEP/claim-management.candidate"
jq -n --arg public "$MANAGEMENT_PUBLIC" --arg seed "$SEED" '
  def pin($role;$index): {role:$role,index:$index,keyId:"8008",keyEpoch:"2",
    publicKeyHex:$public,seedPath:$seed};
  {protocol:"mini-spk-completion-management-v1",app:"8401",
    packageManifest:"8402",managementSubject:"8",
    signers:[pin("4";"0"),pin("4";"1"),pin("8";"0"),pin("8";"1"),
      pin("1";"0"),pin("9";"0")]}'>"$PREPARE_STEP/install-completion-management.candidate"
install_or_match "$PREPARE_STEP/begin-management.candidate" "$BEGIN"
install_or_match "$PREPARE_STEP/claim-management.candidate" "$CLAIM"
install_or_match "$PREPARE_STEP/install-completion-management.candidate" "$INSTALL_COMPLETION"

mkdir -m 700 "$JOURNAL"
protected_dir_chain "$JOURNAL"
jq -n --arg journal "$JOURNAL" --arg spk "$SPK" --arg image "$IMAGE_DIR" \
  --arg uid "$APP_UID" --arg host "$HOST" \
  --arg hostSha "$QUALIFIED_INSTALL_HOST_SHA256" \
  --arg config "$CONFIG" --arg configSha "$CONFIG_SHA" --arg socket "$SOCKET" \
  --arg deployment "$DEPLOYMENT_ID" --arg hostId "$HOST_ID" \
  --arg launch "$QUALIFICATION" \
  --arg begin "$BEGIN" --arg claim "$CLAIM" \
  --arg completion "$INSTALL_COMPLETION" --arg seed "$COMPLETION" \
  --arg semantics "$SEMANTICS" '
  {protocol:"mini-spk-resident-install-v2",journalDir:$journal,
    sourceSpk:$spk,imageDir:$image,
    expectedRawSha256:"2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa",
    appUid:($uid|tonumber),deploymentId:$deployment,hostId:$hostId,
    launchQualification:$launch,miniHost:$host,miniHostSha256:$hostSha,
    miniConfig:$config,miniConfigSha256:$configSha,miniOperatorSocket:$socket,
    beginManagementCustody:$begin,claimManagementCustody:$claim,
    completionManagementCustody:$completion,completionCustodianSeed:$seed,
    completionSemantics:$semantics}' >"$JOURNAL/install.json"
chmod 600 "$JOURNAL/install.json"
sha256sum "$BASE_HOST" "$HOST" "$BASE_CONFIG" "$BASE_REBOUND_CONFIG" "$CONFIG" "$PROFILE" "$SPK" \
  "$(dirname -- "$0")/install-config-scope.jq" \
  "$(dirname -- "$0")/base-helper-rebind-scope.jq" \
  "$STORE_BINARY" "$SIGNATURE_PROTECTED" \
  "$QUALIFICATION" "$HANDOFF" "$HOST_IDENTITY" \
  "$UPGRADE/host-upgrade.json" \
  "$DEPLOYMENT_ID_FILE" "$HOST_ID_FILE" "$BEGIN" "$CLAIM" \
  "$INSTALL_COMPLETION" "$JOURNAL/install.json" \
  >"$JOURNAL/fixture-input-sha256.txt"
echo "private INSTALL config prepared at $JOURNAL/install.json; no lifecycle event submitted"
