#!/bin/sh
# After run-base.sh and operator socket setup, construct private INSTALL
# custody/config only. It does not invoke SPK ingestion or submit Mini events.
set -eu
umask 077

if [ "$#" -ne 6 ]; then
  echo "usage: $0 PREPARED_ROOT QUALIFIED_HOST OPERATOR_SOCKET APP_UID IMAGE_DIR NEW_INSTALL_JOURNAL" >&2
  exit 2
fi
ROOT=$1 HOST=$2 SOCKET=$3 APP_UID=$4 IMAGE_DIR=$5 JOURNAL=$6
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
for input in "$ROOT" "$HOST" "$SOCKET" "$IMAGE_DIR" "$JOURNAL"; do
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
PREPARED_HOST_SHA=$(awk -v path="$HOST" '$2 == path {print $1}' \
  "$ROOT/source-stage/base-executable-sha256.txt")
[ -n "$PREPARED_HOST_SHA" ] &&
  [ "$(sha256sum "$HOST" | cut -d ' ' -f 1)" = "$PREPARED_HOST_SHA" ] || {
  echo "Host differs from fresh base Host" >&2; exit 2;
}
[ ! -e "$JOURNAL" ] && [ ! -L "$JOURNAL" ] || {
  echo "INSTALL journal already exists" >&2; exit 2;
}
protected_dir_chain "${JOURNAL%/*}"
for directory in "$ROOT" "$ROOT/custody" "$ROOT/packages" \
    "$ROOT/base" "$ROOT/base/workroom"; do
  protected_dir_chain "$directory"
done
CONFIG="$ROOT/base/workroom/deployment/pinned-config.json"
SEED="$ROOT/base/workroom/tool.key"
PUBLIC="$ROOT/base/workroom/tool.pub"
COMPLETION="$ROOT/custody/completion.seed"
SPK="$ROOT/packages/gitweb.spk"
for file in "$CONFIG" "$SEED" "$PUBLIC" "$COMPLETION" "$SPK"; do
  [ -s "$file" ] || { echo "missing fresh protected fixture input" >&2; exit 2; }
done
test "$(sha256sum "$SPK" | cut -d ' ' -f 1)" = \
  2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa
test "$(od -An -tx1 -v "$ROOT/custody/completion.pub" | tr -d ' \n')" = \
  "$(jq -er .completionCustodianKey "$CONFIG")"
jq -e '.completionManagement.app == 8401 and
  .residentBeginManagement.app == 8401 and
  .residentClaimManagement.app == 8401 and
  .grainBirthTariff == {base:2,perBirth:1}' "$CONFIG" >/dev/null
SEMANTICS=$(jq -er '.semantics | tostring | select(test("^[1-9][0-9]*$"))' \
  "$ROOT/base/workroom/operator-profile.json")
MANAGEMENT_PUBLIC=$(od -An -tx1 -v "$PUBLIC" | tr -d ' \n')
test "${#MANAGEMENT_PUBLIC}" = 64

BEGIN="$ROOT/custody/begin-management.json"
CLAIM="$ROOT/custody/claim-management.json"
INSTALL_COMPLETION="$ROOT/custody/install-completion-management.json"
for file in "$BEGIN" "$CLAIM" "$INSTALL_COMPLETION"; do
  [ ! -e "$file" ] && [ ! -L "$file" ] || {
    echo "custody output already exists" >&2; exit 2;
  }
done
# Source slot order: NativeHost.prepareLoaded invocation slots, then the
# lifecycle operator's independent observations. Exact Mini plan inspection
# remains decisive; a shape change fails before any signature is emitted.
jq -n --arg public "$MANAGEMENT_PUBLIC" --arg seed "$SEED" '
  def pin($role;$index): {role:$role,index:$index,keyId:"8008",keyEpoch:"2",
    publicKeyHex:$public,seedPath:$seed};
  {protocol:"mini-spk-resident-begin-management-v1",app:"8401",
    packageManifest:"8402",snapshotManifest:"8403",managementSubject:"8",
    signers:[pin("4";"0"),pin("1";"0"),pin("9";"0")]}'>"$BEGIN"
jq -n --arg public "$MANAGEMENT_PUBLIC" --arg seed "$SEED" '
  def pin($role;$index): {role:$role,index:$index,keyId:"8008",keyEpoch:"2",
    publicKeyHex:$public,seedPath:$seed};
  {protocol:"mini-spk-resident-claim-management-v1",app:"8401",
    packageManifest:"8402",managementSubject:"8",
    signers:[pin("4";"0"),pin("1";"0"),pin("9";"0"),pin("10";"0")]}'>"$CLAIM"
jq -n --arg public "$MANAGEMENT_PUBLIC" --arg seed "$SEED" '
  def pin($role;$index): {role:$role,index:$index,keyId:"8008",keyEpoch:"2",
    publicKeyHex:$public,seedPath:$seed};
  {protocol:"mini-spk-completion-management-v1",app:"8401",
    packageManifest:"8402",managementSubject:"8",
    signers:[pin("4";"0"),pin("4";"1"),pin("8";"0"),pin("8";"1"),
      pin("1";"0"),pin("9";"0")]}'>"$INSTALL_COMPLETION"
chmod 600 "$BEGIN" "$CLAIM" "$INSTALL_COMPLETION"

mkdir -m 700 "$JOURNAL"
protected_dir_chain "$JOURNAL"
HOST_SHA=$(sha256sum "$HOST" | cut -d ' ' -f 1)
CONFIG_SHA=$(sha256sum "$CONFIG" | cut -d ' ' -f 1)
jq -n --arg journal "$JOURNAL" --arg spk "$SPK" --arg image "$IMAGE_DIR" \
  --arg uid "$APP_UID" --arg host "$HOST" --arg hostSha "$HOST_SHA" \
  --arg config "$CONFIG" --arg configSha "$CONFIG_SHA" --arg socket "$SOCKET" \
  --arg begin "$BEGIN" --arg claim "$CLAIM" \
  --arg completion "$INSTALL_COMPLETION" --arg seed "$COMPLETION" \
  --arg semantics "$SEMANTICS" '
  {protocol:"mini-spk-resident-install-v1",journalDir:$journal,
    sourceSpk:$spk,imageDir:$image,
    expectedRawSha256:"2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa",
    appUid:($uid|tonumber),miniHost:$host,miniHostSha256:$hostSha,
    miniConfig:$config,miniConfigSha256:$configSha,miniOperatorSocket:$socket,
    beginManagementCustody:$begin,claimManagementCustody:$claim,
    completionManagementCustody:$completion,completionCustodianSeed:$seed,
    completionSemantics:$semantics}' >"$JOURNAL/install.json"
chmod 600 "$JOURNAL/install.json"
sha256sum "$HOST" "$CONFIG" "$SPK" "$BEGIN" "$CLAIM" \
  "$INSTALL_COMPLETION" "$JOURNAL/install.json" \
  >"$JOURNAL/fixture-input-sha256.txt"
echo "private INSTALL config prepared at $JOURNAL/install.json; no lifecycle event submitted"
