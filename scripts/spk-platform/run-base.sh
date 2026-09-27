#!/bin/sh
# Execute only the reviewed fresh birth chain with a source-qualified Host.
# This ends at app8401/package8402/snapshot8403 and Alice's Web session8404;
# INSTALL/START and v1 share tickets are separate later operations.
set -eu
umask 077

if [ "$#" -ne 5 ]; then
  echo "usage: $0 PREPARED_ROOT QUALIFIED_HOST MINI_CLIENT SQLITE_HELPER SIGNATURE_HELPER" >&2
  exit 2
fi
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
ROOT=$1 HOST=$2 MINI=$3 STORE_BINARY=$4 SIGNATURE_BINARY=$5
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
for input in "$ROOT" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY"; do
  canonical_absolute "$input"
done
case "$ROOT" in /var/lib/minidregg/spk/fixtures/*) ;; *) exit 2 ;; esac
for directory in "$ROOT" "$ROOT/custody" "$ROOT/packages" "$ROOT/source-stage"; do
  protected_dir_chain "$directory"
done
for executable in "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY"; do
  [ -x "$executable" ] || { echo "required executable unavailable" >&2; exit 2; }
  case "$executable" in /tmp/*|/var/tmp/*) echo "PrivateTmp hides helper path" >&2; exit 2 ;; esac
done
: "${QUALIFIED_HOST_SHA256:?set reviewed 9746c47 Host binary SHA-256}"
case "$QUALIFIED_HOST_SHA256" in
  *[!0-9a-f]*|'') echo "Host SHA must be lowercase hex" >&2; exit 2 ;;
esac
[ "${#QUALIFIED_HOST_SHA256}" = 64 ] || exit 2
test "$(sha256sum "$HOST" | cut -d ' ' -f 1)" = "$QUALIFIED_HOST_SHA256" || {
  echo "Host differs from qualified binary" >&2; exit 2;
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
export SPK_COMPLETION_PUBLIC
export MINI STORE_BINARY SIGNATURE_BINARY
PROVISION_SOURCE="$ROOT/source-stage/provision-spk.sh"
MEMBER_SOURCE="$REPO/scripts/grain-birth/native-share-member.sh"
APP_SOURCE="$REPO/scripts/application-current-birth/native-share-base.sh"
export PROVISION_SOURCE MEMBER_SOURCE APP_SOURCE

/bin/sh "$REPO/scripts/application-share-issue/native-positive-base.sh" \
  "$HOST" "$ROOT/base" >"$ROOT/source-stage/base-run.stdout" \
  2>"$ROOT/source-stage/base-run.stderr"

CONFIG="$ROOT/base/workroom/deployment/pinned-config.json"
test -s "$CONFIG"
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
jq -e '.app == "8401" and .packageRoot ==
  "87005803221096792113550003106028498326059648433438765766069915491574610318393"' \
  "$REPO/scripts/application-share-issue/gitweb-roots.json" >/dev/null
sha256sum "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" "$CONFIG" \
  >"$ROOT/source-stage/base-executable-sha256.txt"
echo "fresh Store/base births prepared; lifecycle INSTALL and START not submitted"
