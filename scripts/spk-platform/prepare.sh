#!/bin/sh
# Prepare a new, private signed-GitWeb Mini fixture. No Store is bootstrapped.
# The qualified native Host is required only by run-base.sh, after review.
set -eu
umask 077

if [ "$#" -ne 4 ]; then
  echo "usage: $0 NEW_ROOT SIGNED_GITWEB_SPK SOURCE_DESCRIPTOR MINI_CLIENT" >&2
  exit 2
fi
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
ROOT=$1
SPK=$2
DESCRIPTOR=$3
MINI=$4
canonical_absolute() {
  case "$1" in
    /*) ;;
    *) echo "path must be absolute: $1" >&2; exit 2 ;;
  esac
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
for input in "$ROOT" "$SPK" "$DESCRIPTOR" "$MINI"; do
  canonical_absolute "$input"
done
case "$ROOT" in
  /var/lib/minidregg/spk/fixtures/*) ;;
  *) echo "fixture root must be fresh under /var/lib/minidregg/spk/fixtures" >&2; exit 2 ;;
esac
[ ! -e "$ROOT" ] && [ ! -L "$ROOT" ] || {
  echo "fixture root already exists" >&2; exit 2;
}
protected_dir_chain "${ROOT%/*}"
[ -f "$SPK" ] && [ -f "$DESCRIPTOR" ] && [ -x "$MINI" ] || {
  echo "signed SPK, descriptor or Mini client unavailable" >&2; exit 2;
}
command -v jq >/dev/null 2>&1 || { echo "jq required" >&2; exit 2; }
command -v sha256sum >/dev/null 2>&1 || { echo "sha256sum required" >&2; exit 2; }

PROVISION="$REPO/scripts/workroom/provision.sh"
MEMBER="$REPO/scripts/grain-birth/native-share-member.sh"
APP="$REPO/scripts/application-current-birth/native-share-base.sh"
POSITIVE="$REPO/scripts/application-share-issue/native-positive-base.sh"
ROOTS="$REPO/scripts/application-share-issue/gitweb-roots.json"
PACKAGE="$REPO/scripts/application-share-issue/gitweb-verified-package.json"
test "$(sha256sum "$PROVISION" | cut -d ' ' -f 1)" = \
  4648f7222897de69e3454c8b7abad7022719697594c0b987fe24a0bb000ba9c8
test "$(sha256sum "$MEMBER" | cut -d ' ' -f 1)" = \
  b76b7bda932f016e86c3013366132a16458768c3fd59cec1106cee2c0cb3ee9a
test "$(sha256sum "$APP" | cut -d ' ' -f 1)" = \
  b62a2d4ae17b6aa85a663fada3779eca3be10e252bffea1b7066e501ee9015cd
test "$(sha256sum "$POSITIVE" | cut -d ' ' -f 1)" = \
  de9dcbed028d38843a6d3418c4cd81544f4c7dc2006e747773f530087eb45603
test "$(sha256sum "$ROOTS" | cut -d ' ' -f 1)" = \
  0d848da24169771e02fcb32b88465cbe9dec87649432e76a87309cf6f89f272f
test "$(sha256sum "$PACKAGE" | cut -d ' ' -f 1)" = \
  07ec966e1f1917d310462a7847e3644bfbca43da865a8df623b482be0eb5e8b3
test "$(sha256sum "$SPK" | cut -d ' ' -f 1)" = \
  2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa
test "$(sha256sum "$DESCRIPTOR" | cut -d ' ' -f 1)" = \
  a853b57cb79ce72f965d97b682a17c83e1396ef8e8f2f65d130e3207dbec7e7f
test "$(wc -c < "$SPK" | tr -d ' ')" = 14045864

mkdir -m 700 "$ROOT"
mkdir -m 700 "$ROOT/custody" "$ROOT/packages" "$ROOT/source-stage"
protected_dir_chain "$ROOT/custody"
protected_dir_chain "$ROOT/packages"
protected_dir_chain "$ROOT/source-stage"
install -m 600 "$SPK" "$ROOT/packages/gitweb.spk"
install -m 600 "$DESCRIPTOR" "$ROOT/packages/package-identity.bin"
"$MINI" keygen --secret "$ROOT/custody/completion.seed" \
  --public "$ROOT/custody/completion.pub" >"$ROOT/custody/completion-keygen.txt"
test "$(wc -c < "$ROOT/custody/completion.pub" | tr -d ' ')" = 32
test "$(wc -c < "$ROOT/custody/completion.seed" | tr -d ' ')" = 32
COMPLETION_PUBLIC=$(od -An -tx1 -v "$ROOT/custody/completion.pub" | tr -d ' \n')
test "${#COMPLETION_PUBLIC}" = 64

# Keep the original signatureBinary suffix: native-share-member.sh patches it
# to add the operator grain tariff. The completion key and management pins are
# installed *before* bootstrap and copied into pinned-config.json by Mini.
# shellcheck disable=SC2016 # Preserve provisioner's literal shell variables.
sed 's|"storageRoot":"$EVIDENCE/store","signatureBinary"|"storageRoot":"$EVIDENCE/store","completionCustodianKey":"$SPK_COMPLETION_PUBLIC","completionManagement":{"app":8401,"packageManifest":8402,"managementSubject":8,"managementKeyId":8008,"appCapability":141,"appObserveCapability":141,"packageCapability":143,"packageObserveCapability":143},"residentBeginManagement":{"app":8401,"packageManifest":8402,"snapshotManifest":8403,"managementSubject":8,"managementKeyId":8008,"appCapability":141,"packageObserveCapability":143},"residentClaimManagement":{"app":8401,"packageManifest":8402,"managementSubject":8,"managementKeyId":8008,"appCapability":141,"appObserveCapability":141,"packageObserveCapability":143},"signatureBinary"|' \
  "$PROVISION" >"$ROOT/source-stage/provision-spk.sh"
test "$(rg -c 'completionCustodianKey' "$ROOT/source-stage/provision-spk.sh")" = 1
test "$(rg -c 'residentBeginManagement' "$ROOT/source-stage/provision-spk.sh")" = 1
test "$(rg -c 'residentClaimManagement' "$ROOT/source-stage/provision-spk.sh")" = 1
test "$(rg -c '"signatureBinary":"\$SIGNATURE_BINARY"}' "$ROOT/source-stage/provision-spk.sh")" = 1
chmod 700 "$ROOT/source-stage/provision-spk.sh"

sha256sum "$PROVISION" "$MEMBER" "$APP" "$POSITIVE" "$ROOTS" "$PACKAGE" \
  "$ROOT/source-stage/provision-spk.sh" "$ROOT/packages/gitweb.spk" \
  "$ROOT/packages/package-identity.bin" "$MINI" \
  >"$ROOT/source-stage/input-sha256.txt"
jq -n --arg root "$ROOT" --arg spkSha \
    2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa \
  --arg descriptorRoot "$(jq -er .packageRoot "$ROOTS")" \
  --arg completionKey "$COMPLETION_PUBLIC" \
  '{protocol:"mini-spk-integrated-fixture-preparation-v1",root:$root,
    app:"8401",packageManifest:"8402",snapshotManifest:"8403",
    aliceWebSession:"8404",aliceWebDescriptor:"8405",
    bobWebSession:"8406",bobWebDescriptor:"8407",
    aliceApiSession:"8410",aliceApiDescriptor:"8411",
    aliceWebTicket:"8500",bobWebTicket:"8501",aliceApiTicket:"8510",
    spkRawSha256:$spkSha,descriptorRoot:$descriptorRoot,
    completionCustodianKey:$completionKey}' \
  >"$ROOT/source-stage/fixture-public.json"
echo "prepared fresh private fixture source at $ROOT; no Store or lifecycle event submitted"
