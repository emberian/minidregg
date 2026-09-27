#!/bin/sh
# Fresh two-subject app/session base with a positive, operator-pinned initial
# payload byte tariff. All edits happen in a private temporary source copy;
# the reviewed upstream fixtures and any prior Store remain unchanged.
set -eu
umask 077

if [ "$#" -ne 2 ]; then
  echo "usage: $0 SOURCE_MATCHED_HOST NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
HOST=$1
EVIDENCE=$2
PROVISION_SOURCE=${PROVISION_SOURCE:?set exact reviewed provision.sh}
MEMBER_SOURCE=${MEMBER_SOURCE:?set exact reviewed native-share-member.sh}
APP_SOURCE=${APP_SOURCE:?set exact reviewed native-share-base.sh}
MINI=${MINI:?set source-matched Mini}
STORE_BINARY=${STORE_BINARY:?set source-matched SQLite Store helper}
SIGNATURE_BINARY=${SIGNATURE_BINARY:?set source-matched signature helper}
[ ! -e "$EVIDENCE" ] || { echo "evidence directory exists" >&2; exit 2; }
[ ! -e "$EVIDENCE.source-stage" ] || {
  echo "source stage already exists" >&2; exit 2;
}
for file in "$PROVISION_SOURCE" "$MEMBER_SOURCE" "$APP_SOURCE"; do
  [ -f "$file" ] || { echo "missing reviewed source: $file" >&2; exit 2; }
done
STAGE=$EVIDENCE.source-stage
mkdir -m 700 "$STAGE"
sha256sum "$0" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
  "$PROVISION_SOURCE" "$MEMBER_SOURCE" "$APP_SOURCE" \
  >"$STAGE/input-sha256.txt"
sha256sum -c "$STAGE/input-sha256.txt" >"$STAGE/input-precheck.txt"
mkdir -p "$STAGE/scripts/workroom" "$STAGE/scripts/grain-birth" \
  "$STAGE/scripts/application-current-birth"
sed -e 's/"tariffPerInitialPayloadByte":0/"tariffPerInitialPayloadByte":1/' \
  -e 's/"tariffPerInitialPayloadByte":"0"/"tariffPerInitialPayloadByte":"1"/' \
  -e 's/"initialBalance":"100"/"initialBalance":"1000000"/g' \
  "$PROVISION_SOURCE" >"$STAGE/scripts/workroom/provision.sh"
[ "$(rg -c 'tariffPerInitialPayloadByte.*1' \
    "$STAGE/scripts/workroom/provision.sh")" -eq 2 ] || exit 2
[ "$(rg -c 'initialBalance.*1000000' \
    "$STAGE/scripts/workroom/provision.sh")" -eq 2 ] || exit 2
PROVISION_SHA=$(sha256sum "$STAGE/scripts/workroom/provision.sh" | cut -d ' ' -f 1)
sed -e "s/^SOURCE_SHA=[0-9a-f]*$/SOURCE_SHA=$PROVISION_SHA/" \
  -e 's/initialBalance:"100"/initialBalance:"1"/' \
  "$MEMBER_SOURCE" >"$STAGE/scripts/grain-birth/native-share-member.sh"
rg -q "^SOURCE_SHA=$PROVISION_SHA$" \
  "$STAGE/scripts/grain-birth/native-share-member.sh" || exit 2
rg -q 'initialBalance:"1"' \
  "$STAGE/scripts/grain-birth/native-share-member.sh" || exit 2
cp "$APP_SOURCE" "$STAGE/scripts/application-current-birth/native-share-base.sh"
chmod 700 "$STAGE/scripts/workroom/provision.sh" \
  "$STAGE/scripts/grain-birth/native-share-member.sh" \
  "$STAGE/scripts/application-current-birth/native-share-base.sh"
sha256sum "$STAGE/scripts/workroom/provision.sh" \
  "$STAGE/scripts/grain-birth/native-share-member.sh" \
  "$STAGE/scripts/application-current-birth/native-share-base.sh" \
  >"$STAGE/private-source-sha256.txt"
sha256sum -c "$STAGE/private-source-sha256.txt" \
  >"$STAGE/private-source-precheck.txt"
MINI="$MINI" STORE_BINARY="$STORE_BINARY" SIGNATURE_BINARY="$SIGNATURE_BINARY" \
  /bin/sh "$STAGE/scripts/application-current-birth/native-share-base.sh" \
    "$HOST" "$EVIDENCE" \
    >"$STAGE/base.stdout" 2>"$STAGE/base.stderr"
cp "$STAGE/base.stdout" "$EVIDENCE/positive-base.stdout"
cp "$STAGE/base.stderr" "$EVIDENCE/positive-base.stderr"
cp "$STAGE/input-sha256.txt" "$EVIDENCE/positive-input-sha256.txt"
cp "$STAGE/private-source-sha256.txt" "$EVIDENCE/private-source-sha256.txt"
cp "$STAGE/scripts/workroom/provision.sh" "$EVIDENCE/positive-provision.sh"
cp "$STAGE/scripts/grain-birth/native-share-member.sh" \
  "$EVIDENCE/positive-member.sh"
jq -e '.tariffPerInitialPayloadByte == 1' \
  "$EVIDENCE/workroom/operator.json" >/dev/null
jq -e '.tariffPerInitialPayloadByte == "1"' \
  "$EVIDENCE/workroom/genesis.json" >/dev/null
sha256sum -c "$EVIDENCE/positive-input-sha256.txt" \
  >"$EVIDENCE/positive-input-recheck.txt"
sha256sum -c "$EVIDENCE/private-source-sha256.txt" \
  >"$EVIDENCE/private-source-recheck.txt"
echo "positive byte-tariff app/session base PASS"
