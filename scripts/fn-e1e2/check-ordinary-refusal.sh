#!/bin/sh
# Public CLI refusal probe after setup-mini.sh's accepted cap-63 delegation.
set -eu
if [ "$#" -ne 2 ]; then
  echo "usage: $0 MINIDREGG_HOST SETUP_DIRECTORY" >&2
  exit 2
fi
HOST=$1
ROOT=$2
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
MINI=${MINI:-"$REPO/native/resource-client/target/debug/mini"}
CONFIG=$ROOT/deployment/pinned-config.json
SUBJECT=$(jq -er '.birth.resources[0].owner' "$ROOT/birth-intent.json")
ORDINARY=$(jq -er '.enrollments[1].key.subject' "$ROOT/genesis.json")
jq -e '.type == "confirmed" and .confirmation == "installed" and .acceptedCount == "2"' \
  "$ROOT/delegate-attempt/outcome.json" >/dev/null
if [ -e "$ROOT/ordinary-denied-attempt" ]; then
  echo "refusing to replace ordinary-denied-attempt" >&2
  exit 2
fi

cat >"$ROOT/gateway-before-denial.json" <<EOF
{"subject":"$SUBJECT","nonce":"40001",
 "purpose":{"type":"query","kind":"object","target":"600","view":"resource"},
 "grants":[{"kind":"object","target":"600","capability":"61"}]}
EOF
"$MINI" query --host "$HOST" --config "$CONFIG" \
  --intent "$ROOT/gateway-before-denial.json" --key "$ROOT/custody.key" \
  --view resource --dir "$ROOT/gateway-before-denial" \
  >"$ROOT/gateway-before-denial.stdout"
TARGET_ROOT=$(jq -er '.page.root' "$ROOT/gateway-before-denial/view.json")
AUTHORITY_ROOT=$(jq -er '.signing[0].authorityRoot' "$ROOT/gateway-before-denial/challenge.json")
BEFORE_HEIGHT=$(jq -er '.height' "$ROOT/gateway-before-denial/challenge.json")

jq -n --arg ordinary "$ORDINARY" --arg targetRoot "$TARGET_ROOT" \
  --arg authorityRoot "$AUTHORITY_ROOT" \
  '{subject:$ordinary,nonce:"40002",purpose:{type:"prepare",draft:{type:"invoke",
    command:{subject:$ordinary,expectedAuthorityRoot:$authorityRoot,nonce:"40003",
      targets:[{kind:"object",target:"600",capability:"63",observeCapability:null,
        schemaVersion:"1",expectedTargetRoot:$targetRoot,
        payload:{type:"content",actions:[{type:"createDocument",rootElement:"1001",
          schema:"1",body:{type:"container",children:[]}}]}}]}}},
    grants:[{kind:"object",target:"600",capability:"63"}]}' \
  >"$ROOT/ordinary-denied-intent.json"
if "$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$ROOT/ordinary-denied-intent.json" --key "$ROOT/ordinary.key" \
  --dir "$ROOT/ordinary-denied-attempt" \
  >"$ROOT/ordinary-denied.stdout" 2>"$ROOT/ordinary-denied.stderr"; then
  echo "ordinary signer unexpectedly mutated gateway resource" >&2
  exit 1
fi
if ! grep -Fq 'observation refused' "$ROOT/ordinary-denied.stderr"; then
  echo "ordinary submit failed for a reason other than observation refusal" >&2
  cat "$ROOT/ordinary-denied.stderr" >&2
  exit 1
fi

"$MINI" query --host "$HOST" --config "$CONFIG" \
  --intent "$ROOT/gateway-before-denial.json" --key "$ROOT/custody.key" \
  --view resource --dir "$ROOT/gateway-after-denial" \
  >"$ROOT/gateway-after-denial.stdout"
AFTER_HEIGHT=$(jq -er '.height' "$ROOT/gateway-after-denial/challenge.json")
AFTER_ROOT=$(jq -er '.page.root' "$ROOT/gateway-after-denial/view.json")
if [ "$BEFORE_HEIGHT" != "$AFTER_HEIGHT" ] || [ "$TARGET_ROOT" != "$AFTER_ROOT" ]; then
  echo "refusal changed Store height or target root" >&2
  exit 1
fi
printf 'ordinary subject %s with accepted delegated cap 63 refused; height %s and target root unchanged\n' \
  "$ORDINARY" "$AFTER_HEIGHT"
cat "$ROOT/ordinary-denied.stderr"
