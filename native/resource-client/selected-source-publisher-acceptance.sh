#!/bin/sh
# Source Mini authorization and exact protected fn POST for one selected public
# version. The prepared directory comes from selected-release-acceptance.sh with
# SELECTED_RELEASE_STOP_AFTER_ORIGINAL=1; no recipient mutation has occurred.
set -eu
umask 077

if [ "$#" -ne 5 ]; then
  echo "usage: $0 HOST MINI PREPARED-DIR PRIVATE-POST.json NEW-EVIDENCE-DIR" >&2
  exit 2
fi
HOST=$1
MINI=$2
PREPARED=$3
POST_CONFIG=$4
EVIDENCE=$5
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)

for executable in "$HOST" "$MINI"; do
  [ -x "$executable" ] || { echo "not executable: $executable" >&2; exit 2; }
done
for required in "$PREPARED/source/deployment/pinned-config.json" \
    "$PREPARED/candidate-original/packet.bin" \
    "$PREPARED/candidate-original/article.eml" \
    "$PREPARED/owner.key" "$PREPARED/wrong-signer.key" "$POST_CONFIG"; do
  [ -f "$required" ] || { echo "missing input: $required" >&2; exit 2; }
done
[ ! -e "$PREPARED/recipient/original-attempt" ] || {
  echo "recipient was already mutated; require a pre-admission candidate" >&2; exit 2;
}
[ ! -e "$EVIDENCE" ] || { echo "refusing existing evidence directory" >&2; exit 2; }
mkdir -m 700 "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
SOURCE_CONFIG=$PREPARED/source/deployment/pinned-config.json
PACKET=$PREPARED/candidate-original/packet.bin
ARTICLE=$PREPARED/candidate-original/article.eml
DROP_HOST=$HERE/selected-source-drop-reply.sh
SCRIPT=$HERE/selected-source-publisher-acceptance.sh
CERTIFICATE=$(jq -er '.certificatePath' "$POST_CONFIG")
[ -f "$CERTIFICATE" ] || { echo "missing pinned certificate" >&2; exit 2; }
[ -x "$DROP_HOST" ] || { echo "missing test-only drop-reply shim" >&2; exit 2; }
shasum -a 256 "$HOST" "$MINI" "$SCRIPT" "$DROP_HOST" \
  "$SOURCE_CONFIG" "$PACKET" "$ARTICLE" "$POST_CONFIG" "$CERTIFICATE" \
  >"$EVIDENCE/SHA256SUMS.start.private"

"$MINI" selected-source-sign --host "$HOST" --config "$SOURCE_CONFIG" \
  --packet "$PACKET" --delegate-capability 61 \
  --key "$PREPARED/wrong-signer.key" --dir "$EVIDENCE/wrong-sign" \
  >"$EVIDENCE/wrong-sign.stdout"
if "$MINI" selected-source-publish --host "$HOST" --config "$SOURCE_CONFIG" \
    --ingress "$EVIDENCE/wrong-sign/ingress.bin" --article "$ARTICLE" \
    --state-dir "$EVIDENCE/wrong-publish" --post-config "$POST_CONFIG" \
    >"$EVIDENCE/wrong-publish.stdout" 2>"$EVIDENCE/wrong-publish.stderr"; then
  echo "wrong source signer unexpectedly published" >&2; exit 1
fi
[ ! -e "$EVIDENCE/wrong-publish/fn-post-attempt.json" ] || {
  echo "fn POST was attempted after source refusal" >&2; exit 1;
}
jq -e '.type == "refused"' "$EVIDENCE/wrong-publish/source-submit.json" >/dev/null

"$MINI" selected-source-sign --host "$HOST" --config "$SOURCE_CONFIG" \
  --packet "$PACKET" --delegate-capability 61 \
  --key "$PREPARED/owner.key" --dir "$EVIDENCE/owner-sign" \
  >"$EVIDENCE/owner-sign.stdout"
# The test shim invokes the real qualified Host for op24, saves its native
# outcome, then drops only the caller's response. Publisher recovery must use
# exact op25 lookup and still make just one network POST.
export SELECTED_SOURCE_DROP_REAL_HOST="$HOST"
export SELECTED_SOURCE_DROP_EVIDENCE="$EVIDENCE"
"$MINI" selected-source-publish --host "$DROP_HOST" --config "$SOURCE_CONFIG" \
  --ingress "$EVIDENCE/owner-sign/ingress.bin" --article "$ARTICLE" \
  --state-dir "$EVIDENCE/owner-publish" --post-config "$POST_CONFIG" \
  >"$EVIDENCE/owner-publish.stdout"

[ "$(cat "$EVIDENCE/owner-publish/source-submit.bin")" = truncated ]
"$HOST" "$SOURCE_CONFIG" inspect outcome \
  "$EVIDENCE/drop-native-outcome.bin" "$EVIDENCE/drop-native-outcome.json"
jq -e '.type == "confirmed" and .confirmation == "installed"' \
  "$EVIDENCE/drop-native-outcome.json" >/dev/null
jq -e '.type == "confirmed" and .confirmation == "replayed"' \
  "$EVIDENCE/owner-publish/source-lookup-000.json" >/dev/null
jq -e '.type == "confirmed" and .confirmation == "replayed"' \
  "$EVIDENCE/owner-publish/source-proof-lookup-000.json" >/dev/null
for field in transactionId eventId acceptedCount worldRoot; do
  original=$(jq -er --arg field "$field" '.[$field]' "$EVIDENCE/drop-native-outcome.json")
  retained=$(jq -er --arg field "$field" '.[$field]' \
    "$EVIDENCE/owner-publish/source-proof-lookup-000.json")
  [ "$original" = "$retained" ] || {
    echo "exact source lookup changed $field" >&2; exit 1
  }
done
jq -e '.type == "minidregg-selected-fn-post-v1" and
  (.status == "accepted" or .status == "already-stored")' \
  "$EVIDENCE/owner-publish/fn-post-result.json" >/dev/null

# Reentry is an exact local recovery check. It must not add another POST
# attempt or change the accepted result.
cp "$EVIDENCE/owner-publish/fn-post-result.json" "$EVIDENCE/post-result-before.json"
"$MINI" selected-source-publish --host "$DROP_HOST" --config "$SOURCE_CONFIG" \
  --ingress "$EVIDENCE/owner-sign/ingress.bin" --article "$ARTICLE" \
  --state-dir "$EVIDENCE/owner-publish" --post-config "$POST_CONFIG" \
  >"$EVIDENCE/owner-reentry.stdout"
cmp "$EVIDENCE/post-result-before.json" \
  "$EVIDENCE/owner-publish/fn-post-result.json"
test "$(find "$EVIDENCE/owner-publish" -name 'fn-post-attempt*' | wc -l | tr -d ' ')" = 1

shasum -a 256 "$HOST" "$MINI" "$SCRIPT" "$DROP_HOST" \
  "$SOURCE_CONFIG" "$PACKET" "$ARTICLE" "$POST_CONFIG" "$CERTIFICATE" \
  >"$EVIDENCE/SHA256SUMS.end-inputs.private"
cmp "$EVIDENCE/SHA256SUMS.start.private" \
  "$EVIDENCE/SHA256SUMS.end-inputs.private"
cp "$EVIDENCE/SHA256SUMS.end-inputs.private" "$EVIDENCE/SHA256SUMS.end.private"
shasum -a 256 \
  "$EVIDENCE/owner-sign/ingress.bin" \
  "$EVIDENCE/drop-native-outcome.bin" \
  "$EVIDENCE/owner-publish/source-submit.bin" \
  "$EVIDENCE/owner-publish/source-lookup-000.bin" \
  "$EVIDENCE/owner-publish/source-proof-lookup-000.bin" \
  "$EVIDENCE/owner-publish/fn-post-result.json" \
  >>"$EVIDENCE/SHA256SUMS.end.private"
echo "selected source authorization and retained accepted fn result PASS; one local POST marker, network count not independently measured; recipient fn poll/admission separate"
