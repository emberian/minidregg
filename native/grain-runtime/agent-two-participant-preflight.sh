#!/bin/sh
# Fresh, read-only recipient gate for two agent controllers over one signed app.
# The SPK lifecycle owner creates the Store and native source artifacts first.
# This script never issues, reserves, submits, or dispatches an HTTP request.
# It checks the generation-bound event21/v2 profile, not the future event26
# lifetime-grant reconnect route; a hard generation advance needs fresh
# source-owned authorization before any further API dispatch.
set -eu
umask 077

if [ "$#" -ne 10 ]; then
  echo "usage: $0 HOST MINI CONFIG_A INGRESS_A RECEIPT_A CONFIG_B INGRESS_B RECEIPT_B NONCE_BASE NEW_EVIDENCE_DIR" >&2
  exit 2
fi
HOST=$1 MINI=$2 CONFIG_A=$3 INGRESS_A=$4 RECEIPT_A=$5
CONFIG_B=$6 INGRESS_B=$7 RECEIPT_B=$8 NONCE_BASE=$9 EVIDENCE=${10}
SELF=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)/$(basename -- "$0")
: "${QUALIFIED_HOST_SHA256:?set the source-qualified event22+event21 Host SHA}"
: "${QUALIFIED_MINI_SHA256:?set the committed public op55 Mini SHA}"
: "${SIGNED_GITWEB_SPK:?set exact signed GitWeb SPK path}"
: "${QUALIFIED_SPK_SHA256:?pin exact signed GitWeb SPK SHA}"
: "${SOURCE_PACKAGE_DESCRIPTOR:?set source-authored v1 package descriptor path}"
: "${QUALIFIED_PACKAGE_DESCRIPTOR_SHA256:?pin source-authored package descriptor SHA}"
: "${SOURCE_GITWEB_ROOTS:?set source-authored GitWeb roots JSON}"
: "${QUALIFIED_GITWEB_ROOTS_SHA256:?pin source-authored roots JSON SHA}"
: "${LAUNCH_QUALIFICATION:?set offline source-qualified launch result JSON}"
: "${LAUNCH_INSPECTION:?set retained source v2 descriptor inspection JSON}"
: "${LAUNCH_DESCRIPTOR:?set retained canonical v2 launch descriptor bytes}"
: "${SOURCE_ISSUE_INDEX_A:?set source-authored A issue-index file}"
: "${SOURCE_ISSUE_INDEX_B:?set source-authored B issue-index file}"
: "${QUALIFIED_ISSUE_INDEX_A_SHA256:?pin the source-authored A issue-index file}"
: "${QUALIFIED_ISSUE_INDEX_B_SHA256:?pin the source-authored B issue-index file}"
: "${FOREGROUND_RESERVE:?set explicit parent allowance for direct tool calls}"
: "${FOREGROUND_CHARGE:?set explicit parent charge for direct tool calls}"
case "$FOREGROUND_RESERVE" in ''|0|0*|*[!0-9]*) exit 2 ;; esac
case "$FOREGROUND_CHARGE" in ''|*[!0-9]*) exit 2 ;; esac
[ "${#FOREGROUND_RESERVE}" -le 18 ] && [ "${#FOREGROUND_CHARGE}" -le 18 ] || exit 2
[ "$FOREGROUND_CHARGE" -le "$FOREGROUND_RESERVE" ] || exit 2

for file in "$HOST" "$MINI" "$CONFIG_A" "$INGRESS_A" "$RECEIPT_A" \
    "$CONFIG_B" "$INGRESS_B" "$RECEIPT_B" "$SIGNED_GITWEB_SPK" \
    "$SOURCE_PACKAGE_DESCRIPTOR" "$SOURCE_GITWEB_ROOTS" \
    "$LAUNCH_QUALIFICATION" "$LAUNCH_INSPECTION" "$LAUNCH_DESCRIPTOR" \
    "$SOURCE_ISSUE_INDEX_A" "$SOURCE_ISSUE_INDEX_B"; do
  case "$file" in /*) ;; *) echo "input path is not absolute: $file" >&2; exit 2 ;; esac
  [ -f "$file" ] && [ ! -L "$file" ] || {
    echo "input absent or symlink: $file" >&2; exit 2;
  }
done
[ -x "$HOST" ] && [ -x "$MINI" ] || exit 2
case "$EVIDENCE" in /*) ;; *) echo "evidence path must be absolute" >&2; exit 2 ;; esac
[ ! -e "$EVIDENCE" ] && [ ! -L "$EVIDENCE" ] || exit 2
case "$NONCE_BASE" in ''|0*|*[!0-9]*) echo "nonce base must be positive canonical decimal" >&2; exit 2 ;; esac
[ "$NONCE_BASE" -lt 9223372036854775700 ] || exit 2
command -v jq >/dev/null
command -v sha256sum >/dev/null
command -v xxd >/dev/null
test "$(sha256sum "$HOST" | cut -d ' ' -f 1)" = "$QUALIFIED_HOST_SHA256"
test "$(sha256sum "$MINI" | cut -d ' ' -f 1)" = "$QUALIFIED_MINI_SHA256"
test "$(sha256sum "$SIGNED_GITWEB_SPK" | cut -d ' ' -f 1)" = \
  "$QUALIFIED_SPK_SHA256"
test "$(sha256sum "$SOURCE_PACKAGE_DESCRIPTOR" | cut -d ' ' -f 1)" = \
  "$QUALIFIED_PACKAGE_DESCRIPTOR_SHA256"
test "$(sha256sum "$SOURCE_GITWEB_ROOTS" | cut -d ' ' -f 1)" = \
  "$QUALIFIED_GITWEB_ROOTS_SHA256"
test "$(sha256sum "$SOURCE_ISSUE_INDEX_A" | cut -d ' ' -f 1)" = \
  "$QUALIFIED_ISSUE_INDEX_A_SHA256"
test "$(sha256sum "$SOURCE_ISSUE_INDEX_B" | cut -d ' ' -f 1)" = \
  "$QUALIFIED_ISSUE_INDEX_B_SHA256"

# The physical qualifier parses one signed SPK and retains the source v2
# canonical descriptor. This positive comparison rejects a v1-only package
# regardless of its caller-supplied SHA.
launch_sha=$(sha256sum "$LAUNCH_DESCRIPTOR" | cut -d ' ' -f 1)
jq -e --arg raw "$QUALIFIED_SPK_SHA256" --arg launch "$launch_sha" \
  --slurpfile roots "$SOURCE_GITWEB_ROOTS" \
  --slurpfile inspected "$LAUNCH_INSPECTION" '
  .protocol == "mini-spk-launch-qualified-v2" and
  .rawSha256 == $raw and .packageRoot == $roots[0].packageRoot and
  $inspected[0].type == "application-spk-launch-descriptor-v2" and
  .launchRoot == $inspected[0].root and
  .packageRoot == $inspected[0].packageRoot and
  .launchCanonicalSha256 == $launch and
  .createCount == ($inspected[0].createCommands | length | tostring) and
  .createDigests == [$inspected[0].createCommands[].digest] and
  .continueDigest == $inspected[0].continueCommand.digest
' "$LAUNCH_QUALIFICATION" >/dev/null
jq -er .canonical "$LAUNCH_INSPECTION" | xxd -r -p | cmp -s - "$LAUNCH_DESCRIPTOR"
jq -er .packageCanonicalHex "$LAUNCH_INSPECTION" | xxd -r -p | \
  cmp -s - "$SOURCE_PACKAGE_DESCRIPTOR"
for index_file in "$SOURCE_ISSUE_INDEX_A" "$SOURCE_ISSUE_INDEX_B"; do
  index=$(cat "$index_file")
  case "$index" in ''|*[!0-9]*|0*) echo "source issue index is not canonical" >&2; exit 2 ;; esac
  [ "$(wc -c < "$index_file" | tr -d ' ')" -le 80 ] || exit 2
done

check_pin() {
  config=$1 ingress=$2 receipt=$3 parent=$4 participant=$5 tool=$6 \
    purse=$7 payer=$8 provider=$9 provider_subject=${10} session=${11} \
    ticket=${12} issue_file=${13}
  ingress_sha=$(sha256sum "$ingress" | cut -d ' ' -f 1)
  issue_index=$(cat "$issue_file")
  jq -e --arg host "$HOST" --arg mini "$MINI" \
    --arg hostsha "$QUALIFIED_HOST_SHA256" --arg ingress "$ingress" \
    --arg ingresssha "$ingress_sha" --arg parent "$parent" \
    --arg participant "$participant" --arg tool "$tool" \
    --arg purse "$purse" --arg payer "$payer" \
    --arg provider "$provider" --arg providerSubject "$provider_subject" \
    --arg foregroundReserve "$FOREGROUND_RESERVE" \
    --arg foregroundCharge "$FOREGROUND_CHARGE" \
    --arg session "$session" --arg ticket "$ticket" \
    --arg issueIndex "$issue_index" \
    --slurpfile receipt "$receipt" '
    .toolTask.registeredSharedApplications[0] as $shared |
    .toolTask.allowedApplicationApiRoutes[0] as $route |
    .host == $host and .mini == $mini and
    .task == $parent and .subject == $participant and
    .toolTask.task == $tool and .dispatchTask.task == $purse and
    .dispatchTask.subject == $payer and
    .providerTask.task == $provider and
    .providerTask.subject == $providerSubject and
    ([.task,.toolTask.task,.dispatchTask.task,.providerTask.task] | unique | length) == 4 and
    ([.subject,.toolTask.subject,.dispatchTask.subject,.providerTask.subject] | unique | length) == 4 and
    .foregroundTool == {reserve:$foregroundReserve,charge:$foregroundCharge} and
    (.commands | any(.name == "hermes-acp" and
      .args[-1] == "/agent/hermes-acp")) and
    .toolTask.agentApiHostSha256 == $hostsha and
    (.hostSocket | type == "string" and startswith("/")) and
    (.dispatchTask.operatorSocket | type == "string" and startswith("/")) and
    (.toolTask.registeredSharedApplications | length) == 1 and
    (.toolTask.allowedApplicationApiRoutes | length) == 1 and
    $shared.name == "gitweb-app" and
    $shared.appTarget == "8401" and
    $shared.manifestTarget == "8402" and
    $shared.snapshotTarget == "8403" and
    $shared.ticketTarget == $ticket and
    $shared.issue.kind == "grainBackedEvent22" and
    $shared.issue.ingress == $ingress and
    $shared.issue.ingressSha256 == $ingresssha and
    $shared.issue.transactionId == $receipt[0].transactionId and
    $shared.issue.eventId == $receipt[0].eventId and
    $shared.issue.acceptedCount == $receipt[0].acceptedCount and
    $shared.issue.imageBoundary == $receipt[0].imageBoundary and
    $route.name == "gitweb-app" and $route.appResource == "8401" and
    $route.sessionResource == $session and $route.ticketResource == $ticket and
    $route.participantSubject == $participant and
    $route.parentTask == $parent and $route.purseResource == $purse and
    $route.signedApiPath == "/repo.git/" and
    $route.dispatchSelectors.packageManifest == "8402" and
    $route.dispatchSelectors.snapshotManifest == "8403" and
    $route.dispatchSelectors.issueIndex == $issueIndex
  ' "$config" >/dev/null
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (.transactionId | type == "string") and (.eventId | type == "string") and
    (.acceptedCount | type == "string" and test("^[1-9][0-9]*$")) and
    (.imageBoundary | type == "string")' "$receipt" >/dev/null
}

# The source-selected event index comes from the independently retained
# accepted issue inspection. It is never reconstructed from acceptedCount.
check_pin "$CONFIG_A" "$INGRESS_A" "$RECEIPT_A" 7920 10 7930 7940 12 7950 13 8420 8520 \
  "$SOURCE_ISSUE_INDEX_A"
check_pin "$CONFIG_B" "$INGRESS_B" "$RECEIPT_B" 7921 20 7931 7941 22 7951 23 8422 8521 \
  "$SOURCE_ISSUE_INDEX_B"
test "$(jq -er .hostConfig "$CONFIG_A")" = "$(jq -er .hostConfig "$CONFIG_B")"
test "$(jq -er .hostSocket "$CONFIG_A")" = "$(jq -er .hostSocket "$CONFIG_B")"
test "$INGRESS_A" != "$INGRESS_B"

mkdir -m 700 "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
sha256sum "$SELF" "$HOST" "$MINI" "$CONFIG_A" "$CONFIG_B" \
  "$INGRESS_A" "$INGRESS_B" "$RECEIPT_A" "$RECEIPT_B" \
  "$SIGNED_GITWEB_SPK" "$SOURCE_PACKAGE_DESCRIPTOR" \
  "$SOURCE_GITWEB_ROOTS" "$LAUNCH_QUALIFICATION" \
  "$LAUNCH_INSPECTION" "$LAUNCH_DESCRIPTOR" "$SOURCE_ISSUE_INDEX_A" \
  "$SOURCE_ISSUE_INDEX_B" >"$EVIDENCE/input-sha256.txt"

lookup() {
  label=$1 config=$2 ingress=$3 receipt=$4
  socket=$(jq -er .hostSocket "$config")
  transaction=$(jq -er .transactionId "$receipt")
  event=$(jq -er .eventId "$receipt")
  count=$(jq -er .acceptedCount "$receipt")
  boundary=$(jq -er .imageBoundary "$receipt")
  "$MINI" grain-share-issue-receipt-lookup --host "$HOST" \
    --config "$(jq -er .hostConfig "$config")" --socket "$socket" \
    --ingress "$ingress" --transaction-id "$transaction" \
    --event-id "$event" --accepted-count "$count" \
    --image-boundary "$boundary" --dir "$EVIDENCE/$label-op55" \
    >"$EVIDENCE/$label-op55.stdout"
  jq -e --slurpfile original "$receipt" '
    .type == "confirmed" and .confirmation == "replayed" and
    .transactionId == $original[0].transactionId and
    .eventId == $original[0].eventId and
    .acceptedCount == $original[0].acceptedCount and
    .imageBoundary == $original[0].imageBoundary
  ' "$EVIDENCE/$label-op55/outcome.json" >/dev/null
}
lookup a "$CONFIG_A" "$INGRESS_A" "$RECEIPT_A"
lookup b "$CONFIG_B" "$INGRESS_B" "$RECEIPT_B"

signed_read() {
  label=$1 config=$2 subject=$3 key=$4 nonce=$5 target=$6 capability=$7
  jq -n --arg subject "$subject" --arg nonce "$nonce" \
    --arg target "$target" --arg capability "$capability" \
    '{subject:$subject,nonce:$nonce,
      purpose:{type:"query",kind:"object",target:$target,view:"resource"},
      grants:[{kind:"object",target:$target,capability:$capability}]}' \
    >"$EVIDENCE/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$(jq -er .hostConfig "$config")" \
    --socket "$(jq -er .hostSocket "$config")" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" --view resource \
    --dir "$EVIDENCE/$label-read" >"$EVIDENCE/$label-read.stdout"
  jq -e --arg target "$target" '
    .type == "resource" and .page.grain.task == $target and
    (.page.root | type == "string" and test("^[0-9]+$"))
  ' "$EVIDENCE/$label-read/view.json" >/dev/null
  jq -e '(.imageBoundary | type == "string" and test("^[0-9]+$"))' \
    "$EVIDENCE/$label-read/challenge.json" >/dev/null
}
read_agent() {
  label=$1 config=$2 base=$3
  key=$(jq -er .toolTask.custodyKey "$config")
  subject=$(jq -er .toolTask.subject "$config")
  index=0
  for pair in 'appTarget appObserveCapability' \
    'manifestTarget manifestObserveCapability' \
    'snapshotTarget snapshotObserveCapability' \
    'ticketTarget ticketObserveCapability'; do
    target_field=${pair%% *}
    capability_field=${pair#* }
    target=$(jq -er --arg field "$target_field" \
      '.toolTask.registeredSharedApplications[0][$field]' "$config")
    capability=$(jq -er --arg field "$capability_field" \
      '.toolTask.registeredSharedApplications[0][$field]' "$config")
    signed_read "$label-$target_field" "$config" "$subject" "$key" \
      "$((base + index))" "$target" "$capability"
    index=$((index + 1))
  done
  parent=$(jq -er .task "$config")
  signed_read "$label-parent" "$config" "$(jq -er .subject "$config")" \
    "$(jq -er .custodyKey "$config")" "$((base + 4))" "$parent" \
    "$(jq -er .queryCapability "$config")"
  purse=$(jq -er .dispatchTask.task "$config")
  signed_read "$label-purse" "$config" "$(jq -er .dispatchTask.subject "$config")" \
    "$(jq -er .dispatchTask.custodyKey "$config")" "$((base + 5))" "$purse" \
    "$(jq -er .dispatchTask.queryCapability "$config")"
  test "$(jq -er .page.grain.generation "$EVIDENCE/$label-parent-read/view.json")" = \
    "$(jq -er .toolTask.allowedApplicationApiRoutes[0].parentGeneration "$config")"
  test "$(jq -er .page.grain.generation "$EVIDENCE/$label-purse-read/view.json")" = \
    "$(jq -er .toolTask.allowedApplicationApiRoutes[0].dispatchGeneration "$config")"
}
read_agent a "$CONFIG_A" "$NONCE_BASE"
read_agent b "$CONFIG_B" "$((NONCE_BASE + 10))"
same_image=$(jq -er .imageBoundary "$EVIDENCE/a-appTarget-read/challenge.json")
for challenge in "$EVIDENCE"/*-read/challenge.json; do
  test "$(jq -er .imageBoundary "$challenge")" = "$same_image"
done
test "$(jq -er .page.root "$EVIDENCE/a-appTarget-read/view.json")" = \
  "$(jq -er .page.root "$EVIDENCE/b-appTarget-read/view.json")"
sha256sum -c "$EVIDENCE/input-sha256.txt" >"$EVIDENCE/input-postcheck.txt"
echo "two distinct agent recipients: op55 exact replay and current signed views passed; no API dispatch"
