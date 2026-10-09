#!/usr/bin/env bash
# Fresh receiving-path evidence for durable client receipt continuity.
# Fixture dependencies: genesis.sh and genesis-params.example.json beside this file.
# No builds. VERIFIER is the credential-signature verifier; HOST also supplies the
# independent local continuity verifier. Only this script's service PID is stopped.
set -euo pipefail
umask 077
if [[ $# != 5 || ${1:-} == --help ]]; then
  echo "usage: $0 HOST MINI STORE VERIFIER NEW-ABSOLUTE-RUNROOT" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 RUN=$5
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
for path in "$HOST" "$MINI" "$STORE" "$VERIFIER" "$RUN"; do
  [[ $path == /* ]] || { echo "path must be absolute: $path" >&2; exit 2; }
done
for binary in "$HOST" "$MINI" "$STORE" "$VERIFIER"; do
  [[ -x $binary ]] || { echo "not executable: $binary" >&2; exit 2; }
done
for tool in jq sha256sum mktemp; do command -v "$tool" >/dev/null; done
[[ ! -e $RUN && ! -L $RUN ]] || { echo "refusing existing run root: $RUN" >&2; exit 2; }
mkdir "$RUN"
RUN=$(CDPATH='' cd -- "$RUN" && pwd)
mkdir "$RUN/logs" "$RUN/fixture" "$RUN/proofs"
ROWS=$RUN/rows.tsv
printf 'step\tverdict\n' >"$ROWS"
SERVER=
SOCKET_DIR=$(mktemp -d /tmp/mini-continuity.XXXXXX)
SOCKET=$SOCKET_DIR/host.sock
printf '%s\n' "$SOCKET_DIR" >"$RUN/socket-directory.txt"
stop_server() {
  if [[ -n $SERVER ]]; then
    kill "$SERVER" 2>/dev/null || true
    wait "$SERVER" 2>/dev/null || true
    SERVER=
    # This socket was created by the child we just reaped; no other socket is touched.
    [[ ! -S $SOCKET ]] || rm "$SOCKET"
  fi
}
trap stop_server EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
run() {
  local label=$1; shift
  if "$@" >"$RUN/logs/$label.out" 2>"$RUN/logs/$label.err"; then
    printf '%s\tPASS\n' "$label" >>"$ROWS"
  else
    local rc=$?
    printf '%s\tFAIL(%s)\n' "$label" "$rc" >>"$ROWS"
    echo "continuity journey failed at $label; see $RUN/logs/$label.err" >&2
    return "$rc"
  fi
}
refused() {
  local label=$1; shift
  if "$@" >"$RUN/logs/$label.out" 2>"$RUN/logs/$label.err"; then
    printf '%s\tUNEXPECTED-SUCCESS\n' "$label" >>"$ROWS"
    echo "expected refusal at $label" >&2
    return 1
  fi
  printf '%s\tPASS(refused)\n' "$label" >>"$ROWS"
}
start_server() {
  local label=$1
  "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$RUN/logs/$label.out" 2>"$RUN/logs/$label.err" &
  SERVER=$!
  printf '%s\n' "$SERVER" >"$RUN/$label.pid"
  for ((i=0; i<600; i++)); do
    [[ ! -S $SOCKET ]] || return 0
    kill -0 "$SERVER" 2>/dev/null || { echo "service exited; see $RUN/logs/$label.err" >&2; return 1; }
    sleep 0.1
  done
  echo "service socket did not appear" >&2
  return 1
}

run sponsor-key "$MINI" keygen --secret "$RUN/sponsor.key" --public "$RUN/sponsor.pub"
run clock-key "$MINI" keygen --secret "$RUN/clock.key" --public "$RUN/clock.pub"
PUBLIC=$(od -An -tx1 -v "$RUN/sponsor.pub" | tr -d ' \n')
CLOCK_PUBLIC=$(od -An -tx1 -v "$RUN/clock.pub" | tr -d ' \n')
cp "$HERE/genesis-params.example.json" "$RUN/params.json"
. "$HERE/journey.d/lib/genesis-params.sh"
resolve_params_sh "$HERE/../.." || exit 2
sh "$GENESIS_PARAMS_SH" fill-genesis "$RUN/params.json"
run genesis sh "$HERE/genesis.sh" "$RUN/params.json" "$PUBLIC" "$CLOCK_PUBLIC" \
  "$HOST" "$STORE" "$VERIFIER" "$RUN/fixture"
run bootstrap "$MINI" bootstrap --host "$HOST" --config "$RUN/fixture/operator.json" \
  --source "$RUN/fixture/genesis.json" --dir "$RUN/deployment"
CONFIG=$RUN/deployment/pinned-config.json
start_server service-first
WS=$RUN/workspace
run workspace-init "$MINI" workspace --action init --dir "$WS" --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --key "$RUN/sponsor.key" --subject "$(jq -r '.sponsor.subject' "$RUN/params.json")" \
  --birth-context "$RUN/fixture/sponsor-birth-context.json" --namespace-root "$RUN/namespace"
run factory-import "$MINI" workspace --action import --dir "$WS" --name factory --kind object \
  --target "$(jq -r .factoryId "$RUN/params.json")" \
  --observe-capability "$(jq -r .sponsor.factoryObserveCapabilityId "$RUN/params.json")" \
  --control-capability "$(jq -r .factoryControllerCapability "$RUN/params.json")"
printf '%s\n' '{"type":"all","predicates":[]}' >"$RUN/open-law.json"
run stream-create "$MINI" workspace --action create --dir "$WS" --name events --storage stream \
  --predicate "$RUN/open-law.json"
run continuity-init "$MINI" workspace --action continuity-init --dir "$WS" --name events
jq -e '.receiptContinuity == "minidregg-continuity-v1"' "$WS/workspace.json" >/dev/null
CUSTODY=$WS/receipt-continuity
cp "$CUSTODY/anchor.json" "$RUN/anchor-initial.json"
run guarded-read-before "$MINI" workspace --action read --dir "$WS" --name events
OLD_ATTEMPT=$(sed -n 's/^workspace read attempt: //p' "$RUN/logs/guarded-read-before.err")
[[ -f $OLD_ATTEMPT/challenge.json ]]
# Check source-owned normalization: deployment height is deliberately nonzero.
run normalize-observation "$HOST" "$CONFIG" continuity-point "$OLD_ATTEMPT/challenge.json" "$RUN/normalized-point.json"
jq -e --slurpfile a "$RUN/anchor-initial.json" '. == $a[0].point' "$RUN/normalized-point.json" >/dev/null
[[ $(jq -r .height "$OLD_ATTEMPT/challenge.json") -gt $(jq -r .height "$RUN/normalized-point.json") ]]

# Fault injection keeps the trusted wrapper immutable after pinning, and only
# corrupts an actually received forward proof before the real Lean verifier runs.
TAMPER_VERIFIER=$RUN/tamper-verifier.sh
{
  printf '#!/usr/bin/env bash\nset -euo pipefail\n'
  printf 'REAL_HOST=%q\nTAMPER_MARKER=%q\n' "$HOST" "$RUN/tamper-enabled"
  cat <<'WRAPPER'
if [[ ${2:-} == continuity-verify && -f $TAMPER_MARKER ]] && jq -e '.suffix | length > 0' "$4" >/dev/null; then
  jq '.suffix[0] = (if .suffix[0] == "0" then "1" else "0" end)' "$4" >"$4.tampered"
  mv "$4.tampered" "$4"
fi
exec "$REAL_HOST" "$@"
WRAPPER
} >"$TAMPER_VERIFIER"
chmod 700 "$TAMPER_VERIFIER"
TWS=$RUN/tamper-workspace
run tamper-workspace-init "$MINI" workspace --action init --dir "$TWS" --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --key "$RUN/sponsor.key" --subject "$(jq -r '.sponsor.subject' "$RUN/params.json")"
run tamper-reference "$MINI" workspace --action import --dir "$TWS" --name events --kind object \
  --target "$(jq -r .target "$WS/refs/events.json")" \
  --observe-capability "$(jq -r .observeCapability "$WS/refs/events.json")" \
  --operation-capability "$(jq -r .operationCapability "$WS/refs/events.json")"
run tamper-continuity-init "$MINI" workspace --action continuity-init --dir "$TWS" --name events --verifier "$TAMPER_VERIFIER"
cp "$TWS/receipt-continuity/anchor.json" "$RUN/tamper-anchor-initial.json"

printf '%s\n' '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"events","payload":{"type":"append","topic":"continuity","text":"durably observed"}}]}' >"$RUN/append.json"
run append-propose "$MINI" workspace --action propose --dir "$WS" --request "$RUN/append.json" --proposal-id append
run append-submit "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/append/intent.json" \
  --attempt "$WS/attempts/append"
jq -e '.type == "confirmed"' "$WS/attempts/append/outcome.json" >/dev/null
# The mutation's successful output itself must already be covered by durable custody.
jq -e --slurpfile r "$WS/attempts/append/outcome.json" \
  '.point == {height:$r[0].acceptedCount,worldRoot:$r[0].worldRoot}' "$CUSTODY/anchor.json" >/dev/null
cp "$CUSTODY/anchor.json" "$RUN/anchor-at-submit-ack.json"
# A protected --direct retry must fail before dispatch; no retry response is retained.
refused protected-direct-pre-send "$MINI" retry --attempt "$WS/attempts/append" --mode lookup --direct true
grep -q 'require the pinned socket before sending' "$RUN/logs/protected-direct-pre-send.err"
[[ ! -s $RUN/logs/protected-direct-pre-send.out ]]
[[ -z $(find "$WS/attempts/append" -name 'retry-*.bin' -print -quit) ]]
run guarded-read-after "$MINI" workspace --action read --dir "$WS" --name events
NEW_ATTEMPT=$(sed -n 's/^workspace read attempt: //p' "$RUN/logs/guarded-read-after.err")
cp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"
[[ $(jq -r .point.height "$RUN/anchor-advanced.json") -gt $(jq -r .point.height "$RUN/anchor-initial.json") ]]
touch "$RUN/tamper-enabled"
refused client-tampered-received-proof "$MINI" workspace --action read --dir "$TWS" --name events
[[ ! -s $RUN/logs/client-tampered-received-proof.out ]]
# Ensure refusal really came from the local Lean proof boundary, not an unrelated error.
grep -q 'local Lean verifier refused continuity proof' "$RUN/logs/client-tampered-received-proof.err"
cmp "$TWS/receipt-continuity/anchor.json" "$RUN/tamper-anchor-initial.json"
run verifier-upgrade "$MINI" workspace --action continuity-verifier --dir "$TWS" --verifier "$HOST"
cmp "$TWS/receipt-continuity/anchor.json" "$RUN/tamper-anchor-initial.json"
run read-after-verifier-upgrade "$MINI" workspace --action read --dir "$TWS" --name events
jq -e --slurpfile a "$RUN/anchor-advanced.json" '.point == $a[0].point' "$TWS/receipt-continuity/anchor.json" >/dev/null
refused ordinary-old-receipt "$MINI" workspace --action continuity-check --dir "$WS" --attempt "$OLD_ATTEMPT"
run explicit-historical "$MINI" workspace --action continuity-check --dir "$WS" --attempt "$OLD_ATTEMPT" --historical true
cmp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"

# Verify and attack an actual received proof. All integers remain strings; jq
# never rewrites the pinned config (whose seed may exceed its numeric precision).
PROOF=
while IFS= read -r candidate; do
  if jq -e '.suffix | length > 0' "$candidate" >/dev/null; then PROOF=$candidate; break; fi
done < <(find "$WS/attempts" -name response.json -type f)
[[ -n $PROOF ]]
cp "$PROOF" "$RUN/proofs/good-response.json"
cp "$(dirname -- "$PROOF")/request.json" "$RUN/proofs/good-request.json"
run verify-received-proof "$HOST" "$CONFIG" continuity-verify "$RUN/proofs/good-request.json" \
  "$RUN/proofs/good-response.json" "$RUN/proofs/good-result.json"
jq '.suffix[0] = (if .suffix[0] == "0" then "1" else "0" end)' \
  "$PROOF" >"$RUN/proofs/tampered-suffix.json"
refused tampered-suffix "$HOST" "$CONFIG" continuity-verify "$RUN/proofs/good-request.json" \
  "$RUN/proofs/tampered-suffix.json" "$RUN/proofs/tampered-suffix-result.json"
jq -e '.toSiblings | length > 0' "$PROOF" >/dev/null
jq '.toSiblings[0] = (if .toSiblings[0] == "0" then "1" else "0" end)' \
  "$PROOF" >"$RUN/proofs/tampered-opening.json"
refused tampered-opening "$HOST" "$CONFIG" continuity-verify "$RUN/proofs/good-request.json" \
  "$RUN/proofs/tampered-opening.json" "$RUN/proofs/tampered-opening-result.json"
jq '.identity.expectedSeed = (if .identity.expectedSeed == "0" then "1" else "0" end)' \
  "$RUN/proofs/good-request.json" >"$RUN/proofs/wrong-identity.json"
refused wrong-deployment "$HOST" "$CONFIG" continuity-verify "$RUN/proofs/wrong-identity.json" \
  "$PROOF" "$RUN/proofs/wrong-identity-result.json"
jq '.target.worldRoot = (if .target.worldRoot == "0" then "1" else "0" end)' \
  "$RUN/proofs/good-request.json" >"$RUN/proofs/wrong-root.json"
refused wrong-target-root "$HOST" "$CONFIG" continuity-verify "$RUN/proofs/wrong-root.json" \
  "$PROOF" "$RUN/proofs/wrong-root-result.json"
for name in tampered-suffix tampered-opening wrong-identity wrong-root; do
  [[ ! -s $RUN/proofs/$name-result.json ]]
done
cmp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"

mkdir "$WS/attempts/same-height-fork"
jq '.worldRoot = (if .worldRoot == "0" then "1" else "0" end)' \
  "$NEW_ATTEMPT/challenge.json" >"$WS/attempts/same-height-fork/challenge.json"
refused same-height-fork "$MINI" workspace --action continuity-check --dir "$WS" \
  --attempt "$WS/attempts/same-height-fork" --historical true
cmp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"
# Missing individual and whole-directory custody must fail before exposing a read.
mv "$CUSTODY/anchor.json" "$CUSTODY/anchor.saved.json"
refused missing-anchor "$MINI" workspace --action read --dir "$WS" --name events
[[ ! -s $RUN/logs/missing-anchor.out ]]
mv "$CUSTODY/anchor.saved.json" "$CUSTODY/anchor.json"
mv "$CUSTODY" "$WS/receipt-continuity.saved"
refused missing-custody "$MINI" workspace --action read --dir "$WS" --name events
[[ ! -s $RUN/logs/missing-custody.out ]]
refused deleted-memory-rebootstrap "$MINI" workspace --action continuity-init --dir "$WS" --name events
mv "$WS/receipt-continuity.saved" "$CUSTODY"

# A write may be accepted while the client refuses its acknowledgment. Keep the
# exact call, then recover by lookup; never rebuild or resubmit a changed intent.
run verifier-fault-enabled "$MINI" workspace --action continuity-verifier --dir "$TWS" --verifier "$TAMPER_VERIFIER"
run ack-fault-propose "$MINI" workspace --action propose --dir "$TWS" --request "$RUN/append.json" --proposal-id ack-fault
cp "$TWS/receipt-continuity/anchor.json" "$RUN/anchor-before-ack-fault.json"
refused accepted-write-unacknowledged "$MINI" workspace --action submit --dir "$TWS" \
  --intent "$TWS/proposals/ack-fault/intent.json" --attempt "$TWS/attempts/ack-fault"
[[ ! -s $RUN/logs/accepted-write-unacknowledged.out && -s $TWS/attempts/ack-fault/call.bin ]]
grep -q 'mutation may already be accepted' "$RUN/logs/accepted-write-unacknowledged.err"
jq -e '.type == "confirmed"' "$TWS/attempts/ack-fault/outcome.json" >/dev/null
cmp "$TWS/receipt-continuity/anchor.json" "$RUN/anchor-before-ack-fault.json"
rm "$RUN/tamper-enabled"
run recover-unacknowledged "$MINI" workspace --action recover --dir "$TWS" --attempt "$TWS/attempts/ack-fault"
jq -e --slurpfile r "$TWS/attempts/ack-fault/outcome.json" \
  '.point == {height:$r[0].acceptedCount,worldRoot:$r[0].worldRoot}' "$TWS/receipt-continuity/anchor.json" >/dev/null
run guarded-read-after-recovery "$MINI" workspace --action read --dir "$WS" --name events
cp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"

stop_server
start_server service-restarted
run guarded-read-restarted "$MINI" workspace --action read --dir "$WS" --name events
cmp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"
run historical-restarted "$MINI" workspace --action continuity-check --dir "$WS" --attempt "$OLD_ATTEMPT" --historical true
cmp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"
sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" "$HERE/genesis.sh" \
  "$RUN/params.json" "$0" >"$RUN/provenance.sha256"
printf 'CONTINUITY RECEIVING PASS\n%s\n' "$ROWS"
