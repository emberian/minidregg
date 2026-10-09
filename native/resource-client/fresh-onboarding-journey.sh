#!/usr/bin/env bash
# Fresh receiving-path evidence for automatic first continuity trust.
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
REF=$(jq -c '{name:"factory",kind:"object",target:(.factoryId|tostring),observeCapability:(.sponsor.factoryObserveCapabilityId|tostring)}' "$RUN/params.json")
run fresh-init "$MINI" workspace --action init --dir "$WS" --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --key "$RUN/sponsor.key" --subject "$(jq -r '.sponsor.subject' "$RUN/params.json")" \
  --birth-context "$RUN/fixture/sponsor-birth-context.json" --namespace-root "$RUN/namespace" \
  --continuity-ref "$REF"
run factory-import "$MINI" workspace --action import --dir "$WS" --name factory --kind object \
  --target "$(jq -r .factoryId "$RUN/params.json")" \
  --observe-capability "$(jq -r .sponsor.factoryObserveCapabilityId "$RUN/params.json")" \
  --control-capability "$(jq -r .factoryControllerCapability "$RUN/params.json")"
refused pending-read "$MINI" workspace --action read --dir "$WS" --name factory
[[ ! -s $RUN/logs/pending-read.out ]]
run automatic-baseline "$MINI" workspace --action onboard --dir "$WS"
jq -e '.status == "established" and .point.height == "0"' "$RUN/logs/automatic-baseline.out" >/dev/null
CUSTODY=$WS/receipt-continuity
cp "$CUSTODY/anchor.json" "$RUN/anchor-initial.json"
cp "$WS/receipt-continuity.pending.json" "$RUN/enrollment-initial.json"
jq '.candidate.request' "$RUN/enrollment-initial.json" >"$RUN/proofs/request.json"
jq '.candidate.response' "$RUN/enrollment-initial.json" >"$RUN/proofs/response.json"
run verify-initial-candidate "$HOST" "$CONFIG" continuity-verify "$RUN/proofs/request.json" \
  "$RUN/proofs/response.json" "$RUN/proofs/result.json"
run guarded-read "$MINI" workspace --action read --dir "$WS" --name factory
OLD_ATTEMPT=$(sed -n 's/^workspace read attempt: //p' "$RUN/logs/guarded-read.err")
printf '%s\n' '{"type":"all","predicates":[]}' >"$RUN/open-law.json"
run guarded-create "$MINI" workspace --action create --dir "$WS" --name events --storage stream \
  --predicate "$RUN/open-law.json"
cp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"
[[ $(jq -r .point.height "$RUN/anchor-advanced.json") -gt 0 ]]
run repeat-onboard "$MINI" workspace --action onboard --dir "$WS"
jq -e '.status == "verified"' "$RUN/logs/repeat-onboard.out" >/dev/null
cmp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"
cmp "$WS/receipt-continuity.pending.json" "$RUN/enrollment-initial.json"
run historical "$MINI" workspace --action continuity-check --dir "$WS" --attempt "$OLD_ATTEMPT" --historical true
cmp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"
# Completed first-use evidence must never restore missing advancing custody.
mv "$CUSTODY/anchor.json" "$RUN/anchor.saved.json"
refused lost-completed-anchor "$MINI" workspace --action onboard --dir "$WS"
[[ ! -s $RUN/logs/lost-completed-anchor.out && ! -e $CUSTODY/anchor.json ]]
mv "$RUN/anchor.saved.json" "$CUSTODY/anchor.json"
stop_server
start_server service-restarted
run restarted-onboard "$MINI" workspace --action onboard --dir "$WS"
cmp "$CUSTODY/anchor.json" "$RUN/anchor-advanced.json"
cmp "$WS/receipt-continuity.pending.json" "$RUN/enrollment-initial.json"
sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" "$HERE/genesis.sh" \
  "$RUN/params.json" "$0" >"$RUN/provenance.sha256"
printf 'FRESH ONBOARDING RECEIVING PASS\n%s\n' "$ROWS"
