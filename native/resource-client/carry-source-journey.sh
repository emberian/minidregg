#!/usr/bin/env bash
# Retained old-profile source fixture for the actual checked-carry journey.
# Fixture dependencies: genesis.sh and genesis-params.example.json beside this file.
# No builds. VERIFIER is the credential-signature verifier; HOST also supplies the
# independent local continuity verifier. Only this script's service PID is stopped.
set -euo pipefail
umask 077
if [[ $# != 6 || ${1:-} == --help ]]; then
  echo "usage: $0 HOST MINI STORE VERIFIER NEW-ABSOLUTE-RUNROOT OLD-SOURCE" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 RUN=$5
HERE=$6/native/resource-client
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


# A useful document, deliberately using atom ids whose encoded-byte ordering
# must not replace the old reader's numeric ordering during conversion.
run document-create "$MINI" workspace --action create --dir "$WS" --name notes --storage content \
  --predicate "$RUN/open-law.json"
printf '%s\n' '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"notes","payload":{"type":"content","actions":[{"type":"createDocument","rootElement":"1","schema":"0","body":{"type":"runs","runs":[]}},{"type":"createAtom","atom":"255","kind":{"type":"text"},"payload":"6f6c642070726f66696c65206669727374206c696e65"},{"type":"createAtom","atom":"256","kind":{"type":"text"},"payload":"7072657365727665206d65207468726f756768207468652075706772616465"}]}}]}' >"$RUN/document.json"
run document-propose "$MINI" workspace --action propose --dir "$WS" --request "$RUN/document.json" --proposal-id document
run document-submit "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/document/intent.json" --attempt "$WS/attempts/document"
jq -e '.type == "confirmed" and .confirmation == "installed"' "$WS/attempts/document/outcome.json" >/dev/null
run document-read "$MINI" workspace --action read --dir "$WS" --name notes
run document-show "$MINI" workspace --action doc-show --dir "$WS" --name notes
jq -e '[.cell.entries[] | select(.type == "atom") | .id] | length == 2' "$RUN/logs/document-read.out" >/dev/null
# The old content API also allowed useful pages without a DocumentRecord.
# Preserve both atom-only pages and quote-only pages, without inventing ownership.
run atom-only-create "$MINI" workspace --action create --dir "$WS" --name atom-only --storage content \
  --predicate "$RUN/open-law.json"
printf '%s\n' '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"atom-only","payload":{"type":"content","actions":[{"type":"createAtom","atom":"255","kind":{"type":"text"},"payload":"61746f6d2d6f6e6c79206669727374"},{"type":"createAtom","atom":"256","kind":{"type":"text"},"payload":"61746f6d2d6f6e6c79207365636f6e64"}]}}]}' >"$RUN/atom-only.json"
run atom-only-propose "$MINI" workspace --action propose --dir "$WS" --request "$RUN/atom-only.json" --proposal-id atom-only
run atom-only-submit "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/atom-only/intent.json" --attempt "$WS/attempts/atom-only"
run atom-only-read "$MINI" workspace --action read --dir "$WS" --name atom-only
jq -e '([.cell.entries[] | select(.type == "document")] | length == 0) and ([.cell.entries[] | select(.type == "atom")] | length == 2)' "$RUN/logs/atom-only-read.out" >/dev/null
run atom-only-show "$MINI" workspace --action doc-show --dir "$WS" --name atom-only
run quotes-create "$MINI" workspace --action create --dir "$WS" --name quotes --storage content \
  --predicate "$RUN/open-law.json"
jq -n --arg document "$(jq -r .target "$WS/refs/notes.json")" \
  --arg revision "$(jq -r '.cell.entries[] | select(.type == "atom" and .id == "255") | .revision' "$RUN/logs/document-read.out")" \
  '{type:"minidregg-workspace-proposal-v1",action:"invoke",targets:[{name:"quotes",payload:{type:"content",actions:[{type:"quote",element:"8001",link:"9001",reference:{document:$document,atom:"255",revision:$revision,mode:"snapshot"}},{type:"quote",element:"8002",link:"9002",reference:{document:$document,atom:"255",revision:$revision,mode:"live"}}]}}]}' >"$RUN/quotes.json"
run quotes-propose "$MINI" workspace --action propose --dir "$WS" --request "$RUN/quotes.json" --proposal-id quotes
run quotes-submit "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/quotes/intent.json" --attempt "$WS/attempts/quotes"
run quotes-read "$MINI" workspace --action read --dir "$WS" --name quotes
jq -e '([.cell.entries[] | select(.type == "document" or .type == "atom")] | length == 0) and ([.cell.entries[] | select(.type == "element")] | length == 2)' "$RUN/logs/quotes-read.out" >/dev/null
run quotes-show "$MINI" workspace --action doc-show --dir "$WS" --name quotes
# A same-subject delegated reference still has to obey its narrower scope.
jq -n --arg subject "$(jq -r '.sponsor.subject' "$RUN/params.json")" \
  '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"notes",recipient:$subject,verbs:["observe","mutate"],maxCost:"50000",fields:["annotations"]}' >"$RUN/reviewer.json"
run reviewer-propose "$MINI" workspace --action propose --dir "$WS" --request "$RUN/reviewer.json" --proposal-id reviewer
run reviewer-submit "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/reviewer/intent.json" --attempt "$WS/attempts/reviewer"
jq -e '.type == "confirmed"' "$WS/attempts/reviewer/outcome.json" >/dev/null
run reviewer-publish "$MINI" workspace --action publish-delegation --dir "$WS" --proposal-id reviewer --attempt "$WS/attempts/reviewer"
run reviewer-import "$MINI" workspace --action import --dir "$WS" --name reviewer --from-ref "$WS/proposals/reviewer/recipient-reference.json"
run reviewer-read "$MINI" workspace --action read --dir "$WS" --name reviewer
jq -e '[.cell.entries[]? | select(.type == "atom")] | length == 0' "$RUN/logs/reviewer-read.out" >/dev/null
printf '%s\n' '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"reviewer","payload":{"type":"content","actions":[{"type":"link","link":"601","source":null,"target":{"type":"external","scheme":"6874747073","authority":"6578616d706c65","path":"2f"},"relation":"1"}]}}]}' >"$RUN/annotation.json"
run annotation-propose "$MINI" workspace --action propose --dir "$WS" --request "$RUN/annotation.json" --proposal-id annotation
run annotation-submit "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/annotation/intent.json" --attempt "$WS/attempts/annotation"
jq -e '.type == "confirmed" and .confirmation == "installed"' "$WS/attempts/annotation/outcome.json" >/dev/null
printf '%s\n' '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"reviewer","payload":{"type":"content","actions":[{"type":"createAtom","atom":"257","kind":{"type":"text"},"payload":"6d7573742062652072656675736564"}]}}]}' >"$RUN/forbidden-body.json"
run forbidden-body-propose "$MINI" workspace --action propose --dir "$WS" --request "$RUN/forbidden-body.json" --proposal-id forbidden-body
refused forbidden-body-submit "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/forbidden-body/intent.json" --attempt "$WS/attempts/forbidden-body"
jq -e '.type == "refused"' "$WS/attempts/forbidden-body/outcome.json" >/dev/null
run final-document-read "$MINI" workspace --action read --dir "$WS" --name notes
jq -e '[.cell.entries[] | select(.type == "atom")] | length == 2' "$RUN/logs/final-document-read.out" >/dev/null
run final-reviewer-read "$MINI" workspace --action read --dir "$WS" --name reviewer
jq -e '[.cell.entries[]?.type] == ["link"]' "$RUN/logs/final-reviewer-read.out" >/dev/null
stop_server
run source-audit "$HOST" "$CONFIG" audit
run source-profile "$HOST" "$CONFIG" profile
sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" "$HERE/genesis.sh" "$RUN/params.json" >"$RUN/provenance.sha256"
printf '%s\n' "$RUN"
