#!/bin/sh
# One explicitly selected public GitWeb file version through Mini -> fn -> Mini.
# Every authority decision and wire encoding is delegated to the pinned Mini Host.
set -eu
umask 077

usage() {
  echo "usage: $0 prepare|publish|receive|cover-plan|cover-advance|ack|verify CONTRACT.json PRIVATE-STATE [APPROVAL.json]" >&2
  exit 2
}
[ "$#" -ge 3 ] && [ "$#" -le 4 ] || usage
STEP=$1 CONTRACT=$2 STATE=$3
case $STEP in prepare|publish|receive|cover-plan|cover-advance|ack|verify) ;; *) usage ;; esac
command -v jq >/dev/null || { echo 'jq required' >&2; exit 2; }
command -v shasum >/dev/null || { echo 'shasum required' >&2; exit 2; }

field() { jq -er --arg key "$1" '.[$key] | select(type == "string" and length > 0)' "$CONTRACT"; }
decimal() { jq -er --arg key "$1" '.[$key] | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$CONTRACT"; }
hash() { shasum -a 256 "$1" | awk '{print $1}'; }
confirmed() {
  jq -e '.type == "confirmed" and
    (.confirmation == "installed" or .confirmation == "replayed") and
    all(.transactionId, .eventId, .acceptedCount, .imageBoundary;
      type == "string" and test("^(0|[1-9][0-9]*)$"))' "$1" >/dev/null
}
receipt_fields() {
  jq -e 'all(.transactionId, .eventId, .acceptedCount, .imageBoundary;
    type == "string" and test("^(0|[1-9][0-9]*)$"))' "$1" >/dev/null
}
selected_poll() {
  [ -f "$STATE/poll-selected" ] || { echo 'no completed fn projection' >&2; exit 2; }
  poll_name=$(cat "$STATE/poll-selected")
  case $poll_name in poll-[0-9][0-9][0-9][0-9]) ;; *) echo 'invalid retained poll selector' >&2; exit 2 ;; esac
  POLL="$STATE/$poll_name"
  [ -d "$POLL" ] && [ ! -L "$POLL" ] || { echo 'selected fn projection absent' >&2; exit 2; }
  jq -e '.type == "selected-release-fn-poll-v1" and .status == "candidate-unacknowledged"' \
    "$POLL/fn-poll.json" >/dev/null
  cmp "$POLL/received-packet.bin" "$STATE/packet.bin" || {
    echo 'fn projected owner packet differs' >&2; exit 2;
  }
}
recipient_receipt() {
  # The original outcome files are retained. This convenience projection is
  # present only while the latest observation confirms the same receipt.
  rm -f "$STATE/recipient-confirmed.json"
  first_confirmed=''
  latest=''
  for outcome in "$STATE"/recipient-attempt/request-*.outcome.json; do
    [ -f "$outcome" ] || continue
    latest=$outcome
    if confirmed "$outcome"; then
      if [ -z "$first_confirmed" ]; then
        first_confirmed=$outcome
      else
        jq -e --slurpfile first "$first_confirmed" \
          '.transactionId == $first[0].transactionId and
           .eventId == $first[0].eventId and
           .acceptedCount == $first[0].acceptedCount and
           .imageBoundary == $first[0].imageBoundary' "$outcome" >/dev/null || {
          echo 'recipient lookup changed original receipt' >&2; exit 2;
        }
      fi
    fi
  done
  if [ -z "$first_confirmed" ] || [ -z "$latest" ] || ! confirmed "$latest"; then
    echo 'latest recipient lookup does not confirm installation' >&2; exit 2;
  fi
  cp "$first_confirmed" "$STATE/recipient-confirmed.json"
}
private_state() {
  [ -d "$STATE" ] && [ ! -L "$STATE" ] || { echo 'private state absent' >&2; exit 2; }
  mode=$(stat -c %a "$STATE" 2>/dev/null) ||
    mode=$(stat -f %Lp "$STATE" 2>/dev/null) || {
      echo 'cannot inspect private state mode' >&2; exit 2;
    }
  [ "$mode" = 700 ] || {
    echo 'state must have mode 0700' >&2; exit 2;
  }
}
article_size() {
  # This fixture's qualified fn store was initialized with 1,048,576 bytes.
  # Count the exact assembled owner article, not the selected atom payload.
  article_bytes=$(wc -c <"$STATE/article.eml" | tr -d ' ')
  [ "$article_bytes" -le 1048576 ] || {
    echo 'assembled signed article exceeds qualified fn 1MiB admission cap' >&2; exit 2;
  }
}
pin() {
  [ "$(hash "$CONTRACT")" = "$(cat "$STATE/contract.sha256")" ] || {
    echo 'contract changed after preparation' >&2; exit 2;
  }
  [ "$(hash "$(field host)")" = "$(cat "$STATE/host.sha256")" ] || {
    echo 'Host changed after preparation' >&2; exit 2;
  }
  [ "$(hash "$(field mini)")" = "$(cat "$STATE/mini.sha256")" ] || {
    echo 'Mini changed after preparation' >&2; exit 2;
  }
  [ "$(hash "$(field selectedFile)")" = "$(field selectedFileSha256)" ] || {
    echo 'exported GitWeb file changed' >&2; exit 2;
  }
  pin_export_dir=$(CDPATH='' cd -- "$(dirname -- "$(field exportResult)")" && pwd -P)
  shasum -a 256 "$(field sourceConfig)" "$(field recipientConfig)" \
    "$(field sourceSignedQuery)" "$(field sourceViewBin)" \
    "$(field privatePostConfig)" "$(field fnBinary)" "$(field fnScope)" \
    "$(field exportResult)" "$(field gitRawFile)" \
    "$pin_export_dir/selection.json" "$pin_export_dir/expected-payload.bin" \
    >"$STATE/inputs.recheck.sha256"
  cmp "$STATE/inputs.sha256" "$STATE/inputs.recheck.sha256" || {
    echo 'pinned input changed after preparation' >&2; exit 2;
  }
}

HOST=$(field host)
MINI=$(field mini)
SOURCE_CONFIG=$(field sourceConfig)
RECIPIENT_CONFIG=$(field recipientConfig)
for executable in "$HOST" "$MINI"; do
  [ -x "$executable" ] || { echo "missing executable: $executable" >&2; exit 2; }
done

case $STEP in
prepare)
  [ ! -e "$STATE" ] || { echo 'state already exists' >&2; exit 2; }
  jq -e '.gitCommit | type == "string" and test("^([0-9a-f]{40}|[0-9a-f]{64})$")' "$CONTRACT" >/dev/null
  jq -e '.gitPath | type == "string" and length > 0 and
    (startswith("/") | not) and (contains("..") | not)' "$CONTRACT" >/dev/null
  jq -e '.selectedFileSha256 | type == "string" and test("^[0-9a-f]{64}$")' "$CONTRACT" >/dev/null
  [ "$(wc -c <"$(field selectedFile)" | tr -d ' ')" -le 1000000 ] || {
    echo 'selected file exceeds bounded public preview' >&2; exit 2;
  }
  [ "$(hash "$(field selectedFile)")" = "$(field selectedFileSha256)" ] || {
    echo 'exported GitWeb file SHA differs' >&2; exit 2;
  }
  [ "$(hash "$(field gitRawFile)")" = "$(field gitRawFileSha256)" ] || {
    echo 'raw GitWeb file SHA differs' >&2; exit 2;
  }
  EXPORT_DIR=$(CDPATH='' cd -- "$(dirname -- "$(field exportResult)")" && pwd -P)
  [ "$(field selectedFile)" = "$EXPORT_DIR/atom-payload.bin" ] &&
    [ "$(field gitRawFile)" = "$EXPORT_DIR/file.bin" ] &&
    [ "$(field sourceSignedQuery)" = "$EXPORT_DIR/selected/signed-observation.bin" ] || {
      echo 'GitWeb handoff paths differ from frozen export manifest' >&2; exit 2;
    }
  cmp "$(field selectedFile)" "$EXPORT_DIR/expected-payload.bin" || {
    echo 'selected payload differs from source export reconstruction' >&2; exit 2;
  }
  jq -e --slurpfile selection "$EXPORT_DIR/selection.json" \
    '.selection == $selection[0]' "$(field exportResult)" >/dev/null || {
      echo 'GitWeb result differs from its chosen selection' >&2; exit 2;
    }
  [ "$(wc -c <"$(field gitRawFile)" | tr -d ' ')" = \
    "$(jq -er '.fileBytes' "$(field exportResult)")" ] || {
      echo 'raw GitWeb file length differs from export manifest' >&2; exit 2;
    }
  jq -e --arg commit "$(field gitCommit)" --arg path "$(field gitPath)" \
    --arg blob "$(field gitBlob)" --arg file "$(field gitRawFileSha256)" \
    --arg payload "$(field selectedFileSha256)" --arg atom "$(decimal sourceAtom)" \
    --arg resource "$(decimal sourceResource)" \
    '.type == "gitweb-mini-content-export-v1" and
     .gitCommit == $commit and .gitPath == $path and .gitBlob == $blob and
     .fileSha256 == $file and .payloadSha256 == $payload and
     .atom == $atom and .sourceResource == $resource and
     .selectedFile == "atom-payload.bin" and
     .signedQuery == "selected/signed-observation.bin" and
     (.receipt | all(.transactionId, .eventId, .acceptedCount, .imageBoundary;
       type == "string" and test("^(0|[1-9][0-9]*)$")))' \
    "$(field exportResult)" >/dev/null || {
      echo 'GitWeb export manifest differs from selected atom/version' >&2; exit 2;
    }
  mkdir -m 700 "$STATE"
  od -An -tx1 -v "$(field sourceSignedQuery)" | tr -d ' \n' >"$STATE/source-query.hex"
  jq -er '.sourceSignedQueryHex | select(type == "string" and length > 0)' \
    "$CONTRACT" | tr -d '\n' >"$STATE/source-query-expected.hex"
  cmp "$STATE/source-query.hex" "$STATE/source-query-expected.hex" || {
    echo 'request signed query differs from retained query bytes' >&2; exit 2;
  }
  hash "$CONTRACT" >"$STATE/contract.sha256"
  hash "$HOST" >"$STATE/host.sha256"
  hash "$MINI" >"$STATE/mini.sha256"
  [ "$(hash "$(field fnBinary)")" = "$(field fnBinarySha256)" ] || {
    echo 'fn executable differs from qualified image pin' >&2; exit 2;
  }
  shasum -a 256 "$(field sourceConfig)" "$(field recipientConfig)" \
    "$(field sourceSignedQuery)" "$(field sourceViewBin)" \
    "$(field privatePostConfig)" "$(field fnBinary)" "$(field fnScope)" \
    "$(field exportResult)" "$(field gitRawFile)" \
    "$EXPORT_DIR/selection.json" "$EXPORT_DIR/expected-payload.bin" \
    >"$STATE/inputs.sha256"
  "$HOST" "$SOURCE_CONFIG" query "$(field sourceSignedQuery)" "$STATE/source-view.bin"
  cmp "$STATE/source-view.bin" "$(field sourceViewBin)" || {
    echo 'current native query differs from retained signed source view' >&2; exit 2;
  }
  "$HOST" "$SOURCE_CONFIG" inspect view-resource \
    "$STATE/source-view.bin" "$STATE/source-view.json"
  od -An -tx1 -v "$(field selectedFile)" | tr -d ' \n' >"$STATE/selected-payload.hex"
  jq -e --arg atom "$(decimal sourceAtom)" \
    --rawfile bytes "$STATE/selected-payload.hex" \
    '[.page.entries[] | select(.type == "atom" and .id == $atom and .payload == $bytes)] | length == 1' \
    "$STATE/source-view.json" >/dev/null || { echo 'current Mini atom differs from GitWeb export' >&2; exit 2; }
  jq -e --arg root "$(jq -er '.sourceRoot' "$(field exportResult)")" \
    '.page.root == $root' "$STATE/source-view.json" >/dev/null || {
      echo 'source page root differs from accepted GitWeb export' >&2; exit 2;
    }
  # Request is source-owned JSON shape; no release codec is encoded here.
  jq -n --rawfile query "$STATE/source-query.hex" --arg atom "$(decimal sourceAtom)" \
    --arg domain "$(decimal destinationDomain)" \
    --arg semantics "$(decimal destinationSemantics)" \
    --arg target "$(decimal destinationTarget)" \
    --arg group "$(field group)" --arg message "$(field messageId)" \
    --arg policy "$(decimal destinationPolicyRoot)" \
    --arg keyset "$(decimal destinationKeysetRoot)" \
    --arg epoch "$(decimal ownerEpoch)" --arg owner "$(decimal ownerSubject)" \
    --arg nonce "$(decimal ownerNonce)" --arg expiry "$(decimal ownerExpiresAt)" \
    --arg from "$(field from)" --arg date "$(field date)" \
    --arg subject "$(field subject)" \
    '{signedQueryHex:$query,atom:$atom,destinationDomain:$domain,
      destinationSemantics:$semantics,destinationTarget:$target,group:$group,
      messageId:$message,policyRoot:$policy,keysetRoot:$keyset,epoch:$epoch,
      ownerSubject:$owner,ownerNonce:$nonce,expiresAt:$expiry,
      from:$from,date:$date,subject:$subject}' >"$STATE/request.json"
  "$HOST" "$SOURCE_CONFIG" selected-release-prepare "$STATE/request.json" "$STATE/preimage.bin"
  "$MINI" selected-release-sign --host "$HOST" --config "$SOURCE_CONFIG" \
    --preimage "$STATE/preimage.bin" --key "$(field ownerKey)" \
    --output "$STATE/signature.bin"
  "$HOST" "$SOURCE_CONFIG" selected-release-assemble "$STATE/preimage.bin" \
    "$STATE/signature.bin" "$(field from)" "$(field date)" "$(field subject)" \
    "$STATE/packet.bin" "$STATE/article.eml"
  article_size
  "$MINI" selected-source-sign --host "$HOST" --config "$SOURCE_CONFIG" \
    --packet "$STATE/packet.bin" --delegate-capability "$(decimal sourceDelegateCapability)" \
    --key "$(field ownerKey)" --dir "$STATE/source-sign"
  "$HOST" "$SOURCE_CONFIG" selected-release-source-check \
    "$STATE/source-sign/ingress.bin" "$STATE/article.eml"
  jq -n --arg commit "$(field gitCommit)" --arg path "$(field gitPath)" \
    --arg sha "$(field selectedFileSha256)" --arg atom "$(decimal sourceAtom)" \
    --arg query "$(hash "$(field sourceSignedQuery)")" \
    --arg view "$(hash "$STATE/source-view.bin")" \
    '{type:"fn-gitweb-preview-input-v1",commit:$commit,path:$path,
      selectedFileSha256:$sha,sourceAtom:$atom,signedQuerySha256:$query,
      sourceViewSha256:$view,
      authority:"explicit Mini atom and signed query; GitWeb export is comparison input"}' \
    >"$STATE/selection.json"
  echo 'prepared one exact public atom; no Mini publication or fn POST yet'
  ;;
publish)
  private_state; pin
  article_size
  "$HOST" "$SOURCE_CONFIG" selected-release-source-check \
    "$STATE/source-sign/ingress.bin" "$STATE/article.eml"
  "$MINI" selected-source-publish --host "$HOST" --config "$SOURCE_CONFIG" \
    --ingress "$STATE/source-sign/ingress.bin" --article "$STATE/article.eml" \
    --state-dir "$STATE/source-publish" --post-config "$(field privatePostConfig)"
  jq -e '.status == "accepted" or .status == "already-stored"' \
    "$STATE/source-publish/fn-post-result.json" >/dev/null
  echo 'source event14 confirmed and fn POST accepted; recipient remains separate'
  ;;
receive)
  private_state; pin
  jq -e '.status == "accepted" or .status == "already-stored"' \
    "$STATE/source-publish/fn-post-result.json" >/dev/null || {
      echo 'no confirmed source publication and fn acceptance' >&2; exit 2;
    }
  if [ ! -d "$STATE/recipient-attempt" ]; then
    if [ ! -f "$STATE/poll-selected" ]; then
      poll_name=''
      for index in 0001 0002 0003 0004 0005 0006 0007 0008; do
        if [ ! -e "$STATE/poll-$index" ]; then poll_name="poll-$index"; break; fi
      done
      [ -n "$poll_name" ] || { echo 'fn poll reconciliation attempt bound exhausted' >&2; exit 2; }
      POLL="$STATE/$poll_name"
      mkdir -m 700 "$POLL"
      "$HOST" "$RECIPIENT_CONFIG" selected-release-fn-poll \
        "$(field fnBinary)" "$(field fnScope)" "$(field fnControl)" \
        "$(decimal recipientCapability)" "$(decimal recipientAuthorityRoot)" \
        "$(decimal recipientTargetRoot)" \
        "$POLL/cursor.fncu" "$POLL/report.fn-e" "$POLL/source.eml" \
        "$POLL/received-packet.bin" "$POLL/received-ingress.bin" "$POLL/fn-poll.json"
      jq -e '.type == "selected-release-fn-poll-v1" and .status == "candidate-unacknowledged"' \
        "$POLL/fn-poll.json" >/dev/null
      cmp "$POLL/received-packet.bin" "$STATE/packet.bin" || {
        echo 'fn projected owner packet differs' >&2; exit 2;
      }
      printf '%s\n' "$poll_name" >"$STATE/poll-selected"
    fi
    selected_poll
    "$MINI" selected-release-submit --host "$HOST" --config "$RECIPIENT_CONFIG" \
      --socket "$(field recipientSocket)" --ingress "$POLL/received-ingress.bin" \
      --dir "$STATE/recipient-attempt"
  else
    "$MINI" selected-release-lookup --attempt "$STATE/recipient-attempt"
  fi
  recipient_receipt
  echo 'recipient op20/21 confirmed with retained original four-field receipt'
  ;;
cover-plan)
  private_state; pin
  selected_poll
  recipient_receipt
  # Exact recipient acceptance is required by the Host's selected frontier
  # selector. Transport acceptance alone cannot supply this transaction.
  RECEIPT="$STATE/recipient-confirmed.json"
  [ -f "$RECEIPT" ] || { echo 'confirmed recipient receipt required' >&2; exit 2; }
  confirmed "$RECEIPT"
  TX=$(jq -er '.transactionId' "$RECEIPT")
  "$MINI" fn-frontier-plan --host "$HOST" --config "$RECIPIENT_CONFIG" \
    --socket "$(field recipientOperatorSocket)" --kind selected --transaction "$TX" \
    --state-dir "$STATE/frontier"
  cmp "$STATE/frontier/source.eml" "$POLL/source.eml"
  echo 'frontier plan retained; approve its exact source inspection before signing'
  ;;
cover-advance)
  [ "$#" -eq 4 ] || usage
  private_state; pin
  recipient_receipt
  "$MINI" fn-frontier-advance --state-dir "$STATE/frontier" \
    --key "$(field gatewayKey)" --approval "$4"
  echo 'event17 attempt retained; confirm exact receipt before ACK'
  ;;
ack)
  private_state; pin
  selected_poll
  recipient_receipt
  [ -f "$STATE/frontier/confirmed.json" ] || { echo 'event17 receipt absent' >&2; exit 2; }
  receipt_fields "$STATE/frontier/confirmed.json"
  RECEIPT="$STATE/recipient-confirmed.json"
  confirmed "$RECEIPT"
  TX=$(jq -er '.transactionId' "$RECEIPT")
  ack_name=''
  for index in 0001 0002 0003 0004 0005 0006 0007 0008; do
    if [ ! -e "$STATE/ack-$index.json" ]; then ack_name="ack-$index.json"; break; fi
  done
  [ -n "$ack_name" ] || { echo 'fn ACK reconciliation attempt bound exhausted' >&2; exit 2; }
  "$HOST" "$RECIPIENT_CONFIG" selected-release-fn-ack \
    "$POLL/cursor.fncu" "$POLL/report.fn-e" "$TX" \
    "$STATE/frontier/ingress.bin" "$STATE/$ack_name"
  jq -e '.fnAck == "durable-accepted" or .fnAck == "covered-by-durable-frontier"' \
    "$STATE/$ack_name" >/dev/null
  printf '%s\n' "$ack_name" >"$STATE/ack-selected"
  echo 'fn ACK has exact recipient and event17 Mini receipts; signed recipient readback remains required'
  ;;
verify)
  private_state; pin
  recipient_receipt
  receipt_fields "$STATE/frontier/confirmed.json"
  [ -f "$STATE/ack-selected" ] || { echo 'no confirmed fn ACK reconciliation' >&2; exit 2; }
  ack_name=$(cat "$STATE/ack-selected")
  case $ack_name in ack-[0-9][0-9][0-9][0-9].json) ;; *) echo 'invalid retained fn ACK selector' >&2; exit 2 ;; esac
  jq -e '.fnAck == "durable-accepted" or .fnAck == "covered-by-durable-frontier"' \
    "$STATE/$ack_name" >/dev/null
  jq -e --arg target "$(decimal destinationTarget)" \
    --arg cap "$(decimal recipientCapability)" \
    '.purpose.type == "query" and .purpose.kind == "object" and
     .purpose.target == $target and .purpose.view == "resource" and
     any(.grants[]; .kind == "object" and .target == $target and .capability == $cap)' \
    "$(field recipientQueryIntent)" >/dev/null || {
      echo 'recipient signed query is not for exact destination and capability' >&2; exit 2;
    }
  readback_name=''
  for index in 0001 0002 0003 0004 0005 0006 0007 0008; do
    if [ ! -e "$STATE/recipient-readback-$index" ]; then readback_name="recipient-readback-$index"; break; fi
  done
  [ -n "$readback_name" ] || { echo 'recipient readback bound exhausted' >&2; exit 2; }
  "$MINI" query --host "$HOST" --config "$RECIPIENT_CONFIG" \
    --socket "$(field recipientSocket)" --intent "$(field recipientQueryIntent)" \
    --key "$(field recipientQueryKey)" --view resource \
    --dir "$STATE/$readback_name"
  od -An -tx1 -v "$STATE/packet.bin" | tr -d ' \n' >"$STATE/packet.hex"
  ATOM=$(jq -er '.transactionId' "$STATE/recipient-confirmed.json")
  jq -e --arg atom "$ATOM" --rawfile payload "$STATE/packet.hex" \
    '[.page.entries[] | select(.type == "atom" and .id == $atom and
      .kind.type == "inlineObject" and .kind.schema == "11" and
      .tombstonedAt == null and .payload == $payload)] | length == 1' \
    "$STATE/$readback_name/view.json" >/dev/null || {
      echo 'signed recipient page lacks exact accepted event13 atom and owner packet' >&2; exit 2;
    }
  printf '%s\n' "$readback_name" >"$STATE/readback-selected"
  echo 'signed recipient resource read contains exact accepted event13 atom and owner packet'
  ;;
esac
