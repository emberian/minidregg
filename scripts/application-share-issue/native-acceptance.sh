#!/bin/sh
# Source-owned share-ticket issue over a fresh metered app/session birth.
# The positive-fee ticket is deliberately scoped to the fresh app's current
# packageVersion 0. Roots come from the prospective signed GitWeb version-1
# identity, but this issue/receipt gate cannot claim an installed package or a
# dispatch-capable final ticket. The final version-1 ticket needs lifecycle
# install in a separate integrated Store.
set -eu
umask 077

if [ "$#" -ne 2 ]; then
  echo "usage: $0 SOURCE_MATCHED_HOST NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
HOST=$1
EVIDENCE=$2
MINI=${MINI:?set MINI to the source-matched resource client}
STORE_BINARY=${STORE_BINARY:?set STORE_BINARY}
SIGNATURE_BINARY=${SIGNATURE_BINARY:?set SIGNATURE_BINARY}
FEE_INSPECTOR=${FEE_INSPECTOR:?set source-qualified signed-plan fee inspector}
BASE_SCRIPT=${BASE_SCRIPT:?set BASE_SCRIPT to the reviewed fresh app/session fixture}
PREPARED_BASE=${PREPARED_BASE:-}
PACKAGE_ROOT=${PACKAGE_ROOT:?set the source-selected package commitment}
INTERFACE_ROOT=${INTERFACE_ROOT:?set the source-selected interface root}
SCHEMA_ROOT=${SCHEMA_ROOT:?set the source-selected schema root}
IDENTITY_ROOTS=${IDENTITY_ROOTS:?set source-authored GitWeb roots.json}
for value in "$PACKAGE_ROOT" "$INTERFACE_ROOT" "$SCHEMA_ROOT"; do
  case "$value" in ''|0*|*[!0-9]*) echo "invalid selected root" >&2; exit 2 ;; esac
done
for executable in "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
    "$FEE_INSPECTOR"; do
  [ -x "$executable" ] || { echo "not executable: $executable" >&2; exit 2; }
done
[ -f "$BASE_SCRIPT" ] && [ -f "$IDENTITY_ROOTS" ] &&
  [ ! -e "$EVIDENCE" ] || exit 2
command -v jq >/dev/null
command -v xxd >/dev/null
# This fixture selects the exact bounded Lean author output from the signed
# GitWeb descriptor; matching caller-provided root strings alone is not enough.
IDENTITY_ROOTS_SHA=$(shasum -a 256 "$IDENTITY_ROOTS" | cut -d ' ' -f 1)
[ "$IDENTITY_ROOTS_SHA" = \
  0d848da24169771e02fcb32b88465cbe9dec87649432e76a87309cf6f89f272f ] || {
    echo "unexpected source-authored GitWeb roots file" >&2; exit 2;
  }
jq -e --arg package "$PACKAGE_ROOT" --arg interface "$INTERFACE_ROOT" \
  --arg schema "$SCHEMA_ROOT" \
  '.app == "8401" and .prospectivePackageVersion == "1" and
   .packageRoot == $package and .webInterfaceRoot == $interface and
   .schemaRoot == $schema' "$IDENTITY_ROOTS" >/dev/null
mkdir -m 700 "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
shasum -a 256 "$0" "$BASE_SCRIPT" "$HOST" "$MINI" "$STORE_BINARY" \
  "$SIGNATURE_BINARY" "$FEE_INSPECTOR" "$IDENTITY_ROOTS" \
  >"$EVIDENCE/input-sha256.txt"
shasum -a 256 -c "$EVIDENCE/input-sha256.txt" \
  >"$EVIDENCE/input-precheck.txt"

if [ -n "$PREPARED_BASE" ]; then
  BASE=$(CDPATH='' cd -- "$PREPARED_BASE" && pwd)
  [ -s "$BASE/input-recheck.txt" ] || {
    echo "prepared app/session base lacks completed input recheck" >&2; exit 2;
  }
  shasum -a 256 "$BASE/input-recheck.txt" >>"$EVIDENCE/input-sha256.txt"
else
  BASE="$EVIDENCE/base"
  MINI="$MINI" STORE_BINARY="$STORE_BINARY" SIGNATURE_BINARY="$SIGNATURE_BINARY" \
    /bin/sh "$BASE_SCRIPT" "$HOST" "$BASE" \
    >"$EVIDENCE/base.stdout" 2>"$EVIDENCE/base.stderr"
fi
CONFIG="$BASE/workroom/deployment/pinned-config.json"
jq -e '.tariffPerInitialPayloadByte == 1' "$CONFIG" >/dev/null
KEY="$BASE/workroom/tool.key"
PUBLIC="$BASE/workroom/tool.pub"
CONTROLLER_KEY="$BASE/workroom/controller.key"
CONTROLLER_PUBLIC="$BASE/workroom/controller.pub"
STORE="$BASE/workroom/store"

jq -n --arg package "$PACKAGE_ROOT" --arg interface "$INTERFACE_ROOT" \
  --arg schema "$SCHEMA_ROOT" \
  '{spec:{ticket:{resource:"8500",scope:{app:"8401",packageVersion:"0",
      packageRoot:$package,interfaceId:"1",interfaceVersion:"1",
      interfaceRoot:$interface,schemaRoot:$schema,schemaVersion:"10"},
      participant:{session:"8404",descriptorResource:"8405",kind:"web",
        subject:"8",origin:{type:"human"},sessionCapability:"147",
        appObserveCapability:"141",ticketObserveCapability:"173"},
      ceiling:{basis:{type:"role",id:"0"},added:[],removed:[],
        roleSchemaRoot:$schema,roleVersion:"10"},issueNonce:"85000",notAfter:"1000000000"},
      issuer:"8",appDelegateCapability:"141",ticketOwnerCapability:"171",
      ticketControlCapability:"172"},payer:"8",funding:[],
      sourceCapabilities:["42"]}' >"$EVIDENCE/request.json"
"$HOST" "$CONFIG" author application-share-issue-request \
  "$EVIDENCE/request.json" "$EVIDENCE/request.bin"
"$HOST" "$CONFIG" inspect application-share-issue-request \
  "$EVIDENCE/request.bin" "$EVIDENCE/request-inspected.json"
"$HOST" "$CONFIG" application-share-issue-plan \
  "$EVIDENCE/request.bin" "$EVIDENCE/preview-plan.bin"
"$HOST" "$CONFIG" inspect application-share-issue-plan \
  "$EVIDENCE/preview-plan.bin" "$EVIDENCE/preview-plan.json"
jq -e --slurpfile request "$EVIDENCE/request-inspected.json" \
  '.type == "application-share-issue-plan-v2" and
   .canonicalRequest == $request[0].canonicalRequest and
   .canonicalSpec == $request[0].canonicalSpec and
   .spec.issuer == "8" and .spec.ticket.resource == "8500" and
   .spec.ticket.participant.subject == "8"' \
  "$EVIDENCE/preview-plan.json" >/dev/null

COUNT=$(jq -er '.slots | length' "$EVIDENCE/preview-plan.json")
[ "$COUNT" -gt 0 ] || exit 1
: >"$EVIDENCE/signers.ndjson"
index=0
while [ "$index" -lt "$COUNT" ]; do
  slot=$(jq -cer --argjson i "$index" '.slots[$i]' "$EVIDENCE/preview-plan.json")
  key_id=$(printf '%s\n' "$slot" | jq -er '.signing.keyId')
  case "$key_id" in
    7007) key_path=$CONTROLLER_KEY; public_path=$CONTROLLER_PUBLIC ;;
    8008) key_path=$KEY; public_path=$PUBLIC ;;
    *) echo "unexpected signer key ID $key_id" >&2; exit 1 ;;
  esac
  public=$(od -An -tx1 -v "$public_path" | tr -d ' \n')
  header=$(printf '%s\n' "$slot" | jq -er '.header')
  header_sha=$(printf '%s' "$header" | xxd -r -p | shasum -a 256 | cut -d' ' -f1)
  printf '%s\n' "$slot" | jq -c --arg public "$public" \
    --arg headerSha "$header_sha" --arg keyPath "$key_path" \
    '{role,index,keyId:.signing.keyId,keyEpoch:.signing.keyEpoch,
      publicKey:$public,headerSha256:$headerSha,keyPath:$keyPath}' \
    >>"$EVIDENCE/signers.ndjson"
  index=$((index + 1))
done
REQUEST_SHA=$(shasum -a 256 "$EVIDENCE/request.bin" | cut -d' ' -f1)
SPEC=$(jq -er '.canonicalSpec' "$EVIDENCE/request-inspected.json")
jq -s --arg request "$REQUEST_SHA" --arg spec "$SPEC" \
  '{type:"minidregg-application-share-issue-approval-v1",
    requestSha256:$request,canonicalSpec:$spec,issuer:"8",
    participantSubject:"8",appDelegateCapability:"141",ticketResource:"8500",
    signers:.}' "$EVIDENCE/signers.ndjson" >"$EVIDENCE/approval.json"

SERVICE_PID=
cleanup() {
  if [ -n "$SERVICE_PID" ]; then
    kill "$SERVICE_PID" 2>/dev/null || :
    wait "$SERVICE_PID" 2>/dev/null || :
  fi
}
trap cleanup EXIT HUP INT TERM
start_service() {
  mode=$1 name=$2
  mkdir -m 700 "$EVIDENCE/$name"
  SOCKET="$EVIDENCE/$name/mini.sock"
  "$MINI" "$mode" --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$EVIDENCE/$name/stdout" 2>"$EVIDENCE/$name/stderr" &
  SERVICE_PID=$!
  tick=0
  until [ -S "$SOCKET" ]; do
    kill -0 "$SERVICE_PID" 2>/dev/null || exit 1
    tick=$((tick + 1)); [ "$tick" -lt 120 ] || exit 1
    sleep 1
  done
}
stop_service() {
  kill "$SERVICE_PID" 2>/dev/null || :
  wait "$SERVICE_PID" 2>/dev/null || :
  SERVICE_PID=
}
query_payer_balance() {
  name=$1 nonce=$2
  jq -n --arg nonce "$nonce" \
    '{subject:"8",nonce:$nonce,purpose:{type:"query",kind:"account",
      target:"8",view:"resource"},
      grants:[{kind:"account",target:"8",capability:"42"}]}' \
    >"$EVIDENCE/$name-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" \
    --intent "$EVIDENCE/$name-intent.json" --key "$KEY" --view resource \
    --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
  jq -er '[.balances[] | select(.[0] == "0")][0][1]' \
    "$EVIDENCE/$name/view.json" >"$EVIDENCE/$name-balance.txt"
}

# The participant service cannot prepare an unsigned issue plan.
start_service serve participant-service
if "$MINI" share-issue-prepare --host "$HOST" --config "$CONFIG" \
    --socket "$SOCKET" --request "$EVIDENCE/request.json" \
    --approval "$EVIDENCE/approval.json" --dir "$EVIDENCE/public-refusal" \
    >"$EVIDENCE/public-refusal.stdout" 2>"$EVIDENCE/public-refusal.stderr"; then
  echo "participant service admitted op32" >&2; exit 1
fi
[ ! -e "$EVIDENCE/public-refusal/ingress.bin" ]
rg -q 'operation unavailable on selected socket' \
  "$EVIDENCE/public-refusal.stderr"
stop_service

start_service serve-operator operator-service
# The separate subject-9 account has only its genesis 1 unit. The exact
# ticket Spec accepted below is planned once with payer 9 and its real spend
# capability; refusal precedes the same-Spec funded payer-8 control.
jq '.payer="9" | .sourceCapabilities=["43"]' \
  "$EVIDENCE/request.json" >"$EVIDENCE/shortage-request.json"
"$HOST" "$CONFIG" author application-share-issue-request \
  "$EVIDENCE/shortage-request.json" "$EVIDENCE/shortage-request.bin"
"$HOST" "$CONFIG" inspect application-share-issue-request \
  "$EVIDENCE/shortage-request.bin" "$EVIDENCE/shortage-request-inspected.json"
jq -e --slurpfile funded "$EVIDENCE/request-inspected.json" \
  '.canonicalSpec == $funded[0].canonicalSpec and
   .canonicalRequest != $funded[0].canonicalRequest' \
  "$EVIDENCE/shortage-request-inspected.json" >/dev/null
"$STORE_BINARY" read-to "$STORE" "$EVIDENCE/before-shortage-image.bin"
if "$HOST" "$CONFIG" application-share-issue-plan \
    "$EVIDENCE/shortage-request.bin" "$EVIDENCE/shortage-plan.bin" \
    >"$EVIDENCE/shortage.stdout" 2>"$EVIDENCE/shortage.stderr"; then
  echo "underfunded positive-rate ticket planned" >&2; exit 1
fi
[ ! -e "$EVIDENCE/shortage-plan.bin" ]
"$STORE_BINARY" read-to "$STORE" "$EVIDENCE/after-shortage-image.bin"
cmp "$EVIDENCE/before-shortage-image.bin" "$EVIDENCE/after-shortage-image.bin"
# Approval covers payer, funding and source capabilities, not only ticket Spec.
jq '.funding = [{source:"8",destination:"8",asset:"0",amount:"1"}]' \
  "$EVIDENCE/request.json" >"$EVIDENCE/wrong-funding.json"
if "$MINI" share-issue-prepare --host "$HOST" --config "$CONFIG" \
    --socket "$SOCKET" --request "$EVIDENCE/wrong-funding.json" \
    --approval "$EVIDENCE/approval.json" --dir "$EVIDENCE/funding-refusal" \
    >"$EVIDENCE/funding-refusal.stdout" 2>"$EVIDENCE/funding-refusal.stderr"; then
  echo "changed funding passed custody" >&2; exit 1
fi
[ ! -e "$EVIDENCE/funding-refusal/ingress.bin" ]
rg -q 'approval differs from exact source-authored Request' \
  "$EVIDENCE/funding-refusal.stderr"
jq '.signers[0].headerSha256 = ("0" * 64)' "$EVIDENCE/approval.json" \
  >"$EVIDENCE/wrong-header-approval.json"
if "$MINI" share-issue-prepare --host "$HOST" --config "$CONFIG" \
    --socket "$SOCKET" --request "$EVIDENCE/request.json" \
    --approval "$EVIDENCE/wrong-header-approval.json" \
    --dir "$EVIDENCE/header-refusal" \
    >"$EVIDENCE/header-refusal.stdout" 2>"$EVIDENCE/header-refusal.stderr"; then
  echo "changed signing header approval passed custody" >&2; exit 1
fi
[ ! -e "$EVIDENCE/header-refusal/ingress.bin" ]
rg -q 'signing header differs from exact operator approval' \
  "$EVIDENCE/header-refusal.stderr"

"$MINI" share-issue-prepare --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --request "$EVIDENCE/request.json" \
  --approval "$EVIDENCE/approval.json" --dir "$EVIDENCE/issue" \
  >"$EVIDENCE/prepare.stdout"
[ -s "$EVIDENCE/issue/ingress.bin" ]
"$FEE_INSPECTOR" "$EVIDENCE/issue/plan.bin" \
  >"$EVIDENCE/signed-birth-fee.txt"
query_payer_balance payer-before 86000
"$STORE_BINARY" read-to "$STORE" "$EVIDENCE/before-issue-image.bin"
"$MINI" share-issue-submit --socket "$SOCKET" --attempt "$EVIDENCE/issue" \
  >"$EVIDENCE/submit.stdout"
jq -e '.type == "confirmed" and .confirmation == "installed"' \
  "$EVIDENCE/issue/submit.outcome.json" >/dev/null
query_payer_balance payer-after 86001
PAYER_BEFORE=$(cat "$EVIDENCE/payer-before-balance.txt")
PAYER_AFTER=$(cat "$EVIDENCE/payer-after-balance.txt")
jq -en --arg before "$PAYER_BEFORE" --arg after "$PAYER_AFTER" \
  '($before | tonumber) > ($after | tonumber)' >/dev/null
printf '%s\n' "$((PAYER_BEFORE - PAYER_AFTER))" \
  >"$EVIDENCE/actual-book-debit.txt"
cmp "$EVIDENCE/signed-birth-fee.txt" "$EVIDENCE/actual-book-debit.txt"
if "$MINI" share-issue-submit --socket "$SOCKET" --attempt "$EVIDENCE/issue" \
    >"$EVIDENCE/second-submit.stdout" 2>"$EVIDENCE/second-submit.stderr"; then
  echo "second submit was attempted" >&2; exit 1
fi
rg -q 'submit already attempted' "$EVIDENCE/second-submit.stderr"
"$STORE_BINARY" read-to "$STORE" "$EVIDENCE/before-lookup-image.bin"
stop_service
start_service serve ticket-read-service
jq -n '{subject:"8",nonce:"85100",purpose:{type:"query",kind:"object",
    target:"8500",view:"resource"},
    grants:[{kind:"object",target:"8500",capability:"171"}]}' \
  >"$EVIDENCE/ticket-read-intent.json"
"$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/ticket-read-intent.json" --key "$KEY" --view resource \
  --dir "$EVIDENCE/ticket-read" >"$EVIDENCE/ticket-read.stdout"
jq -e '.type == "resource" and (.cell.entries | length) == 1' \
  "$EVIDENCE/ticket-read/view.json" >/dev/null
stop_service
start_service serve-operator reopened-operator
"$MINI" share-issue-lookup --socket "$SOCKET" --attempt "$EVIDENCE/issue" \
  >"$EVIDENCE/lookup.stdout"
jq -e '.type == "confirmed" and .confirmation == "replayed"' \
  "$EVIDENCE/issue/lookup-0000.outcome.json" >/dev/null
jq -S '{transactionId,eventId,acceptedCount,worldRoot}' \
  "$EVIDENCE/issue/submit.outcome.json" >"$EVIDENCE/issue/original-receipt.json"
jq -S '{transactionId,eventId,acceptedCount,worldRoot}' \
  "$EVIDENCE/issue/lookup-0000.outcome.json" >"$EVIDENCE/issue/recovered-receipt.json"
cmp "$EVIDENCE/issue/original-receipt.json" "$EVIDENCE/issue/recovered-receipt.json"
"$STORE_BINARY" read-to "$STORE" "$EVIDENCE/after-lookup-image.bin"
cmp "$EVIDENCE/before-lookup-image.bin" "$EVIDENCE/after-lookup-image.bin"
stop_service

shasum -a 256 -c "$EVIDENCE/input-sha256.txt" >"$EVIDENCE/input-recheck.txt"
echo "application share issue native acceptance PASS"
