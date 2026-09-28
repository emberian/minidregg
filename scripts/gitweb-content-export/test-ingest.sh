#!/bin/sh
# Script-flow test only: the fake Mini here is not an admission or source proof.
set -eu
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
scratch=$(mktemp -d)
git -C "$scratch" init -q
git -C "$scratch" config user.name Test
git -C "$scratch" config user.email test@example.invalid
git -C "$scratch" config commit.gpgsign false
printf 'Selected public bytes.\n' >"$scratch/demo.txt"
git -C "$scratch" add demo.txt
git -C "$scratch" commit -qm demo
commit=$(git -C "$scratch" rev-parse HEAD)
"$here/prepare.sh" "$scratch" "$commit" demo.txt public-demo-file "$scratch/export"
printf 'private fixture config\n' >"$scratch/config.json"
printf 'fixture key\n' >"$scratch/key"
cat >"$scratch/host" <<'SH'
#!/bin/sh
if [ "$2" = assemble ]; then printf 'exact-call\n' >"$5"; fi
exit 0
SH
chmod +x "$scratch/host"
cat >"$scratch/mini" <<'SH'
#!/bin/sh
set -eu
command=$1
shift
directory=
prepare_only=0
mode=
host=
config=
intent=
socket=
while [ "$#" -gt 0 ]; do
  if [ "$1" = --dir ] || [ "$1" = --attempt ]; then directory=$2; fi
  if [ "$1" = --prepare-only ]; then prepare_only=$2; fi
  if [ "$1" = --mode ]; then mode=$2; fi
  if [ "$1" = --host ]; then host=$2; fi
  if [ "$1" = --config ]; then config=$2; fi
  if [ "$1" = --intent ]; then intent=$2; fi
  if [ "$1" = --socket ]; then socket=$2; fi
  shift
done
[ -n "$directory" ] || exit 2
case "$command" in
  query)
    if [ -n "${MOCK_EXPECT_SOCKET:-}" ] && [ "$socket" != "$MOCK_EXPECT_SOCKET" ]; then
      echo "signed query lost its pinned socket" >&2; exit 2
    fi
    mkdir "$directory"
    if [ -e "$MOCK_STATE" ]; then
      jq -n --rawfile payload "$MOCK_PAYLOAD_FILE" \
        '{page:{root:"100",entries:[{type:"atom",id:"7401",kind:{type:"text"},
          payload:$payload,tombstonedAt:null}]}}' >"$directory/view.json"
    else
      printf '%s\n' '{"page":{"root":"99","entries":[]}}' >"$directory/view.json"
    fi
    printf '%s\n' '{"signing":[{"authorityRoot":"42"}]}' >"$directory/challenge.json"
    printf 'signed-query\n' >"$directory/signed-observation.bin"
    printf 'view\n' >"$directory/view.bin"
    ;;
  submit)
    mkdir "$directory"
    [ "$prepare_only" = true ] || exit 2
    printf 'exact-call\n' >"$directory/call.bin"
    cp "$config" "$directory/config.json"
    cp "$intent" "$directory/intent.json"
    : >"$directory/plan.bin"
    : >"$directory/transaction-signatures.bin"
    jq -n --arg host "$host" --arg config "$directory/config.json" \
      --arg socket "$socket" \
      '{format:"minidregg-resource-client-attempt-v1",operation:"submit",
        host:$host,config:$config,socket:(if $socket == "" then null else $socket end)}' \
      >"$directory/attempt.json"
    ;;
  retry)
    index=1
    while [ -e "$(printf '%s/retry-%04d.json' "$directory" "$index")" ] ||
          [ -e "$(printf '%s/retry-%04d.bin' "$directory" "$index")" ]; do
      index=$((index + 1))
    done
    if [ "$mode" = submit ]; then
    printf 'submit\n' >>"$MOCK_SUBMITS"
    : >"$MOCK_STATE"
      if [ "${MOCK_LOST:-0}" = 1 ]; then
        printf '%s\n' '{"type":"uncertain"}' >"$(printf '%s/retry-%04d.json' "$directory" "$index")"
        exit 1
      fi
      printf '%s\n' '{"type":"confirmed","confirmation":"installed","transactionId":"1","eventId":"2","acceptedCount":"1","imageBoundary":"3"}' >"$(printf '%s/retry-%04d.json' "$directory" "$index")"
    elif [ "$mode" = lookup ]; then
    printf 'lookup\n' >>"$MOCK_LOOKUPS"
    if [ "${MOCK_ABSENT:-0}" = 1 ]; then
      printf '%s\n' '{"type":"absent"}' >"$(printf '%s/retry-%04d.json' "$directory" "$index")"
    else
      printf '%s\n' '{"type":"confirmed","confirmation":"replayed","transactionId":"1","eventId":"2","acceptedCount":"1","imageBoundary":"3"}' >"$(printf '%s/retry-%04d.json' "$directory" "$index")"
    fi
    else exit 2
    fi
    ;;
  *) exit 2 ;;
esac
SH
chmod +x "$scratch/mini"
MOCK_STATE="$scratch/accepted"
MOCK_SUBMITS="$scratch/submits"
MOCK_LOOKUPS="$scratch/lookups"
MOCK_PAYLOAD_FILE="$scratch/export/payload.hex"
od -An -tx1 -v "$scratch/export/atom-payload.bin" | tr -d ' \n' >"$MOCK_PAYLOAD_FILE"
export MOCK_STATE MOCK_PAYLOAD_FILE MOCK_SUBMITS MOCK_LOOKUPS
: >"$scratch/private.sock"
MOCK_EXPECT_SOCKET=$(realpath "$scratch/private.sock")
export MOCK_EXPECT_SOCKET
"$here/ingest.sh" "$scratch/host" "$scratch/mini" "$scratch/config.json" \
  "$scratch/key" "$scratch/export" 8001 61 7401 7 30001 30002 30003 30004 \
  "$scratch/ingestion" "$scratch/private.sock"
jq -e --rawfile payload "$MOCK_PAYLOAD_FILE" \
  '.purpose.draft.command.targets[0].payload.actions[0] ==
    {type:"createAtom",atom:"7401",kind:{type:"text"},payload:$payload}' \
  "$scratch/ingestion/create-intent.json" >/dev/null
jq -e '.sourceResource == "8001" and .atom == "7401" and
  .sourceRoot == "100" and .receipt.confirmation == "replayed" and
  .selectedFile == "atom-payload.bin" and .fileBytes == "23" and
  (.fileSha256 | test("^[0-9a-f]{64}$")) and
  (.payloadSha256 | test("^[0-9a-f]{64}$"))' \
  "$scratch/ingestion/result.json" >/dev/null
test -s "$scratch/ingestion/selected/signed-observation.bin"
cp "$scratch/ingestion/result.json" "$scratch/original-result.json"
if "$here/finalize.sh" "$scratch/ingestion" 1abc >/dev/null 2>&1; then
  echo "nondecimal recovery nonce was accepted" >&2; exit 1
fi
"$here/finalize.sh" "$scratch/ingestion" 30005 >/dev/null
cmp "$scratch/original-result.json" "$scratch/ingestion/result.json"
[ "$(wc -l <"$MOCK_SUBMITS" | tr -d ' ')" = 1 ]
[ "$(wc -l <"$MOCK_LOOKUPS" | tr -d ' ')" = 2 ]
unset MOCK_EXPECT_SOCKET
awk 'BEGIN { for (i = 0; i < 65536; i++) printf "x" }' >"$scratch/large.txt"
git -C "$scratch" add large.txt
git -C "$scratch" commit -qm large
large_commit=$(git -C "$scratch" rev-parse HEAD)
"$here/prepare.sh" "$scratch" "$large_commit" large.txt public-demo-file "$scratch/large-export"
MOCK_STATE="$scratch/large-accepted"
MOCK_PAYLOAD_FILE="$scratch/large-export/payload.hex"
od -An -tx1 -v "$scratch/large-export/atom-payload.bin" | tr -d ' \n' >"$MOCK_PAYLOAD_FILE"
export MOCK_STATE MOCK_PAYLOAD_FILE
"$here/ingest.sh" "$scratch/host" "$scratch/mini" "$scratch/config.json" \
  "$scratch/key" "$scratch/large-export" 8001 61 7401 7 35001 35002 35003 35004 \
  "$scratch/large-ingestion" >/dev/null
cmp "$scratch/large-export/atom-payload.bin" "$scratch/large-ingestion/atom-payload.bin"
MOCK_PAYLOAD_FILE="$scratch/export/payload.hex"
export MOCK_PAYLOAD_FILE
MOCK_STATE="$scratch/lost-accepted" MOCK_LOST=1
export MOCK_STATE MOCK_LOST
if "$here/ingest.sh" "$scratch/host" "$scratch/mini" "$scratch/config.json" \
    "$scratch/key" "$scratch/export" 8001 61 7401 7 40001 40002 40003 40004 \
    "$scratch/lost-ingestion" >/dev/null 2>&1; then
  echo "lost submit reply was treated as success" >&2; exit 1
fi
MOCK_ABSENT=1
export MOCK_ABSENT
if "$here/finalize.sh" "$scratch/lost-ingestion" 40005 >/dev/null 2>&1; then
  echo "absent lookup completed a lost submit" >&2; exit 1
fi
rm "$scratch/lost-ingestion/call.sha256"
: >"$scratch/lost-ingestion/create/retry-0003.bin"
unset MOCK_ABSENT
cp "$scratch/host" "$scratch/host.original"
printf 'changed\n' >>"$scratch/host"
if "$here/finalize.sh" "$scratch/lost-ingestion" 40006 >/dev/null 2>&1; then
  echo "changed Host pin completed a lost submit" >&2; exit 1
fi
mv "$scratch/host.original" "$scratch/host"
"$here/finalize.sh" "$scratch/lost-ingestion" 40007 >/dev/null
test -s "$scratch/lost-ingestion/call.sha256"
test -f "$scratch/lost-ingestion/create/retry-0004.json"
jq -e '.receipt.confirmation == "replayed"' "$scratch/lost-ingestion/result.json" >/dev/null
[ "$(wc -l <"$MOCK_SUBMITS" | tr -d ' ')" = 3 ]
printf 'tamper' >>"$scratch/export/file.bin"
if "$here/ingest.sh" "$scratch/host" "$scratch/mini" "$scratch/config.json" \
    "$scratch/key" "$scratch/export" 8001 61 7402 7 30101 30102 30103 30104 \
    "$scratch/reject-tampered" >/dev/null 2>&1; then
  echo "changed exported file was accepted" >&2; exit 1
fi
printf 'PASS: exact selected readback, lookup-only lost-reply recovery, stable reentry (fake Mini only)\n'
