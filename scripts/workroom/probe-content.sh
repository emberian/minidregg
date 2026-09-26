#!/bin/sh
# Exercise one real Mini content page with exact signed create/edit/read calls.
set -eu

if [ "$#" -ne 4 ]; then
  echo "usage: $0 MINIDREGG_HOST PINNED_CONFIG TOOL_KEY NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi

HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
HOST=$1
CONFIG=$2
KEY=$3
EVIDENCE=$4
MINI=${MINI:-"$REPO/native/resource-client/target/debug/mini"}
command -v jq >/dev/null 2>&1 || { echo "jq is required" >&2; exit 2; }
[ -x "$HOST" ] && [ -x "$MINI" ] && [ -f "$CONFIG" ] && [ -f "$KEY" ] || {
  echo "host, Mini client, config, or tool key unavailable" >&2; exit 2;
}
[ ! -e "$EVIDENCE" ] || { echo "refusing existing evidence directory" >&2; exit 2; }
mkdir -m 700 "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)

query_workroom() {
  label=$1
  nonce=$2
  jq -n --arg nonce "$nonce" \
    '{subject:"8",nonce:$nonce,purpose:{type:"query",kind:"object",target:"8001",view:"resource"},
      grants:[{kind:"object",target:"8001",capability:"96"}]}' \
    >"$EVIDENCE/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" \
    --intent "$EVIDENCE/$label-intent.json" --key "$KEY" --view resource \
    --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout"
}

confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (.acceptedCount | type == "string" and test("^[1-9][0-9]*$"))' "$1" >/dev/null
}

query_workroom before 50000
jq -e '.page.document == "8001" and .page.entries == []' \
  "$EVIDENCE/before/view.json" >/dev/null

# The note text is untrusted user content. Shell only encodes its fixed bytes;
# Host.Json and ContentResource own the actual action and its admission.
NOTE_INITIAL_HEX=$(printf '%s' 'Workroom research note: verify the source receipt before reuse.' | od -An -tx1 -v | tr -d ' \n')
NOTE_FINAL_HEX=$(printf '%s' 'Revised workroom note: Mini accepted the receipt; fn provenance remains a separate check.' | od -An -tx1 -v | tr -d ' \n')

jq -n --slurpfile view "$EVIDENCE/before/view.json" \
  --slurpfile challenge "$EVIDENCE/before/challenge.json" \
  --arg payload "$NOTE_INITIAL_HEX" \
  '{subject:"8",nonce:"50001",purpose:{type:"prepare",draft:{type:"invoke",
    command:{subject:"8",expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
      nonce:"50002",targets:[{kind:"object",target:"8001",capability:"95",
        observeCapability:null,schemaVersion:"1",expectedTargetRoot:$view[0].page.root,
        payload:{type:"content",actions:[{type:"createAtom",atom:"7401",
          kind:{type:"text"},payload:$payload}]}}]}}},
    grants:[{kind:"object",target:"8001",capability:"95"}]}' \
  >"$EVIDENCE/create-intent.json"
"$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/create-intent.json" --key "$KEY" \
  --dir "$EVIDENCE/create-attempt" >"$EVIDENCE/create.stdout"
confirmed "$EVIDENCE/create-attempt/outcome.json"
query_workroom created 50003
jq -e --arg payload "$NOTE_INITIAL_HEX" '.page.entries | length == 1 and
  .[0].type == "atom" and .[0].kind.type == "text" and .[0].payload == $payload' \
  "$EVIDENCE/created/view.json" >/dev/null

jq -n --slurpfile view "$EVIDENCE/created/view.json" \
  --slurpfile challenge "$EVIDENCE/created/challenge.json" \
  --arg payload "$NOTE_FINAL_HEX" \
  '{subject:"8",nonce:"50004",purpose:{type:"prepare",draft:{type:"invoke",
    command:{subject:"8",expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
      nonce:"50005",targets:[{kind:"object",target:"8001",capability:"95",
        observeCapability:null,schemaVersion:"1",expectedTargetRoot:$view[0].page.root,
        payload:{type:"content",actions:[{type:"editAtom",atom:"7401",
          before:($view[0].page.entries[0] |
            {document,kind,payload,createdBy,createdAt,tombstonedAt}),
          kind:{type:"text"},payload:$payload,tombstone:false}]}}]}}},
    grants:[{kind:"object",target:"8001",capability:"95"}]}' \
  >"$EVIDENCE/edit-intent.json"
"$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/edit-intent.json" --key "$KEY" \
  --dir "$EVIDENCE/edit-attempt" >"$EVIDENCE/edit.stdout"
confirmed "$EVIDENCE/edit-attempt/outcome.json"
query_workroom edited 50006
jq -e --arg payload "$NOTE_FINAL_HEX" '.page.entries | length == 1 and
  .[0].type == "atom" and .[0].kind.type == "text" and .[0].payload == $payload' \
  "$EVIDENCE/edited/view.json" >/dev/null
printf '%s\n' "$EVIDENCE/edited/view.json"
