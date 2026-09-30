#!/bin/sh
# Owner-signed Mini content mutation and exact signed source readback.
# No fn POST or selected release is performed here.
set -eu
umask 077
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)

die() { echo "gitweb content ingest: $*" >&2; exit 2; }
if [ "$#" -ne 14 ] && [ "$#" -ne 15 ]; then
  die "usage: ingest.sh HOST MINI CONFIG OWNER-KEY EXPORT-DIR RESOURCE CAPABILITY ATOM SUBJECT BEFORE-QUERY-NONCE OBSERVE-NONCE COMMAND-NONCE AFTER-QUERY-NONCE NEW-DIR [PRIVATE-SOCKET]"
fi
host=$1 mini=$2 config=$3 key=$4 export_dir=$5 resource=$6 capability=$7
atom=$8 subject=$9
shift 9
before_nonce=$1 observe_nonce=$2 command_nonce=$3 after_nonce=$4 output=$5
socket=${6:-}
for value in "$resource" "$capability" "$atom" "$subject" \
    "$before_nonce" "$observe_nonce" "$command_nonce" "$after_nonce"; do
  case "$value" in ''|*[!0-9]*) die "coordinates and nonces must be canonical decimals" ;; esac
  case "$value" in 0|[1-9]*) ;; *) die "coordinates and nonces must be canonical decimals" ;; esac
done
[ "$before_nonce" != "$observe_nonce" ] &&
  [ "$before_nonce" != "$command_nonce" ] &&
  [ "$before_nonce" != "$after_nonce" ] &&
  [ "$observe_nonce" != "$command_nonce" ] &&
  [ "$observe_nonce" != "$after_nonce" ] &&
  [ "$command_nonce" != "$after_nonce" ] || die "all four nonces must differ"
for executable in "$host" "$mini"; do [ -x "$executable" ] || die "not executable: $executable"; done
for file in "$config" "$key" "$export_dir/selection.json" \
    "$export_dir/file.bin" "$export_dir/atom-payload.bin"; do
  [ -f "$file" ] || die "missing input: $file"
done
host=$(realpath "$host") mini=$(realpath "$mini") config=$(realpath "$config")
key=$(realpath "$key")
[ -z "$socket" ] || socket=$(realpath "$socket")
[ ! -e "$output" ] || die "output directory already exists"
command -v jq >/dev/null 2>&1 || die "jq is required"
selection_sha=$(jq -er '.payloadSha256 | select(type == "string" and test("^[0-9a-f]{64}$"))' "$export_dir/selection.json")
jq -e '.type == "gitweb-public-file-export-v1"' "$export_dir/selection.json" >/dev/null ||
  die "unsupported export selection"
actual_sha=$(shasum -a 256 "$export_dir/atom-payload.bin" | awk '{print $1}')
[ "$actual_sha" = "$selection_sha" ] || die "exported payload changed"
commit=$(jq -er '.commit | select(type == "string" and test("^([0-9a-f]{40}|[0-9a-f]{64})$"))' "$export_dir/selection.json")
path=$(jq -er '.path | select(type == "string" and test("^[A-Za-z0-9._/-]+$"))' "$export_dir/selection.json")
blob=$(jq -er '.blob | select(type == "string" and test("^([0-9a-f]{40}|[0-9a-f]{64})$"))' "$export_dir/selection.json")
file_sha=$(jq -er '.fileSha256 | select(type == "string" and test("^[0-9a-f]{64}$"))' "$export_dir/selection.json")
file_length=$(jq -er '.fileBytes | select(type == "string" and test("^[1-9][0-9]*$"))' "$export_dir/selection.json")
[ "$(shasum -a 256 "$export_dir/file.bin" | awk '{print $1}')" = "$file_sha" ] ||
  die "selected file digest changed"
[ "$(wc -c <"$export_dir/file.bin" | tr -d ' ')" = "$file_length" ] ||
  die "selected file length changed"
length=$(wc -c <"$export_dir/atom-payload.bin" | tr -d ' ')
[ "$length" -gt 0 ] && [ "$length" -le 66000 ] || die "exported payload exceeds selected bound"
mkdir -m 700 "$output"
output=$(CDPATH='' cd -- "$output" && pwd -P)
cp "$export_dir/selection.json" "$output/selection.json"
cp "$export_dir/file.bin" "$output/file.bin"
cp "$export_dir/atom-payload.bin" "$output/atom-payload.bin"
{
  printf 'DREGG/GITWEB-CONTENT-EXPORT/v1\n'
  printf 'commit %s\npath %s\nblob %s\nsha256 %s\nlength %s\n\n' \
    "$commit" "$path" "$blob" "$file_sha" "$file_length"
  cat "$output/file.bin"
} >"$output/expected-payload.bin"
cmp -s "$output/atom-payload.bin" "$output/expected-payload.bin" ||
  die "selected payload is not the exact provenance header and file bytes"
od -An -tx1 -v "$output/atom-payload.bin" | tr -d ' \n' >"$output/payload.hex"
sha() { shasum -a 256 "$1" | awk '{print $1}'; }
jq -n --arg host "$host" --arg mini "$mini" --arg config "$config" \
  --arg key "$key" --arg hostSha256 "$(sha "$host")" \
  --arg socket "$socket" \
  --arg miniSha256 "$(sha "$mini")" --arg configSha256 "$(sha "$config")" \
  --arg keySha256 "$(sha "$key")" --arg payloadSha256 "$selection_sha" \
  --arg selectionSha256 "$(sha "$output/selection.json")" \
  --arg fileSha256 "$file_sha" \
  --arg resource "$resource" --arg capability "$capability" \
  --arg atom "$atom" --arg subject "$subject" \
  --arg beforeNonce "$before_nonce" --arg observeNonce "$observe_nonce" \
  --arg commandNonce "$command_nonce" \
  '{type:"gitweb-mini-content-ingest-pin-v1",host:$host,mini:$mini,socket:$socket,
    config:$config,key:$key,hostSha256:$hostSha256,miniSha256:$miniSha256,
    configSha256:$configSha256,keySha256:$keySha256,payloadSha256:$payloadSha256,
    selectionSha256:$selectionSha256,fileSha256:$fileSha256,
    resource:$resource,capability:$capability,atom:$atom,subject:$subject,
    beforeNonce:$beforeNonce,observeNonce:$observeNonce,
    commandNonce:$commandNonce}' >"$output/pin.json"

mini_call() {
  if [ -n "$socket" ]; then
    "$mini" "$@" --socket "$socket"
  else
    "$mini" "$@"
  fi
}
query_intent() {
  jq -n --arg subject "$subject" --arg nonce "$1" \
    --arg resource "$resource" --arg capability "$capability" \
    '{subject:$subject,nonce:$nonce,
      purpose:{type:"query",kind:"object",target:$resource,view:"resource"},
      grants:[{kind:"object",target:$resource,capability:$capability}]}' >"$2"
}
query_intent "$before_nonce" "$output/before-intent.json"
mini_call query --host "$host" --config "$config" --intent "$output/before-intent.json" \
  --key "$key" --view resource --dir "$output/before" >"$output/before.stdout"
jq -e --arg atom "$atom" '.cell.root | type == "string"' "$output/before/view.json" >/dev/null
jq -e --arg atom "$atom" \
  '.cell.entries | all(.[]; .type != "atom" or .id != $atom)' \
  "$output/before/view.json" >/dev/null || die "selected AtomId already exists"
root=$(jq -er '.cell.root | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$output/before/view.json")
authority=$(jq -er '.signing[0].authorityRoot | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$output/before/challenge.json")
jq -n --arg subject "$subject" --arg observe "$observe_nonce" \
  --arg command "$command_nonce" --arg authority "$authority" \
  --arg resource "$resource" --arg capability "$capability" \
  --arg root "$root" --arg atom "$atom" --rawfile payload "$output/payload.hex" \
  '{subject:$subject,nonce:$observe,purpose:{type:"prepare",draft:{type:"invoke",
    command:{subject:$subject,expectedAuthorityRoot:$authority,nonce:$command,
      targets:[{kind:"object",target:$resource,capability:$capability,
        observeCapability:null,schemaVersion:"1",expectedTargetRoot:$root,
        payload:{type:"content",actions:[{type:"createAtom",atom:$atom,
          kind:{type:"text"},payload:$payload}]}}]}}},
    grants:[{kind:"object",target:$resource,capability:$capability}]}' \
  >"$output/create-intent.json"

# The source-owned Mini author and current native receiver validate the
# mutation. Keep its exact call/receipt for read-only recovery on uncertainty.
mini_call submit --host "$host" --config "$config" \
  --intent "$output/create-intent.json" --key "$key" --prepare-only true \
  --dir "$output/create" >"$output/create.stdout" ||
  die "source preparation failed; no network submit was attempted"
[ -f "$output/create/call.bin" ] || die "source preparation retained no call"
sha "$output/create/call.bin" >"$output/call.sha256"
submit_status=0
mini_call retry --attempt "$output/create" --mode submit \
  >"$output/create-submit.stdout" || submit_status=$?
if [ "$submit_status" -ne 0 ]; then
  die "submit reply lost or refused; use finalize.sh with a fresh read nonce; never resubmit"
fi
jq -e '.type == "confirmed" and .confirmation == "installed"' \
  "$output/create/retry-0001.json" >/dev/null ||
  die "no fresh installed content receipt; use read-only finalize, never resubmit"
"$here/finalize.sh" "$output" "$after_nonce"
