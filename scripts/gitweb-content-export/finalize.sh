#!/bin/sh
# Read-only recovery of one retained content call, followed by a fresh signed view.
set -eu
umask 077
die() { echo "gitweb content finalize: $*" >&2; exit 2; }
[ "$#" -eq 2 ] || die "usage: finalize.sh INGEST-DIR FRESH-READ-NONCE"
output=$(CDPATH='' cd -- "$1" && pwd -P) || die "missing ingest directory"
nonce=$2
case "$nonce" in ''|*[!0-9]*|0[0-9]*) die "nonce must be a canonical decimal" ;; esac
[ -f "$output/pin.json" ] && [ -f "$output/create/call.bin" ] ||
  die "incomplete retained call; no resubmit"
command -v jq >/dev/null 2>&1 || die "jq is required"
sha() { shasum -a 256 "$1" | awk '{print $1}'; }
pin=$output/pin.json
jq -e '.type == "gitweb-mini-content-ingest-pin-v1"' "$pin" >/dev/null || die "invalid pin"
host=$(jq -er '.host' "$pin") mini=$(jq -er '.mini' "$pin")
config=$(jq -er '.config' "$pin") key=$(jq -er '.key' "$pin")
socket=$(jq -er '.socket' "$pin")
check_pins() {
  for pair in "host:$host:hostSha256" "mini:$mini:miniSha256" \
      "config:$config:configSha256" "key:$key:keySha256"; do
    name=${pair%%:*}; rest=${pair#*:}; field=${rest##*:}; file=${rest%:*}
    [ -f "$file" ] || die "$name pin missing"
    expected=$(jq -er --arg field "$field" '.[$field]' "$pin")
    [ "$(sha "$file")" = "$expected" ] || die "$name pin changed"
  done
  [ "$(sha "$output/atom-payload.bin")" = "$payload_sha" ] || die "payload changed"
  [ "$(sha "$output/selection.json")" = "$(jq -er '.selectionSha256' "$pin")" ] ||
    die "selection changed"
  [ "$(sha "$output/file.bin")" = "$(jq -er '.fileSha256' "$pin")" ] ||
    die "selected file changed"
  [ "$(sha "$output/create/call.bin")" = "$(cat "$output/call.sha256")" ] ||
    die "retained call changed"
}
resource=$(jq -er '.resource' "$pin") atom=$(jq -er '.atom' "$pin")
capability=$(jq -er '.capability' "$pin")
subject=$(jq -er '.subject' "$pin")
payload_sha=$(jq -er '.payloadSha256' "$pin")
jq -e --arg host "$host" --arg config "$output/create/config.json" \
  --arg socket "$socket" \
  '.format == "minidregg-resource-client-attempt-v1" and
    .operation == "submit" and .host == $host and .config == $config and
    (.socket // "") == $socket' "$output/create/attempt.json" >/dev/null ||
  die "retained Mini attempt manifest differs from pins"
cmp -s "$config" "$output/create/config.json" || die "retained config differs"
cmp -s "$output/create-intent.json" "$output/create/intent.json" ||
  die "retained source intent differs"
if [ ! -f "$output/call.sha256" ]; then
  # A driver killed after preparation can leave Mini's durable call but not
  # the shell-side pin. The planned network submit starts only after pinning.
  # Reassemble from Mini's retained source plan and signatures before pinning.
  [ "$(sha "$host")" = "$(jq -er '.hostSha256' "$pin")" ] || die "Host pin changed"
  [ "$(sha "$config")" = "$(jq -er '.configSha256' "$pin")" ] || die "config pin changed"
  "$host" "$config" assemble "$output/create/plan.bin" \
    "$output/create/transaction-signatures.bin" "$output/reassembled-call.bin" ||
    die "cannot source-reassemble retained call"
  cmp -s "$output/reassembled-call.bin" "$output/create/call.bin" ||
    die "retained call differs from source assembly"
  rm "$output/reassembled-call.bin"
  sha "$output/create/call.bin" >"$output/call.sha256"
fi
for field in beforeNonce observeNonce commandNonce; do
  [ "$nonce" != "$(jq -er --arg field "$field" '.[$field]' "$pin")" ] ||
    die "read nonce repeats a retained authoring nonce"
done
for prior in "$output"/readback-*-intent.json; do
  [ -f "$prior" ] || continue
  [ "$nonce" != "$(jq -er '.nonce' "$prior")" ] ||
    die "read nonce already used by a retained attempt"
done
check_pins
[ "$(sha "$output/payload.hex")" = \
  "$(od -An -tx1 -v "$output/atom-payload.bin" | tr -d ' \n' | shasum -a 256 | awk '{print $1}')" ] ||
  die "retained payload hex changed"

# `retry --mode lookup` uses the retained call. Its latest exact receipt is the
# only authority for completing an uncertain submit. Never invoke submit here.
index=1
while [ "$index" -le 9999 ]; do
  candidate=$(printf '%s/create/retry-%04d.json' "$output" "$index")
  candidate_bin=$(printf '%s/create/retry-%04d.bin' "$output" "$index")
  [ -e "$candidate" ] || [ -e "$candidate_bin" ] || break
  index=$((index + 1))
done
[ "$index" -le 9999 ] || die "lookup evidence names exhausted"
latest=$candidate
"$mini" retry --attempt "$output/create" --mode lookup >"$output/lookup.stdout" ||
  die "read-only lookup did not confirm the retained call"
check_pins
[ -f "$latest" ] || die "lookup produced no new retained outcome"
jq -e '.type == "confirmed" and .confirmation == "replayed" and
  (.transactionId | type == "string") and (.eventId | type == "string") and
  (.acceptedCount | type == "string") and (.worldRoot | type == "string")' \
  "$latest" >/dev/null || die "latest lookup is not an exact historical receipt"
receipt_fields='[.transactionId,.eventId,.acceptedCount,.worldRoot]'
if [ -f "$output/create/retry-0001.json" ] &&
    jq -e '.type == "confirmed"' "$output/create/retry-0001.json" >/dev/null; then
  [ "$(jq -c "$receipt_fields" "$latest")" = \
    "$(jq -c "$receipt_fields" "$output/create/retry-0001.json")" ] ||
    die "lookup receipt differs from original confirmed receipt"
fi
if [ -f "$output/result.json" ]; then
  [ "$(jq -c "$receipt_fields" "$latest")" = \
    "$(jq -c '.receipt | [ .transactionId,.eventId,.acceptedCount,.worldRoot ]' "$output/result.json")" ] ||
    die "completed handoff receipt changed"
fi

# Every invocation gets a new bounded readback directory. An interrupted query
# remains retained and the operator may call finalize with another fresh nonce.
index=1
while [ "$index" -le 9999 ]; do
  readback=$(printf '%s/readback-%04d' "$output" "$index")
  intent=$(printf '%s/readback-%04d-intent.json' "$output" "$index")
  [ -e "$readback" ] || [ -e "$intent" ] || break
  index=$((index + 1))
done
[ "$index" -le 9999 ] || die "readback attempt limit reached"
jq -n --arg subject "$subject" --arg nonce "$nonce" \
  --arg resource "$resource" --arg capability "$capability" \
  '{subject:$subject,nonce:$nonce,
    purpose:{type:"query",kind:"object",target:$resource,view:"resource"},
    grants:[{kind:"object",target:$resource,capability:$capability}]}' >"$intent"
if [ -n "$socket" ]; then
  "$mini" query --host "$host" --config "$config" --intent "$intent" \
    --key "$key" --view resource --dir "$readback" --socket "$socket" \
    >"$readback.stdout" ||
    die "signed readback incomplete; retry finalize with a new nonce"
else
  "$mini" query --host "$host" --config "$config" --intent "$intent" \
    --key "$key" --view resource --dir "$readback" >"$readback.stdout" ||
    die "signed readback incomplete; retry finalize with a new nonce"
fi
check_pins
[ -s "$readback/signed-observation.bin" ] && [ -s "$readback/view.bin" ] ||
  die "missing signed source readback"
jq -e --arg atom "$atom" --rawfile payload "$output/payload.hex" \
  '[.cell.entries[] | select(.type == "atom" and .id == $atom and
    .kind == {"type":"text"} and .payload == $payload and .tombstonedAt == null)] |
    length == 1' "$readback/view.json" >/dev/null || die "current atom differs"
root=$(jq -er '.cell.root | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$readback/view.json")
if [ -e "$output/selected" ]; then
  [ -f "$output/selected/view.json" ] && [ -s "$output/selected/signed-observation.bin" ] ||
    die "completed selected readback is incomplete"
  [ "$(jq -er '.cell.root' "$output/selected/view.json")" = "$root" ] ||
    die "completed handoff source root changed"
  jq -e --arg atom "$atom" --rawfile payload "$output/payload.hex" \
    '[.cell.entries[] | select(.type == "atom" and .id == $atom and
      .kind == {"type":"text"} and .payload == $payload and .tombstonedAt == null)] |
      length == 1' "$output/selected/view.json" >/dev/null ||
    die "completed selected atom changed"
else
  mv "$readback" "$output/selected"
fi

selection=$output/selection.json
[ "$(jq -er '.payloadSha256' "$selection")" = "$payload_sha" ] || die "selection changed"
candidate=$output/result.candidate.json
jq -n --slurpfile selection "$selection" --slurpfile receipt "$latest" \
  --arg resource "$resource" --arg atom "$atom" --arg root "$root" \
  '{type:"gitweb-mini-content-export-v1",selection:$selection[0],
    gitCommit:$selection[0].commit,gitPath:$selection[0].path,
    gitBlob:$selection[0].blob,fileSha256:$selection[0].fileSha256,
    fileBytes:$selection[0].fileBytes,payloadSha256:$selection[0].payloadSha256,
    selectedFile:"atom-payload.bin",sourceResource:$resource,atom:$atom,
    sourceRoot:$root,receipt:$receipt[0],
    signedQuery:"selected/signed-observation.bin"}' >"$candidate"
if [ -e "$output/result.json" ]; then
  jq -S 'del(.receipt.confirmation)' "$candidate" >"$candidate.normalized"
  jq -S 'del(.receipt.confirmation)' "$output/result.json" >"$candidate.existing"
  cmp -s "$candidate.normalized" "$candidate.existing" || die "completed handoff changed"
  rm "$candidate" "$candidate.normalized" "$candidate.existing"
else
  mv "$candidate" "$output/result.json"
fi
(cd "$output" && shasum -a 256 selection.json file.bin atom-payload.bin \
  expected-payload.bin create-intent.json create/call.bin \
  selected/signed-observation.bin selected/view.bin result.json >SHA256SUMS.tmp)
if [ -e "$output/SHA256SUMS" ]; then
  cmp -s "$output/SHA256SUMS" "$output/SHA256SUMS.tmp" ||
    die "completed artifact hashes changed"
  rm "$output/SHA256SUMS.tmp"
else
  mv "$output/SHA256SUMS.tmp" "$output/SHA256SUMS"
fi
check_pins
printf '%s\n' "$output/result.json"
