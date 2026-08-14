#!/usr/bin/env bash
# Fail closed unless the source-owned Dregg2 suite payload and its transport
# envelope match the one exact identity admitted by ZkmlSuiteRegistry.lean.
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd -P)
repo_root=$(cd "$script_dir/.." && pwd -P)

registered_suite=dregg.ir2.babybear-ext4.poseidon2-w16.fri.v1
requested_suite=${1:-$registered_suite}

if [[ "$requested_suite" != "$registered_suite" ]]; then
  echo "zkml-suite-artifact: unregistered suite: $requested_suite" >&2
  exit 1
fi

artifact_dir=$repo_root/artifacts/zkml-suites
stem=dregg-ir2-babybear-poseidon2-w16-fri-v1
payload=$artifact_dir/$stem.payload.json
envelope=$artifact_dir/$stem.envelope.json

expected_bytes=6654
expected_sha=b131ed2ad3e9628dbcdbf2bf6c8cf845a6f31f87eea3c91ba8aa00d019c494f0
expected_source_commit=e496fb48d6aaf374d4c0302c95c0fcc69bb8051d
expected_source_tree=434f81f2be045cb50fc05907881284160d3f380d
expected_exporter_blob=762d7180cca7fda6b7140ca0b6cacfb8241925ff
expected_poseidon_blob=9878703829dc8e43a06fc6f1acac217af2ba2fd5
expected_fri_blob=1d7e4302aa6f18a92fdfe8092c03926be75c1998
expected_cargo_lock_blob=4987ba037cad521fc3ced2444ae16ce09188ae48
expected_checker=dregg.ir2.verify_vm_descriptor2_with_config
expected_protocol=p3-batch-stark/TwoAdicFriPcs@82cfad73cd734d37a0d51953094f970c531817ec

for file in "$payload" "$envelope"; do
  if [[ ! -f "$file" ]]; then
    echo "zkml-suite-artifact: missing $file" >&2
    exit 1
  fi
done

hash_stdin() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{print $1}'
  else
    shasum -a 256 | awk '{print $1}'
  fi
}

# The source emitter writes one canonical JSON line followed by one newline;
# only that final newline is excluded from its declared content identity.
if [[ $(wc -l < "$payload" | tr -d ' ') != 1 ]] ||
    [[ $(tail -c 1 "$payload" | od -An -tu1 | tr -d ' ') != 10 ]]; then
  echo "zkml-suite-artifact: payload is not one newline-terminated JSON line" >&2
  exit 1
fi

actual_bytes=$(perl -0777 -pe 's/\n\z//' "$payload" | wc -c | tr -d ' ')
actual_sha=$(perl -0777 -pe 's/\n\z//' "$payload" | hash_stdin)

if [[ "$actual_bytes" != "$expected_bytes" ]] || [[ "$actual_sha" != "$expected_sha" ]]; then
  echo "zkml-suite-artifact: payload identity mismatch" >&2
  echo "  expected bytes=$expected_bytes sha256=$expected_sha" >&2
  echo "  actual   bytes=$actual_bytes sha256=$actual_sha" >&2
  exit 1
fi

jq -e \
  --arg suite "$registered_suite" \
  --arg checker "$expected_checker" \
  --arg protocol "$expected_protocol" \
  '.schema_version == 1 and
   .suite_id == $suite and
   .checker_id == $checker and
   .checker_version == 1 and
   .protocol_id == $protocol and
   .protocol_mode == "IR-v2 FRI" and
   .base_field_modulus == 2013265921 and
   .extension_degree == 4 and
   .extension_polynomial == "X^4-11 over BabyBear" and
   .poseidon_width == 16 and
   .poseidon_rate == 8 and
   .poseidon_capacity == 8 and
   .external_initial_rounds == 4 and
   .internal_rounds == 13 and
   .external_final_rounds == 4 and
   (.external_initial_constants | length) == 4 and
   (all(.external_initial_constants[]; length == 16)) and
   (.internal_constants | length) == 13 and
   (.external_final_constants | length) == 4 and
   (all(.external_final_constants[]; length == 16)) and
   (.external_linear_columns | length) == 16 and
   (all(.external_linear_columns[]; length == 16)) and
   (.internal_linear_columns | length) == 16 and
   (all(.internal_linear_columns[]; length == 16)) and
   .log_blowup == 6 and
   .query_count == 19 and
   .query_grinding_bits == 16 and
   .commit_grinding_bits == 0 and
   .max_log_arity == 3 and
   .log_final_polynomial_length == 0' \
  "$payload" >/dev/null

jq -e \
  --arg suite "$registered_suite" \
  --arg sourceCommit "$expected_source_commit" \
  --arg sourceTree "$expected_source_tree" \
  --arg exporterBlob "$expected_exporter_blob" \
  --arg poseidonBlob "$expected_poseidon_blob" \
  --arg friBlob "$expected_fri_blob" \
  --arg cargoLockBlob "$expected_cargo_lock_blob" \
  --arg payloadPath "$(basename "$payload")" \
  --argjson payloadBytes "$expected_bytes" \
  --arg payloadSha "$expected_sha" \
  --arg checker "$expected_checker" \
  '.schema == "minidregg.zkml-suite-envelope.v1" and
   .suite_id == $suite and
   .source.commit == $sourceCommit and
   .source.tree == $sourceTree and
   .source.exporter_blob == $exporterBlob and
   .source.poseidon_blob == $poseidonBlob and
   .source.fri_verifier_blob == $friBlob and
   .source.cargo_lock_blob == $cargoLockBlob and
   .payload.path == $payloadPath and
   .payload.bytes_excluding_trailing_newline == $payloadBytes and
   .payload.sha256 == $payloadSha and
   .checker.id == $checker and
   .checker.version == 1 and
   .checker.content_identity == ("git:" + $sourceCommit)' \
  "$envelope" >/dev/null

# The committed Lean primitive data is a mechanical view of this exact
# admitted payload, not a second hand-maintained transcription.
generated=$repo_root/Selvage/ZkmlPoseidon2Data.lean
generated_tmp=$(mktemp "${TMPDIR:-/tmp}/zkml-poseidon2-data.XXXXXX")
trap 'rm -f "$generated_tmp"' EXIT
bash "$repo_root/scripts/render-zkml-poseidon2-data.sh" >"$generated_tmp"
if ! diff -u "$generated" "$generated_tmp"; then
  echo "zkml-suite-artifact: generated Lean Poseidon2 data mismatch" >&2
  exit 1
fi

echo "zkml-suite-artifact: PASS suite=$registered_suite bytes=$actual_bytes sha256=$actual_sha"
