#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
manifest="$project_dir/native/hyperdocument-link-store/Cargo.toml"
fixture="$project_dir/native/hyperdocument-link-store/fixtures/hyperdocument-link-recovery-v1.bin"
test_root="$(mktemp -d "${TMPDIR:-/tmp}/minidregg-link-store.XXXXXX")"
trap 'rm -rf "$test_root"' EXIT

generated="$test_root/generated.bin"
lake build Assurance.HyperdocumentLinkLocalFileStore >/dev/null
lake env lean --run scripts/EmitHyperdocumentLinkRecoveryFixture.lean "$generated"
cmp "$fixture" "$generated"

cargo test --quiet --manifest-path "$manifest"
cargo build --quiet --manifest-path "$manifest" --bin minidregg-link-store
store_bin="$project_dir/native/hyperdocument-link-store/target/debug/minidregg-link-store"

stage_root="$test_root/stage-crash"
"$store_bin" stage "$stage_root" "$fixture" >/dev/null
if "$store_bin" read "$stage_root" >"$test_root/unexpected-stage-read.bin" 2>/dev/null; then
  echo "staged bytes became visible before install" >&2
  exit 1
fi
"$store_bin" discard-stage "$stage_root"

live_root="$test_root/lost-response"
# Discard stdout to model a publication response lost after install completed.
"$store_bin" publish "$live_root" "$fixture" >/dev/null
"$store_bin" read "$live_root" >"$test_root/restarted-read.bin"
cmp "$fixture" "$test_root/restarted-read.bin"

# A separate invocation retries the exact bytes and preserves the record.
"$store_bin" publish "$live_root" "$fixture" >/dev/null
"$store_bin" read "$live_root" >"$test_root/retry-read.bin"
cmp "$fixture" "$test_root/retry-read.bin"

# Native storage transports corrupt bytes but does not grant them meaning;
# Lean's `corrupt_file_bytes_fail_closed` is the semantic rejection theorem.
cp "$fixture" "$test_root/corrupt.bin"
dd if=/dev/zero of="$test_root/corrupt.bin" bs=1 seek=13 count=1 \
  conv=notrunc status=none
if "$store_bin" publish "$live_root" "$test_root/corrupt.bin" >/dev/null 2>&1; then
  echo "different retry overwrote the published record" >&2
  exit 1
fi
"$store_bin" read "$live_root" >"$test_root/after-conflict.bin"
cmp "$fixture" "$test_root/after-conflict.bin"

printf 'fixture_bytes=%s\n' "$(wc -c <"$fixture" | tr -d ' ')"
printf 'stage_crash=not_visible\n'
printf 'lost_response_restart=exact\n'
printf 'retry=idempotent\n'
printf 'different_retry=conflict_no_overwrite\n'
printf 'lean_acceptance=Assurance.HyperdocumentLinkLocalFileStore\n'
printf 'trust_ceiling=POSIX_device_and_power_loss_unproved\n'
