#!/usr/bin/env bash
set -euo pipefail
task_source_root=${1:?explicit isolated source root required}
task_target_root=${2:?explicit independent warm target required}
cd "$task_source_root"
free=$(df -B1 --output=avail / | tail -1)
((free>=50000000000)) || { echo 'REFUSED root free space';exit 75; }
export CARGO_TARGET_DIR="$task_target_root" CARGO_BUILD_JOBS=2
cargo nextest run --release --offline --locked --manifest-path native/resource-client/Cargo.toml -E 'test(crypto_transit::tests) | test(shared_crypto_preserves_maximum_profile_through_all_layers) | test(authenticated_stage_sets_refuse_valid_replacement_and_corrupt_operator_forgery) | test(malicious_tag_epoch_replay_and_reply_drain_refuse) | test(cached_readiness_alias_preserves_exact_source_inode_and_refuses_conflicts) | test(unauthenticated_garbage_and_replayed_startup_cannot_consume_enrolled_link) | test(async_custody_live_mailbox_continuation_then_bound_fetch_without_second_dispatch)' --test-threads 1 > traffic-crypto-alias-tests.log 2>&1
cargo build --release --offline --locked --jobs 2 --manifest-path native/resource-client/Cargo.toml --bin mini > traffic-crypto-alias-build.log 2>&1
mkdir -p artifacts
ln "$task_target_root/release/mini" artifacts/mini-crypto-alias-qualified
sha256sum artifacts/mini-crypto-alias-qualified
printf 'PASS eight focused crypto/alias checks and owned mini release\n'
