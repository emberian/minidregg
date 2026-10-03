#!/usr/bin/env bash
set -euo pipefail
task_source_root=${1:?explicit isolated source root required}
task_target_root=${2:?explicit independent warm target required}
cd "$task_source_root"
free=$(df -B1 --output=avail / | tail -1)
((free>=50000000000)) || { echo 'REFUSED root free space';exit 75; }
export CARGO_TARGET_DIR="$task_target_root"
export CARGO_BUILD_JOBS=2
cargo nextest run --release --offline --locked --manifest-path native/resource-client/Cargo.toml -E 'test(cohort_tcp::tests) | test(live_relay_grouped_admission) | test(authenticated_stage_sets) | test(async_custody_live_mailbox_continuation_then_bound_fetch_without_second_dispatch)' --test-threads 2 > traffic-pipeline-tests.log 2>&1
free=$(df -B1 --output=avail / | tail -1)
((free>=50000000000)) || { echo 'REFUSED root free space before release';exit 75; }
cargo build --release --offline --locked --jobs 2 --manifest-path native/resource-client/Cargo.toml --bin mini > traffic-pipeline-build.log 2>&1
mkdir -p artifacts
cp "$task_target_root/release/mini" artifacts/mini-pipeline-fsync
sha256sum artifacts/mini-pipeline-fsync
printf 'PASS focused traffic pipeline tests and native binary build\n'
