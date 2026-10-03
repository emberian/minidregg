#!/usr/bin/env bash
set -euo pipefail
task_source_root=${1:?explicit isolated source root required}
task_target_root=${2:?explicit independent warm target required}
cd "$task_source_root"
free=$(df -B1 --output=avail / | tail -1)
((free>=50000000000)) || { echo 'REFUSED root free space';exit 75; }
export CARGO_TARGET_DIR="$task_target_root"
export CARGO_BUILD_JOBS=2
cargo nextest run --release --offline --locked --manifest-path native/resource-client/Cargo.toml -E 'test(visible_unqualified_record_waits_for_exact_durable_adoption)' --test-threads 1 > traffic-adoption-consumer-tests.log 2>&1
free=$(df -B1 --output=avail / | tail -1)
((free>=50000000000)) || { echo 'REFUSED root free space before release';exit 75; }
cargo build --release --offline --locked --jobs 2 --manifest-path native/resource-client/Cargo.toml --bin mini > traffic-adoption-consumer-build.log 2>&1
mkdir -p artifacts
cp "$task_target_root/release/mini" artifacts/mini-adoption-consumer
sha256sum artifacts/mini-adoption-consumer
printf 'PASS focused adoption consumer test and native binary build\n'
