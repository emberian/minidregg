#!/usr/bin/env bash
# check-rust-tests.sh — the native crates' tests the lanes report, as one gate.
#
# FILTERED lines only (never an unfiltered `cargo test -p` suite): each row is
#   t NAME FLOOR CRATE [cargo args] -- [libtest filters]
# run as `cargo +<pinned> test --release --locked [cargo args] -- [filters]` in
# native/CRATE with CARGO_TARGET_DIR (default <repo>/target-gates). A row is red
# when cargo fails OR fewer than FLOOR tests ran (a filter that stops matching
# runs zero tests and exits 0; the floor is what makes that red).
#   known_red NAME TASK CRATE [cargo args] -- EXACT_TEST
# runs one test that is known to fail and must STILL fail: the day it passes the
# row is red ("delete the known_red row"), so a skip is never silent.
set -uo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root" || exit 2
export PATH=$HOME/.cargo/bin:$PATH
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$root/target-gates}
rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
jobs=${LOCAL_GATES_CARGO_JOBS:-6}
logs=$root/build-logs/rust-tests; mkdir -p "$logs"
red=0
passed_of() { grep -Eo 'test result: [a-zA-Z]+\. [0-9]+ passed' "$1" | awk '{s+=$4} END{print s+0}'; }
t() {
  local name=$1 floor=$2 crate=$3; shift 3
  local log=$logs/$name.log rc n
  printf '  %-22s cargo test --release --locked %s\n' "$name" "$*"
  (cd "native/$crate" && cargo "+$rust" test --release --locked -j "$jobs" "$@") >"$log" 2>&1
  rc=$?
  n=$(passed_of "$log")
  if [ "$rc" != 0 ]; then
    echo "rust-tests: RED: $name: cargo exit $rc, $n passed; $(grep -E '^test .* FAILED$|^error' "$log" | head -3 | tr '\n' ';') ($log)"
    red=$((red + 1))
  elif [ "$n" -lt "$floor" ]; then
    echo "rust-tests: RED: $name: $n tests ran, floor $floor (a filter stopped matching?) ($log)"
    red=$((red + 1))
  else
    echo "rust-tests: ok: $name: $n passed (floor $floor)"
  fi
}
known_red() {
  local name=$1 task=$2 crate=$3; shift 3
  local log=$logs/$name.log rc
  (cd "native/$crate" && cargo "+$rust" test --release --locked -j "$jobs" "$@" --exact) >"$log" 2>&1
  rc=$?
  if [ "$rc" = 0 ] && [ "$(passed_of "$log")" -ge 1 ]; then
    echo "rust-tests: RED: $name: known-red test now PASSES; delete its known_red row (cv task $task)"
    red=$((red + 1))
  elif grep -q '^test .* FAILED$' "$log"; then
    echo "rust-tests: known-red: $name still fails, as recorded (cv task $task)"
  else
    echo "rust-tests: RED: $name: known-red row did not run its test (exit $rc) ($log)"
    red=$((red + 1))
  fi
}

t rc-shell-private-enroll 50 resource-client --bin mini -- shell:: private:: participant_enrollment:: key_generation
t grain-provider          42 grain-runtime -- provider credential publication_refusal \
  --skip foreground_status_uses_signed_parent_lease_without_a_hermes_child
known_red grain-foreground-status 01a0f751-0cb9 grain-runtime --bin grain-runtime -- \
  publication_refusal_tests::foreground_status_uses_signed_parent_lease_without_a_hermes_child
t hermes-test-provider    15 hermes-test-provider -- tests::
t verifier-protocol       10 credential-signature-verifier --test protocol -- protocol_

if [ "$red" != 0 ]; then echo "rust-tests: FAIL: $red row(s) red"; exit 1; fi
echo "rust-tests: PASS"
