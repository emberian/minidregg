#!/usr/bin/env bash
set -euo pipefail
# Source-owned canonical native driver must be qualified before this script runs.
# Both source and compiler artifacts are necessary; no native receipt is mocked.
[[ $# -eq 7 ]] || { echo "usage: check-governed.sh SOURCE_ARTIFACT COMPILER_ARTIFACT COMPILER_SHA256 NATIVE_DRIVER DRIVER_SHA256 NATIVE_SESSION_CONFIG NEW_RUN_DIR" >&2; exit 2; }
task_root="$(cd "$(dirname "$0")/.." && pwd)"
"$task_root/target/release/fhe-bend-owner" "$2" "$3" "$task_root/target/release/fhe-bend" "$7" --governed "$1" "$4" "$5" "$6"
