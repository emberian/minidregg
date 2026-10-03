#!/usr/bin/env bash
set -euo pipefail
[[ $# = 3 ]] || { printf '%s\n' 'usage: check-physical.sh CAPTAIN_CHECKED_ARTIFACT CAPTAIN_ARTIFACT_SHA256 NEW_RUN_DIR' >&2; exit 2; }
cd "$(dirname "$0")/.."
exec target/release/fhe-bend-owner "$1" "$2" "$PWD/target/release/fhe-bend" "$3"
