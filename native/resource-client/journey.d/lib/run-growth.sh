#!/usr/bin/env bash
# The growth row's selected receiving-path journey, for request_journey.
set -euo pipefail
growth_here=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
export JOURNEY_STEPS="J0 J1 J2 J3 J4 G"
export JOURNEY_GROWTH_LEVELS="10 100 500 1000"
exec bash "$growth_here/journey.sh" "$@"
