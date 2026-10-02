#!/usr/bin/env bash
# Continue JDV on its existing Store and service, before journey.sh cleanup.
# No bootstrap, participant enrollment, alternate Store or room-key shortcut.
set -euo pipefail
: "${JOURNEY_RUN:?}" "${JOURNEY_WORLD:?}" "${JOURNEY_STEP_DIR:?}"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
export PD_FIXTURE_DIR="$JOURNEY_RUN/steps/JDV"
export PD_OWNER_WS="$PD_FIXTURE_DIR/w/amy" PD_MEMBER_WS="$PD_FIXTURE_DIR/w/ben"
export PD_OWNER_HOME="$PD_FIXTURE_DIR/h/amy" PD_MEMBER_HOME="$PD_FIXTURE_DIR/h/ben"
export PD_OWNER_PASS=cache-pass-amy PD_MEMBER_PASS=cache-pass-ben
exec "$HERE/../../../scripts/protected-document-journey.sh"
