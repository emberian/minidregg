#!/bin/sh
# Exercise the exact journey helper bodies in an isolated private directory.
set -eu
umask 077
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
SCRATCH=$(mktemp -d /tmp/mini-journey-readonly-XXXXXXXX)
trap 'rm -rf -- "$SCRATCH"' EXIT
ROOT=$SCRATCH
JOURNEY=$ROOT/continuations/gitweb-journey
fail() { echo "journey readonly test: $*" >&2; exit 2; }
protected_chain() { [ -d "$1" ] && [ ! -L "$1" ]; }
# Read the production definitions. The test does not invoke the journey's
# root fixture gate, source signer, Mini Host, or any physical helper.
helpers=$(sed -n '/^claim() {/,/^finish() {/p' "$HERE/journey.sh" | sed '$d')
eval "$helpers"
claim_readonly materialize-request
printf '%s\n' partial >"$STEP/request.json"
[ "$STEP" = "$JOURNEY/materialize-request-0001" ]
claim_readonly materialize-request
[ "$STEP" = "$JOURNEY/materialize-request-0002" ]
printf '%s\n' complete >"$STEP/complete.txt"
[ "$(selected_action materialize-request)" = "$STEP" ]
[ "$(cat "$JOURNEY/materialize-request-0001/request.json")" = partial ]
if (claim_readonly materialize-request >/dev/null 2>&1); then
  fail 'completed action admitted a third claim'
fi
printf '%s\n' 'PASS: partial retained; second selected; third refused'
