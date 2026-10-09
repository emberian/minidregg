#!/bin/sh
# Source this file, then candidate_params_now INPUT.json > NEW_PARAMS.json.
# Numeric zero is the example's wall-clock placeholder; explicit positive
# integer seconds are preserved. Missing, null, strings and negatives refuse.
candidate_params_now() {
  jq --argjson candidate_now "$(date +%s)" '
    def positive_seconds: type == "number" and . > 0 and . == floor and . < 9007199254740992;
    if (.clock.genesisNow | type == "number" and . == 0) then
      .clock.genesisNow = $candidate_now
    else . end
    | if (.clock.genesisNow | positive_seconds) then .
      else error("clock.genesisNow must be positive unix seconds or the numeric zero placeholder") end
    | if (.clock.maxStepSeconds | positive_seconds) then .
      else error("clock.maxStepSeconds must be a positive integer") end
  ' "$1"
}
