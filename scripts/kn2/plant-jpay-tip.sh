#!/usr/bin/env bash
# Two independent teeth for the retained finalized-tip contract.
#   --lean: remove the real guard in TEMP Lean source; chainTip proof must fail.
#   --client MANIFEST.json [PAY_WATCHER]: remove immediate refusal in TEMP mini
#       source by substituting a wait; JPAY4's named tip step must fail.
# Run via the journey runner. Neither mode changes the checkout.
set -euo pipefail
ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
TMP=$(mktemp -d /tmp/plant-jpay-tip.XXXXXX)
trap 'rm -rf -- "$TMP"' EXIT
case ${1:-} in
  --lean)
    MUTANT=$TMP/PayObservation.lean
    cp "$ROOT/Kernel/PayObservation.lean" "$MUTANT"
    python3 - "$MUTANT" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1]); source = p.read_text()
guard = '  if ¬PayChainTip.advances (chainTipOf store) tip then .error .tipInvalidOrRegressing\n  else\n'
assert source.count(guard) == 1, 'PLANT DID NOT APPLY: expected one chain-tip guard'
p.write_text(source.replace(guard, '  -- PLANTED: behind-tip refusal removed\n', 1))
PY
    grep -Fxq '  -- PLANTED: behind-tip refusal removed' "$MUTANT"
    if grep -Fq 'if ¬PayChainTip.advances (chainTipOf store) tip then .error .tipInvalidOrRegressing' "$MUTANT"; then
      echo 'PLANT DID NOT APPLY: chain-tip guard remains' >&2; exit 1
    fi
    if (cd "$ROOT" && lake env lean "$MUTANT" >"$TMP/lean.log" 2>&1); then
      echo 'NOT RED: removed chain-tip guard compiled' >&2; exit 1
    fi
    python3 - "$MUTANT" "$TMP/lean.log" <<'PY'
from pathlib import Path
import re, sys
source, log = map(Path, sys.argv[1:])
lines = source.read_text().splitlines()
start = next(i+1 for i,l in enumerate(lines) if l.startswith('theorem decideObservations_chainTip '))
end = next(i+1 for i,l in enumerate(lines) if l.startswith('theorem decideObservations_tip '))
errors = [l for l in log.read_text().splitlines() if (m := re.search(r':(\d+):\d+: error:', l)) and start <= int(m[1]) < end]
assert errors, 'UNEXPECTED RED: no failure within decideObservations_chainTip\n' + log.read_text()
print('RED as intended: decideObservations_chainTip rejects removed behind-tip guard')
print(errors[0])
PY
    ;;
  --client)
    test "$#" -ge 2
    MANIFEST=$(realpath "$2")
    # Copy only sources: the mutant has independent writable Cargo package state.
    tar -C "$ROOT" --exclude=target --exclude=.git -cf - native deploy/pay deploy/shell/templates | tar -C "$TMP" -xf -
    MUTANT=$TMP/native/resource-client/src/pay.rs
    python3 - "$MUTANT" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1]); source = p.read_text()
old = '(_, Some("tipInvalidOrRegressing")) => return stop(&attempt, &result),'
new = '''(_, Some("tipInvalidOrRegressing")) => {
                    // PLANTED: immediate behind-tip refusal removed; wait instead.
                    decide(&attempt, "waiting", &result)?;
                    waiting(tally, "tipInvalidOrRegressing", tip, &view);
                    return Ok(Step::Stop);
                },'''
assert source.count(old) == 2, 'PLANT DID NOT APPLY: expected report and probe refusal branches'
p.write_text(source.replace(old, new))
PY
    test "$(grep -Fc 'PLANTED: immediate behind-tip refusal removed; wait instead.' "$MUTANT")" -eq 2
    if grep -Fq '(_, Some("tipInvalidOrRegressing")) => return stop(&attempt, &result),' "$MUTANT"; then
      echo 'PLANT DID NOT APPLY: immediate refusal remains' >&2; exit 1
    fi
    # Self-contained plant builds are allowed within request_journey. The
    # direct build/test workflow uses request_cargo, as required by the lane.
    cargo build --release -p minidregg-resource-client --bin mini \
      --manifest-path "$TMP/native/resource-client/Cargo.toml" --target-dir "$TMP/target" \
      >"$TMP/cargo.log" 2>&1 || { cat "$TMP/cargo.log" >&2; exit 1; }
    export HOST MINI STORE VERIFIER JOURNEY_STEP_DIR PAY_WATCHER_BIN
    HOST=$(jq -er '.host' "$MANIFEST")
    MINI=$TMP/target/release/mini
    STORE=$(jq -er '.store' "$MANIFEST")
    VERIFIER=$(jq -er '.verifier' "$MANIFEST")
    PAY_WATCHER_BIN=${3:-$(dirname "$HOST")/pay-watcher}
    JOURNEY_STEP_DIR=$TMP/journey
    mkdir -p "$JOURNEY_STEP_DIR"
    if bash "$TMP/native/resource-client/journey.d/jpay4.sh" >"$TMP/jpay4.out" 2>"$TMP/jpay4.err"; then
      echo 'NOT RED: JPAY4 accepted a behind-tip wait' >&2; exit 1
    fi
    PIN=$'FAIL\ttick C behind retained tip: refused tipInvalidOrRegressing immediately\t'
    if ! grep -F "$PIN" "$TMP/jpay4.err"; then
      echo 'UNEXPECTED RED: JPAY4 did not fail at the retained-tip refusal check' >&2
      cat "$TMP/jpay4.err" >&2; exit 1
    fi
    # Pin the fault itself as well as the check: an unrelated failure is no plant.
    grep -F 'waiting tipInvalidOrRegressing' "$TMP/jpay4.err"
    echo 'RED as intended: JPAY4 rejects waiting after tipInvalidOrRegressing'
    ;;
  *) echo "usage: $0 --lean | --client MANIFEST.json [PAY_WATCHER]" >&2; exit 2 ;;
esac
