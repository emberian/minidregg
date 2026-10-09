#!/usr/bin/env bash
# CLOCK-BOUND receiving evidence using an exact-source Host/client and base custody binaries.
# Usage: plant-clock-bound-acceptance.sh MODE HOST MINI BASE_MANIFEST NEW_ROOT
# MODE: genesis | clock | fixture
set -euo pipefail
MODE=${1:?mode}; HOST=${2:?host}; MINI=${3:?mini}; BASE=${4:?base manifest}; RUN=${5:?new run root}
ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
[ ! -e "$RUN" ] || { echo "clock-bound acceptance: refusing existing $RUN" >&2; exit 2; }
mkdir -m 700 "$RUN"
cd "$ROOT"
CONSENT=$ROOT/.lake/build/bin/minidregg-client-consent
sha256sum "$HOST" "$MINI" "$CONSENT" >"$RUN/changed-binaries.sha256"
jq --arg host "$HOST" --arg mini "$MINI" --arg consent "$CONSENT" \
  --arg hh "$(sha256sum "$HOST" | cut -d' ' -f1)" \
  --arg mh "$(sha256sum "$MINI" | cut -d' ' -f1)" \
  --arg ch "$(sha256sum "$CONSENT" | cut -d' ' -f1)" \
  '.host=$host | .mini=$mini | .shell=$mini | .consent=$consent | .consentHost=$consent | .sha256.host=$hh | .sha256.mini=$mh | .sha256.shell=$mh | .sha256.consent=$ch | .sha256.consentHost=$ch' \
  "$BASE" >"$RUN/manifest.json"
case "$MODE" in
  genesis)
    cp native/resource-client/genesis-params.example.json "$RUN/valid.json"
    sh deploy/candidate/params.sh fill-genesis "$RUN/valid.json"
    sh native/resource-client/genesis.sh --check "$RUN/valid.json"
    refuse() {
      local name=$1 edit=$2 expect=$3
      jq "$edit" "$RUN/valid.json" >"$RUN/$name.json"
      if sh native/resource-client/genesis.sh --check "$RUN/$name.json" >"$RUN/$name.out" 2>"$RUN/$name.err"; then
        echo "genesis unexpectedly accepted $name" >&2; exit 1
      fi
      grep -Fq "$expect" "$RUN/$name.err"
      printf 'PASS %s: %s\n' "$name" "$(cat "$RUN/$name.err")"
    }
    for pair in 'missing|del(.clock.maxStepSeconds)' 'zero|.clock.maxStepSeconds=0' \
      'fraction|.clock.maxStepSeconds=1.5' 'string|.clock.maxStepSeconds="300"' \
      'negative|.clock.maxStepSeconds=-1' 'null|.clock.maxStepSeconds=null' \
      'range|.clock.maxStepSeconds=9007199254740992'; do
      refuse "${pair%%|*}" "${pair#*|}" clockStepBoundInvalid
    done
    refuse seed-missing 'del(.clock.genesisNow)' clockGenesisNowInvalid
    refuse seed-zero '.clock.genesisNow=0' clockGenesisNowInvalid
    refuse clock-missing 'del(.clock)' clockStepBoundInvalid
    # Verify the existing schema's refusal too, on an unmodified base script.
    git show e0a8ba21a3:native/resource-client/genesis.sh >"$RUN/base-genesis.sh"
    if sh "$RUN/base-genesis.sh" --check "$RUN/clock-missing.json" >"$RUN/base.out" 2>"$RUN/base.err"; then
      echo 'base unexpectedly accepted missing .clock' >&2; exit 1
    fi
    grep -Fq 'params file fails' "$RUN/base.err"
    # candidate_resolve needs the valid base manifest; init rejects params before creating state.
    if sh deploy/candidate/run.sh init --manifest "$BASE" --params "$RUN/clock-missing.json" \
      --state "$RUN/state" >"$RUN/init.out" 2>"$RUN/init.err"; then
      echo 'run.sh init unexpectedly accepted missing .clock' >&2; exit 1
    fi
    grep -Fq clockStepBoundInvalid "$RUN/init.err"
    [ ! -e "$RUN/state" ]
    echo 'PASS base schema and run.sh init refuse missing .clock before state creation'
    ;;
  clock)
    # Select KC with its actual dependencies, without touching the journey runner.
    JOURNEY_STEPS='J0 J1 J2 J3 J4 KC' JOURNEY_BUDGET_S=7200 \
      bash native/resource-client/journey.sh "$RUN/manifest.json" "$RUN/journey"
    ;;
  fixture)
    mkdir -m 700 "$RUN/bin"
    ln -s "$HOST" "$RUN/bin/minidregg-host"
    ln -s "$MINI" "$RUN/bin/mini"
    ln -s "$CONSENT" "$RUN/bin/minidregg-client-consent"
    for role in store verifier; do
      path=$(jq -er --arg role "$role" '.[$role]' "$BASE")
      case "$role" in
        store) name=minidregg-link-sqlite-store ;;
        verifier) name=minidregg-credential-signature-verifier ;;
      esac
      ln -s "$path" "$RUN/bin/$name"
    done
    WORLD=$(mktemp -d /tmp/cb-fixture.XXXXXX)
    rmdir "$WORLD" # acceptance creates its own new root; keep Unix socket path short.
    printf '%s\n' "$WORLD" >"$RUN/world-path.txt"
    cleanup() {
      if [ -f "$WORLD/state.json" ]; then
        python3 native/resource-client/objective-native-acceptance.py stop --root "$WORLD"
      fi
      if [ -f "$WORLD-disabled/state.json" ]; then
        python3 native/resource-client/objective-native-acceptance.py stop --root "$WORLD-disabled"
      fi
    }
    trap cleanup EXIT
    python3 native/resource-client/objective-native-acceptance.py all --bin "$RUN/bin" --root "$WORLD"
    bash scripts/native-accepted-fixture/generate.sh "$WORLD"
    ;;
  *) echo 'mode must be genesis, clock or fixture' >&2; exit 2 ;;
esac
