#!/bin/bash
# Re-runnable two-stage plant: prepare a TEMP source copy, build it ONLY via
# request_cargo using the printed spec, then run the same two-world acceptance.
# No compiler is launched from a journey (prod train rule).
set -euo pipefail
usage() { echo "usage: $0 prepare TEMP_COPY | run TEMP_COPY MUTANT_RUST_BIN BASE_BIN NEW_RUN_ROOT [SIGNED_SPK]" >&2; exit 2; }
[[ $# -ge 2 ]] || usage
mode=$1 copy=$2
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
[[ $copy == /tmp/mini-spk-unit-plant-* && $copy != *[!a-zA-Z0-9_./-]* ]] || usage
needle='let name = format!("mini-spk-s{store}-a{app}-g{generation}.service");'
fault='let name = format!("mini-spk-a{app}-g{generation}.service");'
if [[ $mode == prepare ]]; then
  [[ $# == 2 && ! -e $copy ]] || usage
  mkdir -m 700 -p "$copy/deploy"
  cp -a "$repo/native" "$copy/native"
  cp -a "$repo/deploy/spk-host" "$copy/deploy/spk-host"
  source=$copy/native/spk-host/src/broker.rs
  grep -Fq "$needle" "$source"
  # Exact one-line constructor mutation, leaving inverse/guard unchanged.
  sed -i 's/let name = format!("mini-spk-s{store}-a{app}-g{generation}\.service");/let name = format!("mini-spk-a{app}-g{generation}.service");/' "$source"
  grep -Fq "$fault" "$source"
  if grep -Fq "$needle" "$source"; then echo 'constructor mutation did not happen' >&2; exit 1; fi
  sha256sum "$source" >"$copy/mutated-source-sha256.txt"
  printf 'BUILD VIA request_cargo: build --manifest-path %s/native/spk-host/Cargo.toml -p minidregg-spk-host --bins --target-dir %s/target\n' "$copy" "$copy"
  exit 0
fi
[[ $mode == run && ( $# == 5 || $# == 6 ) ]] || usage
mutant=$3 base=$4 run=$5 spk=${6:-}
source=$copy/native/spk-host/src/broker.rs
grep -Fq "$fault" "$source"
sha256sum -c "$copy/mutated-source-sha256.txt"
[[ $mutant == "$copy/target/debug" ]] || usage
log=$(mktemp /tmp/mini-spk-unit-plant-log.XXXXXXXX)
trap 'rm -f "$log"' EXIT
set +e
if [[ -n $spk ]]; then
  "$here/two-world-journey.sh" full "$base" "$mutant" "$run" "$spk" >"$log" 2>&1
else "$here/two-world-journey.sh" full "$base" "$mutant" "$run" >"$log" 2>&1; fi
rc=$?
set -e
[[ -d $run ]] || { cat "$log"; echo 'plant did not reach the two-world receiver' >&2; exit 1; }
cp "$log" "$run/plant-unit-name.log"
[[ $rc != 0 ]] || { echo 'plant failed: two-world run accepted id-less constructor' >&2; exit 1; }
grep -Fq 'unit-name-collision: rendered resident name lost store identity' "$log" || { cat "$log"; exit 1; }
grep -Fq 'removal_assertions=0' "$log" || { cat "$log"; echo 'plant cleanup not qualified' >&2; exit 1; }
printf 'RED unit-name-collision: rendered resident name lost store identity\n'
