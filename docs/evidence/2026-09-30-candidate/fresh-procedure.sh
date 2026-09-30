#!/usr/bin/env bash
# The exact procedure this evidence records, from a `git archive` tar to a
# finished journey, in one new directory. Nothing outside FRESH_DIR is written
# except the toolchain managers' caches (elan, rustup, $CARGO_HOME).
#
# usage: fresh-procedure.sh SOURCE.tar FRESH_DIR
set -euo pipefail
[ $# -eq 2 ] || { echo "usage: $0 SOURCE.tar FRESH_DIR" >&2; exit 2; }
tarball=$(cd "$(dirname "$1")" && pwd -P)/$(basename "$1")
F=$2
[ ! -e "$F" ] || { echo "refusing existing $F" >&2; exit 2; }
mkdir -p "$F"
F=$(cd "$F" && pwd -P)
T=$F/timings.tsv
printf 'phase\tseconds\texit\n' >"$T"
timed() {
  local phase=$1 start rc
  shift
  start=$(date +%s.%N)
  set +e
  "$@"
  rc=$?
  set -e
  printf '%s\t%s\t%s\n' "$phase" "$(awk -v a="$start" -v b="$(date +%s.%N)" 'BEGIN { printf "%.3f", b - a }')" "$rc" >>"$T"
  return "$rc"
}

cp "$tarball" "$F/source.tar"
mkdir "$F/src"
tar -x -f "$F/source.tar" -C "$F/src"
timed build "$F/src/deploy/candidate/build.sh" --source-archive "$F/source.tar" --out "$F/candidate" \
  >"$F/build.out" 2>&1
C=$F/candidate
timed verify-sums sh -c "cd '$C' && sha256sum --check SHA256SUMS" >"$F/verify-sums.out" 2>&1
cp "$C/genesis-params.example.json" "$F/genesis-params.json"
timed init "$C/run.sh" init --manifest "$C/manifest.json" --params "$F/genesis-params.json" \
  --state "$F/store" >"$F/init.out" 2>&1
timed start "$C/run.sh" start --state "$F/store" >"$F/start.out" 2>&1
timed sponsor "$C/run.sh" sponsor --state "$F/store" >"$F/sponsor.out" 2>&1
"$C/run.sh" unit --state "$F/store" >"$F/example.service"
set +e
timed journey "$C/journey.sh" --state "$F/store" --out "$F/journey" >"$F/journey.out" 2>&1
journey_rc=$?
set -e
timed stop "$C/run.sh" stop --state "$F/store" >"$F/stop.out" 2>&1
# The fresh-participant fixture, now driven by the manifest.
acceptance_rc=0
timed acceptance "$F/src/native/resource-client/newparticipant-acceptance.sh" "$C/manifest.json" \
  "$F/acceptance" >"$F/acceptance.out" 2>&1 || acceptance_rc=$?
if [ -f "$F/acceptance/state.json" ]; then
  timed acceptance-stop "$C/run.sh" stop --state "$F/acceptance" >"$F/acceptance-stop.out" 2>&1
fi
cat "$T"
[ "$journey_rc" = 0 ] && [ "$acceptance_rc" = 0 ]
