#!/usr/bin/env bash
# The exact procedure this evidence records, from a `git archive` tar to a
# finished journey, in one new directory. Nothing outside FRESH_DIR is written
# except the toolchain managers' caches (elan, rustup, $CARGO_HOME).
#
# usage: [M7_REFERENCE=OTHER/provenance.json] [JOURNEY_GROWTH_LEVELS=...] \
#          fresh-procedure.sh SOURCE.tar FRESH_DIR
# M7_REFERENCE names an independent build of the same compiled inputs in another
# directory; the journey's M7 step compares all four hashes against it.
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
timed stop "$C/run.sh" stop --state "$F/store" >"$F/stop.out" 2>&1
# The single journey (native/resource-client/journey.sh), from the archive, on
# the candidate's manifest. It stands up its own fresh Store.
journey_rc=0
timed journey "$F/src/native/resource-client/journey.sh" "$C/manifest.json" "$F/journey" \
  >"$F/journey.out" 2>&1 || journey_rc=$?
# The acceptance fixture through the manifest wrapper; stop what it started.
acceptance_rc=0
timed acceptance "$F/src/native/resource-client/newparticipant-from-manifest.sh" "$C/manifest.json" \
  "$F/acceptance" >"$F/acceptance.out" 2>&1 || acceptance_rc=$?
if [ -f "$F/acceptance/public/server.pid" ]; then
  pid=$(cat "$F/acceptance/public/server.pid")
  case "$(tr '\0' ' ' <"/proc/$pid/cmdline" 2>/dev/null)" in
    *" serve "*"--socket $F/acceptance/public/mini.sock"*)
      kill -TERM "$pid"
      while kill -0 "$pid" 2>/dev/null; do sleep 0.2; done
      echo "stopped acceptance server $pid" >"$F/acceptance-stop.out" ;;
  esac
fi
cat "$T"
[ "$journey_rc" = 0 ] && [ "$acceptance_rc" = 0 ]
