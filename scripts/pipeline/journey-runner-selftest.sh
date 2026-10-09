#!/usr/bin/env bash
# Isolated receiving-path plants. Run hub-side via request_journey, never live roots.
set -euo pipefail
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
work=${1:?usage: journey-runner-selftest.sh NEW_EVIDENCE_DIR}
[ ! -e "$work" ]
mkdir -p "$work/source/scripts/pipeline" "$work/artifacts"
work=$(realpath "$work")
export PIPELINE_ROOT=$work/installed ARTIFACT_ROOT=$work/artifacts
tip=1111111111111111111111111111111111111111
setdir=$ARTIFACT_ROOT/$tip
mkdir "$setdir"
for file in journey-runner journey-rows lib.sh journey-red-lines journey-row-finish journey-row-exec; do
  cp "$here/$file" "$work/source/scripts/pipeline/$file"
done
cat >"$work/source/scripts/pipeline/journey-rows" <<'ROWS'
JOURNEY_ROWS=(ok red signal timed oom)
row_ok() { echo 'synthetic driver PASS' >&2; }
row_red() { echo 'synthetic real refusal' >&2; return 17; }
row_signal() { kill -TERM "$BASHPID"; }
row_timed() { sleep 20; }
row_oom() { python3 -c 'allocation = bytearray(256 * 1024 * 1024); print(len(allocation))'; }
ROWS
tar -cf "$setdir/source.tar" -C "$work/source" .
(cd "$setdir" && sha256sum source.tar >SHA256SUMS)
touch "$setdir/READY"

# Mutation: an installed runner differs from the tip's. Assert the mutation and
# refusal through the real runner, without any override that can bypass identity.
mkdir -p "$work/stale"
cp "$here/"{journey-runner,journey-rows,lib.sh,journey-red-lines,journey-row-finish,journey-row-exec} "$work/stale/"
echo '# planted stale installed runner' >>"$work/stale/journey-runner"
if cmp -s "$work/stale/journey-runner" "$work/source/scripts/pipeline/journey-runner"; then exit 1; fi
if bash "$work/stale/journey-runner" --tip "$tip" --row ok --results-root "$work/mismatch" >"$work/mismatch.out" 2>"$work/mismatch.err"; then exit 1; fi
grep -F 'runner/tip mismatch: journey-runner' "$work/mismatch.err"
[ ! -f "$work/mismatch/$tip/DONE" ]

# Installing the stable launcher dispatches the exact tip copy; it must PASS.
bash "$here/install-journey-launcher" "$PIPELINE_ROOT"
cmp "$here/journey-launcher" "$PIPELINE_ROOT/scripts/journey-runner"
for row in ok red signal timed oom; do
  env PIPELINE_ROW_TIMEOUT_S=2 PIPELINE_ROW_MEM_MAX=64M \
    bash "$PIPELINE_ROOT/scripts/journey-runner" --tip "$tip" --row "$row" --results-root "$work/$row"
  result=$work/$row/$tip/results.tsv
  if [ "$row" = ok ]; then
    awk -F'\t' '$1=="ok" && $2=="PASS" {ok=1} END {exit !ok}' "$result"
  else
    awk -F'\t' '$2=="FAIL" && $5 ~ /rc=[0-9]+/ && $5 ~ /Result=/ && $5 ~ /MemoryPeak=[0-9]+/ && $5 ~ /timeout=/ {ok=1} END {exit !ok}' "$result"
    case "$row" in
      red) grep -F 'rc=17' "$result"; grep -F 'synthetic real refusal' "$result" ;;
      signal) grep -F 'signal=TERM sender=unknown' "$result" ;;
      timed) grep -F 'Result=timeout' "$result"; grep -F 'sender=systemd user manager' "$result" ;;
      oom) grep -F 'Result=oom-kill' "$result"; grep -F 'kernel cgroup OOM killer' "$result"
        awk -F= '$1=="MemoryPeak" && $2 >= 67108864 {ok=1} END {exit !ok}' "$work/$row/$tip/rows/$row/cgroup-final.properties" ;;
    esac
  fi
done
echo 'PASS: stale installed runner refused; exact tip dispatched; red/signal/timeout/OOM causes retained'
