#!/usr/bin/env bash
set -euo pipefail
seat=$1; lane=$2; body=$3
case "$seat" in
 lean-main) threads=4; lock=/home/ember/workbox/.codex-persvati-lean-main.lock ;;
 lean-leaf[1-6]) threads=2; lock="/home/ember/workbox/.codex-persvati-$seat.lock" ;;
 rust1) threads=4; lock=/home/ember/workbox/.codex-persvati-build-slot1.lock ;;
 rust2) threads=4; lock=/home/ember/workbox/.codex-persvati-build-slot2.lock ;;
 *) exit 64 ;;
esac
exec >> "$lane/job.log" 2>&1
exec 9>"$lock";flock -n 9 || { echo 'persvati-job: VERDICT outcome=REFUSED reason=seat-busy';exit 75; }
exec 8>"$lane/.job-lifetime.lock";flock -n 8 || { echo 'persvati-job: VERDICT outcome=REFUSED reason=lane-busy';exit 75; }
printf 'owner=%s pid=%s seat=%s host=persvati\n' "${JOB_OWNER:-agent:redregg_evidence}" "$$" "$seat" > "$lane/.pbuild-lease"
trap 'rm -f "$lane/.pbuild-lease"' EXIT
export PATH=/home/ember/.cargo/bin:/home/ember/.elan/bin:/usr/bin:/bin
export RUSTUP_TOOLCHAIN=nightly-2026-06-21 LEAN_NUM_THREADS="$threads" CARGO_BUILD_JOBS="$threads" RAYON_NUM_THREADS="$threads"
export LEAN_BIN=/home/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean
printf 'Started UTC: ';date -u +%FT%TZ
python3 - <<'CG'
from pathlib import Path
p=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split(':')[-1].lstrip('/')
print('Enforced cgroup:',p);print({n:(p/n).read_text().strip() for n in ['memory.max','memory.swap.max','cpu.max','pids.max']})
CG
set +e
bash "$body"
status=$?
set -e
if [ "$status" -eq 0 ];then echo 'persvati-job: VERDICT outcome=PASS';else echo "persvati-job: VERDICT outcome=FAIL status=$status";fi
printf 'Finished UTC: ';date -u +%FT%TZ
exit "$status"
