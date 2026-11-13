#!/usr/bin/env bash
# reverts-probe.sh MINIDREGG_CLONE NANODREGG_CLONE SINCE [JOBS] [REF]
# Runs nanodregg's GATES-30 gate (gates/reverts.py, window 100) on every non-merge commit of
# MINIDREGG_CLONE's REF (default origin/main) since SINCE, skipping the builder's REDS.md and fixture commits.
# Prints one TSV row per flagged landing and a cost line. Read-only on both clones.
set -euo pipefail
mini=$1 nano=$2 since=$3 jobs=${4:-6} ref=${5:-origin/main}
out=$(mktemp -d)
git -C "$mini" log --since="$since" --no-merges --format='%H %s' "$ref" \
  | grep -v ' builder: REDS.md' | grep -v 'fixture rerecord' | cut -d' ' -f1 > "$out/commits"
export mini nano out
one() {
  local s e; s=$(date +%s%N)
  python3 -I "$nano/gates/reverts.py" "$mini" "$1" --window 100 > "$out/$1.txt" 2>&1 || true
  e=$(date +%s%N); echo "$1 $(( (e - s) / 1000000 ))" >> "$out/times"
}
export -f one
xargs -P "$jobs" -n 1 bash -c 'one "$0"' < "$out/commits"
printf 'commit\ttakes_back\thunks\tfiles\n'
for c in $(cat "$out/commits"); do
  { grep '^REVERTS' "$out/$c.txt" || true; } | while read -r _ L n rest; do printf '%s\t%s\t%s\t%s\n' "${c:0:9}" "$L" "$n" "${rest#* :: }"; done
done
sort -k2 -n "$out/times" | awk '{a[NR]=$2/1000} END {i=int(NR/2)+1; j=int(NR*0.95)+1; if (j>NR) j=NR;
  printf "commits %d  per-commit p50 %.2f s  p95 %.2f s  max %.2f s\n", NR, a[i], a[j], a[NR]}'
rm -rf "$out"
