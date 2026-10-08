#!/usr/bin/env bash
# scripts/burst/remote/collect.sh OUT_DIR [--srv /srv] -- burst-down's per-box half: gather everything that must
# outlive the box into OUT_DIR (no build products): the shared remote as one bundle (all refs), every lane's
# commits beyond its base as a thin bundle + its uncommitted diff/status/untracked list + logs/STATUS/LANE-ORIGIN,
# READY artifact sets (not .work), journeys, slots.log, box.env, SLOTS.txt, mini-logs, burst logs. Prints sizes.
set -uo pipefail
OUT=${1:?OUT_DIR}; shift; SRV=/srv; while [ $# -gt 0 ]; do case "$1" in --srv) SRV=$2; shift 2 ;; *) echo "collect: unknown $1" >&2; exit 64 ;; esac; done
export PATH=$HOME/.elan/bin:$PATH
mkdir -p "$OUT/lanes" "$OUT/box"
echo "== collect $(hostname) $(date -u +%FT%TZ) -> $OUT"
if [ -d "$SRV/git/minidregg.git" ]; then git --git-dir="$SRV/git/minidregg.git" bundle create "$OUT/shared-remote.bundle" --all 2>/dev/null && echo "shared remote: $(git --git-dir="$SRV/git/minidregg.git" for-each-ref | wc -l) refs bundled"; fi
base=$(sed -n 's/^tip=//p' "$SRV/warm-base/FROZEN" 2>/dev/null)
for L in "$SRV"/lanes/*/; do
  lane=$(basename "$L"); src=$L/src; [ -d "$src/.git" ] || continue
  d=$OUT/lanes/$lane; mkdir -p "$d"
  head=$(git -C "$src" rev-parse HEAD 2>/dev/null) || continue
  if [ -n "$base" ] && git -C "$src" merge-base --is-ancestor "$base" "$head" 2>/dev/null; then
    [ "$head" != "$base" ] && git -C "$src" bundle create "$d/$lane.bundle" "$base..HEAD" >/dev/null 2>&1 && echo "lane $lane: $(git -C "$src" rev-list --count "$base..HEAD") commits beyond base"
  else git -C "$src" bundle create "$d/$lane.bundle" HEAD --branches >/dev/null 2>&1 && echo "lane $lane: full bundle (base not an ancestor)"; fi
  git -C "$src" status --porcelain > "$d/status.txt" 2>/dev/null; git -C "$src" diff > "$d/uncommitted.diff" 2>/dev/null
  git -C "$src" ls-files --others --exclude-standard > "$d/untracked.txt" 2>/dev/null
  { echo "head=$head"; echo "branch=$(git -C "$src" rev-parse --abbrev-ref HEAD)"; } > "$d/HEAD.txt"
  rsync -a --exclude='*.olean' --exclude='rust-target' "$L/logs" "$d/" 2>/dev/null
  find "$L" -maxdepth 1 -type f \( -name '*.txt' -o -name '*.md' -o -name 'STATUS*' -o -name '*.sh' \) -exec cp -p {} "$d/" \; 2>/dev/null
  find "$src" -maxdepth 1 -type f \( -name 'STATUS*' -o -name '*.STATUS' \) -exec cp -p {} "$d/" \; 2>/dev/null
done
if [ -d "$SRV/artifacts" ]; then mkdir -p "$OUT/artifacts"; rsync -a --exclude='/.work' --exclude='/.leanenv' "$SRV/artifacts/" "$OUT/artifacts/" && echo "artifacts: $(ls -d "$OUT"/artifacts/[0-9a-f]*/ 2>/dev/null | wc -l) sets"; fi
[ -d "$SRV/journeys" ] && rsync -a --exclude='rows/*/run' "$SRV/journeys/" "$OUT/journeys/" 2>/dev/null
for f in "$SRV/pipeline/slots.log" "$SRV/pipeline/box.env" "$SRV/SLOTS.txt" "$SRV/pipeline/sccache.env" "$SRV/warm-base/FROZEN" "$SRV/artifacts/ALERTS"; do [ -f "$f" ] && cp -p "$f" "$OUT/box/"; done
[ -d "$SRV/mini-logs" ] && rsync -a "$SRV/mini-logs/" "$OUT/box/mini-logs/"
[ -d "$SRV/burst" ] && rsync -a "$SRV/burst/" "$OUT/box/burst/"
[ -f /var/log/burst-up.log ] && cp -p /var/log/burst-up.log "$OUT/box/"; [ -f /var/log/burst-bootstrap.log ] && cp -p /var/log/burst-bootstrap.log "$OUT/box/"
systemctl --user list-units --no-pager --no-legend --plain > "$OUT/box/units.txt" 2>/dev/null; "$SRV/pipeline/scripts/slots" --json > "$OUT/box/slots.json" 2>/dev/null
echo "== collected: $(du -sh "$OUT" | cut -f1) in $OUT"; du -sh "$OUT"/* 2>/dev/null | sort -h | tail -6
