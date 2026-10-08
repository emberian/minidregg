#!/usr/bin/env bash
# scripts/burst/make-warm-base.sh -- freeze a copy of the cold-built $SRV/mini as $SRV/warm-base/src, with the
# repo's mk-lane.sh beside it, NOT-READY through the copy and a verify probe (0 modules compiled) before publishing.
set -euo pipefail
SRV=${SRV:-/srv}; W=$SRV/warm-base; [ -f "$SRV/pipeline/box.env" ] && . "$SRV/pipeline/box.env"
export PATH=$HOME/.elan/bin:$PATH
R=$(readlink -f "$SRV/mini-logs/cold-build-latest.result")
grep -q '^build_rc=0 ' "$R" || { echo "cold build not green: $R"; exit 1; }
TIP=$(sed -n 's/^tip=//p' "$R")
[ "$(git -C "$SRV/mini" rev-parse HEAD)" = "$TIP" ] || { echo "$SRV/mini moved off $TIP"; exit 1; }
if [ -f "$W/FROZEN" ] && [ "$(sed -n 's/^tip=//p' "$W/FROZEN")" = "$TIP" ] && [ ! -e "$W/NOT-READY.txt" ]; then echo "warm base already frozen at $TIP"; exit 0; fi
[ ! -e "$W/src" ] || { echo "$W/src exists (advance with scripts/pipeline/advance-base-burst.sh instead)"; exit 1; }
mkdir -p "$W/logs"
echo "base being built $(date -Is)" > "$W/NOT-READY.txt"
rsync -aH "$SRV/mini/" "$W/src/"
cp -p "$(readlink -f "$SRV/mini-logs/cold-build-latest.log")" "$W/logs/green.log"; cp -p "$R" "$W/logs/green.result"
for p in "$W"/src/.lake/packages/*/; do git -C "$p" config core.trustctime false; done
git -C "$W/src" config core.trustctime false
[ -z "$(git -C "$W/src" status --porcelain --untracked-files=no)" ] || { echo "base tracked tree dirty"; exit 1; }
mk=$SRV/mini/scripts/pipeline/mk-lane.sh    # the TIP tree's copy, never a tools-dir one
[ -f "$mk" ] && grep -q MK_LANE_PROBE "$mk" || { echo "make-warm-base: $mk is missing or predates MK_LANE_PROBE"; exit 9; }
install -m 755 "$mk" "$W/mk-lane.sh"
printf 'tip=%s\nfrozen_at=%s\nbuilt_on=%s:%s/mini\n%s\nrule=read-only base; lanes come from %s/mk-lane.sh <lane>; never build in %s/src\n' \
  "$TIP" "$(date -Is)" "$(hostname)" "$SRV" "$(grep -E '^(build_wall|build_rc)' "$R" | tr ' ' '\n' | grep -E '^build_(wall|rc)=' | paste -sd' ')" "$W" "$W" > "$W/FROZEN"
[ "$(git -C "$SRV/mini" rev-parse HEAD)" = "$TIP" ] && [ "$(git -C "$W/src" rev-parse HEAD)" = "$TIP" ] || { echo "tip moved during the copy"; exit 1; }
echo "verifying $TIP (make-warm-base $(date -Is))" > "$W/NOT-READY.txt"
p=mk-verify-${TIP:0:8}
rm -rf /srv/lanes/$p 2>/dev/null || true   # a probe an earlier failed verify left behind is the relay's own
if MK_LANE_PROBE=1 "$W/mk-lane.sh" --verify "$p"; then rm -f "$W/NOT-READY.txt"; rm -rf "$SRV/lanes/$p"; echo "warm base frozen at $TIP (verified replay)"; du -sh "$W/src" "$W/src/.lake"
else echo "verify FAILED after make-warm-base $TIP $(date -Is): see $SRV/lanes/$p/logs/verify-replay.log" > "$W/NOT-READY.txt"; echo "make-warm-base: VERIFY FAILED; base stays NOT-READY"; exit 8; fi
