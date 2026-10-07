#!/usr/bin/env bash
# advance-base-burst.sh TIP [GATED_LANE_DIR]  -- MERGE-KEEPER: move this box's warm base to TIP (GitHub main).
# With GATED_LANE_DIR (a mk-lane clone on THIS box whose src HEAD is TIP and whose umbrella is green):
#   that src becomes the base (no rebuild). Without: mk-lane a clone, fetch TIP, build it there in the gate
#   slot under swarm-build, then swap. Then a probe lane (mk-lane --verify) must replay 0 modules BEFORE the
#   base is published: NOT-READY.txt stays through the swap AND the verify (`verifying ...`), and a failed
#   verify leaves it in place with the reason (exit 8) instead of a FROZEN base nobody can replay from.
# The base's mk-lane.sh is refreshed from this script's directory (the repo's one copy) at every advance.
# Refuses when NOT-READY is set (another advance, or a failed one) or src.prev-<old> already exists.
set -euo pipefail
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
PIPELINE_ROOT=${PIPELINE_ROOT:-/srv/pipeline}
[ -f "$PIPELINE_ROOT/box.env" ] && . "$PIPELINE_ROOT/box.env"
TIP=$1; GL=${2:-}
W=${PIPELINE_WARM_BASE:-/srv/warm-base}; LANES=${PIPELINE_LANES:-/srv/lanes}
export PATH=$HOME/.elan/bin:$PATH
[[ $TIP =~ ^[0-9a-f]{40}$ ]] || { echo "advance: TIP must be 40 hex"; exit 2; }
old=$(sed -n 's/^tip=//p' "$W/FROZEN")
[ "$old" = "$TIP" ] && { echo "advance: already at $TIP"; exit 0; }
[ ! -e "$W/NOT-READY.txt" ] || { echo "advance: REFUSED, $W is NOT-READY: $(cat "$W/NOT-READY.txt")"; exit 6; }
[ ! -e "$W/src.prev-${old:0:8}" ] || { echo "advance: REFUSED, $W/src.prev-${old:0:8} exists (an earlier advance from $old); move it aside"; exit 7; }
if [ -z "$GL" ]; then
  GL=$LANES/mk-adv-${TIP:0:8}
  "$here/mk-lane.sh" "mk-adv-${TIP:0:8}"
  cd "$GL/src" && git fetch -q github main && [ "$(git rev-parse FETCH_HEAD)" = "$TIP" ] || { echo "advance: github main != $TIP"; exit 3; }
  git checkout -q -B main "$TIP"
  ( LEAN_NUM_THREADS=${THREADS:-${LEAN_NUM_THREADS:-8}} SWARM_MEM_MAX=${SWARM_MEM_MAX:-32G} SWARM_BUILD_TAG="advance-${TIP:0:8}" \
      "$here/slot-mk.sh" swarm-build lake build Minidregg +Host.Main:leanArts ObjectiveProofs ) > "$GL/logs/advance-umbrella.log" 2>&1 \
    || { echo "advance: umbrella RED in $GL (logs/advance-umbrella.log)"; exit 4; }
  green=$GL/logs/advance-umbrella.log
else
  cd "$GL/src"; [ "$(git rev-parse HEAD)" = "$TIP" ] || { echo "advance: $GL HEAD != $TIP"; exit 3; }
  green=$(ls -t "$GL"/logs/gate-*-umbrella.log | head -1); grep -q "^UMBRELLA rc=0" "$green" || { echo "advance: $green not green"; exit 4; }
fi
cd "$GL/src"
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "advance: tracked tree dirty in $GL"; exit 5; }
rm -rf build-logs target-gates   # gate outputs (untracked, this keeper's own)
git remote set-url base "$W/src" 2>/dev/null || true
install -m 755 "$here/mk-lane.sh" "$W/.mk-lane.sh.new" && mv -f "$W/.mk-lane.sh.new" "$W/mk-lane.sh"
echo "advancing $old -> $TIP by MERGE-KEEPER $(date -Is)" > "$W/NOT-READY.txt"
mv "$W/src" "$W/src.prev-${old:0:8}"
mv "$GL/src" "$W/src"
cp "$green" "$W/logs/green-${TIP:0:8}.log"
printf 'tip=%s\nfrozen_at=%s\nbuilt_in=%s\ngreen_log=%s\nprev=%s (kept at %s)\nrule=read-only base; lanes come from %s/mk-lane.sh <lane>; never build in %s/src\n' \
  "$TIP" "$(date -Is)" "$GL" "$W/logs/green-${TIP:0:8}.log" "$old" "$W/src.prev-${old:0:8}" "$W" "$W" > "$W/FROZEN.new"
mv -f "$W/FROZEN.new" "$W/FROZEN"
echo "verifying $TIP (advance by MERGE-KEEPER $(date -Is)); lanes wait for the replay probe" > "$W/NOT-READY.txt"
probe=mk-verify-${TIP:0:8}
if MK_LANE_PROBE=1 "$W/mk-lane.sh" --verify "$probe"; then
  rm -f "$W/NOT-READY.txt"; rm -rf "$LANES/$probe"
else
  echo "verify FAILED after advance to $TIP $(date -Is): the base does not replay; see $LANES/$probe/logs/verify-replay.log; fix or roll back ($W/src.prev-${old:0:8})" > "$W/NOT-READY.txt"
  echo "advance: VERIFY FAILED; $W stays NOT-READY ($(cat "$W/NOT-READY.txt"))"; exit 8
fi
rmdir "$GL" 2>/dev/null || mv "$GL" "$LANES/.spent-$(basename "$GL")"
echo "advance: DONE $TIP (verified replay)"
