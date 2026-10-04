#!/usr/bin/env bash
# advance-base-burst.sh TIP [GATED_LANE_DIR]  -- MERGE-KEEPER: move /srv/warm-base to TIP (GitHub main).
# With GATED_LANE_DIR (a mk-lane clone on THIS box whose src HEAD is TIP and whose umbrella is green):
#   that src becomes the base (no rebuild). Without: mk-lane a clone, fetch TIP, build it there under
#   swarm-build, then swap. The base is NOT-READY only for the two renames. Then mk-lane --verify a
#   probe lane (must replay 0 modules) and remove the probe (this script's own).
set -euo pipefail
TIP=$1; GL=${2:-}
W=/srv/warm-base; export PATH=$HOME/.elan/bin:$PATH
old=$(sed -n 's/^tip=//p' $W/FROZEN)
[ "$old" = "$TIP" ] && { echo "advance: already at $TIP"; exit 0; }
if [ -z "$GL" ]; then
  GL=/srv/lanes/mk-adv-${TIP:0:8}
  $W/mk-lane.sh mk-adv-${TIP:0:8}
  cd $GL/src && git fetch -q github main && [ "$(git rev-parse FETCH_HEAD)" = "$TIP" ] || { echo "advance: github main != $TIP"; exit 3; }
  git checkout -q -B main $TIP
  ( LEAN_NUM_THREADS=${THREADS:-8} SWARM_MEM_MAX=${SWARM_MEM_MAX:-32G} /srv/lanes/mk-tools/slot-mk.sh swarm-build lake build Minidregg +Host.Main:leanArts ObjectiveProofs ) > $GL/logs/advance-umbrella.log 2>&1 \
    || { echo "advance: umbrella RED in $GL (logs/advance-umbrella.log)"; exit 4; }
  green=$GL/logs/advance-umbrella.log
else
  cd $GL/src; [ "$(git rev-parse HEAD)" = "$TIP" ] || { echo "advance: $GL HEAD != $TIP"; exit 3; }
  green=$(ls -t $GL/logs/gate-*-umbrella.log | head -1); grep -q "^UMBRELLA rc=0" $green || { echo "advance: $green not green"; exit 4; }
fi
cd $GL/src
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "advance: tracked tree dirty in $GL"; exit 5; }
rm -rf build-logs target-gates   # gate outputs (untracked, this keeper's own)
git remote set-url base $W/src 2>/dev/null || true
echo "advancing $old -> $TIP by MERGE-KEEPER $(date -Is)" > $W/NOT-READY.txt
mv $W/src $W/src.prev-${old:0:8}
mv $GL/src $W/src
cp $green $W/logs/green-${TIP:0:8}.log
printf 'tip=%s\nfrozen_at=%s\nbuilt_in=%s\ngreen_log=%s\nprev=%s (kept at %s)\nrule=read-only base; lanes come from /srv/warm-base/mk-lane.sh <lane>; never build in /srv/warm-base/src\n' \
  $TIP "$(date -Is)" $GL $W/logs/green-${TIP:0:8}.log $old $W/src.prev-${old:0:8} > $W/FROZEN.new
mv -f $W/FROZEN.new $W/FROZEN
rm -f $W/NOT-READY.txt
echo "advance: base at $TIP; verifying"
probe=mk-verify-${TIP:0:8}
$W/mk-lane.sh --verify $probe
rm -rf /srv/lanes/$probe
rmdir $GL 2>/dev/null || mv $GL /srv/lanes/.spent-$(basename $GL)
echo "advance: DONE $TIP"
