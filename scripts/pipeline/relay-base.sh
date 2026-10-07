#!/usr/bin/env bash
# relay-base.sh TIP SRC_HOST DST_HOST [SRC_DIR] : copy the gated warm tree at TIP from SRC_HOST:SRC_DIR
# (default /srv/warm-base/src) into DST_HOST:/srv/warm-base, relayed through this machine (tar|zstd).
# .lake/packages is NOT sent: the receiver hardlinks its own (same lake-manifest). The receiver's src is
# swapped in by rename under NOT-READY, FROZEN rewritten, and the base is PUBLISHED (NOT-READY removed)
# ONLY after a probe lane replays 0 modules; a failed verify leaves NOT-READY with the reason, exit 8.
# The receiver's mk-lane.sh is refreshed from this script's directory (the repo's one copy).
# Remote steps are shell SCRIPTS fed over stdin (bash -s with positional args), not quoted strings.
set -euo pipefail
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
T=$1 SH=$2 DH=$3 SD=${4:-/srv/warm-base/src}
[[ $T =~ ^[0-9a-f]{40}$ ]] || { echo "relay: TIP must be 40 hex" >&2; exit 2; }
ssh "$SH" bash -s -- "$T" "$SD" <<'SRC'
set -e; T=$1 SD=$2; cd "$SD"
[ "$(git rev-parse HEAD)" = "$T" ] || { echo "relay: $(hostname):$SD is at $(git rev-parse --short HEAD), not $T" >&2; exit 3; }
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "relay: $(hostname):$SD tracked tree dirty" >&2; exit 3; }
SRC
ssh "$DH" bash -s -- "$T" <<'PRE'
set -e; T=$1; W=/srv/warm-base; old=$(sed -n 's/^tip=//p' $W/FROZEN)
[ "$old" != "$T" ] || { echo "relay: $(hostname) base already at $T"; exit 10; }
[ ! -e "$W/NOT-READY.txt" ] || { echo "relay: $(hostname) base NOT-READY: $(cat $W/NOT-READY.txt)" >&2; exit 6; }
[ ! -e "$W/src.prev-${old:0:8}" ] || { echo "relay: $W/src.prev-${old:0:8} exists; move it aside" >&2; exit 7; }
git -C $W/src cat-file -e "$T^{commit}" 2>/dev/null || git -C $W/src fetch -q https://github.com/emberian/minidregg.git "$T"
git -C $W/src diff --quiet "$old" "$T" -- lake-manifest.json lean-toolchain || { echo "relay: manifest/toolchain changed $old..$T: cold path needed" >&2; exit 9; }
rm -rf $W/src.new; mkdir -p $W/src.new/.lake; cp -al $W/src/.lake/packages $W/src.new/.lake/packages
PRE
s=$(date +%s)
ssh "$SH" "tar -C '$SD' --exclude=./.lake/packages -cf - . | zstd -3 -T8 -q -c" | ssh "$DH" "zstd -d -q -c | tar -C /srv/warm-base/src.new -xf -"
echo "relay: copied in $(( $(date +%s) - s ))s"
scp -q "$here/mk-lane.sh" "$DH:/srv/warm-base/.mk-lane.sh.new"
ssh "$DH" bash -s -- "$T" "$SH" "$SD" <<'POST'
set -e; T=$1 SH=$2 SD=$3; W=/srv/warm-base; old=$(sed -n 's/^tip=//p' $W/FROZEN)
[ -f /srv/pipeline/box.env ] && . /srv/pipeline/box.env; export PATH=$HOME/.elan/bin:$PATH
cd $W/src.new
[ "$(git rev-parse HEAD)" = "$T" ] || { echo "relay: copy HEAD != $T" >&2; exit 3; }
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "relay: copy tracked tree dirty" >&2; exit 3; }
git remote set-url base $W/src 2>/dev/null || true
chmod 755 $W/.mk-lane.sh.new && mv -f $W/.mk-lane.sh.new $W/mk-lane.sh
echo "advancing $old -> $T (copy from $SH:$SD) $(date -Is)" > $W/NOT-READY.txt
mv $W/src $W/src.prev-${old:0:8}; mv $W/src.new $W/src
printf 'tip=%s\nfrozen_at=%s\nbuilt_in=%s:%s (copied by relay; .lake/packages hardlinked from prev)\nprev=%s (kept at %s)\nrule=read-only base; lanes come from /srv/warm-base/mk-lane.sh <lane>; never build in /srv/warm-base/src\n' \
  "$T" "$(date -Is)" "$SH" "$SD" "$old" "$W/src.prev-${old:0:8}" > $W/FROZEN.new; mv -f $W/FROZEN.new $W/FROZEN
echo "verifying $T (relay from $SH $(date -Is)); lanes wait for the replay probe" > $W/NOT-READY.txt
p=mk-verify-${T:0:8}
if MK_LANE_PROBE=1 timeout 900 $W/mk-lane.sh --verify $p; then rm -f $W/NOT-READY.txt; rm -rf /srv/lanes/$p; echo "relay: $(hostname) base at $T, verified replay"
else echo "verify FAILED after relay to $T $(date -Is): see /srv/lanes/$p/logs/verify-replay.log; roll back from $W/src.prev-${old:0:8}" > $W/NOT-READY.txt; echo "relay: VERIFY FAILED on $(hostname); base stays NOT-READY" >&2; exit 8; fi
POST
