#!/usr/bin/env bash
# relay-base.sh TIP SRC_HOST DST_HOST [SRC_DIR] : copy the gated warm tree at TIP from SRC_HOST:SRC_DIR
# (default /srv/warm-base/src) into DST_HOST:/srv/warm-base, relayed through this machine (tar|zstd).
# .lake/packages is NOT sent: the receiver hardlinks its own (same lake-manifest). The receiver's src is
# swapped in by rename under NOT-READY, FROZEN rewritten, and the base is PUBLISHED (NOT-READY removed)
# ONLY after a probe lane replays 0 modules; a failed verify leaves NOT-READY with the reason, exit 8.
# The receiver's mk-lane.sh is the TIP TREE's scripts/pipeline/mk-lane.sh (copied with the tree), never a tools-dir
# copy (10-07 06:41Z: a stale copy without MK_LANE_PROBE left a base NOT-READY); it must know MK_LANE_PROBE or the relay
# refuses before the swap.
# A receiver with NO base yet (a fresh box, burst-up) gets everything, .lake/packages included: a warm base
# is copied from a sibling, never cold-built twice (WARM BASES, NEVER PARALLEL REBUILDS).
# Remote steps are shell SCRIPTS fed over stdin (bash -s with positional args), not quoted strings.
# PIPELINE_SSH overrides the ssh command (burst-up passes its -F config through it).
set -euo pipefail
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
SSH=${PIPELINE_SSH:-ssh}
T=$1 SH=$2 DH=$3 SD=${4:-/srv/warm-base/src}
# SRC_HOST `local`: the source tree is on THIS machine (run relay-base on the box that has the base).
if [ "$SH" = local ]; then src_sh() { bash -s -- "$@"; }; src_run() { bash -c "$1"; }; else src_sh() { $SSH "$SH" bash -s -- "$@"; }; src_run() { $SSH "$SH" "$1"; }; fi
[[ $T =~ ^[0-9a-f]{40}$ ]] || { echo "relay: TIP must be 40 hex" >&2; exit 2; }
src_sh "$T" "$SD" <<'SRC'
set -e; T=$1 SD=$2; cd "$SD"
[ "$(git rev-parse HEAD)" = "$T" ] || { echo "relay: $(hostname):$SD is at $(git rev-parse --short HEAD), not $T" >&2; exit 3; }
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "relay: $(hostname):$SD tracked tree dirty" >&2; exit 3; }
SRC
fresh=0; $SSH "$DH" "[ -d /srv/warm-base/src/.git ]" || fresh=1
$SSH "$DH" bash -s -- "$T" "$fresh" <<'PRE'
set -e; T=$1 fresh=$2; W=/srv/warm-base; mkdir -p $W/logs
if [ "$fresh" = 1 ]; then rm -rf $W/src.new; mkdir -p $W/src.new; echo "relay: $(hostname) has no base: full copy incl. .lake/packages"; exit 0; fi
old=$(sed -n 's/^tip=//p' $W/FROZEN)
[ "$old" != "$T" ] || { echo "relay: $(hostname) base already at $T"; exit 10; }
[ ! -e "$W/NOT-READY.txt" ] || { echo "relay: $(hostname) base NOT-READY: $(cat $W/NOT-READY.txt)" >&2; exit 6; }
[ ! -e "$W/src.prev-${old:0:8}" ] || { echo "relay: $W/src.prev-${old:0:8} exists; move it aside" >&2; exit 7; }
git -C $W/src cat-file -e "$T^{commit}" 2>/dev/null || git -C $W/src fetch -q https://github.com/emberian/minidregg.git "$T"
git -C $W/src diff --quiet "$old" "$T" -- lake-manifest.json lean-toolchain || { echo "relay: manifest/toolchain changed $old..$T: cold path needed" >&2; exit 9; }
rm -rf $W/src.new; mkdir -p $W/src.new/.lake; cp -al $W/src/.lake/packages $W/src.new/.lake/packages
PRE
s=$(date +%s)
excl="--exclude=./.lake/packages"; [ "$fresh" = 1 ] && excl=""
src_run "tar -C '$SD' $excl -cf - . | zstd -3 -T8 -q -c" | $SSH "$DH" "zstd -d -q -c | tar -C /srv/warm-base/src.new -xf -"
echo "relay: copied in $(( $(date +%s) - s ))s"
# the source base's green log travels too: mk-lane --verify's positive control (the Built-line pattern must match
# a real build log) reads $W/logs/green*.log on the RECEIVER, which a fresh box does not have
src_run "cat \$(ls -t $(dirname "$SD")/logs/green*.log 2>/dev/null | head -1)" | $SSH "$DH" "cat > /srv/warm-base/logs/green-relayed-${T:0:8}.log"
$SSH "$DH" bash -s -- "$T" "$SH" "$SD" "$fresh" <<'POST'
set -e; T=$1 SH=$2 SD=$3 fresh=$4; W=/srv/warm-base; old=$(sed -n 's/^tip=//p' $W/FROZEN 2>/dev/null || true)
if [ "$fresh" = 1 ]; then cp -p $W/src.new/.lake/../lake-manifest.json /dev/null 2>/dev/null || true; for p in $W/src.new/.lake/packages/*/; do git -C "$p" config core.trustctime false; done; git -C $W/src.new config core.trustctime false; fi
[ -f /srv/pipeline/box.env ] && . /srv/pipeline/box.env; export PATH=$HOME/.elan/bin:$PATH
mkdir -p /srv/lanes; cd $W/src.new
[ "$(git rev-parse HEAD)" = "$T" ] || { echo "relay: copy HEAD != $T" >&2; exit 3; }
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "relay: copy tracked tree dirty" >&2; exit 3; }
git remote set-url base $W/src 2>/dev/null || true
mk=$W/src.new/scripts/pipeline/mk-lane.sh
[ -f "$mk" ] && grep -q MK_LANE_PROBE "$mk" || { echo "relay: REFUSED, the tip tree's scripts/pipeline/mk-lane.sh is missing or predates MK_LANE_PROBE" >&2; exit 9; }
install -m 755 "$mk" $W/.mk-lane.sh.new && mv -f $W/.mk-lane.sh.new $W/mk-lane.sh
echo "advancing ${old:-nothing} -> $T (copy from $SH:$SD) $(date -Is)" > $W/NOT-READY.txt
[ -z "$old" ] || mv $W/src $W/src.prev-${old:0:8}; mv $W/src.new $W/src
printf 'tip=%s\nfrozen_at=%s\nbuilt_in=%s:%s (copied by relay; .lake/packages %s)\nprev=%s\nrule=read-only base; lanes come from /srv/warm-base/mk-lane.sh <lane>; never build in /srv/warm-base/src\n' \
  "$T" "$(date -Is)" "$SH" "$SD" "$( [ "$fresh" = 1 ] && echo 'copied too (fresh box)' || echo 'hardlinked from prev')" "${old:+$old (kept at $W/src.prev-${old:0:8})}" > $W/FROZEN.new; mv -f $W/FROZEN.new $W/FROZEN
echo "verifying $T (relay from $SH $(date -Is)); lanes wait for the replay probe" > $W/NOT-READY.txt
p=mk-verify-${T:0:8}
rm -rf /srv/lanes/$p 2>/dev/null || true   # a probe an earlier failed verify left behind is the relay's own
if MK_LANE_PROBE=1 timeout 900 $W/mk-lane.sh --verify $p; then rm -f $W/NOT-READY.txt; rm -rf /srv/lanes/$p; echo "relay: $(hostname) base at $T, verified replay"
else echo "verify FAILED after relay to $T $(date -Is): see /srv/lanes/$p/logs/verify-replay.log${old:+; roll back from $W/src.prev-${old:0:8}}" > $W/NOT-READY.txt; echo "relay: VERIFY FAILED on $(hostname); base stays NOT-READY" >&2; exit 8; fi
POST
