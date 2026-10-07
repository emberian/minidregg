#!/usr/bin/env bash
# mk-lane.sh [--verify] [--from main|next] <lane-name>
#
# Give a lane a PRIVATE warm copy of this box's frozen Mini warm base ($PIPELINE_WARM_BASE/src,
# default /srv/warm-base/src) at $PIPELINE_LANES/<lane-name>/src (+ logs/), warm enough that
# `lake build Minidregg +Host.Main:leanArts ObjectiveProofs` replays without compiling, and
# isolated enough that nothing the lane does writes into the base. ONE copy of this script: the
# repo's scripts/pipeline/mk-lane.sh; advance-base-burst.sh and relay-base.sh install it as
# $PIPELINE_WARM_BASE/mk-lane.sh at every advance (hbox and persvati carry older ports).
#
# What is copied and what is shared (inode-level), and why:
#   - source tree + .git: REAL copies (rsync). Editors and git write in place.
#   - .lake/build (root package): cp -al, then every file UNSHARED except
#       *.olean  (lean writes <f>.olean.tmp.<pid> then rename(2); strace on persvati 2026-10-04)
#       *.o      (leanc writes a tmp then rename(2); same measurement)
#     Everything else lean/lake writes IN PLACE with O_TRUNC (.ilean, .c, .trace, .hash,
#     .setup.json, ...): a shared inode would leak the lane's write into the base.
#   - .lake/packages (mathlib & co): cp -al; UNSHARED are the small files lake may rewrite
#     without recompiling (*.trace, *.hash, *.json, lakefile.olean*, manifests,
#     lean-toolchain) and each package's .git except objects/. Package build products
#     STAY SHARED: lake rewrites them only when it recompiles a package module, which
#     happens only if the lane changes lake-manifest.json or lean-toolchain. A lane that
#     needs a different mathlib or toolchain must NOT use this script.
#     (Each base package has core.trustctime=false so the ctime change a hardlink
#     causes does not make git re-index Mathlib on every run.)
#   - Never symlink anything of a lane into the base.
#
# Refuses unless: the base is READY (no NOT-READY.txt), FROZEN records the tip, the base HEAD
# equals that tip, its tracked tree is clean, the destination can be CLAIMED (mkdir, atomic: two
# agents creating the same lane name at once get exactly one lane and one refusal), and the lanes
# filesystem keeps >= 15% free after the copy.
#
#   --verify     after creating the lane, run the umbrella build in it under swarm-build and
#                require that it compiles NOTHING (pure replay).
#   --from next  copy the speculative base $PIPELINE_NEXT_BASE (/srv/next-base) instead of the
#                main base. Refused by name when this box has no next base (the train's lanes
#                then start from the main base and `git fetch github next` inside it).
#   MK_LANE_PROBE=1  (advance/relay only) proceed while NOT-READY.txt says `verifying`: the
#                probe lane that proves the freshly swapped base replays, before it is published.
#
# TORN-COPY GUARD (SCHOLAR-FN defect, 2026-10-05): the base can be advanced while a copy runs.
# The preconditions are checked BEFORE the copy and AGAIN AFTER it: NOT-READY absent, FROZEN
# byte-identical, the base directory the same inode (an advance swaps src in by rename), and
# base HEAD = the tip. Any change -> the half-made lane is removed and the script refuses.
set -euo pipefail

PIPELINE_ROOT=${PIPELINE_ROOT:-/srv/pipeline}
[ -f "$PIPELINE_ROOT/box.env" ] && . "$PIPELINE_ROOT/box.env"   # the box's slots, threads (box-env)
W=${PIPELINE_WARM_BASE:-/srv/warm-base}
NEXTW=${PIPELINE_NEXT_BASE:-/srv/next-base}
PARENT=${PIPELINE_LANES:-/srv/lanes}
REPO_URL=${PIPELINE_REPO_URL:-https://github.com/emberian/minidregg.git}
SLOT_SH=$PIPELINE_ROOT/scripts/slot.sh

verify=0
args=()
from=main
while [ $# -gt 0 ]; do
  case "$1" in
    --verify) verify=1 ;;
    --from) shift; from=${1:-}; [ "$from" = next ] || [ "$from" = main ] || { echo "mk-lane: REFUSED --from $from (main|next)" >&2; exit 64; } ;;
    -*) echo "mk-lane: REFUSED unknown option $1" >&2; exit 64 ;;
    *) args+=("$1") ;;
  esac
  shift
done
if [ "$from" = next ]; then
  [ -d "$NEXTW/src" ] || { echo "mk-lane: REFUSED --from next: this box has no next base ($NEXTW/src); make a main lane and \`git fetch github next && git rebase github/next\` in it" >&2; exit 66; }
  W=$NEXTW
fi
BASE=$W/src
lane=${args[0]:-}
[ -n "$lane" ] || { echo "usage: mk-lane.sh [--verify] [--from main|next] <lane-name>" >&2; exit 64; }
case "$lane" in *[!A-Za-z0-9._-]*|.*|warm-base) echo "mk-lane: REFUSED lane name '$lane'" >&2; exit 64 ;; esac
DEST=$PARENT/$lane
refuse() { echo "mk-lane: REFUSED $*" >&2; exit 65; }

# NOT-READY is absolute, except for the advance's own verify probe while the marker says so.
not_ready() {
  [ -e "$W/NOT-READY.txt" ] || return 1
  [ "${MK_LANE_PROBE:-}" = 1 ] && grep -q '^verifying' "$W/NOT-READY.txt" && return 1
  return 0
}

# --- preconditions on the base ------------------------------------------------
! not_ready || refuse "base not ready: $(cat "$W/NOT-READY.txt")"
[ -f "$W/FROZEN" ] || refuse "base not frozen ($W/FROZEN missing)"
TIP=$(sed -n 's/^tip=//p' "$W/FROZEN")
[ ${#TIP} -eq 40 ] || refuse "FROZEN records no tip"
head=$(git -C "$BASE" rev-parse HEAD)
[ "$head" = "$TIP" ] || refuse "base HEAD $head != recorded tip $TIP"
[ -z "$(git -C "$BASE" status --porcelain --untracked-files=no)" ] || refuse "base tracked tree is dirty"
frozen_before=$(cat "$W/FROZEN")
inode_before=$(stat -c %i "$BASE")

# --- claim the destination atomically (mkdir fails if it exists) ------------------------
mkdir -p "$PARENT"
mkdir "$DEST" 2>/dev/null || refuse "destination $DEST exists (or another mk-lane is creating it right now)"
unclaim() { rmdir "$DEST" 2>/dev/null || true; }

src_kb=$(du -sk --exclude=.lake "$BASE" | cut -f1)
lakeb_kb=$(du -sk "$BASE/.lake/build" | cut -f1)
need_kb=$((src_kb + lakeb_kb + 2 * 1024 * 1024))
read -r size_kb avail_kb < <(df --output=size,avail -k "$PARENT" | tail -1)
[ $(( (avail_kb - need_kb) * 100 / size_kb )) -ge 15 ] || { unclaim; refuse "disk: $PARENT would drop below 15% free"; }

# --- copy ---------------------------------------------------------------------
mkdir -p "$DEST/logs"
rsync -a --exclude=/.lake "$BASE/" "$DEST/src/"
cp -al "$BASE/.lake" "$DEST/src/.lake"

unshare() { cp -p -- "$1" "$1.mklane.tmp" && mv -f -- "$1.mklane.tmp" "$1"; }
export -f unshare
cd "$DEST/src/.lake"
find . -mindepth 1 -maxdepth 1 ! -name build ! -name packages -print0 |
  xargs -0 -r -I{} find {} -type f -links +1 -print0 |
  xargs -0 -r -n 256 bash -c 'for f; do unshare "$f"; done' _
find build -type f -links +1 ! -name '*.olean' ! -name '*.o' -print0 |
  xargs -0 -r -P 8 -n 256 bash -c 'for f; do unshare "$f"; done' _
find packages \( -path '*/.git/objects' -prune \) -o -type f -links +1 \( \
    -path 'packages/*/.git/*' -o -name '*.trace' -o -name '*.hash' -o -name '*.json' \
    -o -name 'lakefile.olean*' -o -name 'lake-manifest.json' -o -name 'lean-toolchain' \) -print0 |
  xargs -0 -r -P 8 -n 256 bash -c 'for f; do unshare "$f"; done' _

# --- audit: every remaining shared inode must be on the allow-list --------------
cd "$DEST/src"
bad=$( { find .lake -path .lake/packages -prune -o -type f -links +1 ! -path '.lake/build/*' -print
         find .lake/build -type f -links +1 ! -name '*.olean' ! -name '*.o' -print
         find .lake/packages \( -path '*/.git/objects' -prune \) -o -type f -links +1 \( \
           -path '*/.git/*' -o -name '*.trace' -o -name '*.hash' -o -name '*.json' \
           -o -name 'lakefile.olean*' -o -name 'lean-toolchain' \) -print; } | head -20)
[ -z "$bad" ] || { echo "$bad" >&2; refuse "shared inodes outside the allow-list remain in $DEST (left in place for inspection)"; }
outside=$(find . -path ./.lake -prune -o -type f -links +1 -print | head -5)
[ -z "$outside" ] || { echo "$outside" >&2; refuse "shared source/.git inodes in $DEST"; }

# --- torn-copy guard: the base must be exactly what it was when the copy started --------------
torn=""
! not_ready || torn="NOT-READY appeared during the copy"
[ -f "$W/FROZEN" ] && [ "$(cat "$W/FROZEN")" = "$frozen_before" ] || torn="${torn:+$torn; }FROZEN changed during the copy"
[ "$(stat -c %i "$BASE" 2>/dev/null)" = "$inode_before" ] || torn="${torn:+$torn; }base src was replaced during the copy"
[ "$(git -C "$BASE" rev-parse HEAD 2>/dev/null)" = "$TIP" ] || torn="${torn:+$torn; }base HEAD moved during the copy"
[ "$(git rev-parse HEAD)" = "$TIP" ] || torn="${torn:+$torn; }lane copy HEAD != tip"
if [ -n "$torn" ]; then cd /; rm -rf "$DEST"; refuse "torn copy ($torn); $DEST removed, run again"; fi

# --- git: the lane's main is the tip; the base, the shared bare repo and GitHub are remotes ----
git checkout -q -B main "$TIP"
for r in origin github base shared; do git remote remove $r 2>/dev/null || true; done
git remote add base "$BASE"
git remote add github "$REPO_URL"
[ -d /srv/git/minidregg.git ] && git remote add shared /srv/git/minidregg.git
git config user.name "ember arlynx"
git config user.email "cmrx64@gmail.com"
git config commit.gpgsign false
touch .minidregg-native-snapshot

threads=${LEAN_NUM_THREADS:-4}
cat > "$DEST/LANE-ORIGIN.txt" <<ORIGIN
lane=$lane
created=$(date -Is)
from=$BASE
tip=$TIP
shared_inodes=root .lake/build *.olean *.o (tmp+rename); .lake/packages sources and build products, .git/objects
rule=never change lake-manifest.json or lean-toolchain in this lane (package build products are shared inodes)
first: git fetch github next && git rebase github/next     (lanes build on next; the keeper rebases arrivals onto it)
check: $PIPELINE_ROOT/scripts/lean-ask check <File.lean>   (0.4 s; --reload after a fetch/rebase) or $PIPELINE_ROOT/scripts/lane-check <File.lean>
       NEVER bare \`lake env lean\` after a fetch/rebase: it reads stale import oleans (false green AND false red).
build: cd $DEST/src && $SLOT_SH swarm-build lake build <targets>      (per-build cap 48G by default; the box slice is the guard)
       slot.sh takes the first FREE lane slot of this box (box.env PIPELINE_SLOTS) and polls all of them; it sets no
       thread count, so export LEAN_NUM_THREADS=$threads (box.env) or less. NEVER hand-type a flock chain: a
       \`flock -n A cmd || flock B cmd\` blocks on B while other slots are free, and re-runs a FAILED cmd in B.
rust:  export CARGO_TARGET_DIR=$DEST/rust-target
who holds what: systemctl --user list-units 'swarm-*'   (every swarm-build is a named scope: lane, pid, command)
ORIGIN
echo "mk-lane: OK $DEST at $TIP"

if [ "$verify" = 1 ]; then
  log=$DEST/logs/verify-replay.log
  ( LEAN_NUM_THREADS=$threads SWARM_MEM_MAX=${SWARM_MEM_MAX:-48G} SWARM_BUILD_TAG="mk-verify-$lane" swarm-build lake build Minidregg +Host.Main:leanArts ObjectiveProofs ) > "$log" 2>&1 \
    || refuse "verify build failed: $log"
  # Locale-independent pattern; positive control against the base green log.
  ctl=$(cat "$W"/logs/green*.log 2>/dev/null | grep -c '\] Built ' || true)
  [ "$ctl" -gt 0 ] || refuse "verify: the Built-line pattern matches nothing in the base green logs; check disarmed"
  built=$(grep -c '\] Built ' "$log" || true)
  [ "$built" = 0 ] || refuse "verify: $built modules compiled (not a warm replay): $log"
  grep -q 'Build completed successfully' "$log" || refuse "verify: no success line: $log"
  echo "mk-lane: VERIFIED warm replay, 0 modules compiled ($log)"
fi
