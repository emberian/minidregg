#!/usr/bin/env bash
# mk-lane.sh [--verify] <lane-name>
#
# Give a lane a PRIVATE warm copy of this burst box's frozen Mini warm base
# (/srv/warm-base/src) at /srv/lanes/<lane-name>/src (+ logs/), warm enough that
# `lake build Minidregg +Host.Main:leanArts ObjectiveProofs` replays without
# compiling, and isolated enough that nothing the lane does writes into the base.
# burst-20261005 (latitude) port of hbox:/tank/dregg-build/claude-lanes/warm-base/mk-lane.sh,
# itself adapted from the persvati base's tested script. Only the paths differ.
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
# Refuses unless: warm-base/NOT-READY.txt is absent, warm-base/FROZEN records the tip,
# the base HEAD equals that tip, its tracked tree is clean, the destination does not
# exist, and /srv keeps >= 15% free after the copy.
#
#   --verify   after creating the lane, run the umbrella build in it under swarm-build
#              and require that it compiles NOTHING (pure replay).
#   --from next   copy the speculative base /srv/next-base (branch `next` = main + every queued
#              range, PIPELINE-20261005) instead of /srv/warm-base (main).
#
# TORN-COPY GUARD (SCHOLAR-FN defect, 2026-10-05): the base can be advanced while a copy runs.
# The preconditions are checked BEFORE the copy and AGAIN AFTER it: NOT-READY absent, FROZEN
# byte-identical, the base directory the same inode (an advance swaps src in by rename), and
# base HEAD = the tip. Any change -> the half-made lane is removed and the script refuses.
set -euo pipefail

W=/srv/warm-base
PARENT=/srv/lanes

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
[ "$from" = next ] && W=/srv/next-base
BASE=$W/src
lane=${args[0]:-}
[ -n "$lane" ] || { echo "usage: mk-lane.sh [--verify] <lane-name>" >&2; exit 64; }
case "$lane" in *[!A-Za-z0-9._-]*|.*|warm-base) echo "mk-lane: REFUSED lane name '$lane'" >&2; exit 64 ;; esac
DEST=$PARENT/$lane
refuse() { echo "mk-lane: REFUSED $*" >&2; exit 65; }

# --- preconditions on the base ------------------------------------------------
[ ! -e "$W/NOT-READY.txt" ] || refuse "base not ready ($W/NOT-READY.txt)"
[ -f "$W/FROZEN" ] || refuse "base not frozen ($W/FROZEN missing)"
TIP=$(sed -n 's/^tip=//p' "$W/FROZEN")
[ ${#TIP} -eq 40 ] || refuse "FROZEN records no tip"
head=$(git -C "$BASE" rev-parse HEAD)
[ "$head" = "$TIP" ] || refuse "base HEAD $head != recorded tip $TIP"
[ -z "$(git -C "$BASE" status --porcelain --untracked-files=no)" ] || refuse "base tracked tree is dirty"
frozen_before=$(cat "$W/FROZEN")
inode_before=$(stat -c %i "$BASE")
[ ! -e "$DEST" ] || refuse "destination $DEST exists"

src_kb=$(du -sk --exclude=.lake "$BASE" | cut -f1)
lakeb_kb=$(du -sk "$BASE/.lake/build" | cut -f1)
need_kb=$((src_kb + lakeb_kb + 2 * 1024 * 1024))
read -r size_kb avail_kb < <(df --output=size,avail -k "$PARENT" | tail -1)
[ $(( (avail_kb - need_kb) * 100 / size_kb )) -ge 15 ] || refuse "disk: /srv would drop below 15% free"

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

# --- git: the lane's main is the tip; the base and GitHub are remotes -----------
# --- torn-copy guard: the base must be exactly what it was when the copy started --------------
torn=""
[ ! -e "$W/NOT-READY.txt" ] || torn="NOT-READY appeared during the copy"
[ -f "$W/FROZEN" ] && [ "$(cat "$W/FROZEN")" = "$frozen_before" ] || torn="${torn:+$torn; }FROZEN changed during the copy"
[ "$(stat -c %i "$BASE" 2>/dev/null)" = "$inode_before" ] || torn="${torn:+$torn; }base src was replaced during the copy"
[ "$(git -C "$BASE" rev-parse HEAD 2>/dev/null)" = "$TIP" ] || torn="${torn:+$torn; }base HEAD moved during the copy"
if [ -n "$torn" ]; then cd /; rm -rf "$DEST"; refuse "torn copy ($torn); $DEST removed, run again"; fi

git checkout -q -B main "$TIP"
git remote remove origin 2>/dev/null || true
git remote remove github 2>/dev/null || true
git remote remove base 2>/dev/null || true
git remote add base "$BASE"
git remote add github https://github.com/emberian/minidregg.git
git config user.name "ember arlynx"
git config user.email "cmrx64@gmail.com"
git config commit.gpgsign false
touch .minidregg-native-snapshot

cat > "$DEST/LANE-ORIGIN.txt" <<ORIGIN
lane=$lane
created=$(date -Is)
from=$BASE
tip=$TIP
shared_inodes=root .lake/build *.olean *.o (tmp+rename); .lake/packages sources and build products, .git/objects
rule=never change lake-manifest.json or lean-toolchain in this lane (package build products are shared inodes)
build: cd $DEST/src && LEAN_NUM_THREADS=4 SWARM_MEM_MAX=16G swarm-build lake build <targets>
rust: export CARGO_TARGET_DIR=$DEST/rust-target
first: git fetch github && git rebase github/main
ORIGIN
echo "mk-lane: OK $DEST at $TIP"

if [ "$verify" = 1 ]; then
  log=$DEST/logs/verify-replay.log
  ( LEAN_NUM_THREADS=4 SWARM_MEM_MAX=16G swarm-build lake build Minidregg +Host.Main:leanArts ObjectiveProofs ) > "$log" 2>&1 \
    || refuse "verify build failed: $log"
  # Locale-independent pattern; positive control against the base green log.
  ctl=$(grep -c '\] Built ' "$W/logs/green.log" || true)
  [ "$ctl" -gt 0 ] || refuse "verify: the Built-line pattern matches nothing in the base green log; check disarmed"
  built=$(grep -c '\] Built ' "$log" || true)
  [ "$built" = 0 ] || refuse "verify: $built modules compiled (not a warm replay): $log"
  grep -q 'Build completed successfully' "$log" || refuse "verify: no success line: $log"
  echo "mk-lane: VERIFIED warm replay, 0 modules compiled ($log)"
fi
