# scripts/pipeline/lib.sh -- shared settings of the pipeline scripts (source it; no side effects).
#
# The pipeline (designs: PIPELINE + VERIFY-ONCE regimes, 2026-10-05) keeps, per build box:
#   $PIPELINE_ROOT            /srv/pipeline: bin/ (sccache), sccache.env, state, logs
#   $ARTIFACT_ROOT            /srv/artifacts/<tip>/: one candidate per gated tip (SHA256SUMS,
#                             provenance.json, manifest.json, bin/), READY when complete;
#                             <label> symlinks (green, next, main) to the newest READY tip
#   $JOURNEY_ROOT             /srv/journeys/<tip>/: the journey runner's table per tip
# Everything here is plain files on one box; boxes copy each other's results (rsync), never
# rebuild the same tip. The /srv paths are only defaults: a box whose layout lives elsewhere (hbox:
# /tank/dregg-build/pipeline, docs/PIPELINE-HBOX.md) sets PIPELINE_ROOT and its box.env (box-env
# --layout) names every other root.
PIPELINE_ROOT=${PIPELINE_ROOT:-/srv/pipeline}
# The box's own topology (which slot files lanes may take, where artifacts are built and mirrored,
# its Lean thread count) lives in ONE box-local file, written when the box is provisioned
# (scripts/pipeline/box-env); nothing about a particular box is hard-coded here.
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH
[ -f "$PIPELINE_ROOT/box.env" ] && . "$PIPELINE_ROOT/box.env"   # after PATH
# The shared Lake cache (box.env: LAKE_CACHE_DIR, LAKE_ARTIFACT_CACHE=true) is only for a tree whose
# lakefile restores every artifact into .lake/build (restoreAllArtifacts): without it a cache hit leaves
# no .olean in .lake/build and `lake env lean`, lane-check and lean-ask break. A tree without it gets a
# private, empty cache (Lake READS its cache by default, so the directory moves too).
pipeline_lib_dir=$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
pipeline_tree_root=$(git -C "$pipeline_lib_dir" rev-parse --show-toplevel 2>/dev/null || true)
if [ "${LAKE_ARTIFACT_CACHE:-}" = true ] && [ -n "$pipeline_tree_root" ] &&
   ! grep -qE '^restoreAllArtifacts *= *true' "$pipeline_tree_root/lakefile.toml" 2>/dev/null; then
  export LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR=$HOME/.cache/lake-private-unshared
fi
ARTIFACT_ROOT=${ARTIFACT_ROOT:-/srv/artifacts}
JOURNEY_ROOT=${JOURNEY_ROOT:-/srv/journeys}
PIPELINE_REPO_URL=${PIPELINE_REPO_URL:-https://github.com/emberian/minidregg.git}
# Where artifacts are built (the gate box) and where they are mirrored to; user@host each.
PIPELINE_ORIGIN=${PIPELINE_ORIGIN:-}
PIPELINE_MIRRORS=${PIPELINE_MIRRORS:-}
# The build slots a lane may take on this box (flock files, one Lean build each). The merge gate's
# own slots are never in this list; the keeper sets PIPELINE_SLOTS to its slot explicitly.
PIPELINE_SLOTS=${PIPELINE_SLOTS:-/srv/build-slot-1 /srv/build-slot-2}
# The box's warm base (a built, read-only clone at the newest gated tip): the publisher's fallback tree.
PIPELINE_WARM_BASE=${PIPELINE_WARM_BASE:-/srv/warm-base}

pipeline_die() { printf '%s: %s\n' "${PIPELINE_PROG:-$(basename -- "$0")}" "$*" >&2; exit 1; }
pipeline_log() { printf '%s %s: %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "${PIPELINE_PROG:-$(basename -- "$0")}" "$*"; }

# pipeline_full_sha REF_OR_SHA [GIT_DIR]: a 40-hex commit id, or die.
pipeline_full_sha() {
  local r=$1 g=${2:-}
  if [[ $r =~ ^[0-9a-f]{40}$ ]]; then printf '%s\n' "$r"; return; fi
  [ -n "$g" ] || pipeline_die "need a full 40-hex sha (got '$r')"
  git -C "$g" rev-parse --verify -q "$r^{commit}" || pipeline_die "cannot resolve '$r' in $g"
}

# pipeline_verify_set DIR: every line of DIR/SHA256SUMS matches, and the set is READY.
pipeline_verify_set() {
  local d=$1
  [ -f "$d/READY" ] || pipeline_die "$d is not a READY artifact set"
  (cd "$d" && sha256sum --quiet -c SHA256SUMS) || pipeline_die "SHA256SUMS mismatch in $d"
}

# pipeline_slot CMD...: run CMD holding one of the box's lane build slots ($PIPELINE_SLOTS).
# Takes the first free slot; when all are held, waits on whichever frees first (polling, so a
# long build in one slot never blocks a waiter while another slot is free). A FAILING CMD is not
# re-run: only flock's own conflict code (-E 253, so a CMD's own exit 75 is never read as busy)
# moves on to the next slot.
pipeline_slot() {
  local rc s told=0
  while :; do
    for s in $PIPELINE_SLOTS; do
      rc=0; flock -n -E 253 "$s" "$@" || rc=$?
      [ "$rc" = 253 ] || return "$rc"
    done
    if [ "$told" = 0 ]; then told=1
      pipeline_log "all lane slots of $(hostname) are held; waiting for the first to free. \`$(dirname -- "${BASH_SOURCE[0]}")/slots\` shows holders here and the free slots of ${PIPELINE_PEER:-the sibling box} (a lane can move there: mk-lane on it, then git fetch from this box)" >&2
    fi
    sleep "${PIPELINE_SLOT_POLL_S:-5}"
  done
}

# pipeline_build_slot MOD... -- CMD...: like pipeline_slot, but a SMALL rebuild (at most
# PIPELINE_SMALL_MAX, 50, stale in-tree modules by scripts/pipeline/stale-modules) takes one of the
# box's small-check slots ($PIPELINE_SMALL_SLOTS) at LEAN_NUM_THREADS=$PIPELINE_SMALL_THREADS (2) and
# never waits behind a full build; anything larger (or a box without small slots) takes a lane slot.
# lane-check and lean-ask --reload build through this.
pipeline_build_slot() {
  local mods=() n rc s
  while [ $# -gt 0 ] && [ "$1" != -- ]; do mods+=("$1"); shift; done
  shift
  pipeline_cache_audit || pipeline_die "the shared Lake cache is unguarded (lake-cache-audit failed): not building on it"
  n=$(PIPELINE_PROG=stale-modules "$(dirname -- "${BASH_SOURCE[0]}")/stale-modules" "${mods[@]}" 2>/dev/null | head -1)
  if [ -n "${PIPELINE_SMALL_SLOTS:-}" ] && [ -n "$n" ] && [ "$n" -le "${PIPELINE_SMALL_MAX:-50}" ]; then
    pipeline_log "small rebuild ($n stale modules): small-check slot, ${PIPELINE_SMALL_THREADS:-2} threads" >&2
    while :; do
      for s in $PIPELINE_SMALL_SLOTS; do
        rc=0; flock -n -E 253 "$s" env LEAN_NUM_THREADS="${PIPELINE_SMALL_THREADS:-2}" "$@" || rc=$?
        [ "$rc" = 253 ] || return "$rc"
      done
      sleep 2
    done
  fi
  pipeline_log "rebuild of ${n:-?} stale modules: lane slot" >&2
  pipeline_slot "$@"
}

# pipeline_find_tree TIP [HINT_PATH]: print a built, clean clone whose HEAD is TIP, or nothing.
# The keeper writes the gated tree's path into TIPS, then renames that tree into the warm base
# (VERIFY-ONCE 3), so the hint may have moved: look where it goes.
pipeline_find_tree() {
  local tip=$1 hint=${2:-} d
  for d in "$hint" "$PIPELINE_WARM_BASE/src" "${PIPELINE_NEXT_BASE:-/srv/next-base}/src" "$PIPELINE_WARM_BASE"/src.prev-*; do
    [ -n "$d" ] && [ -d "$d/.git" ] && [ -d "$d/.lake/build" ] || continue
    [ "$(git -C "$d" rev-parse HEAD 2>/dev/null)" = "$tip" ] || continue
    [ -z "$(git -C "$d" status --porcelain --untracked-files=no)" ] || continue
    printf '%s\n' "$d"; return 0
  done
}

# pipeline_label LABEL TIP: point ARTIFACT_ROOT/LABEL at the READY set TIP (atomic rename).
pipeline_label() {
  local label=$1 tip=$2
  [ -f "$ARTIFACT_ROOT/$tip/READY" ] || pipeline_die "label $label: $tip is not READY"
  ln -sfn "$tip" "$ARTIFACT_ROOT/.$label.new" && mv -Tf "$ARTIFACT_ROOT/.$label.new" "$ARTIFACT_ROOT/$label"
}

# pipeline_cache_audit [TREE]: the guard of the box's shared Lake cache, run from THIS (the tip's) tree
# before every slot build, lane-check, landing gate and publish. lake-cache-audit --since --purge drops,
# before the next reader can fetch it, every cache entry written since the last audit that (a) holds C
# naming an in-tree initializer or declaration without the package prefix (a compile outside Lake's
# package setup, burst2-b 10-07: 79 poisoned .c, no lean_exe linked) or (b) records an artifact whose
# bytes were modified after the entry stored it (a write through a restored hard link: the cache file
# IS the lane's .lake/build file). Returns 0 when the cache is clean or was purged clean (a purge is
# logged here and in $ARTIFACT_ROOT/ALERTS), 2 when the audit itself could not run: the caller refuses
# rather than build on an unguarded cache. A no-op when the cache is off or still empty.
pipeline_cache_audit() {
  local tree=${1:-$pipeline_tree_root} rc=0
  [ "${LAKE_ARTIFACT_CACHE:-}" = true ] && [ -n "${LAKE_CACHE_DIR:-}" ] && [ -d "$LAKE_CACHE_DIR" ] || return 0
  [ -d "$LAKE_CACHE_DIR/outputs" ] || return 0      # an empty cache: nothing to guard yet
  python3 "$pipeline_lib_dir/lake-cache-audit" --cache "$LAKE_CACHE_DIR" --tree "$tree" \
    --since --purge --quiet || rc=$?
  case $rc in
    0) return 0 ;;
    1) pipeline_log "lake-cache-audit PURGED entries from $LAKE_CACHE_DIR (see \$ARTIFACT_ROOT/ALERTS); continuing on the clean cache" >&2; return 0 ;;
    *) pipeline_log "lake-cache-audit could not run (rc $rc) on $LAKE_CACHE_DIR" >&2; return 2 ;;
  esac
}
