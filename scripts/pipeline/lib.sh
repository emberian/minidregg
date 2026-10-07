# scripts/pipeline/lib.sh -- shared settings of the pipeline scripts (source it; no side effects).
#
# The pipeline (designs: PIPELINE + VERIFY-ONCE regimes, 2026-10-05) keeps, per build box:
#   $PIPELINE_ROOT            /srv/pipeline: bin/ (sccache), sccache.env, state, logs
#   $ARTIFACT_ROOT            /srv/artifacts/<tip>/: one candidate per gated tip (SHA256SUMS,
#                             provenance.json, manifest.json, bin/), READY when complete;
#                             <label> symlinks (green, next, main) to the newest READY tip
#   $JOURNEY_ROOT             /srv/journeys/<tip>/: the journey runner's table per tip
# Everything here is plain files on one box; boxes copy each other's results (rsync), never
# rebuild the same tip.
PIPELINE_ROOT=${PIPELINE_ROOT:-/srv/pipeline}
# The box's own topology (which slot files lanes may take, where artifacts are built and mirrored,
# its Lean thread count) lives in ONE box-local file, written when the box is provisioned
# (scripts/pipeline/box-env); nothing about a particular box is hard-coded here.
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH
[ -f "$PIPELINE_ROOT/box.env" ] && . "$PIPELINE_ROOT/box.env"   # after PATH: it may put the lake shim first
ARTIFACT_ROOT=${ARTIFACT_ROOT:-/srv/artifacts}
JOURNEY_ROOT=${JOURNEY_ROOT:-/srv/journeys}
PIPELINE_REPO_URL=${PIPELINE_REPO_URL:-https://github.com/emberian/minidregg.git}
# Where artifacts are built (the gate box) and where they are mirrored to; user@host each.
PIPELINE_ORIGIN=${PIPELINE_ORIGIN:-}
PIPELINE_MIRRORS=${PIPELINE_MIRRORS:-}
# The build slots a lane may take on this box (flock files, one Lean build each). The merge gate's
# own slots are never in this list; the keeper sets PIPELINE_SLOTS to its slot explicitly.
PIPELINE_SLOTS=${PIPELINE_SLOTS:-/srv/build-slot-1 /srv/build-slot-2}

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
# re-run: only flock's own conflict code 75 moves on to the next slot.
pipeline_slot() {
  local rc s told=0
  while :; do
    for s in $PIPELINE_SLOTS; do
      rc=0; flock -n -E 75 "$s" "$@" || rc=$?
      [ "$rc" = 75 ] || return "$rc"
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
  n=$(PIPELINE_PROG=stale-modules "$(dirname -- "${BASH_SOURCE[0]}")/stale-modules" "${mods[@]}" 2>/dev/null | head -1)
  if [ -n "${PIPELINE_SMALL_SLOTS:-}" ] && [ -n "$n" ] && [ "$n" -le "${PIPELINE_SMALL_MAX:-50}" ]; then
    pipeline_log "small rebuild ($n stale modules): small-check slot, ${PIPELINE_SMALL_THREADS:-2} threads" >&2
    while :; do
      for s in $PIPELINE_SMALL_SLOTS; do
        rc=0; flock -n -E 75 "$s" env LEAN_NUM_THREADS="${PIPELINE_SMALL_THREADS:-2}" "$@" || rc=$?
        [ "$rc" = 75 ] || return "$rc"
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
  for d in "$hint" /srv/warm-base/src /srv/next-base/src /srv/warm-base/src.prev-*; do
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
