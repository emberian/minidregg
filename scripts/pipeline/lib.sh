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
ARTIFACT_ROOT=${ARTIFACT_ROOT:-/srv/artifacts}
JOURNEY_ROOT=${JOURNEY_ROOT:-/srv/journeys}
PIPELINE_REPO_URL=${PIPELINE_REPO_URL:-https://github.com/emberian/minidregg.git}
# Where artifacts are built (the gate box) and where they are mirrored to; user@host each.
PIPELINE_ORIGIN=${PIPELINE_ORIGIN:-ember@67.213.124.13}
PIPELINE_MIRRORS=${PIPELINE_MIRRORS:-ember@162.43.189.7 ember@152.236.4.24}
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH

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

# pipeline_slot CMD...: run CMD holding one of the box's two build slots (burst brief amendment
# 16:45Z: at most two concurrent Lean builds per f4). Try slot 1 without waiting, then wait for
# slot 2; a FAILING CMD is not re-run (only flock's own conflict code 75 falls through).
pipeline_slot() {
  local rc=0
  flock -n -E 75 "${PIPELINE_SLOT_1:-/srv/build-slot-1}" "$@" || rc=$?
  [ "$rc" = 75 ] || return "$rc"
  flock -E 75 "${PIPELINE_SLOT_2:-/srv/build-slot-2}" "$@"
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
