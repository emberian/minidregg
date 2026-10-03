#!/usr/bin/env bash
# Source-matched v10 native receiving recipe. Does not deploy or seed authority.
set -euo pipefail
umask 077
WORKSPACE=${WORKSPACE:-${SPONSOR_WS:?}}
RUN_DIR=${RUN_DIR:-${JOURNEY_STEP_DIR:?}/jworld-construction}
: "$MINI" "$HOST" "$CONFIG" "$SOCKET" "$WORKSPACE" "$RUN_DIR"
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
test ! -e "$RUN_DIR" || { echo "refusing existing RUN_DIR: $RUN_DIR" >&2; exit 2; }
mkdir -p "$RUN_DIR/home/requests" "$RUN_DIR/log"
N=0
say() {
  N=$((N+1))
  printf '%s\n' "$1" >"$RUN_DIR/log/$N.line"
  "$MINI" shell --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --workspace "$WORKSPACE" --home "$RUN_DIR/home" --line "$1" \
    >"$RUN_DIR/log/$N.out" 2>"$RUN_DIR/log/$N.err" || { local status=$?; cat "$RUN_DIR/log/$N.err" >&2; return "$status"; }
}
source_variant() {
  local variant=$1 mark=$2 revision=$3 kind=${4:-}
  local output="$RUN_DIR/home/requests"
  local extras=()
  [ -z "$kind" ] || extras=(--kind "$kind")
  python3 "$HERE/jworld-composed-source.py" --out "$output" --mark "$mark"
  say "program create construct-bundle-$variant @bundle.json open"
  local library
  library=$(jq -er '.programId' "$WORKSPACE/programs/construct-bundle-$variant.json")
  python3 "$HERE/jworld-composed-source.py" --out "$output" --mark "$mark" --library-id "$library"
  say "program create construct-base-$variant @base.json open"
  say "program create construct-close-$variant @close.json open"
  local base close
  base=$(jq -er '.programId' "$WORKSPACE/programs/construct-base-$variant.json")
  close=$(jq -er '.programId' "$WORKSPACE/programs/construct-close-$variant.json")
  python3 "$HERE/jworld-composed-source.py" --out "$output" --mark "$mark" --revision "$revision" \
    --library-id "$library" --base-program-id "$base" --close-program-id "$close" "${extras[@]}"
}
source_variant v1 1 1
say 'kind create construct-parent @kind.json open'
printf '%s\n' '{"selector":{"physicalKinds":["18"],"verbs":["2"]},"parents":[],"predicate":{"type":"all","predicates":[]}}' >"$RUN_DIR/home/requests/open-export.json"
say 'law export construct-parent-open construct-parent @open-export.json'
say 'submit construct-parent-open' 
say 'kind create construct-derived @kind.json open'
say 'create construct-old --from construct-derived open'
TARGET=$(jq -er '.target' "$WORKSPACE/refs/construct-derived.json")
PARENT=$(jq -er '.target' "$WORKSPACE/refs/construct-parent.json")
printf '%s\n' '["construct-parent"]' >"$RUN_DIR/home/requests/parents.json"
construct() {
  local id=$1 revision=$2
  say 'kind show construct-parent'
  cp "$RUN_DIR/log/$N.out" "$RUN_DIR/parent-$id.json"
  python3 "$HERE/jworld-construction.py" --parent "$RUN_DIR/parent-$id.json" --target "$TARGET" \
    --revision "$revision" --out "$RUN_DIR/home/requests"
  say "program create constructor-$id @constructor.json open"
  local program
  program=$(jq -er '.programId' "$WORKSPACE/programs/constructor-$id.json")
  say "kind construct $id construct-derived $program @parents.json"
  jq -e --slurpfile expected "$RUN_DIR/home/requests/expected.json" \
    '.construction.definitionBytes==$expected[0].definitionBytes' "$RUN_DIR/log/$N.out" >/dev/null
  cp "$WORKSPACE/proposals/$id/intent.bin" "$RUN_DIR/$id-original.bin"
  say "submit $id"
  say "kind construct $id construct-derived $program @parents.json"
  cmp "$RUN_DIR/$id-original.bin" "$WORKSPACE/proposals/$id/intent.bin"
  say "retry $id"
}
construct construct-first 2
say 'create construct-middle --from construct-derived open'
source_variant v2 2 2 "$PARENT"
say 'kind revise construct-parent-v2 construct-parent @kind.json'
say 'submit construct-parent-v2'
construct construct-second 3
say 'create construct-new --from construct-derived open'
for pair in old:1:1 middle:2:1 new:3:2; do
  IFS=: read -r object revision marker <<<"$pair"
  say "instance show construct-$object"
  jq -e --arg revision "$revision" '.value.descriptor.revision==$revision' "$RUN_DIR/log/$N.out" >/dev/null
  say "instance set vote-$object construct-$object votes 7 1"
  say "submit vote-$object"
  say "instance call close-$object construct-$object close"
  say "submit close-$object"
  say "instance show construct-$object"
  jq -e --arg marker "$marker" '(.value.entries|any(.field=="4" and .value=="1")) and
    (.value.entries|any(.field=="6" and .value==$marker)) and
    (.value.entries|any(.field=="7" and .value==$marker))' "$RUN_DIR/log/$N.out" >/dev/null
  cp "$RUN_DIR/log/$N.out" "$RUN_DIR/instance-$object.json"
done
# Restrictive parents use ordinary policy refs, separate from behavior order.
jq -n --arg parent "$PARENT" '{selector:{physicalKinds:["18"],verbs:["2"]},
  parents:[{policyId:$parent,facet:"descendants",selection:{type:"head"}}],
  predicate:{type:"all",predicates:[]}}' >"$RUN_DIR/home/requests/inherited.json"
say 'law export construct-inherit construct-derived @inherited.json'
say 'submit construct-inherit'
printf '%s\n' '{"selector":{"physicalKinds":["18"],"verbs":["2"]},"parents":[],"predicate":{"type":"any","predicates":[]}}' >"$RUN_DIR/home/requests/sealed.json"
say 'law export construct-seal construct-parent @sealed.json'
say 'submit construct-seal'
set +e
say 'instance call construct-blocked construct-new close'
RC=$?
if [ "$RC" = 0 ]; then say 'submit construct-blocked'; RC=$?; fi
set -e
test "$RC" = 3 && grep -q '^refused:' "$RUN_DIR/log/$N.err"
printf 'member-authenticated construction/revision/self-super/pinning/retry/inherited law: PASS\n' >&2
printf '%s\n' "$RUN_DIR"
