#!/usr/bin/env bash
# rerecord.sh -- re-record the accepted Objective fixture from a candidate when the front end moved.
#
#   scripts/native-accepted-fixture/rerecord.sh [--check | --force] CANDIDATE_DIR SCRATCH_DIR
#
# Run from (or in) the tree the candidate was built from, with its Lean built (the replay is
# `lake env lean --run`). CANDIDATE_DIR is a READY candidate of that tree's HEAD (bin/ holds
# minidregg-host, mini and the verifier); SCRATCH_DIR is an empty directory for one fresh scratch world.
#
# Two fixtures are recorded from real native runs: the accepted Objective call
# (Fixtures.NativeAcceptedFixture*) and the retained document write (Fixtures.NativeDocWriteFixture*).
# The recorded data is stale when either
#   * the candidate's Objective front-end identity (`minidregg-host /dev/null objective-constants`:
#     `ObjectiveBendFrontEndIdentity.identity`, a fingerprint of the front-end sources) is not the one
#     the recorded policy pins (`Fixtures.NativeAcceptedFixtureData.pinObjectivePolicyHex`;
#     `front_end_current` refuses by name until it is), or
#   * the fixture module no longer elaborates against this tree (`lake env lean Fixtures/<F>.lean`):
#     the recorded bytes name event ids, codec frames or a world root the tree has moved past (a codec
#     epoch moves them without touching the front end; 7d90da717 was such a change).
# Each fixture is judged on its own and only the stale ones are re-recorded. When stale (or --force):
#   1. a fresh world under SCRATCH_DIR with the candidate's binaries, and exactly the driver steps the
#      fixture reads (objective-native-acceptance.py world, publish, invoke --label first,
#      refuse --label r01-source-is-package), then the world's server is stopped;
#   2. generate.sh replays both admissions in Lean and refuses unless the record and world root are the
#      Host's and the projection is the hand-written authority; it writes the data module;
#   3. the new data is committed onto branch fixture-regen/<HEAD sha> (parent: HEAD) with git plumbing:
#      HEAD, the index and the checkout are not moved, and the working file is restored afterwards.
#      The data is a generated file (scripts/pipeline/fixture-authorities.txt): no authority changes.
# If the run's projection differs from the authority, NOTHING is committed: the field-by-field
# difference is written to SCRATCH_DIR/authority-diff.txt and the script exits 4. The authority is
# hand-written and changes only in its own reviewed Authority-Change commit; no script writes it.
#
# The doc-write fixture follows the same three steps with doc-write-native-acceptance.py and
# scripts/native-doc-write-fixture/generate.sh; both data modules land in the one fixture-regen commit.
# Output (last line): `unchanged`, `stale` (--check), `recorded fixture-regen/<sha> <commit>`, or
# `authority-differs SCRATCH_DIR/authority-diff.txt`. Exit 0, 0, 0, 4; 1 when a step fails; 3 is
# `stale` under --check. Cost: one world (four driver steps) and two Lean replays, a few minutes; the
# caller seats it (swarm-build) like the umbrellas.
set -euo pipefail
mode=auto
case "${1:-}" in --check) mode=check; shift ;; --force) mode=force; shift ;; esac
usage="usage: rerecord.sh [--check|--force] CANDIDATE_DIR SCRATCH_DIR"
cand=$(cd "${1:?$usage}" && pwd)
here=$(cd "$(dirname "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
data=Fixtures/NativeAcceptedFixtureData.lean
bin=$cand/bin
[ -x "$bin/minidregg-host" ] || { echo "rerecord: no $bin/minidregg-host" >&2; exit 1; }
front=$("$bin/minidregg-host" /dev/null objective-constants |
  python3 -c 'import json,sys; print(json.load(sys.stdin)["frontEnd"])')
# PolicyRecordCodec.stringStream frames each character as 0xFF then its byte.
framed=$(python3 -c 'import sys; print("".join("ff%02x" % b for b in sys.argv[1].encode()))' "$front")
doc_data=Fixtures/NativeDocWriteFixtureData.lean
elaborates() { (cd "$root" && timeout 1800 lake env lean "$1" > /dev/null 2>&1); }
accepted=current; doc=current
grep -q "$framed" "$root/$data" || accepted=stale
[ "$accepted" = stale ] || elaborates Fixtures/NativeAcceptedFixture.lean || accepted=stale
elaborates Fixtures/NativeDocWriteFixture.lean || doc=stale
[ "$mode" = force ] && { accepted=stale; doc=stale; }
state=current; [ "$accepted$doc" = currentcurrent ] || state=stale
echo "rerecord: candidate front end $front; accepted fixture $accepted, doc-write fixture $doc" >&2
if [ "$mode" = check ]; then echo "$state"; [ "$state" = current ] && exit 0 || exit 3; fi
if [ "$state" = current ]; then echo unchanged; exit 0; fi

scratch=$(mkdir -p "${2:?$usage}" && cd "$2" && pwd)
[ -z "$(ls -A "$scratch")" ] || { echo "rerecord: $scratch is not empty" >&2; exit 1; }
head=$(git -C "$root" rev-parse HEAD)
git -C "$root" diff --quiet HEAD -- "$data" "$doc_data" || { echo "rerecord: fixture data has uncommitted changes" >&2; exit 1; }
cd "$root"
restore() { git checkout -q HEAD -- "$data" "$doc_data"; }
differs() { cp "$1" "$scratch/authority-diff.txt"; restore; echo "authority-differs $scratch/authority-diff.txt"; exit 4; }
if [ "$accepted" = stale ]; then
  world=$scratch/world
  drive() { python3 native/resource-client/objective-native-acceptance.py "$@" >> "$scratch/driver.log" 2>&1 ||
    { tail -5 "$scratch/driver.log" >&2; echo "rerecord: driver step $1 failed" >&2; return 1; }; }
  trap 'python3 native/resource-client/objective-native-acceptance.py stop --root "$world" >> "$scratch/driver.log" 2>&1 || true' EXIT
  drive world --bin "$bin" --root "$world"
  drive publish --root "$world"
  drive invoke --root "$world" --label first
  drive refuse --root "$world" --label r01-source-is-package --mutation source-atom --argument @package
  python3 native/resource-client/objective-native-acceptance.py stop --root "$world" >> "$scratch/driver.log" 2>&1
  trap - EXIT
  if ! TMPDIR=$scratch bash "$here/generate.sh" "$world" > "$scratch/generate.out" 2> "$scratch/generate.err"; then
    grep -q "projection differs from the authority" "$scratch/generate.err" && differs "$scratch/generate.err"
    cat "$scratch/generate.err" >&2; restore; echo "rerecord: generate.sh failed" >&2; exit 1
  fi
fi
if [ "$doc" = stale ]; then
  dworld=$scratch/doc-world
  python3 native/resource-client/doc-write-native-acceptance.py --bin "$bin" --root "$dworld" >> "$scratch/doc-driver.log" 2>&1 ||
    { tail -5 "$scratch/doc-driver.log" >&2; restore; echo "rerecord: doc-write driver failed" >&2; exit 1; }
  if ! TMPDIR=$scratch bash "$root/scripts/native-doc-write-fixture/generate.sh" "$dworld" > "$scratch/doc-generate.out" 2> "$scratch/doc-generate.err"; then
    grep -q "projection differs from the authority" "$scratch/doc-generate.err" && differs "$scratch/doc-generate.err"
    cat "$scratch/doc-generate.err" >&2; restore; echo "rerecord: doc-write generate.sh failed" >&2; exit 1
  fi
fi

# A fixture that fails to elaborate while re-recording reproduces its bytes fails for another reason.
if git diff --quiet HEAD -- "$data" "$doc_data"; then
  restore; echo "rerecord: re-recorded data is identical to HEAD's; the stale fixture fails for another reason" >&2; exit 1
fi

# Commit the data onto fixture-regen/<HEAD> without touching HEAD, the index or the checkout.
export GIT_INDEX_FILE=$scratch/index
git read-tree "$head"
for f in "$data" "$doc_data"; do git update-index --add --cacheinfo "100644,$(git hash-object -w "$f"),$f"; done
tree=$(git write-tree)
unset GIT_INDEX_FILE
restore
cat > "$scratch/message" <<EOF
fixtures: native runs re-recorded from candidate ${head:0:12} (accepted $accepted, doc-write $doc)

The recorded data was stale against this tree (front end now $front; a fixture that no longer
elaborates names event ids, frames or a world root the tree moved past).
scripts/native-accepted-fixture/rerecord.sh re-ran each stale fixture's driver steps on a fresh
world with the candidate's binaries ($cand) and its generate.sh replayed the admissions in Lean:
record and world root the Host's, projection the hand-written authority.
EOF
# A build box may have no git identity: name the commit after this script when none is configured.
if [ -z "$(git config user.email || true)" ]; then
  export GIT_AUTHOR_NAME=${GIT_AUTHOR_NAME:-minidregg fixture rerecord} GIT_AUTHOR_EMAIL=${GIT_AUTHOR_EMAIL:-rerecord@minidregg.invalid}
  export GIT_COMMITTER_NAME=${GIT_COMMITTER_NAME:-$GIT_AUTHOR_NAME} GIT_COMMITTER_EMAIL=${GIT_COMMITTER_EMAIL:-$GIT_AUTHOR_EMAIL}
fi
commit=$(git commit-tree "$tree" -p "$head" -F "$scratch/message")
git update-ref "refs/heads/fixture-regen/${head:0:12}" "$commit"
echo "recorded fixture-regen/${head:0:12} $commit"
