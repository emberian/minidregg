#!/usr/bin/env bash
# rerecord.sh -- re-record the accepted Objective fixture from a candidate when the front end moved.
#
#   scripts/native-accepted-fixture/rerecord.sh [--check | --force] CANDIDATE_DIR SCRATCH_DIR
#
# Run from (or in) the tree the candidate was built from, with its Lean built (the replay is
# `lake env lean --run`). CANDIDATE_DIR is a READY candidate of that tree's HEAD (bin/ holds
# minidregg-host, mini and the verifier); SCRATCH_DIR is an empty directory for one fresh scratch world.
#
# The recorded run is stale exactly when the candidate's Objective front-end identity
# (`minidregg-host /dev/null objective-constants`: `ObjectiveBendFrontEndIdentity.identity`, a
# fingerprint of the front-end sources) is not the one the recorded policy pins
# (`Fixtures.NativeAcceptedFixtureData.pinObjectivePolicyHex`); `front_end_current` in
# Fixtures.NativeAcceptedFixture refuses by name until it is. When stale (or under --force):
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
if grep -q "$framed" "$root/$data"; then state=current; else state=stale; fi
echo "rerecord: candidate front end $front; recorded fixture $state" >&2
if [ "$mode" = check ]; then echo "$state"; [ "$state" = current ] && exit 0 || exit 3; fi
if [ "$state" = current ] && [ "$mode" != force ]; then echo unchanged; exit 0; fi

scratch=$(mkdir -p "${2:?$usage}" && cd "$2" && pwd)
[ -z "$(ls -A "$scratch")" ] || { echo "rerecord: $scratch is not empty" >&2; exit 1; }
head=$(git -C "$root" rev-parse HEAD)
git -C "$root" diff --quiet HEAD -- "$data" || { echo "rerecord: $data has uncommitted changes" >&2; exit 1; }
cd "$root"
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
  if grep -q "projection differs from the authority" "$scratch/generate.err"; then
    cp "$scratch/generate.err" "$scratch/authority-diff.txt"
    git checkout -q HEAD -- "$data"
    echo "authority-differs $scratch/authority-diff.txt"; exit 4
  fi
  cat "$scratch/generate.err" >&2; git checkout -q HEAD -- "$data"; echo "rerecord: generate.sh failed" >&2; exit 1
fi

# Commit the data onto fixture-regen/<HEAD> without touching HEAD, the index or the checkout.
export GIT_INDEX_FILE=$scratch/index
git read-tree "$head"
git update-index --add --cacheinfo "100644,$(git hash-object -w "$data"),$data"
tree=$(git write-tree)
unset GIT_INDEX_FILE
git checkout -q HEAD -- "$data"
cat > "$scratch/message" <<EOF
fixtures: the accepted run re-recorded from candidate ${head:0:12}

The Objective front-end identity moved to $front, so the recorded honest call named a stale
front end (front_end_current). scripts/native-accepted-fixture/rerecord.sh re-ran the fixture's
driver steps on a fresh world with the candidate's binaries ($cand) and generate.sh replayed both
admissions in Lean: record and world root the Host's, projection the hand-written authority.
EOF
commit=$(git commit-tree "$tree" -p "$head" -F "$scratch/message")
git update-ref "refs/heads/fixture-regen/${head:0:12}" "$commit"
echo "recorded fixture-regen/${head:0:12} $commit"
