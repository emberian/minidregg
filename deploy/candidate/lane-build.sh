#!/usr/bin/env bash
# Build a candidate's roles in a LANE clone (incrementally from a warm base), then package them.
# This is the path when a full `deploy/candidate/build.sh` (which rebuilds all of Lean) is not wanted.
# build.sh stays the from-scratch, byte-reproducible path; both end in deploy/candidate/package.py.
#
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh host    [build-native-host.sh args: --incremental-suffix-from ...]
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh consent                      (after host: a companion of that build)
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh rust
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh pack OUT_DIR
#
# LANE_DIR holds the clone at LANE_DIR/src (a snapshot: `touch src/.minidregg-native-snapshot`); evidence
# goes to LANE_DIR/{logs,cycle,native-out,consent-out}, binaries to LANE_DIR/artifacts. Run each step as
# `swarm-build deploy/candidate/lane-build.sh ...` on hbox, one at a time, in the foreground.
#
# pack REFUSES unless the tree is clean and no compiled input differs between each build commit
# (logs/host-build.commit, logs/rust-build.commit) and HEAD, so a candidate never claims a commit that
# its binaries were not built at. package.py then REFUSES a role set without the consent pair or the key broker, or missing any role
# of `package.py --rust-roles` (the one Rust role list this script and build.sh both read).
set -euo pipefail
LANE_DIR=${LANE_DIR:?LANE_DIR=/abs/path/of/the/lane}
[[ $LANE_DIR = /* ]] || { echo "lane-build: LANE_DIR must be absolute" >&2; exit 64; }
step=${1:?host|consent|rust|pack}; shift
src=$LANE_DIR/src
[ -d "$src/.git" ] || { echo "lane-build: $src is not a clone" >&2; exit 64; }
mkdir -p "$LANE_DIR/artifacts" "$LANE_DIR/cycle" "$LANE_DIR/logs"
cd "$src"
native() {  # OUTPUT_DIR BINARY [builder args...]
  local out=$1 bin=$2; shift 2
  MINIDREGG_NATIVE_JOBS=${MINIDREGG_NATIVE_JOBS:-2} MINIDREGG_LEAN_THREADS=${MINIDREGG_LEAN_THREADS:-2} \
    MINIDREGG_CYCLE_DIR="$LANE_DIR/cycle" LEAN_NUM_THREADS=2 \
    scripts/build-native-host.sh "$@" --output "$out" --binary "$bin"
}
# The inputs a binary is compiled from. A commit that changes none of them (a script, a doc) does not
# move what a build at an earlier commit produced; one that changes any of them does.
compiled=(':(glob)**/*.lean' lakefile.toml lake-manifest.json lean-toolchain rust-toolchain.toml
          ':(glob)native/*/Cargo.toml' ':(glob)native/*/Cargo.lock' ':(glob)native/*/build.rs'
          ':(glob)native/*/src/**' ':(glob)protocol/**' scripts/build-native-host.sh)
unchanged_since() {  # BUILD (host|rust): refuse unless HEAD's compiled inputs equal that build's commit
  local b=$1 at changed
  [ -f "$LANE_DIR/logs/$b-build.commit" ] || { echo "lane-build: no $b build recorded; run $b" >&2; exit 1; }
  at=$(cat "$LANE_DIR/logs/$b-build.commit")
  changed=$(git diff --name-only "$at" HEAD -- "${compiled[@]}")
  [ -z "$changed" ] || { echo "lane-build: compiled inputs changed since the $b build at $at:" >&2; echo "$changed" >&2; exit 1; }
  echo "lane-build: $b roles built at ${at:0:12}; compiled inputs identical at $(git rev-parse --short=12 HEAD)"
}
case $step in
  host)
    git rev-parse HEAD >"$LANE_DIR/logs/host-build.commit"
    git status --porcelain --untracked-files=no >"$LANE_DIR/logs/host-build.dirty"
    [ ! -s "$LANE_DIR/logs/host-build.dirty" ] || { echo "lane-build: tracked changes uncommitted; commit first" >&2; exit 1; }
    native "$LANE_DIR/native-out" "$LANE_DIR/artifacts/minidregg-host" "$@" ;;
  consent)
    [ -f "$LANE_DIR/native-out/manifest.txt" ] || { echo "lane-build: run host first (the consent build is its companion)" >&2; exit 1; }
    unchanged_since host
    native "$LANE_DIR/consent-out" "$LANE_DIR/artifacts/minidregg-client-consent" \
      --root Host.ClientConsentSession --usage-prefix 'minidregg-client-consent:' --companion-of "$LANE_DIR/native-out" ;;
  rust)
    rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
    [ -n "$rust" ] || { echo "lane-build: no Rust channel in rust-toolchain.toml" >&2; exit 1; }
    export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$LANE_DIR/rust-target} CARGO_INCREMENTAL=0
    export RUSTFLAGS="--remap-path-prefix=$src=/minidregg --remap-path-prefix=$HOME/.cargo=/cargo"
    git rev-parse HEAD >"$LANE_DIR/logs/rust-build.commit"
    python3 deploy/candidate/package.py --rust-roles >"$LANE_DIR/logs/rust-roles.txt"
    while read -r _ crate bin; do
      echo "== $crate/$bin $(date -u +%H:%M:%S)"
      cargo "+$rust" build --release --offline --locked -j "${MINI_CANDIDATE_CARGO_JOBS:-4}" \
        --manifest-path "native/$crate/Cargo.toml" --bin "$bin" </dev/null >"$LANE_DIR/logs/cargo-$crate-$bin.log" 2>&1 \
        || { echo "FAIL $crate/$bin"; tail -30 "$LANE_DIR/logs/cargo-$crate-$bin.log"; exit 1; }
      install -m 0555 "$CARGO_TARGET_DIR/release/$bin" "$LANE_DIR/artifacts/$bin"
    done <"$LANE_DIR/logs/rust-roles.txt"
    echo "rust done $(date -u +%H:%M:%S)" ;;
  pack)
    OUT=${1:?OUT_DIR}
    head=$(git rev-parse HEAD)
    [ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "lane-build: tracked changes uncommitted" >&2; exit 1; }
    for b in host rust; do unchanged_since $b; done
    git archive --format=tar "$head" >"$LANE_DIR/logs/source-$head.tar"
    A=$LANE_DIR/artifacts
    roles=$(jq -n --arg c "$head" --arg hb "$(cat "$LANE_DIR/logs/host-build.commit")" --arg rb "$(cat "$LANE_DIR/logs/rust-build.commit")" \
      '{sourceCommit: $c, origin: "lane-build", builtAt: {host: $hb, rust: $rb}, compiledInputsEqualAt: $c}')
    for pair in host:minidregg-host consent:minidregg-client-consent \
        $(python3 deploy/candidate/package.py --rust-roles | awk '{print $1 ":" $3}'); do
      r=${pair%%:*} f=$A/${pair#*:}
      [ -f "$f" ] || { echo "lane-build: missing $f (role $r)" >&2; exit 1; }
      roles=$(jq --arg r "$r" --arg p "$f" --arg h "$(sha256sum "$f" | cut -d' ' -f1)" '.[$r] = $p | .sha256[$r] = $h' <<<"$roles")
    done
    printf '%s\n' "$roles" >"$LANE_DIR/logs/roles-$head.json"
    rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
    jq -n --arg lean "$(lean --version)" --arg lake "$(lake --version)" --arg leanPin "$(cat lean-toolchain)" \
      --arg rustPin "$rust" --arg rustc "$(rustc "+$rust" -vV | tr '\n' ';')" --arg cargo "$(cargo "+$rust" -V)" \
      --arg cc "$(cc --version | head -1)" --arg host "$(hostname)" \
      '{recorded: "lane-build", builtOn: $host, leanToolchain: $leanPin, lean: $lean, lake: $lake,
        rustToolchain: $rustPin, rustc: $rustc, cargo: $cargo, cc: $cc,
        rustflags: "remap source=/minidregg, CARGO_HOME=/cargo",
        nativeHost: "scripts/build-native-host.sh via lane-build.sh (incremental or full), consent as its companion"}' \
      >"$LANE_DIR/logs/toolchains-$head.json"
    python3 deploy/candidate/package.py --roles "$LANE_DIR/logs/roles-$head.json" --source-archive "$LANE_DIR/logs/source-$head.tar" \
      --out "$OUT" --toolchains "$LANE_DIR/logs/toolchains-$head.json" --host-build-manifest "$LANE_DIR/native-out/manifest.txt" ;;
  *) echo "lane-build: unknown step $step" >&2; exit 64 ;;
esac
