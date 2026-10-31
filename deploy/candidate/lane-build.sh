#!/usr/bin/env bash
# Build a candidate's roles in a LANE clone (incrementally from a warm base), then package them.
# This is the path when a full `deploy/candidate/build.sh` (which rebuilds all of Lean) is not wanted.
# build.sh stays the from-scratch, byte-reproducible path; both end in deploy/candidate/package.py.
#
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh host    [build-native-host.sh args: --incremental-suffix-from ...]
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh consent                      (after host: a companion of that build)
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh umbrellas                    (after host: the libraries no shipped root imports)
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh rust-check                   (no Lean needed: `cargo check` of every rust role)
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh rust [--crate CRATE]...    (--crate: only those crates' roles)
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh pack OUT_DIR
#   LANE_DIR=/abs/lane  deploy/candidate/lane-build.sh overlay BASE_CANDIDATE OUT_DIR ROLE...
#
# overlay (hot-swap, ember 10-30: hotpatch worlds between batch candidates): OUT_DIR is BASE_CANDIDATE
# with ROLE's binaries replaced by this lane's builds (package.py --overlay: whole build families only,
# every pin re-emitted, provenance.json .overlay records base, commit and roles). Build them first:
# `rust --crate CRATE` for Rust roles (seconds to minutes, warm), `host` and `consent` for the Lean pair.
# The same clean-tree and compiled-inputs checks as pack. A gate then stands worlds up from OUT_DIR.
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
CANDIDATE_PROG=lane-build.sh
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
# shellcheck source=deploy/candidate/lib.sh
. "$here/lib.sh"
LANE_DIR=${LANE_DIR:?LANE_DIR=/abs/path/of/the/lane}
[[ $LANE_DIR = /* ]] || { echo "lane-build: LANE_DIR must be absolute" >&2; exit 64; }
step=${1:?host|consent|umbrellas|rust-check|rust|pack|overlay}; shift
src=$LANE_DIR/src
[ -e "$src/.git" ] || { echo "lane-build: $src is not a clone" >&2; exit 64; }   # a worktree (lane-tree) has a .git file
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
compiled=(':(glob)**/*.lean' lakefile.toml lake-manifest.json lean-toolchain rust-toolchain.toml Cargo.toml Cargo.lock ':(glob).cargo/**'
          ':(glob)native/*/Cargo.toml' ':(glob)native/*/Cargo.lock' ':(glob)native/*/build.rs'
          ':(glob)native/*/src/**' ':(glob)protocol/**' scripts/build-native-host.sh
          deploy/grain-host/launch-gate.rs)  # native/launch-gate's [[bin]] source
unchanged_since() {  # BUILD (host|rust): refuse unless HEAD's compiled inputs equal that build's commit
  local b=$1 at changed
  [ -f "$LANE_DIR/logs/$b-build.commit" ] || { echo "lane-build: no $b build recorded; run $b" >&2; exit 1; }
  at=$(cat "$LANE_DIR/logs/$b-build.commit")
  changed=$(git diff --name-only "$at" HEAD -- "${compiled[@]}")
  [ -z "$changed" ] || { echo "lane-build: compiled inputs changed since the $b build at $at:" >&2; echo "$changed" >&2; exit 1; }
  echo "lane-build: $b roles built at ${at:0:12}; compiled inputs identical at $(git rev-parse --short=12 HEAD)"
}
toolchains_json() {  # HEAD: the builder evidence package.py requires, as logs/toolchains-HEAD.json
  local head=$1 rust
  rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
  jq -n --arg lean "$(lean --version)" --arg lake "$(lake --version)" --arg leanPin "$(cat lean-toolchain)" \
    --arg rustPin "$rust" --arg rustc "$(rustc "+$rust" -vV)" --arg cargo "$(cargo "+$rust" -V)" \
    --arg cc "$(cc --version | head -1)" --arg host "$(hostname)" \
    --arg rustflags "$(cat "$LANE_DIR/logs/rust-build.flags")" \
    '{recorded: "lane-build", builtOn: $host, leanToolchain: $leanPin, lean: $lean, lake: $lake,
      rustToolchain: $rustPin, rustc: $rustc, cargo: $cargo, cc: $cc,
      rustflags: $rustflags,
      buildFlags: {rust: {RUSTFLAGS: $rustflags, CARGO_INCREMENTAL: "0", profile: "release", locked: true},
        native: {builder: "scripts/build-native-host.sh", hostRoot: "Host.Main", consentRoot: "Host.ClientConsentSession"}},
      nativeHost: "scripts/build-native-host.sh via lane-build.sh (incremental or full), consent as its companion"}' \
    >"$LANE_DIR/logs/toolchains-$head.json"
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
  umbrellas)
    # Fixtures, ObjectiveProofs and CensusChecks: no shipped root imports them, so the host and consent
    # stages never elaborate them, and a red there sat unseen on main (NativeDocWriteFixture, stale since
    # 3315a908). Seated like the host stage; a red here reds the candidate.
    [ -f "$LANE_DIR/native-out/manifest.txt" ] || { echo "lane-build: run host first (umbrellas reuse its closure)" >&2; exit 1; }
    unchanged_since host
    u="$LANE_DIR/umbrellas-out/$(date -u +%Y%m%dT%H%M%SZ)"
    mkdir -p "$LANE_DIR/umbrellas-out"
    targets=(); for t in $(bash scripts/pipeline/umbrella-targets --unshipped); do targets+=(--umbrella-target "$t"); done
    native "$u" "$u.no-binary" --umbrella --umbrella-only "${targets[@]}" ;;
  rust-check)
    # The rust step's exact role list, features included, as `cargo check --release`: a cfg or
    # feature red shows here in minutes, before the host stage, instead of after it.
    rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
    [ -n "$rust" ] || { echo "lane-build: no Rust channel in rust-toolchain.toml" >&2; exit 1; }
    export CARGO_TARGET_DIR=$LANE_DIR/rust-check-target
    { python3 deploy/candidate/package.py --rust-roles
      if grep -q -- '--fixture-roles' deploy/candidate/package.py; then python3 deploy/candidate/package.py --fixture-roles; fi
    } >"$LANE_DIR/logs/rust-check-roles.txt"
    while read -r _ crate bin features; do
      (cd "$src" && cargo "+$rust" check --release --offline --locked -j "${MINI_CANDIDATE_CARGO_JOBS:-4}" \
        --manifest-path "$src/native/$crate/Cargo.toml" --bin "$bin" ${features:+--features "$features"}) </dev/null >"$LANE_DIR/logs/check-$crate-$bin.log" 2>&1 \
        || { echo "FAIL check $crate/$bin${features:+ --features $features}"; grep -m5 -A6 '^error' "$LANE_DIR/logs/check-$crate-$bin.log"; exit 1; }
    done <"$LANE_DIR/logs/rust-check-roles.txt"
    echo "rust-check done $(date -u +%H:%M:%S)" ;;
  rust)
    rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
    [ -n "$rust" ] || { echo "lane-build: no Rust channel in rust-toolchain.toml" >&2; exit 1; }
    export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$LANE_DIR/rust-target} CARGO_INCREMENTAL=0
    mkdir -p "$CARGO_TARGET_DIR"
    CARGO_TARGET_DIR=$(CDPATH='' cd -- "$CARGO_TARGET_DIR" && pwd -P)
    export CARGO_TARGET_DIR
    # One workspace/lock: Cargo hashes member paths relative to its root.
    # Qualifying builds must use independent target directories and lexical roots.
    cargo_home=$(CDPATH='' cd -- "${CARGO_HOME:-$HOME/.cargo}" && pwd -P)
    export RUSTFLAGS="--remap-path-prefix=$src=/minidregg --remap-path-prefix=$cargo_home=/cargo --remap-path-prefix=$CARGO_TARGET_DIR=/target"
    printf '%s\n' "$RUSTFLAGS" >"$LANE_DIR/logs/rust-build.flags"
    printf '%s\n' "$src" >"$LANE_DIR/logs/rust-build.root"
    git rev-parse HEAD >"$LANE_DIR/logs/rust-build.commit"
    python3 deploy/candidate/package.py --rust-roles >"$LANE_DIR/logs/rust-roles.txt"
    # --crate CRATE...: only those crates (a hot-swap); pack then refuses until a full rust run.
    crates=()
    while [ $# -gt 0 ]; do
      case $1 in --crate) crates+=("${2:?--crate CRATE}"); shift 2 ;; *) echo "lane-build: rust takes --crate CRATE" >&2; exit 64 ;; esac
    done
    if [ ${#crates[@]} -gt 0 ]; then
      for c in "${crates[@]}"; do awk -v c="$c" '$2 == c {f=1} END {exit !f}' "$LANE_DIR/logs/rust-roles.txt" \
        || { echo "lane-build: no Rust role is built from crate $c" >&2; exit 64; }; done
      awk -v cs=" ${crates[*]} " 'index(cs, " " $2 " ")' "$LANE_DIR/logs/rust-roles.txt" >"$LANE_DIR/logs/rust-roles.partial"
      mv "$LANE_DIR/logs/rust-roles.partial" "$LANE_DIR/logs/rust-roles.txt"
      printf '%s\n' "${crates[@]}" >"$LANE_DIR/logs/rust-build.partial"
    else
      rm -f "$LANE_DIR/logs/rust-build.partial"
    fi
    while read -r _ crate bin features; do
      echo "== $crate/$bin $(date -u +%H:%M:%S)"
      (cd "$src" && cargo "+$rust" build --release --offline --locked -j "${MINI_CANDIDATE_CARGO_JOBS:-4}" \
        --manifest-path "$src/native/$crate/Cargo.toml" --bin "$bin" ${features:+--features "$features"}) </dev/null >"$LANE_DIR/logs/cargo-$crate-$bin.log" 2>&1 \
        || { echo "FAIL $crate/$bin"; tail -30 "$LANE_DIR/logs/cargo-$crate-$bin.log"; exit 1; }
      install -m 0555 "$CARGO_TARGET_DIR/release/$bin" "$LANE_DIR/artifacts/$bin"
    done <"$LANE_DIR/logs/rust-roles.txt"
    # Journey fixtures (package.py --fixture-roles): same tree, same flags, never candidate outputs.
    # (This builder also packs older tips, whose package.py still ships them as roles: an empty list.)
    rm -rf "$LANE_DIR/fixtures"; mkdir -p "$LANE_DIR/fixtures"
    : >"$LANE_DIR/logs/fixture-roles.txt"
    if [ ! -f "$LANE_DIR/logs/rust-build.partial" ] && grep -q -- '--fixture-roles' deploy/candidate/package.py; then
      python3 deploy/candidate/package.py --fixture-roles >"$LANE_DIR/logs/fixture-roles.txt"
    fi
    while read -r _ crate bin; do
      echo "== fixture $crate/$bin $(date -u +%H:%M:%S)"
      (cd "$src" && cargo "+$rust" build --release --offline --locked -j "${MINI_CANDIDATE_CARGO_JOBS:-4}" \
        --manifest-path "$src/native/$crate/Cargo.toml" --bin "$bin") </dev/null >"$LANE_DIR/logs/cargo-$crate-$bin.log" 2>&1 \
        || { echo "FAIL fixture $crate/$bin"; tail -30 "$LANE_DIR/logs/cargo-$crate-$bin.log"; exit 1; }
      install -m 0555 "$CARGO_TARGET_DIR/release/$bin" "$LANE_DIR/fixtures/$bin"
    done <"$LANE_DIR/logs/fixture-roles.txt"
    echo "rust done $(date -u +%H:%M:%S)" ;;
  pack)
    OUT=${1:?OUT_DIR}
    head=$(git rev-parse HEAD)
    [ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "lane-build: tracked changes uncommitted" >&2; exit 1; }
    for b in host rust; do unchanged_since $b; done
    [ ! -f "$LANE_DIR/logs/rust-build.partial" ] || { echo "lane-build: the last rust run built only $(paste -sd' ' "$LANE_DIR/logs/rust-build.partial"); run rust in full to pack" >&2; exit 1; }
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
    toolchains_json "$head"
    python3 deploy/candidate/package.py --roles "$LANE_DIR/logs/roles-$head.json" --source-archive "$LANE_DIR/logs/source-$head.tar" \
      --out "$OUT" --toolchains "$LANE_DIR/logs/toolchains-$head.json" --host-build-manifest "$LANE_DIR/native-out/manifest.txt"
    # Journey fixtures ride beside the candidate, outside bin/, the manifest and SHA256SUMS.
    if grep -q -- '--fixture-roles' deploy/candidate/package.py; then
      mkdir "$OUT/fixtures"
      while read -r _ _ bin; do
        [ -f "$LANE_DIR/fixtures/$bin" ] || { echo "lane-build: missing fixture $bin; run rust" >&2; exit 1; }
        install -m 0555 "$LANE_DIR/fixtures/$bin" "$OUT/fixtures/$bin"
      done < <(python3 deploy/candidate/package.py --fixture-roles)
      (cd "$OUT/fixtures" && sha256sum -- * >SHA256SUMS)
    fi ;;
  overlay)
    base=${1:?overlay BASE_CANDIDATE OUT_DIR ROLE...}; OUT=${2:?overlay BASE_CANDIDATE OUT_DIR ROLE...}; shift 2
    [ $# -gt 0 ] || { echo "lane-build: overlay names the roles it swaps" >&2; exit 64; }
    head=$(git rev-parse HEAD)
    [ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "lane-build: tracked changes uncommitted" >&2; exit 1; }
    A=$LANE_DIR/artifacts swaps=() lean=0 rustroles=0 hbm=()
    for r in "$@"; do
      case $r in
        host) f=$A/minidregg-host; lean=1 ;;
        consent) f=$A/minidregg-client-consent; lean=1 ;;
        *) f=$(python3 deploy/candidate/package.py --rust-roles | awk -v r="$r" '$1 == r {print $3}')
           [ -n "$f" ] || { echo "lane-build: $r is not a role" >&2; exit 64; }
           f=$A/$f; rustroles=1
           if [ -f "$LANE_DIR/logs/rust-build.partial" ]; then
             crate=$(python3 deploy/candidate/package.py --rust-roles | awk -v r="$r" '$1 == r {print $2}')
             grep -qx "$crate" "$LANE_DIR/logs/rust-build.partial" \
               || { echo "lane-build: the last rust run did not build $crate (role $r); rust --crate $crate" >&2; exit 1; }
           fi ;;
      esac
      [ -f "$f" ] || { echo "lane-build: missing $f (role $r)" >&2; exit 1; }
      swaps+=("--role=$r=$f")
    done
    [ $lean = 0 ] || { unchanged_since host; hbm=(--host-build-manifest "$LANE_DIR/native-out/manifest.txt"); }
    [ $rustroles = 0 ] || unchanged_since rust
    git archive --format=tar "$head" >"$LANE_DIR/logs/source-$head.tar"
    toolchains_json "$head"
    python3 deploy/candidate/package.py --overlay "$base" "${swaps[@]}" --source-archive "$LANE_DIR/logs/source-$head.tar" \
      --toolchains "$LANE_DIR/logs/toolchains-$head.json" --out "$OUT" "${hbm[@]}"
    # the base's journey fixtures, unchanged (they ride beside the candidate, never in its pins)
    if [ -d "$base/fixtures" ] && [ ! -e "$OUT/fixtures" ]; then cp -al "$base/fixtures" "$OUT/fixtures"; fi ;;
  *) echo "lane-build: unknown step $step" >&2; exit 64 ;;
esac
