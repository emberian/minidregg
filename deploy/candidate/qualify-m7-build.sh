#!/usr/bin/env bash
# Two complete builds in independent snapshots, targets and lexical roots.
# Run ONLY through request_journey. Creates an unreferenced snapshot commit;
# never changes the working checkout's index or refs. Evidence stays outside src.
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
work=${1:?new evidence directory}
warm=${2:-/srv/warm-base/src}
native_baseline=${3:-}
[ ! -e "$work" ]
mkdir -p "$work"
work=$(realpath "$work")
case "$work/" in "$repo/"*) echo 'qualification evidence must be outside source tree' >&2; exit 1 ;; esac
# Named authorized paths only. WORKLOG is deliberately not part of the snapshot.
paths=(Cargo.toml Cargo.lock deploy/candidate native/grain-runtime/Cargo.lock
  native/credential-signature-verifier/Cargo.lock native/discord-entrance/Cargo.lock
  native/hyperdocument-link-sqlite-store/Cargo.lock native/hyperdocument-link-sqlite-store/Cargo.toml
  native/inference-scheduler/Cargo.lock native/mini-keys/Cargo.lock native/mini-sdk/Cargo.lock
  native/pay-watcher/Cargo.lock native/resource-client/Cargo.lock native/resource-client/Cargo.toml
  native/resource-client/journey.d/m7.sh native/signed-api-path/Cargo.lock
  native/spk-host/Cargo.lock native/spk-rpc/Cargo.lock scripts/kn2/plant-m7-tamper.sh
  scripts/kn2/plant-m7-no-verification.sh)
export GIT_INDEX_FILE=$work/snapshot.index
git read-tree HEAD
git add -A -- "${paths[@]}"
tree=$(git write-tree)
snapshot=$(git -c user.name='M7 qualification' -c user.email='m7@localhost' -c commit.gpgsign=false \
  commit-tree "$tree" -p HEAD -m 'Unreferenced exact-source M7 qualification snapshot')
unset GIT_INDEX_FILE
printf '%s\n' "$snapshot" >"$work/snapshot.commit"
printf '%s\n' "$tree" >"$work/snapshot.tree"
unset RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER CARGO_ENCODED_RUSTFLAGS CARGO_TARGET_DIR
export CARGO_INCREMENTAL=0 MINI_CANDIDATE_CARGO_JOBS=4
for side in A B; do
  lane=$work/$side
  mkdir -p "$lane"
  "$repo/scripts/pipeline/clone-warm" "$warm" "$lane/src" >"$work/clone-$side.log" 2>&1
  git -C "$lane/src" fetch --no-tags "$repo" "$snapshot" >"$work/fetch-$side.log" 2>&1
  # The disposable clone gets its own detached HEAD, leaving the worker and warm base untouched.
  git -C "$lane/src" checkout --detach "$snapshot" >"$work/checkout-$side.log" 2>&1
  export LANE_DIR=$lane
  if [ -n "$native_baseline" ]; then
    old=$native_baseline/$side
    # Native source/flags are unchanged. Preserve separate A/B compiled evidence;
    # never copy A's Host into B or claim a new native compilation happened.
    git -C "$repo" diff --exit-code "$(cat "$old/logs/host-build.commit")" "$snapshot" -- \
      '*.lean' lean-toolchain lakefile.toml lake-manifest.json scripts/build-native-host.sh
    cp -a --reflink=auto "$old/native-out" "$lane/native-out"
    cp -a --reflink=auto "$old/consent-out" "$lane/consent-out"
    mkdir -p "$lane/artifacts" "$lane/logs"
    cp "$old/artifacts/minidregg-host" "$old/artifacts/minidregg-client-consent" "$lane/artifacts/"
    printf '%s\n' "$snapshot" >"$lane/logs/host-build.commit"
    printf 'native outputs built independently at %s; native compiled inputs unchanged at %s\n' \
      "$(cat "$old/logs/host-build.commit")" "$snapshot" >"$lane/logs/native-reuse.txt"
    steps=(rust)
  else
    steps=(host consent rust)
  fi
  for step in "${steps[@]}"; do
    "$lane/src/deploy/candidate/lane-build.sh" "$step" >"$work/$side-$step.log" 2>&1
  done
  "$lane/src/deploy/candidate/lane-build.sh" pack "$lane/candidate" >"$work/$side-pack.log" 2>&1
  (cd "$lane/candidate" && find bin -type f -print0 | sort -z | xargs -0 sha256sum) >"$work/$side.sha256"
  cat "$work/$side.sha256"
done
cmp "$work/A.sha256" "$work/B.sha256"
echo "M7 build: every output reproduces across $work/A/src and $work/B/src"
