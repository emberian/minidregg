#!/usr/bin/env bash
set -euo pipefail

# Exercise the production prefix selector on tiny, isolated source/artifact
# closures. This does not claim a full Lean or native-link acceptance.
repo_root=$(cd "$(dirname "$0")/../.." && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/mini-success-prefix.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
baseline="$scratch/baseline"
current="$scratch/current"
checkpoints="$scratch/checkpoints"
evidence="$scratch/evidence"
mkdir -p "$baseline" "$current" "$checkpoints" "$evidence"

# Load the exact functions under test without running the build script.
functions="$scratch/functions.sh"
sed -n '/^module_checkpoint_paths() {/,/^}/p' \
  "$repo_root/scripts/build-native-host.sh" > "$functions"
sed -n '/^select_qualified_success_prefix() {/,/^}/p' \
  "$repo_root/scripts/build-native-host.sh" >> "$functions"
# shellcheck source=/dev/null
source "$functions"

modules=(A.Base B.Middle C.Host)
for module in "${modules[@]}"; do
  stem=${module//./\/}
  mkdir -p "$baseline/${stem%/*}" \
    "$baseline/.lake/build/lib/lean/${stem%/*}" \
    "$baseline/.lake/build/ir/${stem%/*}"
  printf 'source %s\n' "$module" > "$baseline/$stem.lean"
  printf 'olean %s\n' "$module" > "$baseline/.lake/build/lib/lean/$stem.olean"
  printf 'ilean %s\n' "$module" > "$baseline/.lake/build/lib/lean/$stem.ilean"
  printf 'private %s\n' "$module" > "$baseline/.lake/build/lib/lean/$stem.olean.private"
  printf 'c %s\n' "$module" > "$baseline/.lake/build/ir/$stem.c"
  printf '%s\n' "$module" >> "$scratch/baseline-modules.txt"
done
cp -R "$baseline/." "$current/"
cp "$scratch/baseline-modules.txt" "$scratch/current-modules.txt"

(
  cd "$baseline"
  index=0
  for module in "${modules[@]}"; do
    index=$((index + 1))
    stem=${module//./\/}
    checkpoint="$checkpoints/$(printf '%04d' "$index")-${module//./_}.sha256"
    module_checkpoint_paths "$stem" | while IFS= read -r artifact; do
      shasum -a 256 "$artifact"
    done > "$checkpoint"
  done
)

# Read by the sourced production selector.
# shellcheck disable=SC2034
success_baseline_root=$baseline
expect_prefix() {
  local expected=$1 actual
  actual=$(cd "$current" && select_qualified_success_prefix \
    "$scratch/current-modules.txt" "$scratch/baseline-modules.txt" \
    "$checkpoints" "$evidence")
  [[ "$actual" == "$expected" ]] || {
    printf 'expected prefix %s, got %s\n' "$expected" "$actual" >&2
    exit 1
  }
}

expect_prefix 3
printf 'changed dependency\n' > "$current/A/Base.lean"
expect_prefix 0
cp "$baseline/A/Base.lean" "$current/A/Base.lean"
printf 'changed middle\n' > "$current/B/Middle.lean"
expect_prefix 1
cp "$baseline/B/Middle.lean" "$current/B/Middle.lean"
printf 'changed last\n' > "$current/C/Host.lean"
expect_prefix 2
cp "$baseline/C/Host.lean" "$current/C/Host.lean"
printf 'A.Base\nA.Inserted\nB.Middle\nC.Host\n' > "$scratch/current-modules.txt"
expect_prefix 1
cp "$scratch/baseline-modules.txt" "$scratch/current-modules.txt"
printf 'drift\n' > "$current/.lake/build/lib/lean/A/Base.olean.private"
if (cd "$current" && select_qualified_success_prefix \
    "$scratch/current-modules.txt" "$scratch/baseline-modules.txt" \
    "$checkpoints" "$evidence" > "$scratch/drift.out" 2> "$scratch/drift.err"); then
  printf 'artifact drift was accepted\n' >&2
  exit 1
fi
grep -q 'successful prefix artifact changed: A.Base' "$scratch/drift.err"
cp "$baseline/.lake/build/lib/lean/A/Base.olean.private" \
  "$current/.lake/build/lib/lean/A/Base.olean.private"
ln -s Base.olean "$current/.lake/build/lib/lean/A/Base.olean.server"
if (cd "$current" && select_qualified_success_prefix \
    "$scratch/current-modules.txt" "$scratch/baseline-modules.txt" \
    "$checkpoints" "$evidence" > "$scratch/link.out" 2> "$scratch/link.err"); then
  printf 'optional artifact symlink was accepted\n' >&2
  exit 1
fi
grep -q 'linked prefix artifact:.*Base.olean.server' "$scratch/link.err"
printf 'PASS identical=3 dependency-change=0 middle-change=1 final-change=2 insertion=1 artifact-drift=refused artifact-symlink=refused\n'
