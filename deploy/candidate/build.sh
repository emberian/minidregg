#!/usr/bin/env bash
# Build a Mini candidate from one exact source archive:
#   bin/minidregg-host                          Lean-authored native Host
#   bin/mini                                    participant/operator client
#   bin/minidregg-link-sqlite-store             durable Store helper
#   bin/minidregg-credential-signature-verifier Ed25519 verifier helper
# plus SHA256SUMS and manifest.json (source commit, toolchains, hashes).
#
# usage: deploy/candidate/build.sh --out NEW_DIR [--source-archive SOURCE.tar]
#
# Without --source-archive the script must run inside a clean git checkout and
# archives HEAD itself. Either way every binary is built from the archive's
# bytes, extracted into NEW_DIR/work/src; nothing is read from the checkout the
# script was started from. See deploy/candidate/INTERFACES.md.
set -euo pipefail
export LC_ALL=C
CANDIDATE_PROG=build.sh
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
# shellcheck source=deploy/candidate/lib.sh
. "$here/lib.sh"

out=""
archive=""
while [ $# -gt 0 ]; do
  case "$1" in
    --out) [ $# -ge 2 ] || candidate_die "--out needs a value"; out=$2; shift 2 ;;
    --source-archive) [ $# -ge 2 ] || candidate_die "--source-archive needs a value"; archive=$2; shift 2 ;;
    -h|--help) sed -n '2,14p' "$0"; exit 0 ;;
    *) candidate_die "unknown argument: $1" ;;
  esac
done
[ -n "$out" ] || candidate_die "--out NEW_DIR is required"

case "$(uname -s):$(uname -m)" in
  Linux:x86_64) ;;
  *) candidate_die "qualified target is Linux x86_64 only; this is $(uname -s) $(uname -m)" ;;
esac
candidate_require git jq tar sha256sum file curl lake rustup cargo cc
cargo_jobs=${MINI_CANDIDATE_CARGO_JOBS:-2}
case "$cargo_jobs" in ''|*[!0-9]*) candidate_die "MINI_CANDIDATE_CARGO_JOBS must be a positive integer" ;; esac

out=$(candidate_abs "$out")
[ ! -e "$out" ] && [ ! -L "$out" ] || candidate_die "refusing existing output: $out"
mkdir -p "$out"
mkdir "$out/bin" "$out/work" "$out/logs"
log="$out/logs/build.log"
stamp() { printf '%s %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*" | tee -a "$log"; }
t_start=$(date +%s)

# 1. Exact source archive.
if [ -n "$archive" ]; then
  archive=$(candidate_abs "$archive")
  cp "$archive" "$out/source.tar"
  source_origin="supplied-archive"
else
  repo=$(git -C "$here" rev-parse --show-toplevel 2>/dev/null) \
    || candidate_die "not in a git checkout; pass --source-archive SOURCE.tar (from git archive)"
  [ -z "$(git -C "$repo" status --porcelain --untracked-files=no)" ] \
    || candidate_die "checkout has uncommitted tracked changes; commit them or pass --source-archive"
  git -C "$repo" archive --format=tar HEAD > "$out/source.tar"
  source_origin="git-archive-HEAD"
fi
commit=$(git get-tar-commit-id < "$out/source.tar") \
  || candidate_die "source archive carries no commit id; create it with git archive <commit>"
archive_sha=$(candidate_sha256 "$out/source.tar")
src="$out/work/src"
mkdir -p "$src"
tar -x -f "$out/source.tar" -C "$src"
(cd "$src" && find . -type f ! -path './.lake/*' -print0 | sort -z | xargs -0 sha256sum) \
  > "$out/logs/source-files.sha256"
source_files_sha=$(candidate_sha256 "$out/logs/source-files.sha256")
stamp "source commit=$commit archive_sha256=$archive_sha origin=$source_origin"

# 2. Toolchains, as the source pins them.
lean_pin=$(cat "$src/lean-toolchain")
rust_pin=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' "$src/rust-toolchain.toml")
[ -n "$rust_pin" ] || candidate_die "cannot read the Rust channel from rust-toolchain.toml"
rustup toolchain install "$rust_pin" --profile minimal >>"$log" 2>&1
# elan selects (and on first use installs) the toolchain named by lean-toolchain.
lake_version=$(cd "$src" && lake --version 2>>"$log" | sed -n 1p)
lean_version=$(cd "$src" && lean --version 2>>"$log" | sed -n 1p)
case "$lean_version" in
  *"${lean_pin##*:v}"*) ;;
  *) candidate_die "lean on PATH ($lean_version) is not the pinned $lean_pin; put elan's lake/lean first on PATH" ;;
esac
rustc_version=$(cd "$src/native/resource-client" && rustc -vV | tr '\n' ';')
cargo_version=$(cd "$src/native/resource-client" && cargo -V)
cc_version=$(cc --version | sed -n 1p)
stamp "lean=$lean_version rust=$rust_pin"

# 3. Lean packages: exact pinned revisions from lake-manifest.json, and the
# mathlib artifact cache for that revision (it carries .olean and generated C).
# The cache is downloaded into this build, not into the user's home.
t_lean=$(date +%s)
export MATHLIB_CACHE_DIR="$out/work/mathlib-cache"
(cd "$src" && lake exe cache get) >"$out/logs/mathlib-cache.log" 2>&1 \
  || { tail -40 "$out/logs/mathlib-cache.log" >&2; candidate_die "mathlib cache fetch failed"; }
t_cache=$(date +%s)
stamp "lean packages + mathlib cache: $((t_cache - t_lean))s"

# 4. Native Host through the repository's bounded builder. The extracted tree is
# an independent snapshot by construction, so it carries the snapshot marker.
: > "$src/.minidregg-native-snapshot"
(cd "$src" && MINIDREGG_CYCLE_DIR="$out/work/host-cycle" \
  scripts/build-native-host.sh --output "$out/work/host-build" \
    --binary "$out/work/host-bin/minidregg-host") >"$out/logs/host-build.log" 2>&1 \
  || { tail -60 "$out/logs/host-build.log" >&2; candidate_die "native Host build failed"; }
install -m 0555 "$out/work/host-bin/minidregg-host" "$out/bin/minidregg-host"
t_host=$(date +%s)
stamp "native Host: $((t_host - t_cache))s"

# 5. Rust binaries. Paths are remapped so the bytes do not depend on where the
# operator unpacked the source or keeps the cargo registry.
cargo_home=${CARGO_HOME:-$HOME/.cargo}
cargo_home=$(CDPATH='' cd -- "$cargo_home" && pwd -P)
export RUSTFLAGS="--remap-path-prefix=$src=/minidregg --remap-path-prefix=$cargo_home=/cargo"
export CARGO_INCREMENTAL=0
build_rust() {
  crate=$1 bin=$2
  cargo build --release --locked -j "$cargo_jobs" \
    --manifest-path "$src/native/$crate/Cargo.toml" \
    --target-dir "$out/work/target/$crate" --bin "$bin" \
    >"$out/logs/cargo-$crate.log" 2>&1 \
    || { tail -40 "$out/logs/cargo-$crate.log" >&2; candidate_die "cargo build failed: $crate"; }
  install -m 0555 "$out/work/target/$crate/release/$bin" "$out/bin/$bin"
}
build_rust resource-client mini
build_rust hyperdocument-link-sqlite-store minidregg-link-sqlite-store
build_rust credential-signature-verifier minidregg-credential-signature-verifier
t_rust=$(date +%s)
stamp "Rust binaries: $((t_rust - t_host))s"

# 6. Smoke: every binary runs and prints its usage contract.
"$out/bin/minidregg-host" >"$out/logs/usage-host.txt" 2>&1 || true
grep -q '^minidregg-host:' "$out/logs/usage-host.txt" || candidate_die "Host did not print its usage"
"$out/bin/mini" --help >"$out/logs/usage-mini.txt" 2>&1 || true
grep -q '^mini ' "$out/logs/usage-mini.txt" || candidate_die "mini did not print its usage"
"$out/bin/minidregg-link-sqlite-store" >"$out/logs/usage-store.txt" 2>&1 || true
grep -q '^usage:' "$out/logs/usage-store.txt" || candidate_die "Store helper did not print its usage"
"$out/bin/minidregg-credential-signature-verifier" >"$out/logs/usage-verifier.txt" 2>&1 || true
grep -q '^usage:' "$out/logs/usage-verifier.txt" || candidate_die "verifier did not print its usage"
file "$out"/bin/* > "$out/logs/file-types.txt"

# 7. Hashes and manifest. Paths in the manifest are relative to its directory.
(cd "$out" && sha256sum bin/minidregg-host bin/mini bin/minidregg-link-sqlite-store \
  bin/minidregg-credential-signature-verifier source.tar) > "$out/SHA256SUMS"
sum_of() { grep "  $1\$" "$out/SHA256SUMS" | cut -d ' ' -f 1; }
host_build_manifest_sha=$(candidate_sha256 "$out/work/host-build/manifest.txt")
jq -n \
  --arg commit "$commit" --arg archive "$archive_sha" --arg origin "$source_origin" \
  --arg files "$source_files_sha" \
  --arg leanPin "$lean_pin" --arg lean "$lean_version" --arg lake "$lake_version" \
  --arg rustPin "$rust_pin" --arg rustc "$rustc_version" --arg cargo "$cargo_version" \
  --arg cc "$cc_version" --arg rustflags "remap source=/minidregg, CARGO_HOME=/cargo" \
  --arg mathlib "$(jq -r '.packages[] | select(.name == "mathlib") | .rev' "$src/lake-manifest.json")" \
  --arg host "$(sum_of bin/minidregg-host)" --arg mini "$(sum_of bin/mini)" \
  --arg store "$(sum_of bin/minidregg-link-sqlite-store)" \
  --arg verifier "$(sum_of bin/minidregg-credential-signature-verifier)" \
  --arg hostManifest "$host_build_manifest_sha" \
  --argjson tCache "$((t_cache - t_lean))" --argjson tHost "$((t_host - t_cache))" \
  --argjson tRust "$((t_rust - t_host))" --argjson tTotal "$(( $(date +%s) - t_start ))" \
  --arg built "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  '{type: "minidregg-candidate-manifest-v1",
    source: {commit: $commit, archive: "source.tar", archiveSha256: $archive,
             origin: $origin, fileListSha256: $files},
    target: "x86_64-linux",
    toolchains: {leanToolchain: $leanPin, lean: $lean, lake: $lake, mathlibRev: $mathlib,
                 rustToolchain: $rustPin, rustc: $rustc, cargo: $cargo, cc: $cc,
                 rustflags: $rustflags},
    binaries: {host: {path: "bin/minidregg-host", sha256: $host},
               mini: {path: "bin/mini", sha256: $mini},
               store: {path: "bin/minidregg-link-sqlite-store", sha256: $store},
               verifier: {path: "bin/minidregg-credential-signature-verifier", sha256: $verifier}},
    hostBuildManifest: {path: "work/host-build/manifest.txt", sha256: $hostManifest},
    seconds: {leanPackagesAndMathlibCache: $tCache, nativeHost: $tHost, rust: $tRust, total: $tTotal},
    builtUtc: $built}' > "$out/manifest.json"
stamp "done: $out/manifest.json"
cat "$out/SHA256SUMS"
