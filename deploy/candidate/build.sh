#!/usr/bin/env bash
# Build a Mini candidate from one exact source archive:
#   bin/minidregg-host                          Lean-authored native Host
#   bin/minidregg-client-consent                local signing consent (MINI_CONSENT_HOST)
#   bin/mini                                    participant/operator client
#   bin/minidregg-link-sqlite-store             durable Store helper
#   bin/minidregg-credential-signature-verifier Ed25519 verifier helper
#   bin/grain-runtime                           agent grain controller (Hermes host)
#   bin/grain-provider-bridge                   sandbox inference bridge
#   bin/spk-host                                application custody and broker
#   bin/spk-browser-proxy                       TLS browser entrance
#   bin/mini-spk-broker, bin/spk-hostd          SPK broker and grain host daemon (shipped, not installed by default)
#   bin/mini-spk-volume-helper                  per-store root volume helper (deploy/spk-host/install-user-world installs it)
#   bin/mini-discord                            Discord entrance
#   bin/mini-keys                               key broker (seal key, provider and Discord secrets)
#   bin/pay-watcher                             Solana pay watcher
# packaged by deploy/candidate/package.py into the one candidate format:
# provenance.json (source commit, toolchains, hashes, each ELF's glibc needs),
# SHA256SUMS, and manifest.json (the journey-format manifest: absolute paths +
# SHA-256 pins). package.py --capsule packages a sealed hbox family the same way.
# Signing needs a locally selected consent pair: MINI_LOCAL_HOST (the native
# Host, for pure codecs) and MINI_CONSENT_HOST (minidregg-client-consent, which
# reconstructs every plan before a key signs it), plus MINI_CONSENT_CONFIG.
# Without the pair the client refuses to sign; it never signs the box's bytes.
# package.py links bin/clients/x86_64-unknown-linux-gnu/ (the Linux friend bundle:
# mini, both consent executables, the verifier and the Store helper) and refuses a
# candidate without the consent pair. The macOS client has no native consent pair
# yet (provenance .clients[..].consent is null); it cannot sign.
# Friend builds of the client ride along: bin/mini is the Linux x86-64 client,
# and each target in MINI_CLIENT_TARGETS (default aarch64-apple-darwin) is
# cross-built to bin/clients/TARGET/mini, hashed into provenance.json
# (.clients) and SHA256SUMS. macOS arm64 links with zig (`zig cc -target
# aarch64-macos`, ad-hoc signed by the linker); MINI_CLIENT_TARGETS= builds none.
# --client-only builds just the clients (no Lean, no Host, no helpers) and
# writes provenance.json of type minidregg-client-provenance-v1, no manifest.
#
# usage: deploy/candidate/build.sh --out NEW_DIR [--source-archive SOURCE.tar] [--client-only]
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
client_only=0
while [ $# -gt 0 ]; do
  case "$1" in
    --out) [ $# -ge 2 ] || candidate_die "--out needs a value"; out=$2; shift 2 ;;
    --source-archive) [ $# -ge 2 ] || candidate_die "--source-archive needs a value"; archive=$2; shift 2 ;;
    --client-only) client_only=1; shift ;;
    -h|--help) sed -n '2,/^# usage:/p' "$0"; exit 0 ;;
    *) candidate_die "unknown argument: $1" ;;
  esac
done
[ -n "$out" ] || candidate_die "--out NEW_DIR is required"

case "$(uname -s):$(uname -m)" in
  Linux:x86_64) ;;
  *) candidate_die "qualified target is Linux x86_64 only; this is $(uname -s) $(uname -m)" ;;
esac
if [ "$client_only" = 1 ]; then
  candidate_require git jq tar sha256sum file rustup cargo cc flock
else
  candidate_require git jq tar sha256sum file curl lake rustup cargo cc python3 readelf flock
fi
client_targets=${MINI_CLIENT_TARGETS-aarch64-apple-darwin}
for target in $client_targets; do
  case "$target" in
    aarch64-apple-darwin) candidate_require zig ;;
    *) candidate_die "unsupported client target $target (supported: aarch64-apple-darwin; Linux x86-64 is bin/mini)" ;;
  esac
done
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
rustup toolchain install --no-self-update "$rust_pin" --profile minimal >>"$log" 2>&1
for target in $client_targets; do
  rustup target add --toolchain "$rust_pin" "$target" >>"$log" 2>&1 \
    || candidate_die "cannot add Rust target $target to $rust_pin"
done
lake_version="" lean_version=""
if [ "$client_only" = 0 ]; then
# elan selects (and on first use installs) the toolchain named by lean-toolchain.
lake_version=$(cd "$src" && lake --version 2>>"$log" | sed -n 1p)
lean_version=$(cd "$src" && lean --version 2>>"$log" | sed -n 1p)
case "$lean_version" in
  *"${lean_pin##*:v}"*) ;;
  *) candidate_die "lean on PATH ($lean_version) is not the pinned $lean_pin; put elan's lake/lean first on PATH" ;;
esac
fi
# rustup chooses a toolchain from the working directory, not from
# --manifest-path, so every Rust command names the pinned channel explicitly.
rustc_version=$(rustc "+$rust_pin" -vV)
rustc_line=$(rustc "+$rust_pin" -V)
cargo_version=$(cargo "+$rust_pin" -V)
cc_version=$(cc --version | sed -n 1p)
if [ "$client_only" = 1 ]; then stamp "rust=$rust_pin (client only)"; else stamp "lean=$lean_version rust=$rust_pin"; fi

t_lean=$(date +%s) t_cache=$t_lean t_host=$t_lean
if [ "$client_only" = 0 ]; then
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

# 4b. Local signing consent from the same snapshot. Every module the Host build
# compiled is reused after a byte check; only the consent-only modules compile.
(cd "$src" && MINIDREGG_CYCLE_DIR="$out/work/host-cycle" \
  scripts/build-native-host.sh --root Host.ClientConsentSession \
    --usage-prefix 'minidregg-client-consent:' --companion-of "$out/work/host-build" \
    --output "$out/work/consent-build" \
    --binary "$out/work/consent-bin/minidregg-client-consent") >"$out/logs/consent-build.log" 2>&1 \
  || { tail -60 "$out/logs/consent-build.log" >&2; candidate_die "native consent build failed"; }
install -m 0555 "$out/work/consent-bin/minidregg-client-consent" "$out/bin/minidregg-client-consent"
t_consent=$(date +%s)
stamp "native consent: $((t_consent - t_host))s"
t_host=$t_consent
fi

# 5. Workspace members use relative dependency identity at every absolute build root.
# Do not compile through a shared symlink: qualification compares distinct lexical roots.
bsrc=$src
cargo_home=${CARGO_HOME:-$HOME/.cargo}
cargo_home=$(CDPATH='' cd -- "$cargo_home" && pwd -P)
export RUSTFLAGS="--remap-path-prefix=$bsrc=/minidregg --remap-path-prefix=$cargo_home=/cargo --remap-path-prefix=$out/work/target=/target"
export CARGO_INCREMENTAL=0
build_rust() {
  crate=$1 bin=$2
  (cd "$bsrc" && cargo "+$rust_pin" build --release --locked -j "$cargo_jobs" \
    --manifest-path "$bsrc/native/$crate/Cargo.toml" \
    --target-dir "$out/work/target" --bin "$bin" \
    >"$out/logs/cargo-$crate-$bin.log" 2>&1) \
    || { tail -40 "$out/logs/cargo-$crate-$bin.log" >&2; candidate_die "cargo build failed: $crate/$bin"; }
  # The binary must name the pinned compiler (ELF .comment "rustc version ...").
  grep -aqF "rustc version ${rustc_line#rustc }" "$out/work/target/release/$bin" \
    || candidate_die "$bin was not built by $rustc_line"
  install -m 0555 "$out/work/target/release/$bin" "$out/bin/$bin"
}
# The Rust roles are package.py's one list (`--rust-roles`: ROLE CRATE BINARY), read from the archive.
python3 "$src/deploy/candidate/package.py" --rust-roles >"$out/work/rust-roles.txt" \
  || candidate_die "package.py --rust-roles failed"
build_rust resource-client mini
if [ "$client_only" = 0 ]; then
  while read -r role crate bin; do
    [ "$role" = mini ] || build_rust "$crate" "$bin" </dev/null
  done <"$out/work/rust-roles.txt"
fi

# 5b. Friend clients. The C parts (ring) and the link go through zig for the
# target; the Apple-style target/arch flags rustc and cc-rs add are dropped
# (zig takes -target), and -liconv with them (zig's libSystem stubs carry no
# separate iconv; the client uses none). An empty SDKROOT stands in for an
# Xcode SDK, which rustc otherwise asks xcrun for.
zig_version=""
clients_json='{}'
clients_json=$(jq -n --arg sha "$(candidate_sha256 "$out/bin/mini")" \
  '{"x86_64-unknown-linux-gnu": {path: "bin/mini", sha256: $sha, consent: null}}')
for target in $client_targets; do
  zig_version=$(zig version)
  cc_wrap="$out/work/zig-cc-$target"
  cat >"$cc_wrap" <<'WRAP'
#!/usr/bin/env bash
out=()
skip=0
for a in "$@"; do
  if [[ $skip == 1 ]]; then skip=0; continue; fi
  case "$a" in
    --target=*) ;;
    -target|-arch) skip=1 ;;
    -liconv) ;;
    *) out+=("$a") ;;
  esac
done
exec zig cc -target aarch64-macos "${out[@]}"
WRAP
  chmod 0555 "$cc_wrap"
  mkdir -p "$out/work/sdk/MacOSX.sdk"
  target_env=$(printf '%s' "$target" | tr 'a-z-' 'A-Z_')
  target_cc=$(printf '%s' "$target" | tr '-' '_')
  # The linker computes the Mach-O LC_UUID over the file it writes, and that
  # file's debug map (N_OSO stabs) names every object by its path under --out;
  # rustc strips the stabs afterwards but the UUID stays. -Wl,-S keeps the
  # debug map out of the link, so the bytes do not depend on --out. The prefix
  # maps keep the build directory out of ring's C objects as well.
  (cd "$bsrc" && env "CC_$target_cc=$cc_wrap" \
      "CFLAGS_$target_cc=-ffile-prefix-map=$out=/out -ffile-prefix-map=$cargo_home=/cargo" \
      RUSTFLAGS="--remap-path-prefix=$out=/out $RUSTFLAGS -C link-arg=-Wl,-S" \
      "CARGO_TARGET_${target_env}_LINKER=$cc_wrap" SDKROOT="$out/work/sdk/MacOSX.sdk" \
      ZIG_GLOBAL_CACHE_DIR="$out/work/zig-cache" ZIG_LOCAL_CACHE_DIR="$out/work/zig-cache" \
    cargo "+$rust_pin" build --release --locked -j "$cargo_jobs" \
    --manifest-path "$bsrc/native/resource-client/Cargo.toml" --target "$target" \
    --target-dir "$out/work/target/client-$target" --bin mini \
    >"$out/logs/cargo-client-$target.log" 2>&1) \
    || { tail -40 "$out/logs/cargo-client-$target.log" >&2; candidate_die "client build failed: $target"; }
  mkdir -p "$out/bin/clients/$target"
  install -m 0555 "$out/work/target/client-$target/$target/release/mini" "$out/bin/clients/$target/mini"
  file "$out/bin/clients/$target/mini" | grep -q 'Mach-O 64-bit arm64 executable' \
    || candidate_die "$target client is not a Mach-O arm64 executable"
  clients_json=$(printf '%s' "$clients_json" | jq --arg t "$target" --arg p "bin/clients/$target/mini" \
    --arg sha "$(candidate_sha256 "$out/bin/clients/$target/mini")" --arg linker "zig $zig_version cc -target aarch64-macos" \
    '.[$t] = {path: $p, sha256: $sha, linker: $linker, consent: null}')
done
t_rust=$(date +%s)
stamp "Rust binaries: $((t_rust - t_host))s"

# 6. Smoke: every binary runs and prints its usage contract; the client names
# the friend surface (shell, join, --remote).
"$out/bin/mini" --help >"$out/logs/usage-mini.txt" 2>&1 || usage_status=$?
grep -q '^mini ' "$out/logs/usage-mini.txt" || candidate_die "mini did not print its usage"
for word in 'mini shell' 'mini join' '--remote'; do
  grep -qF -- "$word" "$out/logs/usage-mini.txt" || candidate_die "mini --help does not list $word"
done
if [ "$client_only" = 1 ]; then
  file "$out"/bin/mini "$out"/bin/clients/*/mini > "$out/logs/file-types.txt" 2>/dev/null || usage_status=$?
  jq -n \
    --arg commit "$commit" --arg archive "$archive_sha" --arg origin "$source_origin" \
    --arg files "$source_files_sha" --arg rustPin "$rust_pin" --arg rustc "$rustc_version" \
    --arg cargo "$cargo_version" --arg cc "$cc_version" --arg zig "$zig_version" \
    --arg rustflags "$RUSTFLAGS" \
    --argjson clients "$clients_json" --arg built "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    '{type: "minidregg-client-provenance-v1",
      source: {commit: $commit, archive: "source.tar", archiveSha256: $archive,
               origin: $origin, fileList: "logs/source-files.sha256", fileListSha256: $files},
      toolchains: {rustToolchain: $rustPin, rustc: $rustc, cargo: $cargo, cc: $cc, zig: $zig,
                   rustflags: $rustflags},
      clients: $clients, builtUtc: $built}' > "$out/provenance.json"
  (cd "$out" && sha256sum bin/mini $(jq -r '.clients[].path' provenance.json | grep -vx bin/mini) \
    provenance.json source.tar logs/source-files.sha256) > "$out/SHA256SUMS"
  stamp "done (client only): $out/provenance.json"
  cat "$out/SHA256SUMS"
  exit 0
fi
"$out/bin/minidregg-host" >"$out/logs/usage-host.txt" 2>&1 || usage_status=$?
grep -q '^minidregg-host:' "$out/logs/usage-host.txt" || candidate_die "Host did not print its usage"
"$out/bin/minidregg-client-consent" >"$out/logs/usage-consent.txt" 2>&1 || usage_status=$?
grep -q '^minidregg-client-consent: .*minidregg-client-consent CONFIG stdio' "$out/logs/usage-consent.txt" \
  || candidate_die "consent provider did not print its usage"
# The Host starts without doing work: every start of `mini serve` pays its initializers.
"$src/scripts/check-host-cold-start.sh" "$out/bin/minidregg-host" >"$out/logs/host-cold-start.txt" 2>&1 \
  || { cat "$out/logs/host-cold-start.txt" >&2; candidate_die "Host cold start over budget"; }
"$out/bin/minidregg-link-sqlite-store" >"$out/logs/usage-store.txt" 2>&1 || usage_status=$?
grep -q '^usage:' "$out/logs/usage-store.txt" || candidate_die "Store helper did not print its usage"
"$out/bin/minidregg-credential-signature-verifier" >"$out/logs/usage-verifier.txt" 2>&1 || usage_status=$?
grep -q '^usage:' "$out/logs/usage-verifier.txt" || candidate_die "verifier did not print its usage"
file "$out"/bin/minidregg-host "$out"/bin/minidregg-client-consent "$out"/bin/mini "$out"/bin/minidregg-link-sqlite-store \
  "$out"/bin/minidregg-credential-signature-verifier "$out"/bin/clients/*/mini \
  > "$out/logs/file-types.txt" 2>/dev/null || usage_status=$?

# 7. Package: the one candidate format, written by deploy/candidate/package.py
# from THIS archive's bytes (the copy extracted into work/src). The roles are the
# binaries built above; package.py copies nothing (they are already in bin/),
# installs run.sh, lib.sh, params.sh, genesis.sh, genesis-params.example.json and
# INTERFACES.md from source.tar, records each ELF's glibc needs, and writes
# provenance.json, SHA256SUMS and manifest.json.
roles_json="$out/work/roles.json"
roles='{}'
for pair in host:minidregg-host $(awk '{print $1 ":" $3}' "$out/work/rust-roles.txt"); do
  role=${pair%%:*} file=$out/bin/${pair#*:}
  roles=$(printf '%s' "$roles" | jq --arg r "$role" --arg p "$file" --arg h "$(candidate_sha256 "$file")" \
    '.[$r] = $p | .sha256[$r] = $h')
done
# The local signing consent pair (step 4b): a candidate that cannot sign is not a candidate.
[ -x "$out/bin/minidregg-client-consent" ] || candidate_die "bin/minidregg-client-consent is absent after step 4b"
roles=$(printf '%s' "$roles" | jq --arg p "$out/bin/minidregg-client-consent" \
  --arg h "$(candidate_sha256 "$out/bin/minidregg-client-consent")" '.consent = $p | .sha256.consent = $h')
printf '%s' "$roles" | jq --arg c "$commit" '. + {sourceCommit: $c, origin: "build.sh"}' >"$roles_json"
jq -n --arg leanPin "$lean_pin" --arg lean "$lean_version" --arg lake "$lake_version" \
  --arg mathlib "$(jq -r '.packages[] | select(.name == "mathlib") | .rev' "$src/lake-manifest.json")" \
  --arg rustPin "$rust_pin" --arg rustc "$rustc_version" --arg cargo "$cargo_version" \
  --arg cc "$cc_version" --arg zig "$zig_version" --arg rustflags "$RUSTFLAGS" \
  --arg sourceOrigin "$source_origin" \
  --argjson tCache "$((t_cache - t_lean))" --argjson tHost "$((t_host - t_cache))" \
  --argjson tRust "$((t_rust - t_host))" --argjson tTotal "$(( $(date +%s) - t_start ))" \
  '{recorded: "build.sh", sourceOrigin: $sourceOrigin, leanToolchain: $leanPin, lean: $lean, lake: $lake,
    mathlibRev: $mathlib, rustToolchain: $rustPin, rustc: $rustc, cargo: $cargo, cc: $cc, zig: $zig,
    rustflags: $rustflags,
    buildFlags: {rust: {RUSTFLAGS: $rustflags, CARGO_INCREMENTAL: "0", profile: "release", locked: true},
      native: {builder: "scripts/build-native-host.sh", hostRoot: "Host.Main", consentRoot: "Host.ClientConsentSession"}},
    seconds: {leanPackagesAndMathlibCache: $tCache, nativeHost: $tHost, rust: $tRust, total: $tTotal}}' \
  >"$out/work/toolchains.json"
python3 "$src/deploy/candidate/package.py" --roles "$roles_json" --source-archive "$out/source.tar" \
  --out "$out" --into-existing --toolchains "$out/work/toolchains.json" \
  --host-build-manifest "$out/work/host-build/manifest.txt" >"$out/logs/package.json" \
  || candidate_die "package.py refused the build (above)"
# The consent pair is in the shipped candidate, not just built: provenance pins it as a binary and
# as the Linux friend bundle, and the bundle's files are the pinned bytes.
jq -e '.binaries.consent.path == "bin/minidregg-client-consent"
    and (.clients["x86_64-unknown-linux-gnu"].consent.consentHost.sha256 == .binaries.consent.sha256)
    and (.clients["x86_64-unknown-linux-gnu"].consent.localHost.sha256 == .binaries.host.sha256)' \
  "$out/provenance.json" >/dev/null \
  || candidate_die "provenance.json does not pin the consent pair in .binaries and the Linux friend bundle"
for exe in mini minidregg-host minidregg-client-consent minidregg-credential-signature-verifier \
    minidregg-link-sqlite-store; do
  cmp -s "$out/bin/$exe" "$out/bin/clients/x86_64-unknown-linux-gnu/$exe" \
    || candidate_die "friend bundle file $exe is absent or differs from bin/$exe"
done
stamp "done: $out/manifest.json"
cat "$out/SHA256SUMS"
