#!/usr/bin/env bash
# Check one explicit committed minidregg snapshot on hbox or persvati.
#
# Source identity is the transferred git archive plus a SHA-256 manifest of
# every regular source file.  Each invocation receives a unique source/build
# tree and a run-local read-only snapshot of the exact dependency seed: project
# builds never share a checkout, writable package worktree, or build output.
set -euo pipefail

usage() {
  local status=${1:-2}
  cat >&2 <<'EOF'
usage: scripts/remote-check.sh [--dry-run] HOST COMMIT -- COMMAND [ARG ...]

Examples:
  scripts/remote-check.sh hbox HEAD -- lake build Compiler.NativeKernelPlan
  scripts/remote-check.sh persvati dcea7d1 -- lake env lean Compiler/AuthenticatedColumnLogupBridge.lean

COMMIT is required and is resolved locally to one commit before any transfer.
The command is executed as an exact argument vector, not through a shell.
Evidence defaults to /tmp/minidregg-evidence and must remain outside the repo.

Optional environment limits:
  MINIDREGG_EVIDENCE_DIR       local evidence directory (outside the repo)
  MINIDREGG_REMOTE_CPUSET      Linux CPU set (default: 0-7)
  MINIDREGG_REMOTE_MEMORY_KIB  virtual-memory limit in KiB (default: 67108864)
  MINIDREGG_REMOTE_TIMEOUT     timeout(1) duration (default: 45m)
EOF
  exit "$status"
}

die() {
  echo "remote-check: $*" >&2
  exit 2
}

sha256_file() {
  shasum -a 256 "$1" | awk '{print $1}'
}

dry_run=false
case "${1:-}" in
  -h|--help)
    usage 0
    ;;
  --dry-run)
    dry_run=true
    shift
    ;;
esac

if [[ $# -lt 4 || "$3" != "--" ]]; then
  usage 2
fi

host=$1
requested_revision=$2
shift 3
command_args=("$@")
[[ ${#command_args[@]} -gt 0 ]] || usage 2

case "$host" in
  hbox)
    remote_root=/tank/dregg-build/minidregg-checks
    remote_elan=/home/hbox/.elan/bin/elan
    remote_lake=/home/hbox/.elan/bin/lake
    remote_cargo=/home/hbox/.cargo/bin/cargo
    ;;
  persvati)
    remote_root=/home/ember/minidregg-checks
    remote_elan=/home/ember/.elan/bin/elan
    remote_lake=/home/ember/.elan/bin/lake
    remote_cargo=/home/ember/.cargo/bin/cargo
    ;;
  *)
    die "unsupported worker '$host' (expected hbox or persvati)"
    ;;
esac

remote_cpuset=${MINIDREGG_REMOTE_CPUSET:-0-7}
remote_memory_kib=${MINIDREGG_REMOTE_MEMORY_KIB:-67108864}
remote_timeout=${MINIDREGG_REMOTE_TIMEOUT:-45m}
[[ "$remote_cpuset" =~ ^[0-9]+([,-][0-9]+)*$ ]] ||
  die "invalid MINIDREGG_REMOTE_CPUSET '$remote_cpuset'"
[[ "$remote_memory_kib" =~ ^[1-9][0-9]*$ ]] ||
  die "invalid MINIDREGG_REMOTE_MEMORY_KIB '$remote_memory_kib'"
[[ "$remote_timeout" =~ ^[1-9][0-9]*[smhd]$ ]] ||
  die "invalid MINIDREGG_REMOTE_TIMEOUT '$remote_timeout'"

for local_tool in git jq shasum base64 ssh scp tar find sort xargs; do
  command -v "$local_tool" >/dev/null 2>&1 || die "required local tool '$local_tool' is missing"
done

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"
commit=$(git rev-parse --verify "${requested_revision}^{commit}" 2>/dev/null) ||
  die "'$requested_revision' does not resolve to a local commit"
tree=$(git rev-parse "${commit}^{tree}")
short_commit=${commit:0:12}

# git archives do not contain submodule contents.  Refuse a partial snapshot
# rather than silently recording evidence for something other than the tree.
if git ls-tree -r "$commit" | awk '$1 == "160000" { found = 1 } END { exit !found }'; then
  die "commit $commit contains submodules; exact archive checks do not yet support them"
fi
# The post-run integrity checker currently hashes regular files.  Reject source
# symlinks so its claim remains exact instead of silently omitting link targets.
if git ls-tree -r "$commit" | awk '$1 == "120000" { found = 1 } END { exit !found }'; then
  die "commit $commit contains source symlinks; exact archive checks do not yet support them"
fi

local_tmp=$(mktemp -d /tmp/minidregg-remote-check.XXXXXX)
trap 'rm -rf -- "$local_tmp"' EXIT
archive=$local_tmp/source.tar
snapshot=$local_tmp/snapshot
source_manifest=$local_tmp/source.files.sha256
dependency_manifest=$local_tmp/dependency-revisions.tsv
mkdir "$snapshot"
git archive --format=tar --output="$archive" "$commit"
tar -xf "$archive" -C "$snapshot"

(cd "$snapshot" &&
  LC_ALL=C find . -type f -print0 |
    LC_ALL=C sort -z |
    xargs -0 shasum -a 256) > "$source_manifest"

[[ -f "$snapshot/lean-toolchain" ]] || die "snapshot has no lean-toolchain"
[[ -f "$snapshot/lake-manifest.json" ]] || die "snapshot has no lake-manifest.json"
toolchain_sha=$(sha256_file "$snapshot/lean-toolchain")
lake_manifest_sha=$(sha256_file "$snapshot/lake-manifest.json")
archive_sha=$(sha256_file "$archive")
source_manifest_sha=$(sha256_file "$source_manifest")

package_count=$(jq '.packages | length' "$snapshot/lake-manifest.json")
git_package_count=$(jq '[.packages[] | select(.type == "git")] | length' \
  "$snapshot/lake-manifest.json")
[[ "$package_count" == "$git_package_count" ]] ||
  die "only git-pinned Lake dependencies are supported"
jq -r '.packages[] | [.name, .rev] | @tsv' "$snapshot/lake-manifest.json" |
  LC_ALL=C sort > "$dependency_manifest"
[[ -s "$dependency_manifest" ]] || die "Lake manifest contains no pinned dependencies"
while IFS=$'\t' read -r package_name package_rev; do
  [[ "$package_name" =~ ^[A-Za-z0-9_.-]+$ ]] ||
    die "unsafe Lake package name '$package_name'"
  [[ "$package_rev" =~ ^[0-9a-f]{40}$ ]] ||
    die "Lake package '$package_name' is not pinned to a full Git revision"
done < "$dependency_manifest"
dependency_manifest_sha=$(sha256_file "$dependency_manifest")

rust_toolchain_sha=none
if [[ -f "$snapshot/rust-toolchain.toml" ]]; then
  rust_toolchain_sha=$(sha256_file "$snapshot/rust-toolchain.toml")
fi
seed_key="v2-${toolchain_sha:0:24}-${lake_manifest_sha:0:24}"

printf_command() {
  printf '%q ' "${command_args[@]}"
  printf '\n'
}

if $dry_run; then
  printf 'host=%s\nrequested_revision=%s\ncommit=%s\ntree=%s\n' \
    "$host" "$requested_revision" "$commit" "$tree"
  printf 'archive_sha256=%s\nsource_manifest_sha256=%s\n' \
    "$archive_sha" "$source_manifest_sha"
  printf 'lean_toolchain_sha256=%s\nlake_manifest_sha256=%s\n' \
    "$toolchain_sha" "$lake_manifest_sha"
  printf 'dependency_manifest_sha256=%s\nseed_key=%s\n' \
    "$dependency_manifest_sha" "$seed_key"
  printf 'limits=cpuset:%s,memory_kib:%s,timeout:%s\ncommand=' \
    "$remote_cpuset" "$remote_memory_kib" "$remote_timeout"
  printf_command
  exit 0
fi

evidence_dir=${MINIDREGG_EVIDENCE_DIR:-/tmp/minidregg-evidence}
mkdir -p "$evidence_dir"
evidence_dir=$(cd "$evidence_dir" && pwd -P)
case "$evidence_dir/" in
  "$repo_root/"*) die "evidence directory must be outside the repository" ;;
esac

ssh_options=(
  -o BatchMode=yes
  -o ConnectTimeout=10
  -o ServerAliveInterval=15
  -o ServerAliveCountMax=3
)

remote_run=$(ssh "${ssh_options[@]}" "$host" bash -s -- \
  "$remote_root" "$short_commit" <<'REMOTE'
set -euo pipefail
root=$1
short_commit=$2
umask 077
mkdir -p "$root"
[[ -d "$root" && ! -L "$root" ]]
mkdir -p "$root/runs" "$root/seeds" "$root/locks"
[[ ! -L "$root/runs" && ! -L "$root/seeds" && ! -L "$root/locks" ]]
mktemp -d "$root/runs/run-$short_commit-XXXXXXXX"
REMOTE
)
case "$remote_run" in
  "$remote_root"/runs/run-"$short_commit"-*) ;;
  *) die "worker returned unsafe run directory '$remote_run'" ;;
esac
[[ "$remote_run" =~ ^[A-Za-z0-9._/-]+$ ]] || die "worker returned unsafe run path"
remote_source=$remote_run/source

stamp=$(date -u +%Y%m%dT%H%M%S)-$$
command_name=$(printf '%s' "$(basename "${command_args[0]}")" | tr -cs 'A-Za-z0-9_.-' '_')
run_id="E-$stamp-$host-$short_commit-$command_name"
log_path=$evidence_dir/$run_id.log
json_path=$evidence_dir/$run_id.json
source_path=$evidence_dir/$run_id.source.sha256
dependency_path=$evidence_dir/$run_id.dependencies.tsv
olean_path=$evidence_dir/$run_id.oleans.sha256
integrity_path=$evidence_dir/$run_id.source-integrity.log
started=$(date -u +%Y-%m-%dT%H:%M:%SZ)

printf 'run=%s\ncommit=%s\ntree=%s\nhost_alias=%s\nremote_run=%s\ncommand=' \
  "$run_id" "$commit" "$tree" "$host" "$remote_run" | tee "$log_path"
printf_command | tee -a "$log_path"

# Transfer only the locally created archive and its independently generated
# file manifest.  Partial names are verified before being made visible.
scp "${ssh_options[@]}" -q "$archive" "$host:$remote_run/source.tar.partial"
scp "${ssh_options[@]}" -q "$source_manifest" \
  "$host:$remote_run/source.files.sha256.partial"

ssh "${ssh_options[@]}" "$host" bash -s -- \
  "$remote_run" "$archive_sha" "$source_manifest_sha" "$toolchain_sha" \
  "$lake_manifest_sha" "$rust_toolchain_sha" <<'REMOTE'
set -euo pipefail
run=$1
archive_sha=$2
source_manifest_sha=$3
toolchain_sha=$4
lake_manifest_sha=$5
rust_toolchain_sha=$6
[[ "$(sha256sum "$run/source.tar.partial" | awk '{print $1}')" == "$archive_sha" ]]
[[ "$(sha256sum "$run/source.files.sha256.partial" | awk '{print $1}')" == "$source_manifest_sha" ]]
mv "$run/source.tar.partial" "$run/source.tar"
mv "$run/source.files.sha256.partial" "$run/source.files.sha256"
mkdir "$run/source"
tar -xf "$run/source.tar" -C "$run/source"
(cd "$run/source" &&
  LC_ALL=C find . -type f -print0 |
    LC_ALL=C sort -z |
    xargs -0 -r sha256sum) > "$run/source.extracted.sha256"
cmp -s "$run/source.files.sha256" "$run/source.extracted.sha256"
[[ "$(sha256sum "$run/source/lean-toolchain" | awk '{print $1}')" == "$toolchain_sha" ]]
[[ "$(sha256sum "$run/source/lake-manifest.json" | awk '{print $1}')" == "$lake_manifest_sha" ]]
if [[ "$rust_toolchain_sha" != none ]]; then
  [[ "$(sha256sum "$run/source/rust-toolchain.toml" | awk '{print $1}')" == "$rust_toolchain_sha" ]]
fi
REMOTE

# Build an immutable dependency seed once per exact Lean-toolchain/Lake-manifest
# pair.  Seed creation has its own extracted bootstrap tree.  Runs receive
# run-local directory trees whose prebuilt files are read-only hard links to the
# immutable seed; no source or package directory is symlinked.  New/replaced
# build files live only in the run-local writable directories.
scp "${ssh_options[@]}" -q "$dependency_manifest" \
  "$host:$remote_run/dependency-revisions.expected.tsv"
ssh "${ssh_options[@]}" "$host" bash -s -- \
  "$remote_root" "$remote_run" "$seed_key" "$remote_lake" \
  "$toolchain_sha" "$lake_manifest_sha" "$dependency_manifest_sha" <<'REMOTE'
set -euo pipefail
root=$1
run=$2
seed_key=$3
lake=$4
toolchain_sha=$5
lake_manifest_sha=$6
dependency_manifest_sha=$7
source=$run/source
seed=$root/seeds/$seed_key
lock=$root/locks/$seed_key.lock

[[ "$lake" == /* && -x "$lake" ]]
[[ "$(sha256sum "$run/dependency-revisions.expected.tsv" | awk '{print $1}')" == "$dependency_manifest_sha" ]]

verify_packages() {
  local packages=$1
  local output=$2
  local name rev actual
  : > "$output"
  while IFS=$'\t' read -r name rev; do
    [[ "$name" =~ ^[A-Za-z0-9_.-]+$ ]]
    [[ "$rev" =~ ^[0-9a-f]{40}$ ]]
    [[ -d "$packages/$name/.git" && ! -L "$packages/$name" ]]
    actual=$(git -C "$packages/$name" rev-parse HEAD)
    [[ "$actual" == "$rev" ]]
    git -C "$packages/$name" diff --quiet
    git -C "$packages/$name" diff --cached --quiet
    printf '%s\t%s\n' "$name" "$actual" >> "$output"
  done < "$run/dependency-revisions.expected.tsv"
  LC_ALL=C sort -o "$output" "$output"
  cmp -s "$run/dependency-revisions.expected.tsv" "$output"
}

exec 9>"$lock"
flock 9
if [[ ! -f "$seed/.complete" ]]; then
  incoming=$(mktemp -d "$root/seeds/.incoming-$seed_key-XXXXXXXX")
  bootstrap=$(mktemp -d "$run/bootstrap-XXXXXXXX")
  mkdir "$bootstrap/source"
  tar -xf "$run/source.tar" -C "$bootstrap/source"
  (
    cd "$bootstrap/source"
    "$lake" update
    [[ "$(sha256sum lake-manifest.json | awk '{print $1}')" == "$lake_manifest_sha" ]]
    "$lake" exe cache get
  )
  verify_packages "$bootstrap/source/.lake/packages" "$incoming/dependency-revisions.tsv"
  mv "$bootstrap/source/.lake/packages" "$incoming/packages"
  printf 'schema=v2\ntoolchain_sha256=%s\nlake_manifest_sha256=%s\ndependency_manifest_sha256=%s\n' \
    "$toolchain_sha" "$lake_manifest_sha" "$dependency_manifest_sha" > "$incoming/identity"
  printf '%s\n' "$seed_key" > "$incoming/.complete"
  chmod -R a-w "$incoming"
  mv "$incoming" "$seed"
fi

[[ -d "$seed" && ! -L "$seed" && -d "$seed/packages" && ! -L "$seed/packages" ]]
[[ "$(sha256sum "$seed/dependency-revisions.tsv" | awk '{print $1}')" == "$dependency_manifest_sha" ]]
expected_identity=$(printf 'schema=v2\ntoolchain_sha256=%s\nlake_manifest_sha256=%s\ndependency_manifest_sha256=%s' \
  "$toolchain_sha" "$lake_manifest_sha" "$dependency_manifest_sha")
[[ "$(cat "$seed/identity")" == "$expected_identity" ]]
# POSIX symlink modes commonly display as 0777 even though opening the link
# writes its target; only regular seed inodes/directories must be non-writable.
[[ -z "$(find "$seed" ! -type l -perm /222 -print -quit)" ]]
verify_packages "$seed/packages" "$run/dependency-revisions.tsv"

mkdir -p "$source/.lake/packages" "$run/build/cargo"
[[ ! -L "$source/.lake" && ! -L "$source/.lake/packages" ]]
cp -al "$seed/packages/." "$source/.lake/packages/"
# Directories are distinct in a hard-link copy, so making them writable cannot
# affect the seed.  Seed-backed files stay read-only; build tools may add or
# atomically replace files without gaining a writable path to seed contents.
find "$source/.lake/packages" -type d -exec chmod u+w {} +
# Lake replays update tiny hash/trace metadata in place even when the cached
# oleans are current.  Break only those hard links via tar's unlink-first mode;
# the large source/olean/code files remain immutable seed links.
mutable_metadata=$run/mutable-package-metadata.tar
(
  cd "$source/.lake/packages"
  find . -type f \( -name '*.hash' -o -name '*.trace' \) -print0 |
    tar --null -T - -cf "$mutable_metadata"
  tar --unlink-first -xf "$mutable_metadata"
  find . -type f \( -name '*.hash' -o -name '*.trace' \) -exec chmod u+w {} +
)
printf '%s\n' hardlink-readonly-with-private-metadata > "$run/dependency-copy-mode"
verify_packages "$source/.lake/packages" "$run/dependency-revisions.private.tsv"
cmp -s "$run/dependency-revisions.tsv" "$run/dependency-revisions.private.tsv"
# Snapshot files remain read-only; all expected build state lives under the
# run-private .lake or build directories.
find "$source" -path "$source/.lake" -prune -o -type f -exec chmod a-w {} +
REMOTE

worker_json=$(ssh "${ssh_options[@]}" "$host" bash -s -- \
  "$remote_source" "$remote_run" "$remote_elan" "$remote_lake" "$remote_cargo" <<'REMOTE'
set -euo pipefail
source=$1
run=$2
elan=$3
lake=$4
cargo=$5
for tool in "$elan" "$lake" "$cargo"; do [[ "$tool" == /* && -x "$tool" ]]; done
cd "$source"
hostname_value=$(hostname)
uname_value=$(uname -a)
cpu_value=$(lscpu | sed -n 's/^Model name:[[:space:]]*//p' | head -1)
threads_value=$(nproc)
memory_value=$(awk '/MemTotal/{print $2}' /proc/meminfo)
gpu_value=$(lspci 2>/dev/null | grep -Ei 'vga|3d|display' || true)
elan_version=$($elan --version)
lake_version=$($lake --version)
lean_version=$($lake env lean --version)
lean_path=$($lake env which lean)
cargo_version=$($cargo --version)
rustc_path=$(dirname "$cargo")/rustc
[[ "$rustc_path" == /* && -x "$rustc_path" ]]
rustc_version=$($rustc_path --version)
jq -n \
  --arg hostname "$hostname_value" --arg uname "$uname_value" --arg cpu "$cpu_value" \
  --argjson threads "$threads_value" --argjson memoryKiB "$memory_value" --arg gpu "$gpu_value" \
  --arg elanPath "$elan" --arg elanVersion "$elan_version" \
  --arg lakePath "$lake" --arg lakeVersion "$lake_version" \
  --arg leanPath "$lean_path" --arg leanVersion "$lean_version" \
  --arg cargoPath "$cargo" --arg cargoVersion "$cargo_version" \
  --arg rustcPath "$rustc_path" --arg rustcVersion "$rustc_version" \
  --arg remoteRun "$run" \
  '{hostname:$hostname,uname:$uname,cpu:$cpu,threads:$threads,memoryKiB:$memoryKiB,gpu:$gpu,
    tools:{elan:{path:$elanPath,version:$elanVersion},lake:{path:$lakePath,version:$lakeVersion},
      lean:{path:$leanPath,version:$leanVersion},cargo:{path:$cargoPath,version:$cargoVersion},
      rustc:{path:$rustcPath,version:$rustcVersion}},remoteRun:$remoteRun}'
REMOTE
)
jq -e . >/dev/null <<< "$worker_json" || die "worker fact collection returned invalid JSON"

encoded_args=()
for argument in "${command_args[@]}"; do
  encoded_args+=("x$(printf '%s' "$argument" | base64 | tr -d '\n')")
done

set +e
ssh "${ssh_options[@]}" "$host" bash -s -- \
  "$remote_source" "$remote_run" "$remote_elan" "$remote_lake" "$remote_cargo" \
  "$remote_cpuset" "$remote_memory_kib" "$remote_timeout" "${encoded_args[@]}" \
  <<'REMOTE' 2>&1 | tee -a "$log_path"
set -euo pipefail
source=$1
run=$2
elan=$3
lake=$4
cargo=$5
cpuset=$6
memory_kib=$7
timeout_duration=$8
shift 8
argv=()
for token in "$@"; do
  [[ "$token" == x* ]]
  # The sentinel survives command substitution's trailing-newline stripping,
  # preserving even empty arguments and arguments ending in newlines.
  decoded=$(printf '%s' "${token#x}" | base64 -d; printf x)
  argv+=("${decoded%x}")
done
[[ ${#argv[@]} -gt 0 ]]
cd "$source"
export PATH="$(dirname "$elan"):$(dirname "$cargo"):/usr/local/bin:/usr/bin:/bin"
export CARGO_TARGET_DIR="$run/build/cargo"
case "${argv[0]}" in
  elan) argv[0]=$elan ;;
  lake) argv[0]=$lake ;;
  cargo) argv[0]=$cargo ;;
esac
if [[ "${argv[0]}" != */* ]]; then
  argv[0]=$(command -v "${argv[0]}")
elif [[ "${argv[0]}" != /* ]]; then
  argv[0]=$(readlink -f "$source/${argv[0]}")
fi
[[ "${argv[0]}" == /* && -x "${argv[0]}" ]]
printf '%s\n' "${argv[0]}" > "$run/resolved-executable"
printf 'resolved_executable=%s\n' "${argv[0]}"

ulimit -v "$memory_kib"

set +e
/usr/bin/timeout --kill-after=30s "$timeout_duration" \
  /usr/bin/taskset -c "$cpuset" "${argv[@]}"
command_exit=$?
set -e
printf '%s\n' "$command_exit" > "$run/command.exit"

set +e
sha256sum -c "$run/source.files.sha256" > "$run/source-integrity.log" 2>&1
source_integrity_exit=$?
set -e
printf '%s\n' "$source_integrity_exit" > "$run/source-integrity.exit"
printf 'command_exit=%s\nsource_integrity_exit=%s\n' "$command_exit" "$source_integrity_exit"
if [[ "$source_integrity_exit" -ne 0 ]]; then
  exit 86
fi
exit "$command_exit"
REMOTE
runner_exit=${PIPESTATUS[0]}
set -e

post_json=$(ssh "${ssh_options[@]}" "$host" bash -s -- \
  "$remote_source" "$remote_run" <<'REMOTE'
set -euo pipefail
source=$1
run=$2
olean_manifest=$run/project-oleans.sha256
: > "$olean_manifest"
if [[ -d "$source/.lake/build/lib/lean" ]]; then
  (
    cd "$source"
    LC_ALL=C find .lake/build/lib/lean -type f \( -name '*.olean' -o -name '*.ilean' \) -print0 |
      LC_ALL=C sort -z |
      xargs -0 -r sha256sum
  ) > "$olean_manifest"
fi
command_exit=$(cat "$run/command.exit")
source_integrity_exit=$(cat "$run/source-integrity.exit")
resolved_executable=$(cat "$run/resolved-executable")
dependency_copy_mode=$(cat "$run/dependency-copy-mode")
jq -n \
  --argjson commandExit "$command_exit" --argjson sourceIntegrityExit "$source_integrity_exit" \
  --arg resolvedExecutable "$resolved_executable" \
  --arg dependencyCopyMode "$dependency_copy_mode" \
  --arg dependencySha256 "$(sha256sum "$run/dependency-revisions.tsv" | awk '{print $1}')" \
  --arg oleanSha256 "$(sha256sum "$olean_manifest" | awk '{print $1}')" \
  --arg integritySha256 "$(sha256sum "$run/source-integrity.log" | awk '{print $1}')" \
  '{commandExit:$commandExit,sourceIntegrityExit:$sourceIntegrityExit,
    resolvedExecutable:$resolvedExecutable,dependencyCopyMode:$dependencyCopyMode,
    dependencySha256:$dependencySha256,
    oleanSha256:$oleanSha256,integritySha256:$integritySha256}'
REMOTE
)
jq -e . >/dev/null <<< "$post_json" || die "worker artifact collection returned invalid JSON"

scp "${ssh_options[@]}" -q "$host:$remote_run/dependency-revisions.tsv" "$dependency_path"
scp "${ssh_options[@]}" -q "$host:$remote_run/project-oleans.sha256" "$olean_path"
scp "${ssh_options[@]}" -q "$host:$remote_run/source-integrity.log" "$integrity_path"
cp "$source_manifest" "$source_path"

[[ "$(sha256_file "$dependency_path")" == "$(jq -r .dependencySha256 <<< "$post_json")" ]] ||
  die "dependency manifest transfer hash mismatch"
[[ "$(sha256_file "$olean_path")" == "$(jq -r .oleanSha256 <<< "$post_json")" ]] ||
  die "olean manifest transfer hash mismatch"
[[ "$(sha256_file "$integrity_path")" == "$(jq -r .integritySha256 <<< "$post_json")" ]] ||
  die "source-integrity log transfer hash mismatch"
[[ "$(sha256_file "$dependency_path")" == "$dependency_manifest_sha" ]] ||
  die "worker dependency revisions differ from the snapshot manifest"

finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
log_sha=$(sha256_file "$log_path")
olean_sha=$(sha256_file "$olean_path")
integrity_sha=$(sha256_file "$integrity_path")
command_json='[]'
for argument in "${command_args[@]}"; do
  command_json=$(jq --arg argument "$argument" '. + [$argument]' <<< "$command_json")
done

jq -n \
  --arg schema minidregg/remote-evidence/v2 \
  --arg runId "$run_id" --arg requestedRevision "$requested_revision" \
  --arg commit "$commit" --arg tree "$tree" --arg archiveSha256 "$archive_sha" \
  --arg toolchainSha256 "$toolchain_sha" --arg lakeManifestSha256 "$lake_manifest_sha" \
  --arg rustToolchainSha256 "$rust_toolchain_sha" \
  --arg sourceFile "$(basename "$source_path")" --arg sourceManifestSha256 "$source_manifest_sha" \
  --arg dependencyFile "$(basename "$dependency_path")" \
  --arg dependencyManifestSha256 "$dependency_manifest_sha" --arg seedKey "$seed_key" \
  --arg dependencyCopyMode "$(jq -r .dependencyCopyMode <<< "$post_json")" \
  --argjson command "$command_json" --arg resolvedExecutable "$(jq -r .resolvedExecutable <<< "$post_json")" \
  --arg hostAlias "$host" --argjson worker "$worker_json" \
  --arg cpuset "$remote_cpuset" --argjson memoryKiB "$remote_memory_kib" \
  --arg timeout "$remote_timeout" --arg startedAt "$started" --arg finishedAt "$finished" \
  --argjson runnerExit "$runner_exit" --argjson commandExit "$(jq -r .commandExit <<< "$post_json")" \
  --argjson sourceIntegrityExit "$(jq -r .sourceIntegrityExit <<< "$post_json")" \
  --arg logFile "$(basename "$log_path")" --arg logSha256 "$log_sha" \
  --arg oleanFile "$(basename "$olean_path")" --arg oleanSha256 "$olean_sha" \
  --arg integrityFile "$(basename "$integrity_path")" --arg integritySha256 "$integrity_sha" \
  '{schema:$schema,runId:$runId,
    source:{requestedRevision:$requestedRevision,commit:$commit,tree:$tree,dirty:false,
      archiveSha256:$archiveSha256,leanToolchainSha256:$toolchainSha256,
      lakeManifestSha256:$lakeManifestSha256,rustToolchainSha256:$rustToolchainSha256,
      fileManifest:{file:$sourceFile,sha256:$sourceManifestSha256}},
    dependencies:{seedKey:$seedKey,runLocalTree:true,copyMode:$dependencyCopyMode,
      revisionManifest:{file:$dependencyFile,sha256:$dependencyManifestSha256}},
    command:$command,resolvedExecutable:$resolvedExecutable,
    worker:($worker + {alias:$hostAlias,limits:{cpuSet:$cpuset,
      virtualMemoryKiB:$memoryKiB,timeout:$timeout,killAfterSeconds:30}}),
    startedAt:$startedAt,finishedAt:$finishedAt,
    result:{runnerExit:$runnerExit,commandExit:$commandExit,
      sourceIntegrityExit:$sourceIntegrityExit},
    rawLog:{file:$logFile,sha256:$logSha256},
    projectOleans:{file:$oleanFile,sha256:$oleanSha256},
    sourceIntegrity:{file:$integrityFile,sha256:$integritySha256},
    claimCeiling:"Exact explicit-commit source/dependency/build evidence only; not a benchmark, native-semantics claim, or cryptographic-security claim."}' \
  > "$json_path"

echo "evidence: $json_path"
exit "$runner_exit"
