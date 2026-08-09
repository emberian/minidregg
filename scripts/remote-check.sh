#!/usr/bin/env bash
# Check one explicit committed minidregg snapshot on hbox or persvati.
#
# Source identity is the transferred git archive plus a SHA-256 manifest of
# every regular source file.  Each invocation receives a unique writable source
# tree and a run-local read-only snapshot of the exact dependency seed: project
# builds never share a checkout, writable package worktree, or build output.
set -euo pipefail

usage() {
  local status=${1:-2}
  cat >&2 <<'EOF'
usage: scripts/remote-check.sh [--dry-run] [--allow-generated PATH=SHA256]... HOST COMMIT -- COMMAND [ARG ...]

Examples:
  scripts/remote-check.sh hbox HEAD -- lake build Compiler.NativeKernelPlan
  scripts/remote-check.sh persvati dcea7d1 -- lake env lean Compiler/AuthenticatedColumnLogupBridge.lean
  scripts/remote-check.sh --allow-generated generated/table.json=0123... hbox HEAD -- lake build EmitTable

COMMIT is required and is resolved locally to one commit before any transfer.
The command is executed as an exact argument vector, not through a shell.
Evidence defaults to /tmp/minidregg-evidence and must remain outside the repo.
The private source is writable, but its complete post-run manifest must equal
the committed pre-run manifest.  --allow-generated admits one exact relative
path only at its declared full SHA-256; it never copies output into the repo.

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
generated_output_specs=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage 0
      ;;
    --dry-run)
      dry_run=true
      shift
      ;;
    --allow-generated)
      [[ $# -ge 2 ]] || die "--allow-generated requires PATH=SHA256"
      generated_output_specs+=("$2")
      shift 2
      ;;
    --allow-generated=*)
      generated_output_specs+=("${1#--allow-generated=}")
      shift
      ;;
    --)
      die "options must precede HOST COMMIT"
      ;;
    -*)
      die "unknown option '$1'"
      ;;
    *)
      break
      ;;
  esac
done

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
generated_output_allowlist=$local_tmp/generated-output-allowlist.tsv
mkdir "$snapshot"
git archive --format=tar --output="$archive" "$commit"
tar -xf "$archive" -C "$snapshot"

(cd "$snapshot" &&
  LC_ALL=C find . -path './.lake' -prune -o -type f -print0 |
    LC_ALL=C sort -z |
    xargs -0 shasum -a 256) > "$source_manifest"

: > "$generated_output_allowlist"
for generated_spec in "${generated_output_specs[@]}"; do
  generated_path=${generated_spec%=*}
  generated_sha=${generated_spec##*=}
  [[ "$generated_path" != "$generated_spec" && -n "$generated_path" ]] ||
    die "generated output must have form PATH=SHA256"
  [[ "$generated_path" =~ ^[A-Za-z0-9._/-]+$ ]] ||
    die "unsafe generated-output path '$generated_path'"
  [[ "$generated_path" != /* && "$generated_path" != .lake && "$generated_path" != .lake/* ]] ||
    die "generated-output path must be relative and outside .lake"
  case "/$generated_path/" in
    *//*|*/./*|*/../*) die "generated-output path is not normalized: '$generated_path'" ;;
  esac
  [[ "$generated_sha" =~ ^[0-9a-f]{64}$ ]] ||
    die "generated output '$generated_path' needs a full lowercase SHA-256"
  printf '%s\t%s\n' "$generated_path" "$generated_sha" >> "$generated_output_allowlist"
done
LC_ALL=C sort -o "$generated_output_allowlist" "$generated_output_allowlist"
if [[ -n "$(cut -f1 "$generated_output_allowlist" | uniq -d | head -1)" ]]; then
  die "generated-output paths must be unique"
fi
generated_output_allowlist_sha=$(sha256_file "$generated_output_allowlist")
generated_output_count=$(wc -l < "$generated_output_allowlist" | tr -d ' ')

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
  printf 'generated_output_count=%s\ngenerated_output_allowlist_sha256=%s\n' \
    "$generated_output_count" "$generated_output_allowlist_sha"
  if [[ "$generated_output_count" -gt 0 ]]; then
    sed 's/^/allow_generated=/' "$generated_output_allowlist"
  fi
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
post_source_path=$evidence_dir/$run_id.source-after.sha256
allowlist_path=$evidence_dir/$run_id.generated-outputs.tsv
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
scp "${ssh_options[@]}" -q "$generated_output_allowlist" \
  "$host:$remote_run/generated-output-allowlist.tsv.partial"

ssh "${ssh_options[@]}" "$host" bash -s -- \
  "$remote_run" "$archive_sha" "$source_manifest_sha" "$toolchain_sha" \
  "$lake_manifest_sha" "$rust_toolchain_sha" "$generated_output_allowlist_sha" <<'REMOTE'
set -euo pipefail
run=$1
archive_sha=$2
source_manifest_sha=$3
toolchain_sha=$4
lake_manifest_sha=$5
rust_toolchain_sha=$6
generated_output_allowlist_sha=$7
[[ "$(sha256sum "$run/source.tar.partial" | awk '{print $1}')" == "$archive_sha" ]]
[[ "$(sha256sum "$run/source.files.sha256.partial" | awk '{print $1}')" == "$source_manifest_sha" ]]
[[ "$(sha256sum "$run/generated-output-allowlist.tsv.partial" | awk '{print $1}')" == "$generated_output_allowlist_sha" ]]
mv "$run/source.tar.partial" "$run/source.tar"
mv "$run/source.files.sha256.partial" "$run/source.files.sha256"
mv "$run/generated-output-allowlist.tsv.partial" "$run/generated-output-allowlist.tsv"
mkdir "$run/source"
tar -xf "$run/source.tar" -C "$run/source"
(cd "$run/source" &&
  LC_ALL=C find . -path './.lake' -prune -o -type f -print0 |
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
# The archived source itself is a unique private copy.  Make it writable so
# deterministic Lean generators may rewrite their committed targets.  The
# complete post-run manifest check below, not filesystem permissions, enforces
# source integrity.  Package-cache files retain their separate policy above.
find "$source" -path "$source/.lake" -prune -o \
  \( -type d -o -type f \) -exec chmod u+w {} +
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

# Record the entire post-run source tree, including newly generated files.
# Root .lake is the run-private build directory and is deliberately outside the
# source-mutation claim; Cargo output is separately directed to $run/build.
post_source_manifest=$run/source.after.sha256
(
  cd "$source"
  LC_ALL=C find . -path './.lake' -prune -o -type f -print0 |
    LC_ALL=C sort -z |
    xargs -0 -r sha256sum
) > "$post_source_manifest"

filter_allowed_paths() {
  local input=$1
  local output=$2
  local line path allowed_path allowed_sha skip
  : > "$output"
  while IFS= read -r line || [[ -n "$line" ]]; do
    path=${line#*  }
    [[ "$path" != "$line" ]] || return 1
    skip=false
    while IFS=$'\t' read -r allowed_path allowed_sha; do
      if [[ "$path" == "./$allowed_path" ]]; then
        skip=true
        break
      fi
    done < "$run/generated-output-allowlist.tsv"
    $skip || printf '%s\n' "$line" >> "$output"
  done < "$input"
}

validate_allowed_outputs() {
  local allowed_path expected_sha actual_sha status=0
  while IFS=$'\t' read -r allowed_path expected_sha; do
    if [[ ! -f "$source/$allowed_path" || -L "$source/$allowed_path" ]]; then
      printf 'allowed output missing or non-regular: %s\n' "$allowed_path"
      status=1
      continue
    fi
    actual_sha=$(sha256sum "$source/$allowed_path" | awk '{print $1}')
    printf 'allowed output %s expected=%s actual=%s\n' \
      "$allowed_path" "$expected_sha" "$actual_sha"
    [[ "$actual_sha" == "$expected_sha" ]] || status=1
  done < "$run/generated-output-allowlist.tsv"
  return "$status"
}

set +e
source_integrity_exit=0
{
  printf 'before_manifest_sha256=%s\n' \
    "$(sha256sum "$run/source.files.sha256" | awk '{print $1}')"
  printf 'after_manifest_sha256=%s\n' \
    "$(sha256sum "$post_source_manifest" | awk '{print $1}')"
  printf 'generated_output_allowlist_sha256=%s\n' \
    "$(sha256sum "$run/generated-output-allowlist.tsv" | awk '{print $1}')"
  printf 'generated_output_count=%s\n' \
    "$(wc -l < "$run/generated-output-allowlist.tsv" | tr -d ' ')"

  validate_allowed_outputs
  allowed_status=$?
  filter_allowed_paths "$run/source.files.sha256" "$run/source.before.filtered.sha256"
  before_filter_status=$?
  filter_allowed_paths "$post_source_manifest" "$run/source.after.filtered.sha256"
  after_filter_status=$?
  cmp -s "$run/source.before.filtered.sha256" "$run/source.after.filtered.sha256"
  manifest_status=$?

  if [[ "$manifest_status" -eq 0 ]]; then
    echo 'non-allowlisted source manifest: exact match'
  else
    echo 'non-allowlisted source manifest: MISMATCH'
    diff -u "$run/source.before.filtered.sha256" "$run/source.after.filtered.sha256"
  fi
  printf 'allowed_output_status=%s\nbefore_filter_status=%s\nafter_filter_status=%s\nmanifest_status=%s\n' \
    "$allowed_status" "$before_filter_status" "$after_filter_status" "$manifest_status"
  if [[ "$allowed_status" -ne 0 || "$before_filter_status" -ne 0 ||
        "$after_filter_status" -ne 0 || "$manifest_status" -ne 0 ]]; then
    source_integrity_exit=1
  fi
} > "$run/source-integrity.log" 2>&1
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
  --arg postSourceSha256 "$(sha256sum "$run/source.after.sha256" | awk '{print $1}')" \
  --arg generatedAllowlistSha256 "$(sha256sum "$run/generated-output-allowlist.tsv" | awk '{print $1}')" \
  '{commandExit:$commandExit,sourceIntegrityExit:$sourceIntegrityExit,
    resolvedExecutable:$resolvedExecutable,dependencyCopyMode:$dependencyCopyMode,
    dependencySha256:$dependencySha256,
    oleanSha256:$oleanSha256,integritySha256:$integritySha256,
    postSourceSha256:$postSourceSha256,generatedAllowlistSha256:$generatedAllowlistSha256}'
REMOTE
)
jq -e . >/dev/null <<< "$post_json" || die "worker artifact collection returned invalid JSON"

scp "${ssh_options[@]}" -q "$host:$remote_run/dependency-revisions.tsv" "$dependency_path"
scp "${ssh_options[@]}" -q "$host:$remote_run/project-oleans.sha256" "$olean_path"
scp "${ssh_options[@]}" -q "$host:$remote_run/source-integrity.log" "$integrity_path"
scp "${ssh_options[@]}" -q "$host:$remote_run/source.after.sha256" "$post_source_path"
cp "$source_manifest" "$source_path"
cp "$generated_output_allowlist" "$allowlist_path"

[[ "$(sha256_file "$dependency_path")" == "$(jq -r .dependencySha256 <<< "$post_json")" ]] ||
  die "dependency manifest transfer hash mismatch"
[[ "$(sha256_file "$olean_path")" == "$(jq -r .oleanSha256 <<< "$post_json")" ]] ||
  die "olean manifest transfer hash mismatch"
[[ "$(sha256_file "$integrity_path")" == "$(jq -r .integritySha256 <<< "$post_json")" ]] ||
  die "source-integrity log transfer hash mismatch"
[[ "$(sha256_file "$post_source_path")" == "$(jq -r .postSourceSha256 <<< "$post_json")" ]] ||
  die "post-source manifest transfer hash mismatch"
[[ "$(sha256_file "$allowlist_path")" == "$(jq -r .generatedAllowlistSha256 <<< "$post_json")" ]] ||
  die "generated-output allowlist transfer hash mismatch"
[[ "$(sha256_file "$allowlist_path")" == "$generated_output_allowlist_sha" ]] ||
  die "generated-output allowlist differs from the requested policy"
[[ "$(sha256_file "$dependency_path")" == "$dependency_manifest_sha" ]] ||
  die "worker dependency revisions differ from the snapshot manifest"

finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
log_sha=$(sha256_file "$log_path")
olean_sha=$(sha256_file "$olean_path")
integrity_sha=$(sha256_file "$integrity_path")
post_source_sha=$(sha256_file "$post_source_path")
command_json='[]'
for argument in "${command_args[@]}"; do
  command_json=$(jq --arg argument "$argument" '. + [$argument]' <<< "$command_json")
done
generated_outputs_json=$(jq -R 'select(length > 0) | split("\t") |
  {path:.[0],sha256:.[1]}' "$allowlist_path" | jq -s .)

jq -n \
  --arg schema minidregg/remote-evidence/v3 \
  --arg runId "$run_id" --arg requestedRevision "$requested_revision" \
  --arg commit "$commit" --arg tree "$tree" --arg archiveSha256 "$archive_sha" \
  --arg toolchainSha256 "$toolchain_sha" --arg lakeManifestSha256 "$lake_manifest_sha" \
  --arg rustToolchainSha256 "$rust_toolchain_sha" \
  --arg sourceFile "$(basename "$source_path")" --arg sourceManifestSha256 "$source_manifest_sha" \
  --arg postSourceFile "$(basename "$post_source_path")" --arg postSourceSha256 "$post_source_sha" \
  --arg allowlistFile "$(basename "$allowlist_path")" \
  --arg allowlistSha256 "$generated_output_allowlist_sha" \
  --argjson generatedOutputs "$generated_outputs_json" \
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
      beforeManifest:{file:$sourceFile,sha256:$sourceManifestSha256},
      afterManifest:{file:$postSourceFile,sha256:$postSourceSha256},
      mutationPolicy:{default:"exact-manifest-equality",autoSync:false,
        allowlist:{file:$allowlistFile,sha256:$allowlistSha256,outputs:$generatedOutputs}}},
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
    claimCeiling:"Exact explicit-commit source/dependency/build evidence with post-run source equality modulo explicitly hashed generated outputs only; not a benchmark, native-semantics claim, or cryptographic-security claim."}' \
  > "$json_path"

echo "evidence: $json_path"
exit "$runner_exit"
