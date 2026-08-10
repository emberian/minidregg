#!/usr/bin/env bash
# Check one explicit committed minidregg snapshot without consulting the
# repository's current .lake tree or any developer dependency checkout.
#
# The committed source is extracted into a unique writable run tree.  Lake
# packages come from an immutable, content-identified seed and are copied (or
# APFS-cloned) into that run tree with distinct inodes before Lake can touch
# them.  Source, dependency, tool, and build-output manifests are retained as
# evidence outside the repository.
if (( BASH_VERSINFO[0] < 5 )); then
  for minidregg_bash in /opt/homebrew/bin/bash /usr/local/bin/bash; do
    if [[ -x "$minidregg_bash" ]]; then
      exec "$minidregg_bash" "$0" "$@"
    fi
  done
  echo "local-check: Bash >= 5 is required (running $BASH_VERSION)" >&2
  exit 2
fi
set -euo pipefail

usage() {
  local status=${1:-2}
  cat >&2 <<'EOF'
usage: scripts/local-check.sh [--dry-run] [--allow-generated PATH=SHA256]... COMMIT -- COMMAND [ARG ...]

Examples:
  scripts/local-check.sh HEAD -- lake build Theory Kernel Compiler Assurance
  scripts/local-check.sh dcea7d1 -- lake env lean Theory/CanonicalTransition.lean
  scripts/local-check.sh --allow-generated generated/table.json=0123... HEAD -- lake build EmitTable

COMMIT is required and is resolved to one commit before the run.  The command
is executed as an exact argument vector, never through an implicit shell.
Neither the current worktree's .lake directory nor another package checkout is
read, linked, rewritten, or used as a dependency seed.

Optional environment:
  MINIDREGG_LOCAL_CHECK_ROOT   isolated runs/seeds root outside the repo
                               (default: ${TMPDIR:-/tmp}/minidregg-local-checks)
  MINIDREGG_EVIDENCE_DIR       evidence directory outside the repo
                               (default: CHECK_ROOT/evidence)
  MINIDREGG_LOCAL_TIMEOUT      timeout duration: integer plus s/m/h (default: 45m)
  MINIDREGG_LOCAL_MEMORY_KIB   address-space ceiling in KiB, auto, or none
                               (default: auto; 64 GiB when RLIMIT_AS works)
  MINIDREGG_LOCAL_COPY_MODE    auto, clone, or copy (default: auto)

Exit 86 means the command returned but source-integrity policy rejected its
result.  Exit 87 means the immutable dependency seed changed during the run.
Evidence is still written for either rejection.
EOF
  exit "$status"
}

die() {
  echo "local-check: $*" >&2
  exit 2
}

sha256_file() {
  shasum -a 256 "$1" | awk '{print $1}'
}

canonical_dir() {
  (cd "$1" && pwd -P)
}

path_is_within() {
  local child=$1
  local parent=$2
  case "$child/" in
    "$parent"/*) return 0 ;;
    *) return 1 ;;
  esac
}

source_manifest() {
  local source=$1
  local output=$2
  (
    cd "$source"
    LC_ALL=C find . -path './.lake' -prune -o -type f -print0 |
      LC_ALL=C sort -z |
      xargs -0 shasum -a 256
  ) > "$output"
}

verify_package_revisions() {
  local packages=$1
  local expected=$2
  local output=$3
  local name rev actual
  : > "$output"
  while IFS=$'\t' read -r name rev; do
    [[ "$name" =~ ^[A-Za-z0-9_.-]+$ ]] || return 1
    [[ "$rev" =~ ^[0-9a-f]{40}$ ]] || return 1
    [[ -d "$packages/$name/.git" && ! -L "$packages/$name" ]] || return 1
    actual=$(git -C "$packages/$name" rev-parse HEAD) || return 1
    [[ "$actual" == "$rev" ]] || return 1
    git -C "$packages/$name" diff --quiet || return 1
    git -C "$packages/$name" diff --cached --quiet || return 1
    [[ -z "$(git -C "$packages/$name" status --porcelain=v1 --untracked-files=all)" ]] || return 1
    printf '%s\t%s\n' "$name" "$actual" >> "$output"
  done < "$expected"
  LC_ALL=C sort -o "$output" "$output"
  cmp -s "$expected" "$output"
}

verify_confined_symlinks() {
  local root=$1
  "$python_path" - "$root" <<'PY'
import os
import pathlib
import sys

root = pathlib.Path(sys.argv[1]).resolve(strict=True)
for directory, names, files in os.walk(root, followlinks=False):
    for name in names + files:
        path = pathlib.Path(directory, name)
        if not path.is_symlink():
            continue
        target = path.resolve(strict=False)
        try:
            target.relative_to(root)
        except ValueError:
            raise SystemExit(f"symlink escapes package tree: {path} -> {os.readlink(path)}")
PY
}

verify_no_shared_regular_inodes() {
  local seed=$1
  local private=$2
  "$python_path" - "$seed" "$private" <<'PY'
import os
import pathlib
import sys

seed = pathlib.Path(sys.argv[1])
private = pathlib.Path(sys.argv[2])
seed_inodes = set()
for directory, _, files in os.walk(seed, followlinks=False):
    for name in files:
        path = pathlib.Path(directory, name)
        if path.is_symlink():
            continue
        stat = path.stat()
        seed_inodes.add((stat.st_dev, stat.st_ino))
for directory, _, files in os.walk(private, followlinks=False):
    for name in files:
        path = pathlib.Path(directory, name)
        if path.is_symlink():
            continue
        stat = path.stat()
        if (stat.st_dev, stat.st_ino) in seed_inodes:
            raise SystemExit(f"run package file shares an inode with seed: {path}")
PY
}

copy_packages() {
  local seed_packages=$1
  local private_packages=$2
  local requested_mode=$3
  local clone_probe=$run/clone-probe
  local mode
  mkdir "$clone_probe"
  printf x > "$clone_probe/source"
  mode=$requested_mode
  if [[ "$mode" == auto ]]; then
    if cp -c "$clone_probe/source" "$clone_probe/destination" 2>/dev/null; then
      mode=clone
    else
      mode=copy
    fi
  fi
  case "$mode" in
    clone)
      cp -cR "$seed_packages/." "$private_packages/" ||
        die "copy mode 'clone' is unavailable on this filesystem"
      printf '%s\n' apfs-clone-distinct-inodes
      ;;
    copy)
      cp -R "$seed_packages/." "$private_packages/"
      printf '%s\n' full-copy-distinct-inodes
      ;;
    *) die "invalid MINIDREGG_LOCAL_COPY_MODE '$requested_mode'" ;;
  esac
}

filter_allowed_paths() {
  local input=$1
  local output=$2
  local line path allowed_path _allowed_sha skip
  : > "$output"
  while IFS= read -r line || [[ -n "$line" ]]; do
    path=${line#*  }
    [[ "$path" != "$line" ]] || return 1
    skip=false
    while IFS=$'\t' read -r allowed_path _allowed_sha; do
      if [[ "$path" == "./$allowed_path" ]]; then
        skip=true
        break
      fi
    done < "$generated_output_allowlist"
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
    actual_sha=$(sha256_file "$source/$allowed_path")
    printf 'allowed output %s expected=%s actual=%s\n' \
      "$allowed_path" "$expected_sha" "$actual_sha"
    [[ "$actual_sha" == "$expected_sha" ]] || status=1
  done < "$generated_output_allowlist"
  return "$status"
}

printf_command() {
  printf '%q ' "${command_args[@]}"
  printf '\n'
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
      die "options must precede COMMIT"
      ;;
    -*)
      die "unknown option '$1'"
      ;;
    *)
      break
      ;;
  esac
done

if [[ $# -lt 3 || "$2" != "--" ]]; then
  usage 2
fi
requested_revision=$1
shift 2
command_args=("$@")
[[ ${#command_args[@]} -gt 0 ]] || usage 2

local_timeout=${MINIDREGG_LOCAL_TIMEOUT:-45m}
requested_memory_kib=${MINIDREGG_LOCAL_MEMORY_KIB:-auto}
local_copy_mode=${MINIDREGG_LOCAL_COPY_MODE:-auto}
[[ "$local_timeout" =~ ^[1-9][0-9]*[smh]$ ]] ||
  die "invalid MINIDREGG_LOCAL_TIMEOUT '$local_timeout'"
case "$requested_memory_kib" in
  auto|none) ;;
  *) [[ "$requested_memory_kib" =~ ^[1-9][0-9]*$ ]] ||
       die "invalid MINIDREGG_LOCAL_MEMORY_KIB '$requested_memory_kib'" ;;
esac
case "$local_copy_mode" in auto|clone|copy) ;; *)
  die "invalid MINIDREGG_LOCAL_COPY_MODE '$local_copy_mode'" ;;
esac

for tool in git jq shasum tar find sort xargs cp chmod mktemp hostname uname sysctl; do
  command -v "$tool" >/dev/null 2>&1 || die "required tool '$tool' is missing"
done
python_path=$(command -v python3) || die "required tool 'python3' is missing"
lake_path=$(command -v lake) || die "required tool 'lake' is missing"
elan_path=$(command -v elan) || die "required tool 'elan' is missing"
cargo_path=$(command -v cargo) || die "required tool 'cargo' is missing"
rustc_path=$(command -v rustc) || die "required tool 'rustc' is missing"
for tool_path in "$python_path" "$lake_path" "$elan_path" "$cargo_path" "$rustc_path"; do
  [[ "$tool_path" == /* && -x "$tool_path" ]] || die "tool path is not absolute/executable: $tool_path"
done

# Darwin's resource module currently exposes RLIMIT_AS but rejects lowering it
# (Python reports "current limit exceeds maximum limit").  Probe in a disposable
# process.  An explicit numeric request fails closed when unsupported; `auto`
# records the absence and retains the independently enforced wall-clock timeout.
memory_candidate=$requested_memory_kib
[[ "$memory_candidate" != auto ]] || memory_candidate=67108864
if [[ "$memory_candidate" == none ]]; then
  local_memory_kib=0
  memory_limit_mode=disabled-by-request
else
  set +e
  memory_probe=$($python_path - "$memory_candidate" <<'PY' 2>&1
import resource
import sys

ceiling = int(sys.argv[1]) * 1024
soft, hard = resource.getrlimit(resource.RLIMIT_AS)
new_soft = ceiling if hard == resource.RLIM_INFINITY or ceiling <= hard else hard
resource.setrlimit(resource.RLIMIT_AS, (new_soft, hard))
print(new_soft // 1024)
PY
  )
  memory_probe_status=$?
  set -e
  if [[ "$memory_probe_status" -eq 0 ]]; then
    local_memory_kib=$memory_probe
    memory_limit_mode=rlimit-as
  elif [[ "$requested_memory_kib" == auto ]]; then
    local_memory_kib=0
    memory_limit_mode=unsupported-recorded
  else
    die "requested address-space limit is unsupported: $memory_probe"
  fi
fi

# Git dependency acquisition is intentionally independent of user/global Git
# configuration.  This also prevents a broken external config symlink from
# changing the evidence runner.
export GIT_CONFIG_NOSYSTEM=1
export GIT_CONFIG_GLOBAL=/dev/null

repo_root=$(git rev-parse --show-toplevel)
repo_root=$(canonical_dir "$repo_root")
cd "$repo_root"
commit=$(git rev-parse --verify "${requested_revision}^{commit}" 2>/dev/null) ||
  die "'$requested_revision' does not resolve to a local commit"
tree=$(git rev-parse "${commit}^{tree}")
short_commit=${commit:0:12}

if git ls-tree -r "$commit" | awk '$1 == "160000" { found = 1 } END { exit !found }'; then
  die "commit $commit contains submodules; exact archive checks do not yet support them"
fi
if git ls-tree -r "$commit" | awk '$1 == "120000" { found = 1 } END { exit !found }'; then
  die "commit $commit contains source symlinks; exact archive checks do not yet support them"
fi

default_root=${TMPDIR:-/tmp}
default_root=${default_root%/}/minidregg-local-checks
check_root=${MINIDREGG_LOCAL_CHECK_ROOT:-$default_root}
mkdir -p "$check_root"
check_root=$(canonical_dir "$check_root")
path_is_within "$check_root" "$repo_root" &&
  die "local-check root must be outside the repository"
[[ -d "$check_root" && ! -L "$check_root" ]] || die "local-check root must not be a symlink"
mkdir -p "$check_root/runs" "$check_root/seeds" "$check_root/locks"
for directory in "$check_root/runs" "$check_root/seeds" "$check_root/locks"; do
  [[ -d "$directory" && ! -L "$directory" ]] || die "unsafe local-check directory '$directory'"
done

run=$(mktemp -d "$check_root/runs/run-$short_commit-XXXXXXXX")
[[ -d "$run" && ! -L "$run" ]] || die "failed to create a private run tree"
run=$(canonical_dir "$run")
path_is_within "$run" "$check_root/runs" || die "unsafe run path '$run'"
source=$run/source
archive=$run/source.tar
source_before=$run/source.files.sha256
source_after=$run/source.after.sha256
dependency_expected=$run/dependency-revisions.expected.tsv
generated_output_allowlist=$run/generated-output-allowlist.tsv
mkdir "$source" "$run/build" "$run/tmp" "$run/cargo-home"

git archive --format=tar --output="$archive" "$commit"
tar -xf "$archive" -C "$source"
source_manifest "$source" "$source_before"
archive_sha=$(sha256_file "$archive")
source_manifest_sha=$(sha256_file "$source_before")

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

[[ -f "$source/lean-toolchain" ]] || die "snapshot has no lean-toolchain"
[[ -f "$source/lake-manifest.json" ]] || die "snapshot has no lake-manifest.json"
toolchain_sha=$(sha256_file "$source/lean-toolchain")
lake_manifest_sha=$(sha256_file "$source/lake-manifest.json")
rust_toolchain_sha=none
[[ ! -f "$source/rust-toolchain.toml" ]] || rust_toolchain_sha=$(sha256_file "$source/rust-toolchain.toml")
cargo_lock_sha=none
[[ ! -f "$source/prover/Cargo.lock" ]] || cargo_lock_sha=$(sha256_file "$source/prover/Cargo.lock")

package_count=$(jq '.packages | length' "$source/lake-manifest.json")
git_package_count=$(jq '[.packages[] | select(.type == "git")] | length' "$source/lake-manifest.json")
[[ "$package_count" == "$git_package_count" ]] || die "only git-pinned Lake dependencies are supported"
jq -r '.packages[] | [.name, .rev] | @tsv' "$source/lake-manifest.json" |
  LC_ALL=C sort > "$dependency_expected"
[[ -s "$dependency_expected" ]] || die "Lake manifest contains no pinned dependencies"
while IFS=$'\t' read -r package_name package_rev; do
  [[ "$package_name" =~ ^[A-Za-z0-9_.-]+$ ]] || die "unsafe Lake package name '$package_name'"
  [[ "$package_rev" =~ ^[0-9a-f]{40}$ ]] ||
    die "Lake package '$package_name' is not pinned to a full Git revision"
done < "$dependency_expected"
dependency_manifest_sha=$(sha256_file "$dependency_expected")
seed_key="v2-${toolchain_sha:0:24}-${lake_manifest_sha:0:24}"
seed=$check_root/seeds/$seed_key

if $dry_run; then
  printf 'requested_revision=%s\ncommit=%s\ntree=%s\nrun=%s\n' \
    "$requested_revision" "$commit" "$tree" "$run"
  printf 'archive_sha256=%s\nsource_manifest_sha256=%s\n' \
    "$archive_sha" "$source_manifest_sha"
  printf 'lean_toolchain_sha256=%s\nlake_manifest_sha256=%s\n' \
    "$toolchain_sha" "$lake_manifest_sha"
  printf 'dependency_manifest_sha256=%s\nseed_key=%s\n' \
    "$dependency_manifest_sha" "$seed_key"
  printf 'generated_output_count=%s\ngenerated_output_allowlist_sha256=%s\n' \
    "$generated_output_count" "$generated_output_allowlist_sha"
  printf 'limits=memory_kib:%s,memory_mode:%s,timeout:%s\ncopy_mode=%s\ncommand=' \
    "$local_memory_kib" "$memory_limit_mode" "$local_timeout" "$local_copy_mode"
  printf_command
  exit 0
fi

evidence_dir=${MINIDREGG_EVIDENCE_DIR:-$check_root/evidence}
mkdir -p "$evidence_dir"
evidence_dir=$(canonical_dir "$evidence_dir")
path_is_within "$evidence_dir" "$repo_root" && die "evidence directory must be outside the repository"
[[ -d "$evidence_dir" && ! -L "$evidence_dir" ]] || die "evidence directory must not be a symlink"

# Construct one immutable seed per exact Lean/Lake identity.  The bootstrap is
# itself extracted from the committed archive.  It never sees the developer
# worktree's .lake directory.  mkdir is the portable local serialization lock;
# a busy/stale lock is reported rather than broken destructively.
lock=$check_root/locks/$seed_key.lock
if [[ ! -f "$seed/.complete" ]]; then
  mkdir "$lock" 2>/dev/null || die "dependency seed lock is busy or stale: $lock"
  lock_held=true
  # shellcheck disable=SC2329 # invoked indirectly by the EXIT trap
  cleanup_lock() {
    if [[ ${lock_held:-false} == true ]]; then
      rmdir "$lock" 2>/dev/null || true
    fi
  }
  trap cleanup_lock EXIT
  if [[ ! -f "$seed/.complete" ]]; then
    incoming=$(mktemp -d "$check_root/seeds/.incoming-$seed_key-XXXXXXXX")
    bootstrap=$(mktemp -d "$run/bootstrap-XXXXXXXX")
    mkdir "$bootstrap/source"
    tar -xf "$archive" -C "$bootstrap/source"
    (
      cd "$bootstrap/source"
      "$lake_path" update
      [[ "$(sha256_file lake-manifest.json)" == "$lake_manifest_sha" ]]
      "$lake_path" exe cache get
    )
    # The bootstrap belongs only to this seed construction.  Move its package
    # tree instead of duplicating the multi-gigabyte cache; no other checkout
    # or run ever retains an alias to these inodes.
    mv "$bootstrap/source/.lake/packages" "$incoming/packages"
    verify_confined_symlinks "$incoming/packages"
    verify_package_revisions "$incoming/packages" "$dependency_expected" \
      "$incoming/dependency-revisions.tsv" || die "dependency seed revisions are not exact/clean"
    printf 'schema=v2\ntoolchain_sha256=%s\nlake_manifest_sha256=%s\ndependency_manifest_sha256=%s\n' \
      "$toolchain_sha" "$lake_manifest_sha" "$dependency_manifest_sha" \
      > "$incoming/identity"
    printf '%s\n' "$seed_key" > "$incoming/.complete"
    find "$incoming" ! -type l \( -type d -o -type f \) -exec chmod a-w {} +
    mv "$incoming" "$seed"
  fi
  lock_held=false
  rmdir "$lock"
  trap - EXIT
fi

[[ -d "$seed" && ! -L "$seed" && -d "$seed/packages" && ! -L "$seed/packages" ]] ||
  die "dependency seed is absent or unsafe"
[[ -z "$(find "$seed" ! -type l -perm +222 -print -quit)" ]] || die "dependency seed is writable"
[[ "$(cat "$seed/.complete")" == "$seed_key" ]] || die "dependency seed completion marker is invalid"
[[ "$(sha256_file "$seed/dependency-revisions.tsv")" == "$dependency_manifest_sha" ]] ||
  die "dependency seed revision manifest identity is invalid"
verify_confined_symlinks "$seed/packages"
verify_package_revisions "$seed/packages" "$dependency_expected" "$run/dependency-revisions.tsv" ||
  die "dependency seed revision verification failed"
expected_seed_identity=$(printf 'schema=v2\ntoolchain_sha256=%s\nlake_manifest_sha256=%s\ndependency_manifest_sha256=%s' \
  "$toolchain_sha" "$lake_manifest_sha" "$dependency_manifest_sha")
[[ "$(cat "$seed/identity")" == "$expected_seed_identity" ]] ||
  die "dependency seed identity does not match the exact snapshot pins"
seed_identity_sha=$(sha256_file "$seed/identity")

mkdir -p "$source/.lake/packages" "$run/build/cargo"
[[ ! -L "$source/.lake" && ! -L "$source/.lake/packages" ]] || die "run-local .lake path is unsafe"
dependency_copy_mode=$(copy_packages "$seed/packages" "$source/.lake/packages" "$local_copy_mode")
verify_no_shared_regular_inodes "$seed/packages" "$source/.lake/packages"
verify_confined_symlinks "$source/.lake/packages"
# Permission changes are safe only after the cross-tree inode check above.
find "$source/.lake/packages" ! -type l \( -type d -o -type f \) -exec chmod u+w {} +
verify_package_revisions "$source/.lake/packages" "$dependency_expected" \
  "$run/dependency-revisions.private.tsv" || die "private dependency copy is not exact/clean"
cmp -s "$run/dependency-revisions.tsv" "$run/dependency-revisions.private.tsv" ||
  die "private dependency revision manifest mismatch"

# The archived project source is a unique private copy.  It may be writable for
# checked generators; the complete post-command manifest below is authoritative.
find "$source" -path "$source/.lake" -prune -o \
  \( -type d -o -type f \) -exec chmod u+w {} +

hostname_value=$(hostname)
host_label=$(printf '%s' "$hostname_value" | tr -cs 'A-Za-z0-9_.-' '_')
uname_value=$(uname -a)
cpu_value=$(sysctl -n machdep.cpu.brand_string 2>/dev/null || sysctl -n hw.model 2>/dev/null || true)
threads_value=$(sysctl -n hw.logicalcpu 2>/dev/null || echo 0)
memory_bytes=$(sysctl -n hw.memsize 2>/dev/null || echo 0)
os_value=$(sw_vers 2>/dev/null | tr '\n' ';' || true)
python_version=$($python_path --version 2>&1)
elan_version=$($elan_path --version)
lake_version=$($lake_path --version)
lean_version=$(cd "$source" && "$lake_path" env lean --version)
lean_path=$(cd "$source" && "$lake_path" env which lean)
cargo_version=$($cargo_path --version)
rustc_version=$($rustc_path --version)

case "$local_timeout" in
  *s) timeout_seconds=${local_timeout%s} ;;
  *m) timeout_seconds=$(( ${local_timeout%m} * 60 )) ;;
  *h) timeout_seconds=$(( ${local_timeout%h} * 3600 )) ;;
esac

case "${command_args[0]}" in
  lake) resolved_executable=$lake_path ;;
  elan) resolved_executable=$elan_path ;;
  cargo) resolved_executable=$cargo_path ;;
  rustc) resolved_executable=$rustc_path ;;
  */*)
    if [[ "${command_args[0]}" == /* ]]; then
      resolved_executable=${command_args[0]}
    else
      resolved_executable=$source/${command_args[0]#./}
    fi
    ;;
  *) resolved_executable=$(command -v "${command_args[0]}" 2>/dev/null) ||
       die "command '${command_args[0]}' is not executable" ;;
esac
[[ "$resolved_executable" == /* && -x "$resolved_executable" ]] ||
  die "resolved command is not an absolute executable: $resolved_executable"
command_args[0]=$resolved_executable

stamp=$(date -u +%Y%m%dT%H%M%S)-$$
command_name=$(printf '%s' "$(basename "$resolved_executable")" | tr -cs 'A-Za-z0-9_.-' '_')
run_id="E-$stamp-local-$host_label-$short_commit-$command_name"
log_path=$evidence_dir/$run_id.log
json_path=$evidence_dir/$run_id.json
source_path=$evidence_dir/$run_id.source.sha256
post_source_path=$evidence_dir/$run_id.source-after.sha256
allowlist_path=$evidence_dir/$run_id.generated-outputs.tsv
dependency_path=$evidence_dir/$run_id.dependencies.tsv
dependency_after_path=$evidence_dir/$run_id.dependencies-after.tsv
olean_path=$evidence_dir/$run_id.oleans.sha256
integrity_path=$evidence_dir/$run_id.source-integrity.log
dependency_integrity_path=$evidence_dir/$run_id.dependency-integrity.log
started=$(date -u +%Y-%m-%dT%H:%M:%SZ)

printf 'run=%s\ncommit=%s\ntree=%s\nlocal_run=%s\ncopy_mode=%s\ncommand=' \
  "$run_id" "$commit" "$tree" "$run" "$dependency_copy_mode" | tee "$log_path"
printf_command | tee -a "$log_path"

runner_python=$run/run-with-limits.py
cat > "$runner_python" <<'PY'
import os
import resource
import signal
import subprocess
import sys

timeout = int(sys.argv[1])
memory_kib = int(sys.argv[2])
argv = sys.argv[3:]
if not argv:
    raise SystemExit(2)

def limits():
    if memory_kib == 0:
        return
    ceiling = memory_kib * 1024
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    new_soft = ceiling if hard == resource.RLIM_INFINITY or ceiling <= hard else hard
    resource.setrlimit(resource.RLIMIT_AS, (new_soft, hard))

process = subprocess.Popen(argv, start_new_session=True, preexec_fn=limits)
try:
    raise SystemExit(process.wait(timeout=timeout))
except subprocess.TimeoutExpired:
    os.killpg(process.pid, signal.SIGTERM)
    try:
        process.wait(timeout=30)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()
    raise SystemExit(124)
PY
runner_python_sha=$(sha256_file "$runner_python")

set +e
(
  cd "$source"
  command_path="$(dirname "$elan_path"):$(dirname "$cargo_path"):/usr/local/bin:/usr/bin:/bin"
  export PATH="$command_path"
  export CARGO_HOME="$run/cargo-home"
  export CARGO_TARGET_DIR="$run/build/cargo"
  export TMPDIR="$run/tmp"
  export XDG_CACHE_HOME="$run/build/xdg-cache"
  unset LEAN_PATH LEAN_SYSROOT
  printf 'resolved_executable=%s\n' "$resolved_executable"
  "$python_path" "$runner_python" "$timeout_seconds" "$local_memory_kib" "${command_args[@]}"
) 2>&1 | tee -a "$log_path"
command_exit=${PIPESTATUS[0]}
set -e
printf '%s\n' "$command_exit" > "$run/command.exit"

source_manifest "$source" "$source_after"
set +e
source_integrity_exit=0
{
  printf 'before_manifest_sha256=%s\n' "$(sha256_file "$source_before")"
  printf 'after_manifest_sha256=%s\n' "$(sha256_file "$source_after")"
  printf 'generated_output_allowlist_sha256=%s\n' "$generated_output_allowlist_sha"
  printf 'generated_output_count=%s\n' "$generated_output_count"
  validate_allowed_outputs
  allowed_status=$?
  filter_allowed_paths "$source_before" "$run/source.before.filtered.sha256"
  before_filter_status=$?
  filter_allowed_paths "$source_after" "$run/source.after.filtered.sha256"
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

set +e
dependency_integrity_exit=0
{
  verify_package_revisions "$source/.lake/packages" "$dependency_expected" \
    "$run/dependency-revisions.after.tsv"
  private_revision_status=$?
  verify_package_revisions "$seed/packages" "$dependency_expected" \
    "$run/dependency-seed-revisions.after.tsv"
  seed_revision_status=$?
  if [[ "$(sha256_file "$seed/identity")" == "$seed_identity_sha" ]]; then
    seed_identity_status=0
  else
    seed_identity_status=1
  fi
  if [[ -z "$(find "$seed" ! -type l -perm +222 -print -quit)" ]]; then
    seed_permissions_status=0
  else
    seed_permissions_status=1
  fi
  printf 'private_revision_status=%s\nseed_revision_status=%s\nseed_identity_status=%s\nseed_permissions_status=%s\n' \
    "$private_revision_status" "$seed_revision_status" "$seed_identity_status" \
    "$seed_permissions_status"
  if [[ "$private_revision_status" -ne 0 || "$seed_revision_status" -ne 0 ||
        "$seed_identity_status" -ne 0 || "$seed_permissions_status" -ne 0 ]]; then
    dependency_integrity_exit=1
  fi
} > "$run/dependency-integrity.log" 2>&1
set -e

olean_manifest=$run/project-oleans.sha256
: > "$olean_manifest"
if [[ -d "$source/.lake/build/lib/lean" ]]; then
  (
    cd "$source"
    LC_ALL=C find .lake/build/lib/lean -type f \( -name '*.olean' -o -name '*.ilean' \) -print0 |
      LC_ALL=C sort -z |
      xargs -0 shasum -a 256
  ) > "$olean_manifest"
fi

if [[ "$source_integrity_exit" -ne 0 ]]; then
  runner_exit=86
elif [[ "$dependency_integrity_exit" -ne 0 ]]; then
  runner_exit=87
else
  runner_exit=$command_exit
fi
printf 'command_exit=%s\nsource_integrity_exit=%s\ndependency_integrity_exit=%s\n' \
  "$command_exit" "$source_integrity_exit" "$dependency_integrity_exit" | tee -a "$log_path"

cp "$source_before" "$source_path"
cp "$source_after" "$post_source_path"
cp "$generated_output_allowlist" "$allowlist_path"
cp "$run/dependency-revisions.tsv" "$dependency_path"
if [[ -f "$run/dependency-revisions.after.tsv" ]]; then
  cp "$run/dependency-revisions.after.tsv" "$dependency_after_path"
else
  : > "$dependency_after_path"
fi
cp "$olean_manifest" "$olean_path"
cp "$run/source-integrity.log" "$integrity_path"
cp "$run/dependency-integrity.log" "$dependency_integrity_path"

finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
command_json='[]'
for argument in "${command_args[@]}"; do
  command_json=$(jq --arg argument "$argument" '. + [$argument]' <<< "$command_json")
done
generated_outputs_json=$(jq -R 'select(length > 0) | split("\t") |
  {path:.[0],sha256:.[1]}' "$allowlist_path" | jq -s .)

jq -n \
  --arg schema minidregg/local-evidence/v1 \
  --arg runId "$run_id" --arg requestedRevision "$requested_revision" \
  --arg commit "$commit" --arg tree "$tree" --arg archiveSha256 "$archive_sha" \
  --arg toolchainSha256 "$toolchain_sha" --arg lakeManifestSha256 "$lake_manifest_sha" \
  --arg rustToolchainSha256 "$rust_toolchain_sha" --arg cargoLockSha256 "$cargo_lock_sha" \
  --arg sourceFile "$(basename "$source_path")" --arg sourceManifestSha256 "$(sha256_file "$source_path")" \
  --arg postSourceFile "$(basename "$post_source_path")" --arg postSourceSha256 "$(sha256_file "$post_source_path")" \
  --arg allowlistFile "$(basename "$allowlist_path")" --arg allowlistSha256 "$(sha256_file "$allowlist_path")" \
  --argjson generatedOutputs "$generated_outputs_json" \
  --arg dependencyFile "$(basename "$dependency_path")" \
  --arg dependencyAfterFile "$(basename "$dependency_after_path")" \
  --arg dependencyManifestSha256 "$(sha256_file "$dependency_path")" \
  --arg dependencyAfterSha256 "$(sha256_file "$dependency_after_path")" \
  --arg seedKey "$seed_key" --arg seedIdentitySha256 "$seed_identity_sha" \
  --arg dependencyCopyMode "$dependency_copy_mode" --argjson command "$command_json" \
  --arg resolvedExecutable "$resolved_executable" --arg localRun "$run" \
  --arg hostname "$hostname_value" --arg uname "$uname_value" --arg os "$os_value" \
  --arg cpu "$cpu_value" --argjson threads "$threads_value" --argjson memoryBytes "$memory_bytes" \
  --arg pythonPath "$python_path" --arg pythonVersion "$python_version" \
  --arg elanPath "$elan_path" --arg elanVersion "$elan_version" \
  --arg lakePath "$lake_path" --arg lakeVersion "$lake_version" \
  --arg leanPath "$lean_path" --arg leanVersion "$lean_version" \
  --arg cargoPath "$cargo_path" --arg cargoVersion "$cargo_version" \
  --arg rustcPath "$rustc_path" --arg rustcVersion "$rustc_version" \
  --arg timeout "$local_timeout" --argjson timeoutSeconds "$timeout_seconds" \
  --argjson memoryKiB "$local_memory_kib" --arg memoryLimitMode "$memory_limit_mode" \
  --arg runnerPythonSha256 "$runner_python_sha" \
  --arg startedAt "$started" --arg finishedAt "$finished" \
  --argjson runnerExit "$runner_exit" --argjson commandExit "$command_exit" \
  --argjson sourceIntegrityExit "$source_integrity_exit" \
  --argjson dependencyIntegrityExit "$dependency_integrity_exit" \
  --arg logFile "$(basename "$log_path")" --arg logSha256 "$(sha256_file "$log_path")" \
  --arg oleanFile "$(basename "$olean_path")" --arg oleanSha256 "$(sha256_file "$olean_path")" \
  --arg integrityFile "$(basename "$integrity_path")" --arg integritySha256 "$(sha256_file "$integrity_path")" \
  --arg dependencyIntegrityFile "$(basename "$dependency_integrity_path")" \
  --arg dependencyIntegritySha256 "$(sha256_file "$dependency_integrity_path")" \
  '{schema:$schema,runId:$runId,
    source:{requestedRevision:$requestedRevision,commit:$commit,tree:$tree,dirty:false,
      archiveSha256:$archiveSha256,leanToolchainSha256:$toolchainSha256,
      lakeManifestSha256:$lakeManifestSha256,rustToolchainSha256:$rustToolchainSha256,
      cargoLockSha256:$cargoLockSha256,
      beforeManifest:{file:$sourceFile,sha256:$sourceManifestSha256},
      afterManifest:{file:$postSourceFile,sha256:$postSourceSha256},
      mutationPolicy:{default:"exact-manifest-equality",autoSync:false,
        allowlist:{file:$allowlistFile,sha256:$allowlistSha256,outputs:$generatedOutputs}}},
    dependencies:{seedKey:$seedKey,seedIdentitySha256:$seedIdentitySha256,
      runLocalTree:true,copyMode:$dependencyCopyMode,sharedInodes:false,
      revisionManifest:{file:$dependencyFile,sha256:$dependencyManifestSha256},
      postRevisionManifest:{file:$dependencyAfterFile,sha256:$dependencyAfterSha256}},
    command:$command,resolvedExecutable:$resolvedExecutable,
    worker:{kind:"local",hostname:$hostname,uname:$uname,os:$os,cpu:$cpu,
      threads:$threads,memoryBytes:$memoryBytes,runTree:$localRun,
      tools:{python:{path:$pythonPath,version:$pythonVersion},
        elan:{path:$elanPath,version:$elanVersion},lake:{path:$lakePath,version:$lakeVersion},
        lean:{path:$leanPath,version:$leanVersion},cargo:{path:$cargoPath,version:$cargoVersion},
        rustc:{path:$rustcPath,version:$rustcVersion}},
      limits:{addressSpaceKiB:$memoryKiB,timeout:$timeout,
        addressSpaceMode:$memoryLimitMode,
        timeoutSeconds:$timeoutSeconds,killAfterSeconds:30,
        wrapperSha256:$runnerPythonSha256,cpuAffinity:null}},
    startedAt:$startedAt,finishedAt:$finishedAt,
    result:{runnerExit:$runnerExit,commandExit:$commandExit,
      sourceIntegrityExit:$sourceIntegrityExit,
      dependencyIntegrityExit:$dependencyIntegrityExit},
    rawLog:{file:$logFile,sha256:$logSha256},
    projectOleans:{file:$oleanFile,sha256:$oleanSha256},
    sourceIntegrity:{file:$integrityFile,sha256:$integritySha256},
    dependencyIntegrity:{file:$dependencyIntegrityFile,sha256:$dependencyIntegritySha256},
    claimCeiling:"Exact explicit-commit local source/dependency/build evidence with post-run source equality modulo caller-predeclared generated outputs only; not an independent-host result, benchmark, native-semantics claim, or cryptographic-security claim."}' \
  > "$json_path"

echo "evidence: $json_path"
exit "$runner_exit"
