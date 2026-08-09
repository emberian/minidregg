#!/usr/bin/env bash
# Execute one exact committed minidregg snapshot on hbox or persvati.
#
# Every invocation gets a unique remote source/build tree.  The transferred git
# archive, Lean pins, raw log, and resulting project-olean manifest are hashed.
# Dependency packages come from a locked, immutable seed keyed by the Lean and
# Lake manifests; project build output is never shared between runs.
set -euo pipefail

usage() {
  cat >&2 <<'EOF'
usage: scripts/remote-check.sh HOST -- COMMAND [ARG ...]

Examples:
  scripts/remote-check.sh hbox -- lake build Compiler.NativeKernelPlan
  scripts/remote-check.sh persvati -- lake env lean Assurance/BfvNativeBufferAdmission.lean

Only committed HEAD is transferred.  Evidence defaults to /tmp/minidregg-evidence.
EOF
  exit 2
}

if [[ $# -lt 3 || "$2" != "--" ]]; then
  usage
fi

host=$1
shift 2
command_args=("$@")

case "$host" in
  hbox)
    remote_root=/tank/dregg-build/minidregg-checks
    remote_lake=/home/hbox/.elan/bin/lake
    remote_cargo=/home/hbox/.cargo/bin/cargo
    package_candidate=/home/hbox/dev/minidregg/.lake/packages
    ;;
  persvati)
    remote_root=/home/ember/minidregg-checks
    remote_lake=/home/ember/.elan/bin/lake
    remote_cargo=/home/ember/.cargo/bin/cargo
    # Keep this a nonempty argv value: OpenSSH reconstructs a remote command
    # string and would otherwise erase an empty positional argument.
    package_candidate=/home/ember/.cache/minidregg-no-package-candidate
    ;;
  *)
    echo "unsupported worker '$host' (expected hbox or persvati)" >&2
    exit 2
    ;;
esac

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

if [[ -n "$(git status --porcelain)" ]]; then
  echo "remote checks require a clean, committed source tree" >&2
  exit 2
fi

commit=$(git rev-parse HEAD)
tree=$(git rev-parse 'HEAD^{tree}')
short_commit=${commit:0:12}
toolchain_sha=$(shasum -a 256 lean-toolchain | awk '{print $1}')
manifest_sha=$(shasum -a 256 lake-manifest.json | awk '{print $1}')
seed_key=${toolchain_sha:0:16}-${manifest_sha:0:16}
mathlib_rev=$(awk '
  $0 == "name = \"mathlib\"" { in_mathlib = 1; next }
  in_mathlib && /^rev = / { gsub(/^rev = \"|\"$/, ""); print; exit }
' lakefile.toml)
[[ -n "$mathlib_rev" ]] || { echo "could not resolve pinned mathlib revision" >&2; exit 2; }

local_tmp=$(mktemp -d /tmp/minidregg-remote-check.XXXXXX)
trap 'rm -rf "$local_tmp"' EXIT
archive=$local_tmp/source.tar
git archive --format=tar --output="$archive" "$commit"
archive_sha=$(shasum -a 256 "$archive" | awk '{print $1}')

remote_run=$(ssh -o BatchMode=yes "$host" bash -s -- "$remote_root" "$short_commit" <<'REMOTE'
set -euo pipefail
root=$1
short_commit=$2
mkdir -p "$root/runs" "$root/seeds"
mktemp -d "$root/runs/run-$short_commit-XXXXXXXX"
REMOTE
)
remote_source=$remote_run/source

ssh -o BatchMode=yes "$host" "cat > '$remote_run/source.tar'" < "$archive"
remote_archive_sha=$(ssh -o BatchMode=yes "$host" "sha256sum '$remote_run/source.tar' | awk '{print \$1}'")
if [[ "$remote_archive_sha" != "$archive_sha" ]]; then
  echo "archive hash mismatch: local=$archive_sha remote=$remote_archive_sha" >&2
  exit 1
fi

ssh -o BatchMode=yes "$host" bash -s -- \
  "$remote_run" "$commit" "$tree" "$archive_sha" "$toolchain_sha" "$manifest_sha" <<'REMOTE'
set -euo pipefail
run=$1
commit=$2
tree=$3
archive_sha=$4
toolchain_sha=$5
manifest_sha=$6
mkdir "$run/source"
tar -xf "$run/source.tar" -C "$run/source"
[[ "$(sha256sum "$run/source/lean-toolchain" | awk '{print $1}')" == "$toolchain_sha" ]]
[[ "$(sha256sum "$run/source/lake-manifest.json" | awk '{print $1}')" == "$manifest_sha" ]]
printf '%s %s %s\n' "$commit" "$tree" "$archive_sha" > "$run/source.identity"
REMOTE

# Construct the dependency seed once under a host-local lock.  hbox starts from
# a copy of its exact-revision warm package tree; persvati bootstraps with Lake.
# The finished seed is made immutable before any run links it.
ssh -o BatchMode=yes "$host" bash -s -- \
  "$remote_root" "$remote_run" "$remote_source" "$seed_key" "$remote_lake" \
  "$package_candidate" "$mathlib_rev" "$manifest_sha" <<'REMOTE'
set -euo pipefail
root=$1
run=$2
source=$3
seed_key=$4
lake=$5
candidate=$6
mathlib_rev=$7
manifest_sha=$8
seed="$root/seeds/$seed_key"
lock="$root/seeds/$seed_key.lock"
exec 9>"$lock"
flock 9
if [[ ! -f "$seed/.complete" ]]; then
  incoming=$(mktemp -d "$root/seeds/.incoming-$seed_key-XXXXXXXX")
  mkdir -p "$incoming/packages"
  if [[ -n "$candidate" && -d "$candidate/mathlib/.git" &&
        "$(git -C "$candidate/mathlib" rev-parse HEAD)" == "$mathlib_rev" ]]; then
    cp -a --reflink=auto "$candidate/." "$incoming/packages/"
  else
    mkdir -p "$source/.lake"
    ln -s "$incoming/packages" "$source/.lake/packages"
    (cd "$source" && "$lake" update && "$lake" exe cache get)
    rm "$source/.lake/packages"
  fi
  [[ -d "$incoming/packages/mathlib/.git" ]]
  [[ "$(git -C "$incoming/packages/mathlib" rev-parse HEAD)" == "$mathlib_rev" ]]
  [[ "$(sha256sum "$source/lake-manifest.json" | awk '{print $1}')" == "$manifest_sha" ]]
  printf '%s\n' "$seed_key" > "$incoming/.complete"
  chmod -R a-w "$incoming"
  mv "$incoming" "$seed"
fi
mkdir -p "$source/.lake"
ln -s "$seed/packages" "$source/.lake/packages"
REMOTE

evidence_dir=${MINIDREGG_EVIDENCE_DIR:-/tmp/minidregg-evidence}
mkdir -p "$evidence_dir"
started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
stamp=$(date -u +%Y%m%dT%H%M%S)-$$
command_name=$(basename "${command_args[0]}")
run_id="E-$stamp-$host-$short_commit-$command_name"
log_path=$evidence_dir/$run_id.log
json_path=$evidence_dir/$run_id.json
olean_path=$evidence_dir/$run_id.oleans.sha256

remote_hostname=$(ssh -o BatchMode=yes "$host" hostname)
remote_uname=$(ssh -o BatchMode=yes "$host" uname -a)
remote_cpu=$(ssh -o BatchMode=yes "$host" "lscpu | sed -n 's/^Model name:[[:space:]]*//p' | head -1")
remote_threads=$(ssh -o BatchMode=yes "$host" nproc)
remote_mem_kib=$(ssh -o BatchMode=yes "$host" "awk '/MemTotal/{print \$2}' /proc/meminfo")
remote_gpu=$(ssh -o BatchMode=yes "$host" "lspci 2>/dev/null | grep -Ei 'vga|3d|display' || true")
lake_version=$(ssh -o BatchMode=yes "$host" "cd '$remote_source' && '$remote_lake' --version")
cargo_version=$(ssh -o BatchMode=yes "$host" "'$remote_cargo' --version")

printf 'run=%s\ncommit=%s\nhost=%s\nremote_run=%s\ncommand=' \
  "$run_id" "$commit" "$remote_hostname" "$remote_run" | tee "$log_path"
printf '%q ' "${command_args[@]}" | tee -a "$log_path"
printf '\n' | tee -a "$log_path"

command_text=$(printf '%q ' "${command_args[@]}")
set +e
ssh -o BatchMode=yes "$host" bash -s -- \
  "$remote_source" "$remote_lake" "$remote_cargo" "$command_text" <<'REMOTE' 2>&1 | tee -a "$log_path"
set -euo pipefail
source=$1
lake=$2
cargo=$3
command_text=$4
cd "$source"
export PATH="$(dirname "$lake"):$(dirname "$cargo"):/usr/local/bin:/usr/bin:/bin"
ulimit -v $((24 * 1024 * 1024))
exec timeout --kill-after=30s 45m taskset -c 0-7 bash -lc "$command_text"
REMOTE
exit_code=${PIPESTATUS[0]}
set -e

ssh -o BatchMode=yes "$host" bash -s -- "$remote_source" <<'REMOTE' > "$olean_path"
set -euo pipefail
source=$1
cd "$source"
if [[ -d .lake/build/lib/lean ]]; then
  find .lake/build/lib/lean -type f \( -name '*.olean' -o -name '*.ilean' \) -print0 \
    | sort -z | xargs -0 -r sha256sum
fi
REMOTE

finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
log_sha=$(shasum -a 256 "$log_path" | awk '{print $1}')
olean_sha=$(shasum -a 256 "$olean_path" | awk '{print $1}')
command_json=$(printf '%s\n' "${command_args[@]}" | jq -R . | jq -s .)

jq -n \
  --arg schema minidregg/remote-evidence/v1 \
  --arg runId "$run_id" \
  --arg commit "$commit" --arg tree "$tree" --arg archiveSha256 "$archive_sha" \
  --arg toolchainSha256 "$toolchain_sha" --arg manifestSha256 "$manifest_sha" \
  --argjson command "$command_json" --arg hostAlias "$host" --arg hostname "$remote_hostname" \
  --arg uname "$remote_uname" --arg cpu "$remote_cpu" --argjson threads "$remote_threads" \
  --argjson memoryKiB "$remote_mem_kib" --arg gpu "$remote_gpu" \
  --arg lake "$lake_version" --arg cargo "$cargo_version" --arg remoteRun "$remote_run" \
  --arg startedAt "$started" --arg finishedAt "$finished" --argjson exitCode "$exit_code" \
  --arg logFile "$(basename "$log_path")" --arg logSha256 "$log_sha" \
  --arg oleanFile "$(basename "$olean_path")" --arg oleanSha256 "$olean_sha" \
  '{schema:$schema,runId:$runId,
    source:{commit:$commit,tree:$tree,dirty:false,archiveSha256:$archiveSha256,
      leanToolchainSha256:$toolchainSha256,lakeManifestSha256:$manifestSha256},
    command:$command,
    worker:{alias:$hostAlias,hostname:$hostname,uname:$uname,cpu:$cpu,threads:$threads,
      memoryKiB:$memoryKiB,gpu:$gpu,lake:$lake,cargo:$cargo,remoteRun:$remoteRun,
      limits:{cpuSet:"0-7",virtualMemoryGiB:24,timeoutMinutes:45}},
    startedAt:$startedAt,finishedAt:$finishedAt,exitCode:$exitCode,
    rawLog:{file:$logFile,sha256:$logSha256},
    projectOleans:{file:$oleanFile,sha256:$oleanSha256},
    claimCeiling:"Exact committed-source build/check evidence only; not a benchmark, native-semantics claim, or cryptographic-security claim."}' \
  > "$json_path"

echo "evidence: $json_path"
exit "$exit_code"
