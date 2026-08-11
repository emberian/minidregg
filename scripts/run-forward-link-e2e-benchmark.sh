#!/usr/bin/env bash
set -euo pipefail

project_dir=${MINIDREGG_BENCH_PROJECT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}

# hbox builds must enter the shared memory-capped swarm.slice.  Capture the
# archive's absolute source path before systemd-run changes the working
# directory, then re-enter this same runner inside the scope.
if [[ "$(hostname -s)" == hbox && -z "${SWARM_BUILD_INNER:-}" ]]; then
  exec swarm-build env MINIDREGG_BENCH_PROJECT_DIR="$project_dir" \
    bash "$project_dir/scripts/run-forward-link-e2e-benchmark.sh"
fi

cd "$project_dir"

cargo_target=$(mktemp -d /tmp/minidregg-forward-link-bench.XXXXXX)
trap 'rm -rf -- "$cargo_target"' EXIT

cpu_model=$(lscpu 2>/dev/null | sed -n 's/^Model name:[[:space:]]*//p' | head -1 || true)
if [[ -z "$cpu_model" ]] && command -v sysctl >/dev/null 2>&1; then
  cpu_model=$(sysctl -n machdep.cpu.brand_string 2>/dev/null || true)
fi

if source_commit=$(git rev-parse HEAD 2>/dev/null) &&
    source_tree=$(git rev-parse HEAD^{tree} 2>/dev/null); then
  printf 'source_commit=%s\n' "$source_commit"
  printf 'source_tree=%s\n' "$source_tree"
else
  printf 'source_commit=external-exact-archive-runner\n'
  printf 'source_tree=external-exact-archive-runner\n'
fi
printf 'host=%s\n' "$(hostname)"
printf 'kernel=%s\n' "$(uname -srvmo 2>/dev/null || uname -a)"
printf 'cpu=%s\n' "${cpu_model:-unknown}"
printf 'logical_cpus=%s\n' "$(getconf _NPROCESSORS_ONLN 2>/dev/null || printf unknown)"
printf 'lean=%s\n' "$(lake env lean --version | head -1)"
printf 'rustc=%s\n' "$(rustc --version)"
printf 'cargo=%s\n' "$(cargo --version)"
printf 'prepare=proof joins + computable bounded page + release opaque-store benchmark\n'

lake build \
  Assurance.HyperdocumentLinkEndpointController \
  Assurance.HyperdocumentLinkPageDurableWeld \
  Assurance.HyperdocumentLinkLocalFileStore \
  Assurance.HyperdocumentLinkClientLocalFileCutover \
  Compiler.HyperdocumentContentPageMaterializer >/dev/null

CARGO_TARGET_DIR="$cargo_target" cargo build --release --quiet \
  --manifest-path native/hyperdocument-link-store/Cargo.toml \
  --bin forward-link-e2e-bench

printf 'semantic_command=lake env lean --run scripts/ForwardLinkSemanticBenchmark.lean\n'
lake env lean --run scripts/ForwardLinkSemanticBenchmark.lean

printf 'native_command=%s/release/forward-link-e2e-bench\n' "$cargo_target"
"$cargo_target/release/forward-link-e2e-bench"

printf 'combined_status=PASS\n'
