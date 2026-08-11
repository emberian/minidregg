#!/usr/bin/env bash
set -euo pipefail

project_dir=${MINIDREGG_BENCH_PROJECT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}

# hbox builds must enter the shared memory-capped swarm.slice.  Capture the
# archive's absolute source path before systemd-run changes the working
# directory, then re-enter this same runner inside the scope.
if [[ "$(hostname -s)" == hbox && -z "${SWARM_BUILD_INNER:-}" ]]; then
  exec swarm-build env MINIDREGG_BENCH_PROJECT_DIR="$project_dir" \
    bash "$project_dir/scripts/run-bounded-page-materializer-benchmark.sh"
fi

cd "$project_dir"

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
printf 'prepare=lake build Compiler.CredentialAuthorityPageMaterializer Compiler.HyperdocumentContentPageMaterializer Compiler.HyperdocumentEventPageMaterializer\n'
printf 'command=lake env lean --run scripts/BoundedPageMaterializerBenchmark.lean\n'

lake build Compiler.CredentialAuthorityPageMaterializer \
  Compiler.HyperdocumentContentPageMaterializer \
  Compiler.HyperdocumentEventPageMaterializer >/dev/null

exec lake env lean --run scripts/BoundedPageMaterializerBenchmark.lean
