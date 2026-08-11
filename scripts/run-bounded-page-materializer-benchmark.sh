#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"

cpu_model=$(lscpu 2>/dev/null | sed -n 's/^Model name:[[:space:]]*//p' | head -1 || true)
if [[ -z "$cpu_model" ]] && command -v sysctl >/dev/null 2>&1; then
  cpu_model=$(sysctl -n machdep.cpu.brand_string 2>/dev/null || true)
fi

printf 'source_commit=%s\n' "$(git rev-parse HEAD)"
printf 'source_tree=%s\n' "$(git rev-parse HEAD^{tree})"
printf 'host=%s\n' "$(hostname)"
printf 'kernel=%s\n' "$(uname -srvmo 2>/dev/null || uname -a)"
printf 'cpu=%s\n' "${cpu_model:-unknown}"
printf 'logical_cpus=%s\n' "$(getconf _NPROCESSORS_ONLN 2>/dev/null || printf unknown)"
printf 'lean=%s\n' "$(lake env lean --version | head -1)"
printf 'command=lake env lean --run scripts/BoundedPageMaterializerBenchmark.lean\n'

exec lake env lean --run scripts/BoundedPageMaterializerBenchmark.lean
