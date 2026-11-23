#!/usr/bin/env bash
# Run in the same isolated Linux tree as a successful native Host build.
# Arguments: Host build output, verifier, public fixture signer, Store executable.
set -euo pipefail
if [[ $# != 4 ]]; then
  echo "usage: $0 HOST-BUILD-OUTPUT VERIFIER SIGN-PROBE STORE" >&2
  exit 2
fi
build=$(realpath "$1")
shift
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
source=scripts/kn2/neutral-birth-install.lean
leanc="$(lake env lean --print-prefix)/bin/leanc"

# Link the checked Host objects and the full-walk oracle modules the deployed
# Host deliberately omits. Lake selects the exact imports of the test source.
mapfile -t roots < <(awk '/^public import / {print $3}' "$source")
for root in "${roots[@]}"; do
  lake query "+$root:transImports" --json >"$scratch/$root.json"
done
{
  printf '%s\n' "${roots[@]}"
  jq -r '.[]' "$scratch"/*.json
} | LC_ALL=C sort -u >"$scratch/modules"
declare -a extras=()
while IFS= read -r module; do
  stem=${module//./\/}
  [[ -f "$stem.lean" ]] || continue
  if grep -Fxq "$module" "$build/source-modules.txt"; then
    echo ".lake/build/ir/$stem.c.o.native"
  else
    extras+=("+$module:c.o.export")
    echo ".lake/build/ir/$stem.c.o.export"
  fi
done <"$scratch/modules" >"$scratch/probe.rsp"
if (( ${#extras[@]} )); then lake build "${extras[@]}"; fi
lake env lean --load-dynlib=.lake/native/libmini_kernels_lean.so -c "$scratch/probe.c" "$source"
"$leanc" -O1 -c "$scratch/probe.c" -o "$scratch/probe.o"
printf '%s\n' "$scratch/probe.o" >>"$scratch/probe.rsp"
cat "$build/package-objects.txt" .lake/native/link-inputs.txt >>"$scratch/probe.rsp"
"$leanc" -o "$scratch/probe" "@$scratch/probe.rsp"
"$scratch/probe" "$@" frontier-reads
