#!/usr/bin/env bash
set -euo pipefail
source_file=$(cd -- "$(dirname -- "$0")/.." && pwd)/prepare-install-config.sh
scratch=$(mktemp -d /tmp/mini-install-config-resume-XXXXXXXX)
trap 'rm -rf -- "$scratch"' EXIT
eval "$(sed -n '/^install_or_match() {/,/^}/p' "$source_file")"
printf 'same deterministic custody' >"$scratch/first"
install_or_match "$scratch/first" "$scratch/final"
[[ ! -e $scratch/first && -f $scratch/final &&
   $(stat -c '%a:%h' "$scratch/final") == 600:1 ]]
printf 'same deterministic custody' >"$scratch/second"
install_or_match "$scratch/second" "$scratch/final"
[[ ! -e $scratch/second ]]
printf 'different custody' >"$scratch/third"
if (install_or_match "$scratch/third" "$scratch/final"); then
  echo 'different deterministic custody reused' >&2; exit 1
fi
[[ $(cat "$scratch/final") == 'same deterministic custody' ]]
echo 'PASS: complete pure custody output reused; mismatched recovery refused'
