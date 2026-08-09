#!/usr/bin/env bash
# Compile the two Tower256 controller modules.  Exact remote snapshots are
# read-only, while a few existing checked generators intentionally rewrite
# committed test vectors during a cold Lake build.  In that case build in a
# disposable writable source copy and leave the evidence snapshot untouched.
set -euo pipefail

repo_dir=$PWD
work_dir=$repo_dir
temp_dir=

if [[ ! -w prover/testdata/demo_descriptor.json ]]; then
  temp_dir=$(mktemp -d /tmp/minidregg-tower-controller.XXXXXX)
  trap 'rm -rf -- "$temp_dir"' EXIT
  work_dir=$temp_dir/source
  mkdir -p "$work_dir"
  tar --exclude=.git --exclude=.lake --exclude='*.olean' -cf - . |
    tar -xf - -C "$work_dir"
  chmod u+w "$work_dir"/prover/testdata/*.json
  mkdir -p "$work_dir/.lake"
  ln -s "$repo_dir/.lake/packages" "$work_dir/.lake/packages"
fi

cd "$work_dir"
lake build Compiler.Tower256LogupControllerPlan
