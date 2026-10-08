#!/usr/bin/env bash
# check-fixture-authority.sh RANGE -- the fixture-authority gate row (cv 01a1147b-103d).
#
# Over the commits of RANGE (e.g. main..next, or a queued lane range):
#   1. a commit that changes an AUTHORITY file (scripts/pipeline/fixture-authorities.txt, column 3, or a
#      `self` row's file) changes nothing in Kernel/, Compiler/, Host/, Theory/ or native/ (one commit may
#      not move the implementation and the answer that tests it together), and carries an
#      `Authority-Change: <reason>` trailer;
#   2. a commit that changes a file that LOOKS generated (*FixtureData*, golden/, *.snapshot,
#      native/*/fixtures/) has it listed in fixture-authorities.txt (no unlisted generated fixture).
# It prints each authority-change commit (the keeper logs them as semantic changes) and exits 1 on a
# violation, naming the commit and the files.
set -euo pipefail
range=${1:?usage: check-fixture-authority.sh RANGE}
root=$(git rev-parse --show-toplevel)
table=$root/scripts/pipeline/fixture-authorities.txt
mapfile -t rows < <(grep -v '^\s*#' "$table" | grep -v '^\s*$')
authorities=() ; generated=()
for row in "${rows[@]}"; do
  IFS='|' read -r gen _ auth status <<<"$row"
  gen=$(echo "$gen" | xargs); auth=$(echo "$auth" | xargs); status=$(echo "$status" | xargs)
  generated+=("$gen")
  [ "$auth" != "-" ] && authorities+=("$auth")
done
is_authority() { local f=$1 a; for a in "${authorities[@]}"; do [ "$f" = "$a" ] && return 0; done; return 1; }
is_listed() { local f=$1 g; for g in "${generated[@]}"; do [[ "$f" == $g ]] && return 0; done; return 1; }
looks_generated() { [[ "$1" == *FixtureData* || "$1" == */golden/* || "$1" == *.snapshot || "$1" == native/*/fixtures/* ]]; }
red=0
for commit in $(git rev-list --reverse "$range"); do
  mapfile -t files < <(git diff-tree --no-commit-id --name-only -r "$commit")
  auth_files=() ; impl_files=() ; unlisted=()
  for f in "${files[@]}"; do
    is_authority "$f" && auth_files+=("$f")
    case "$f" in Kernel/*|Compiler/*|Host/*|Theory/*|native/*) is_authority "$f" || impl_files+=("$f");; esac
    if looks_generated "$f" && ! is_listed "$f" && ! is_authority "$f"; then unlisted+=("$f"); fi
  done
  subject=$(git log -1 --format=%s "$commit")
  if [ ${#auth_files[@]} -gt 0 ]; then
    trailer=$(git log -1 --format=%B "$commit" | grep -m1 '^Authority-Change:' || true)
    echo "fixture-authority: AUTHORITY CHANGE $commit ${auth_files[*]} -- ${trailer:-<no trailer>} ($subject)"
    if [ ${#impl_files[@]} -gt 0 ]; then
      echo "fixture-authority: RED $commit changes the authority (${auth_files[*]}) AND the implementation (${impl_files[*]:0:5}...) in one commit" >&2
      red=1
    fi
    if [ -z "$trailer" ]; then
      echo "fixture-authority: RED $commit changes an authority without an Authority-Change: trailer" >&2
      red=1
    fi
  fi
  if [ ${#unlisted[@]} -gt 0 ]; then
    echo "fixture-authority: RED $commit changes generated-looking files with no row in fixture-authorities.txt: ${unlisted[*]}" >&2
    red=1
  fi
done
[ $red = 0 ] && echo "fixture-authority: OK over $range"
exit $red
