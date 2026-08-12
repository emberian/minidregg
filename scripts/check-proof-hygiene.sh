#!/usr/bin/env bash
# Fail closed when a tracked Lean source prints an axiom footprint without a
# `#guard_msgs` expectation.  A bare `#print axioms` is diagnostic output only:
# the build stays green if the footprint later grows.  The guarded form turns
# that footprint into a regression gate.
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

scan_file() {
  local file=$1
  awk '
    BEGIN { previous = ""; failed = 0 }
    /^[[:space:]]*#print[[:space:]]+axioms([[:space:]]|$)/ {
      guarded_here = ($0 ~ /#guard_msgs/)
      guarded_above = (previous ~ /#guard_msgs/)
      if (!guarded_here && !guarded_above) {
        printf "%s:%d: bare #print axioms: %s\n", FILENAME, FNR, $0
        failed = 1
      }
    }
    /^[[:space:]]*axiom[[:space:]]/ {
      printf "%s:%d: project axiom declaration: %s\n", FILENAME, FNR, $0
      failed = 1
    }
    { previous = $0 }
    END { exit failed }
  ' "$file"
}

self_test_root=$(mktemp -d "${TMPDIR:-/tmp}/minidregg-proof-hygiene.XXXXXXXX")
trap 'rm -rf "$self_test_root"' EXIT
printf '%s\n' \
  "/-- info: 'fixture' depends on axioms: [propext] -/" \
  '#guard_msgs (whitespace := lax) in #print axioms fixture' \
  > "$self_test_root/guarded.lean"
printf '%s\n' '#print axioms fixture' > "$self_test_root/bare.lean"
printf '%s\n' 'axiom fixture : True' > "$self_test_root/axiom.lean"

scan_file "$self_test_root/guarded.lean" >/dev/null || {
  echo 'proof-hygiene: self-test rejected a guarded footprint' >&2
  exit 1
}
if scan_file "$self_test_root/bare.lean" >/dev/null 2>&1; then
  echo 'proof-hygiene: self-test failed to detect a bare footprint' >&2
  exit 1
fi
if scan_file "$self_test_root/axiom.lean" >/dev/null 2>&1; then
  echo 'proof-hygiene: self-test failed to detect a project axiom' >&2
  exit 1
fi

status=0
file_count=0
print_count=0
while IFS= read -r -d '' file; do
  file_count=$((file_count + 1))
  count=$(awk '/^[[:space:]]*#print[[:space:]]+axioms([[:space:]]|$)/ { n++ }
    END { print n + 0 }' "$file")
  print_count=$((print_count + count))
  scan_file "$file" || status=1
done < <(git ls-files -z -- '*.lean')

if [[ "$status" -ne 0 ]]; then
  echo 'proof-hygiene: FAILED' >&2
  exit "$status"
fi

printf 'proof-hygiene: PASS (%d tracked Lean files, %d guarded axiom footprints)\n' \
  "$file_count" "$print_count"

