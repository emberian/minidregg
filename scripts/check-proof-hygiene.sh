#!/usr/bin/env bash
# Fail closed when a tracked Lean source prints an axiom footprint without a
# `#guard_msgs` expectation.  A bare `#print axioms` is diagnostic output only:
# the build stays green if the footprint later grows.  The guarded form turns
# that footprint into a regression gate.
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd -P)
if repo_root=$(git -C "$script_dir" rev-parse --show-toplevel 2>/dev/null); then
  in_git_worktree=true
else
  repo_root=$(cd "$script_dir/.." && pwd -P)
  in_git_worktree=false
fi
cd "$repo_root"

scan_file() {
  local file=$1
  awk '
    BEGIN {
      previous = ""; failed = 0
      # `open Foo in #print axioms x` and `set_option ... in #print axioms x` print too
      print_axioms = "^[[:space:]]*((open|set_option|attribute|variable|universe)[^#]*[[:space:]]in[[:space:]]+)*#print[[:space:]]+axioms([[:space:]]|$)"
      # an axiom declaration behind any modifier or attribute: `private axiom`, `@[simp] axiom`, ...
      axiom_decl = "^[[:space:]]*(/--.*-/[[:space:]]*)?((@\\[[^]]*\\]|private|protected|noncomputable|unsafe|partial|nonrec)[[:space:]]+)*axiom[[:space:]]"
    }
    $0 ~ print_axioms {
      # the expectation is an `#guard_msgs ... in` COMMAND on the line above, not a
      # comment that mentions it, and not a guard of some other command
      guarded_here = ($0 ~ /#guard_msgs/)
      guarded_above = (previous ~ /^[[:space:]]*#guard_msgs([^[:alnum:]_].*)?[[:space:]]in[[:space:]]*$/)
      if (!guarded_here && !guarded_above) {
        printf "%s:%d: bare #print axioms: %s\n", FILENAME, FNR, $0
        failed = 1
      }
    }
    $0 ~ axiom_decl {
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
printf '%s\n' 'private axiom fixture : True' > "$self_test_root/axiom-private.lean"
printf '%s\n' '@[simp] axiom fixture : True' > "$self_test_root/axiom-attr.lean"
printf '%s\n' 'noncomputable axiom fixture : True' > "$self_test_root/axiom-noncomputable.lean"
printf '%s\n' 'open Nat in #print axioms fixture' > "$self_test_root/bare-open-in.lean"
printf '%s\n' '-- a #guard_msgs expectation used to be here' '#print axioms fixture' > "$self_test_root/bare-after-comment.lean"
printf '%s\n' '#guard_msgs in #eval 1' '#print axioms fixture' > "$self_test_root/bare-after-other-guard.lean"

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
for evasion in axiom-private axiom-attr axiom-noncomputable bare-open-in bare-after-comment bare-after-other-guard; do
  if scan_file "$self_test_root/$evasion.lean" >/dev/null 2>&1; then
    echo "proof-hygiene: self-test failed to detect: $evasion" >&2
    exit 1
  fi
done

status=0
file_count=0
print_count=0
if $in_git_worktree; then
  file_stream=(git ls-files -z -- '*.lean')
else
  file_stream=(find . -path './.lake' -prune -o -type f -name '*.lean' -print0)
fi
while IFS= read -r -d '' file; do
  file_count=$((file_count + 1))
  count=$(awk 'BEGIN { print_axioms = "^[[:space:]]*((open|set_option|attribute|variable|universe)[^#]*[[:space:]]in[[:space:]]+)*#print[[:space:]]+axioms([[:space:]]|$)" }
    $0 ~ print_axioms { n++ }
    END { print n + 0 }' "$file")
  print_count=$((print_count + count))
  scan_file "$file" || status=1
done < <("${file_stream[@]}")

if [[ "$status" -ne 0 ]]; then
  echo 'proof-hygiene: FAILED' >&2
  exit "$status"
fi

printf 'proof-hygiene: PASS (%d tracked Lean files, %d guarded axiom footprints)\n' \
  "$file_count" "$print_count"
