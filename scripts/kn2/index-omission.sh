#!/usr/bin/env bash
# Usage: bash scripts/kn2/index-omission.sh [EVIDENCE_DIRECTORY]
# Requires built dependencies (lake build Compiler.DurableIndex). Checks an
# unmodified full-source control, then one mutation in a temporary copy only.
# The actual source and every existing theorem/assertion remain intact.
set -euo pipefail
cd "$(dirname "$0")/../.."
if [[ ${1:-} == --help ]]; then
  sed -n '2,5p' "$0"
  exit 0
fi
out=${1:-$(mktemp -d /tmp/kn2-index-omission.XXXXXX)}
mkdir -p "$out"
out=$(cd "$out" && pwd)
control="$out/index-control.lean"
mutant="$out/index-mutant.lean"
cp Compiler/DurableIndex.lean "$control"
if ! lake env lean "$control" > "$out/control.log" 2>&1; then
  cat "$out/control.log" >&2
  exit 1
fi
if ! lake env lean scripts/kn2/index-omission.lean > "$out/witness.log" 2>&1; then
  cat "$out/witness.log" >&2
  exit 1
fi
printf '%s\n' 'CONTROL: full source and kernel-checked wrong-root absence witness pass'
needle='  insert height store root (keys transactionId nullifiers)'
replacement='  insert height store root (keys transactionId [])'
[[ $(grep -Fxc "$needle" "$control") == 1 ]]
# No declarations or checks are removed: mutate the sole deployed entry point.
awk -v needle="$needle" -v replacement="$replacement" \
  '{ if ($0 == needle) print replacement; else print }' "$control" > "$mutant"
[[ $(grep -Fxc "$replacement" "$mutant") == 1 ]]
if grep -Fxq "$needle" "$mutant"; then
  printf '%s\n' 'FAIL: mutation did not replace the nullifier list' >&2
  exit 1
fi
printf '%s\n' 'PLANTED: IndexRows.apply drops every consumed nullifier'
if lake env lean "$mutant" > "$out/mutant.log" 2>&1; then
  printf '%s\n' 'FAIL: omitted-nullifier mutation compiled' >&2
  exit 1
fi
# Pin the rejection to the unconditional theorem's proof, not an unrelated error.
proof_line=$(awk '/^theorem apply_eq_setAll / { found=1 } found && /  exact insert_eq_setAll/ { print NR; exit }' "$mutant")
[[ -n "$proof_line" ]]
grep -E "index-mutant.lean:${proof_line}:[0-9]+: error" "$out/mutant.log"
printf '%s\n' 'RED: IndexRows.apply_eq_setAll rejects the omitted consumed nullifiers (no SetPreserves premise)'
printf '%s\n' 'WITNESS: the transaction-only root accepts genuine absence of a logically consumed nullifier'
printf 'Evidence: %s\n' "$out"
