#!/usr/bin/env bash
# check-fn-wire.sh — fn's exported wire grammar (protocol/fn/wire-grammar.json, fn
# specs/wire-grammar.json at the revision Compiler/FnWirePinned.lean pins) read by Mini's ONE
# interpreter of the language (Compiler/FnWireGrammar.lean; round trips in FnWireRoundTrip).
#
#   1. Compiler/FnWirePinned.lean re-elaborates against the vendored bytes: the file's BLAKE3
#      is the pinned digest, every vector gets exactly the decoder answer the file prints
#      (value, consumed, rest; or the refusal word), fncu.cursor is the grammar Mini runs,
#      and three planted faults are refused (#assert_compiled on each).
#   2. The driver run on the vendored file prints OK (pinned).
#   3. Controls, each asserting first that its mutation happened: one vector's `consumed`
#      off by one, one accepted vector's `rest` changed, one trailer refusal renamed
#      `malformed` -> RED naming the fault (unpinned); the same mutated file pinned -> RED by
#      digest; the unmutated copy unpinned -> OK.
#   4. With FN_REPO set (an fn clone holding the pinned revision): the vendored file is
#      byte-identical to `git show REV:specs/wire-grammar.json`. Without it, says so.
# Exit status: the number of failed checks. Run after the lake-build gate (needs the oleans).
set -uo pipefail
cd "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)" || exit 1
export PATH=$HOME/.elan/bin:$PATH
file=protocol/fn/wire-grammar.json
drv=scripts/check-fn-wire.lean
tmp=$(mktemp -d "${TMPDIR:-/tmp}/check-fn-wire.XXXXXX"); trap 'rm -rf "$tmp"' EXIT
red=0
fail() { echo "check-fn-wire: FAIL $*"; red=$((red + 1)); }
ok() { echo "check-fn-wire: ok   $*"; }

if lake env lean Compiler/FnWirePinned.lean >"$tmp/pinned.log" 2>&1 && [ ! -s "$tmp/pinned.log" ]; then
  ok "Compiler/FnWirePinned.lean elaborates silently (digest, vectors, fncu.cursor, three teeth)"
else
  cat "$tmp/pinned.log"; fail "Compiler/FnWirePinned.lean"
fi

run() { lake env lean --run "$drv" "$@" 2>&1; }
out=$(run "$file"); rc=$?
echo "$out"
if [ "$rc" = 0 ] && grep -q '^fn-wire: OK .* pinned fn ' <<<"$out"; then ok "vendored file, pinned"; else fail "vendored file (rc=$rc)"; fi

mutate() { # NAME OLD NEW -> $tmp/NAME.json with the FIRST occurrence of OLD replaced
  python3 - "$file" "$tmp/$1.json" "$2" "$3" <<'PY'
import sys
src, dst, old, new = sys.argv[1:]
text = open(src, encoding="utf-8").read()
assert text.count(old) >= 1, "mutation target absent: " + old
out = text.replace(old, new, 1)
assert out != text
open(dst, "w", encoding="utf-8").write(out)
PY
}
control() { # NAME OLD NEW EXPECT
  if ! mutate "$1" "$2" "$3"; then fail "control $1: could not plant the fault"; return; fi
  cmp -s "$file" "$tmp/$1.json" && { fail "control $1: mutation did not happen"; return; }
  local o r
  o=$(run "$tmp/$1.json" --unpinned); r=$?
  if [ "$r" != 0 ] && grep -q "^fn-wire: RED .*$4" <<<"$o"; then ok "control $1 refused: $o"
  else fail "control $1 not refused as '$4' (rc=$r): $o"; fi
  o=$(run "$tmp/$1.json"); r=$?
  if [ "$r" != 0 ] && grep -q '^fn-wire: RED digest' <<<"$o"; then ok "control $1 pinned: refused by digest"
  else fail "control $1 pinned not refused by digest (rc=$r): $o"; fi
}
control consumed '"consumed":32,' '"consumed":33,' 'consumed'
control rest '"rest":""' '"rest":"00"' 'rest'
control word '"refused":"trailer"' '"refused":"malformed"' 'refused trailer where the file says malformed'
cp "$file" "$tmp/copy.json"
o=$(run "$tmp/copy.json" --unpinned); r=$?
if [ "$r" = 0 ] && grep -q '^fn-wire: OK ' <<<"$o"; then ok "control copy (unmutated, unpinned) passes"; else fail "control copy (rc=$r): $o"; fi

rev=$(sed -n 's/^def pinnedRevision : String := "\([0-9a-f]*\)"$/\1/p' Compiler/FnWirePinned.lean)
[ -n "$rev" ] || fail "no pinnedRevision in Compiler/FnWirePinned.lean"
if [ -n "${FN_REPO:-}" ]; then
  if git -C "$FN_REPO" show "$rev:specs/wire-grammar.json" >"$tmp/fn.json" 2>"$tmp/fn.err" && cmp -s "$tmp/fn.json" "$file"; then
    ok "vendored file is fn $rev:specs/wire-grammar.json byte for byte"
  else
    cat "$tmp/fn.err"; fail "vendored file differs from fn $rev:specs/wire-grammar.json ($FN_REPO)"
  fi
else
  echo "check-fn-wire: fn source NOT compared (FN_REPO unset); the pinned digest stands for it"
fi
[ "$red" = 0 ] && echo "check-fn-wire: PASS" || echo "check-fn-wire: $red FAILED"
exit "$red"
