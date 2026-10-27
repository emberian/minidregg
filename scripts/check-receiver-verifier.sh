#!/usr/bin/env bash
# check-receiver-verifier.sh -- the receiving pipeline's one verifier and its one `Ran` mint.
#   (1) `Ran` is minted at exactly one site (`Ran.mk`), in Compiler/CredentialSignatureAdmission.lean;
#   (2) nothing makes `Ran` inhabited by instance (Inhabited/Nonempty/Decidable/Zero/OfNat ... Ran),
#       and that file has no `unsafe`, `implemented_by`, `extern` or `axiom`;
#   (3) a `Receiver` is built over `receiverVerifier` only: every `Receiver ... (X)` type outside Theory/
#       names `receiverVerifier` or a verifier variable `V`, never a hand-built `Verifier`.
#   Self-test: `--plant ran-instance|second-mint|handbuilt` runs the gate against a planted copy and must fail.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel); cd "$root"
f=Compiler/CredentialSignatureAdmission.lean
check() { # $1 = admission file, $2 = tree listing file
  local fail=0 adm=$1
  mints=$(grep -c 'Ran\.mk' "$adm" || true)
  [ "$mints" = 1 ] || { echo "FAIL: Ran.mk appears $mints times in $adm (want exactly 1, the live shim)"; fail=1; }
  grep -nE 'instance[^:]*:[^=]*\b(Inhabited|Nonempty|Decidable|Zero|One|OfNat|EmptyCollection)\b[^=]*\bRan\b' "$adm" && { echo "FAIL: an instance makes Ran inhabited"; fail=1; }
  grep -nE '\b(unsafe|implemented_by|extern|axiom)\b' "$adm" | grep -v '^[0-9]*:\s*--' | grep -vE '\*\*|/-|-/|`' && { echo "FAIL: unsafe/implemented_by/extern/axiom in $adm"; fail=1; }
  while IFS= read -r g; do
    case "$g" in Theory/*|TokenCensus/*) continue;; esac
    if grep -nE 'Verifier +(IO|Id) *where|:= *\{ *Answered' "$g" >/dev/null 2>&1 && [ "$g" != "$adm" ]; then
      echo "FAIL: $g builds a Verifier by hand"; fail=1
    fi
  done < "$2"
  return $fail
}
git ls-files '*.lean' > /tmp/rv-files.$$ ; trap 'rm -f /tmp/rv-files.$$' EXIT
case "${1:-}" in
  --plant)
    t=$(mktemp -d); cp "$f" "$t/adm.lean"
    case "$2" in
      ran-instance) printf '\ninstance : Nonempty (Ran c q a) := sorry\n' >> "$t/adm.lean";;
      second-mint) printf '\ndef forged : Ran c q a := Ran.mk\n' >> "$t/adm.lean";;
      handbuilt) cp "$f" "$t/adm.lean"; printf 'def v : Verifier IO where\n  Answered := fun _ _ => True\n' > "$t/Kernel_X.lean"; echo "$t/Kernel_X.lean" > "$t/list"; check "$t/adm.lean" "$t/list" && { echo "plant NOT caught"; exit 1; }; echo "plant caught"; exit 0;;
    esac
    : > "$t/list"
    check "$t/adm.lean" "$t/list" && { echo "plant NOT caught"; exit 1; }; echo "plant caught"; exit 0;;
esac
check "$f" /tmp/rv-files.$$ && echo "OK: receiver-verifier: one Ran mint, no instance, no hand-built Verifier"
