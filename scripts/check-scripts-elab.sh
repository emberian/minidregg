#!/usr/bin/env bash
# scripts/check-scripts-elab.sh : every standalone Lean script (git ls-files scripts/**.lean native/**.lean)
# elaborates against this tree's build (`lake env lean <file>`; nothing is run unless the file runs
# it at elaboration). scripts/gates/scripts-elab.tsv is the SHRINK-ONLY list of the exceptions
# (ROOT 10-07, after replay.lean, the fixture generator, sat uncompilable from b21 to b25 unseen):
#   path <TAB> class <TAB> owner <TAB> env <TAB> reason
#   class covered  not elaborated here: a gate row runs it with its environment; the reason names the
#                  check script that does, and that script must mention the file (checked)
#   class env      elaborated with `env` (KEY=VAL ...): must PASS. `-` = no stated values yet:
#                  expected to fail, until the script elaborates without them
#   class stale    expected to fail (it rotted); the owner fixes it or deletes it
#   class unbuilt  expected to fail (imports a module no target builds): add the module to a target,
#                  or delete the script
# RED: a script not listed (or class env with values) that fails; a listed failing script that now
# ELABORATES (remove its line: it may never break again); a listed path that is not tracked.
set -uo pipefail
L=scripts/gates/scripts-elab.tsv; J=${SCRIPTS_ELAB_JOBS:-6}
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
export PATH=$HOME/.elan/bin:$PATH
declare -A cls envv
red=0; n=0
while IFS=$'\t' read -r p c o e r; do
  [ -z "$p" ] || [[ $p == \#* ]] && continue
  case "$c" in covered|env|stale|unbuilt) ;; *) echo "scripts-elab: RED $L: $p: class '$c' is not covered|env|stale|unbuilt"; red=1; continue ;; esac
  [ -n "$o" ] && [ -n "$r" ] || { echo "scripts-elab: RED $L: $p: owner and reason are required"; red=1; }
  git ls-files --error-unmatch -- "$p" >/dev/null 2>&1 || { echo "scripts-elab: RED $p is listed but not tracked: remove its line"; red=1; continue; }
  if [ "$c" = covered ]; then
    by=$(grep -oE 'scripts/[A-Za-z0-9_./-]+\.sh' <<<"$r" | head -1)
    if [ -z "$by" ] || ! grep -qF "$(basename "$p")" "$by" 2>/dev/null; then
      echo "scripts-elab: RED $p: covered, but its reason names no check script that runs it ($by)"; red=1
    fi
  fi
  cls[$p]=$c; envv[$p]=$e
done < "$L"
# Library roots that scripts import but the umbrella does not build. Building them here is the
# check that their sources compile at all (SimplexQualification: the explicit qualification roots
# scripts/lean-build-surfaces.py reads; report-simplex-qualification.lean imports it; Verify: the
# qualification fixtures, e.g. Verify.ResourceReserveBirthFixture that scripts/kn2/neutral-birth.lean
# imports). A root that does not build is RED by name, not a cascade of per-script failures.
for t in ${SCRIPTS_ELAB_ROOTS:-SimplexQualification Compiler.QualificationReport Verify}; do
  if ! lake build "$t" >"$out/root-$t.log" 2>&1; then
    echo "scripts-elab: RED library root $t does not build: $(grep -m1 'error' "$out/root-$t.log" | cut -c1-220)"; red=1
  fi
done
mapfile -t files < <(git ls-files 'scripts/**.lean' 'native/**.lean' | sort)
for f in "${files[@]}"; do
  [ "${cls[$f]:-}" = covered ] && continue
  e=${envv[$f]:--}; [ "$e" = - ] && e=""
  printf '%s\t%s\n' "$f" "$e"
done | xargs -P "$J" -d '\n' -I{} bash -c '
  f=${1%%$'"'"'\t'"'"'*}; e=${1#*$'"'"'\t'"'"'}; o='"$out"'/$(echo "$f" | tr / _)
  if env $e timeout 900 lake env lean "$f" >"$o.log" 2>&1; then echo PASS >"$o.v"; else echo FAIL >"$o.v"; fi' _ {}
for f in "${files[@]}"; do
  c=${cls[$f]:-}; [ "$c" = covered ] && continue
  o=$out/$(echo "$f" | tr / _); v=$(cat "$o.v" 2>/dev/null || echo FAIL); n=$((n+1))
  expect=PASS; case "$c" in stale|unbuilt) expect=FAIL ;; env) [ "${envv[$f]}" = - ] && expect=FAIL ;; esac
  if [ "$v" = FAIL ] && [ "$expect" = PASS ]; then
    echo "scripts-elab: RED $f does not elaborate: $(grep -m1 'error' "$o.log" | sed "s#^$PWD/##" | cut -c1-220)"; red=1
  elif [ "$v" = PASS ] && [ "$expect" = FAIL ]; then
    echo "scripts-elab: RED $f elaborates now: remove its line from $L (the list only shrinks)"; red=1
  fi
done
listed=$(grep -cvE '^(#|$)' "$L")
echo "scripts-elab: $n elaborated, $listed listed exceptions: $([ $red = 0 ] && echo PASS || echo RED)"
exit $red
