#!/usr/bin/env bash
# FD-1 R4a journey: for every retained Store in STORES.json ({row, config}),
# process 1 exports the Store as a Turn log (and checks the World it folds
# against the Store's own cells, spent set and height); process 2 reads ONLY
# genesis.bin + turns.bin (no Store, no post image), folds, and must print the
# same ROOT.  Plant: one byte of one entry flipped -> the follower must STOP at
# that entry's height, by name.  Any refusal, mismatch or missing ROOT fails.
set -euo pipefail
if [[ $# != 3 ]]; then echo 'usage: turn-log-follower.sh EXE STORES.json NEW_OUTPUT' >&2; exit 2; fi
exe=$1 stores=$2 out=$3
[[ -x $exe ]] || { echo 'exe not executable' >&2; exit 2; }
[[ ! -e $out ]] || { echo 'output must be new' >&2; exit 2; }
mkdir -m 700 -- "$out"
n=$(jq length "$stores")
[[ $n -gt 0 ]] || { echo 'no stores' >&2; exit 1; }
status=0 checked=0
for i in $(seq 0 $((n - 1))); do
  row=$(jq -r ".[$i].row" "$stores") config=$(jq -r ".[$i].config" "$stores")
  d=$out/$i-$row
  if ! "$exe" export "$config" "$d" >"$d.export" 2>&1; then
    printf 'ROW %s %s export-failed: %s\n' "$i" "$row" "$(tail -1 "$d.export")"; status=1; continue
  fi
  want=$(awk '$1 == "ROOT" { print $2 }' "$d.export")
  "$exe" follow "$d" >"$d.follow" 2>&1 || true
  got=$(awk '$1 == "ROOT" { print $2 }' "$d.follow")
  if [[ -n $want && $want == "$got" ]]; then
    printf 'ROW %s %s PASS %s\n' "$i" "$row" "$(grep '^EXPORT' "$d.export")"
    checked=$((checked + 1))
  else
    printf 'ROW %s %s FAIL want=%s got=%s %s\n' "$i" "$row" "$want" "$got" "$(tail -1 "$d.follow")"; status=1
  fi
done
# Plant on the first exported log with at least one turn: flip the last byte of
# the framed log (inside the last entry) and require a STOP at the last height.
for d in "$out"/*/; do
  turns=$(awk '$1 == "EXPORT" { print $3 }' "${d%/}.export" 2>/dev/null || true)
  [[ -n $turns && $turns -gt 0 ]] || continue
  p=$out/plant; cp -r "$d" "$p"
  python3 -c 'import sys; p=sys.argv[1]; b=bytearray(open(p,"rb").read()); b[-1]^=0xff; open(p,"wb").write(b)' "$p/turns.bin"
  "$exe" follow "$p" >"$p.follow" 2>&1 || true
  if grep -qE "^STOP (undecodable|refused) $((turns - 1))( |$)" "$p.follow"; then
    printf 'PLANT tamper-last-entry RED-AS-EXPECTED %s\n' "$(head -1 "$p.follow")"
  else
    printf 'PLANT tamper-last-entry NOT-CAUGHT %s\n' "$(head -1 "$p.follow")"; status=1
  fi
  # Plant 2: the follower is handed the log without entry 0 (every Store's first
  # turn writes cells a later turn guards): it must STOP at height 0 -- a digest
  # guard that no longer matches its world reads as undecodable, a value guard
  # as refused -- and never reach a root.
  "$exe" follow "$d" --plant-drop 0 >"$p.drop" 2>&1 || true
  if grep -qE "^STOP (undecodable|refused) 0( |$)" "$p.drop"; then
    printf 'PLANT drop-entry-0 RED-AS-EXPECTED %s\n' "$(head -1 "$p.drop")"
  else
    printf 'PLANT drop-entry-0 NOT-CAUGHT %s\n' "$(head -1 "$p.drop")"; status=1
  fi
  break
done
[[ $checked -gt 0 ]] || status=1
printf 'TOTAL stores %s pass %s\n' "$n" "$checked"
exit "$status"
