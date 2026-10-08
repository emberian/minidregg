#!/usr/bin/env bash
# Separate memory scopes preserve other rows if one retained history OOMs.
set -euo pipefail
if [[ $# -lt 3 || $# -gt 4 ]]; then
  echo 'usage: replay-totality-stores.sh RUNNER STORES.json NEW_OUTPUT [--plant-drop-absent|--plant-absent-refuses]' >&2
  exit 2
fi
runner=$1 stores=$2 output=$3
plant=()
if [[ $# == 4 ]]; then
  case $4 in --plant-drop-absent|--plant-absent-refuses) plant=("$4") ;; *) exit 2 ;; esac
fi
[[ ! -e $output && ! -L $output ]] || { echo 'output must be new' >&2; exit 2; }
mkdir -m 700 -- "$output"
status=0 total=0 oks=0 refusals=0
for row in activity objectrecord call send seats domain upgrade; do
  jq --arg row "$row" '[.[] | select(.row == $row)]' "$stores" >"$output/$row.json"
  unit="kp-$(basename "$output")-$row-$$"
  if systemd-run --user --scope --unit "$unit" -q -p MemoryMax=10G -p MemorySwapMax=0 \
      "$runner" "${plant[@]}" --row "$row" "$output/$row.json" \
      >"$output/$row.out" 2>"$output/$row.err"; then
    rc=0
  else
    rc=$?
  fi
  # Count flushed lines even when a capped process could not print a summary.
  read -r n ok refused < <(awk '$3 == "ok" { ok++ } $3 == "refusal" { refused++ }
    END { print ok+refused,ok+0,refused+0 }' "$output/$row.out")
  if [[ $rc != 0 ]]; then
    scopeResult=$(systemctl --user show "$unit.scope" -p Result --value 2>/dev/null) || scopeResult=unavailable
    if [[ $rc == 137 || $scopeResult == oom-kill ]]; then
      printf 'REPLAY %s oom\n' "$row" >&2
    elif [[ $refused -gt 0 && $n -gt 0 ]] && rg -q "^ROW $row " "$output/$row.out"; then
      printf 'REPLAY %s refused\n' "$row" >&2
    else
      printf 'REPLAY %s failed %s\n' "$row" "$rc" >&2
    fi
    status=1
  fi
  if ! rg -q "^ROW $row " "$output/$row.out"; then
    printf 'REPLAY %s incomplete\n' "$row" >&2
    status=1
  fi
  if [[ $n == 0 ]]; then status=1; fi
  awk '$1 != "ROW" && $1 != "TOTAL" { print }' "$output/$row.out"
  printf 'ROW %s %s ok %s refused %s\n' "$row" "$n" "$ok" "$refused"
  cat "$output/$row.err" >&2
  total=$((total+n)) oks=$((oks+ok)) refusals=$((refusals+refused))
done
printf 'TOTAL %s ok %s refused %s\n' "$total" "$oks" "$refusals"
exit "$status"
