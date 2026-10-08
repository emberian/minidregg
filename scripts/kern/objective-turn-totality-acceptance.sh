#!/usr/bin/env bash
# Actual receiving-path logs plus two refusal plants and the empty-run pole.
set -euo pipefail
if [[ $# -lt 3 || $# -gt 5 ]]; then
  echo 'usage: objective-turn-totality-acceptance.sh --lane-builds RUST_TARGET LEAN_BIN' >&2
  echo '       objective-turn-totality-acceptance.sh --recorded ROOT RUNNER' >&2
  echo '       objective-turn-totality-acceptance.sh BIN MANIFEST RUNNER [HOST [CONSENT]]' >&2
  exit 2
fi
src=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
mkdir -p "$src/.lake"
evidence=$(mktemp -d "$src/.lake/kp.XXXXXX")
printf 'EVIDENCE %s\n' "$evidence"
host=()
recorded=
if [[ $1 == --recorded ]]; then
  [[ $# == 3 ]] || exit 2
  recorded=$2 runner=$3
elif [[ $1 == --lane-builds ]]; then
  [[ $# == 3 ]] || exit 2
  rust=$2/release lean=$3
  bin=$evidence/lane-bin
  mkdir -m 700 -- "$bin"
  for name in mini minidregg-link-sqlite-store minidregg-credential-signature-verifier; do
    [[ -x $rust/$name ]] || { echo "missing lane Rust binary $name" >&2; exit 1; }
    cp -L --reflink=auto -- "$rust/$name" "$bin/$name"
  done
  for name in minidregg-host minidregg-client-consent objective-turn-totality; do
    [[ -x $lean/$name ]] || { echo "missing lane Lean binary $name" >&2; exit 1; }
    cp -L --reflink=auto -- "$lean/$name" "$bin/$name"
  done
  manifest=$evidence/lane-manifest.json
  jq -n --arg sourceCommit "$(git -C "$src" rev-parse HEAD)" \
    --arg bin "$bin" '{sourceCommit:$sourceCommit,bin:$bin,kind:"lane-builds"}' >"$manifest"
  sha256sum "$bin"/* >"$evidence/lane-binary-sha256"
  runner=$bin/objective-turn-totality
else
  bin=$1 manifest=$2 runner=$3
  if [[ $# -ge 4 ]]; then host=(--host "$4"); fi
  if [[ $# == 5 ]]; then host+=(--consent "$5"); fi
fi
status=0
if [[ -n $recorded ]]; then
  stores=$recorded/stores.json
  baselineErr=$evidence/normal.err
  if bash "$src/scripts/kern/replay-totality-stores.sh" "$runner" "$stores" \
      "$evidence/normal" >"$evidence/normal.out" 2>"$baselineErr"; then
    printf 'NORMAL replay ok\n'
  else
    status=1
  fi
  [[ -s $recorded/journeys-ok ]] || status=1
  cat "$evidence/normal.out"
  cat "$baselineErr" >&2
elif bash "$src/scripts/kern/objective-turn-totality.sh" --bin "$bin" \
    --manifest "$manifest" --runner "$runner" "${host[@]}" --root "$evidence/r" \
    >"$evidence/journey.out" 2>"$evidence/journey.err"; then
  printf 'NORMAL ok\n'
else
  rc=$?
  printf 'NORMAL failed %s (retained partial logs will still be measured)\n' "$rc"
  status=1
fi
if [[ -z $recorded ]]; then
  stores=$evidence/r/stores.json
  baselineErr=$evidence/r/totality.err
  cat "$evidence/journey.out"
  cat "$evidence/journey.err" >&2
fi

for plant in drop-absent absent-refuses; do
  if bash "$src/scripts/kern/replay-totality-stores.sh" "$runner" "$stores" \
      "$evidence/plant-$plant" "--plant-$plant" \
      >"$evidence/$plant.out" 2>"$evidence/$plant.err"; then
    rc=0
  else
    rc=$?
  fi
  printf 'PLANT %s exit %s\n' "$plant" "$rc"
  cat "$evidence/$plant.out"
  cat "$evidence/$plant.err" >&2
  if [[ $rc != 1 ]]; then status=1; fi
  if rg -q 'replay-error|REPLAY .* (oom|incomplete|failed)' "$evidence/$plant.err"; then status=1; fi
done

# P1 must flag exactly every normal turn carrying absence pins, per row.
if awk '
  FNR == NR && $1 == "COVERAGE" { expected[$2] = $8; pins += $8; next }
  FNR != NR && $3 == "refusal" && $4 == "pin-missing" { actual[$1]++ }
  END {
    good = (pins > 0)
    for (row in expected) {
      printf "PIN-PLANT %s expected %d refused %d\n", row, expected[row], actual[row]
      if (expected[row] != actual[row]) good = 0
    }
    exit !good
  }' "$baselineErr" "$evidence/drop-absent.out"; then
  printf 'PIN-PLANT detected\n'
else
  printf 'PIN-PLANT blind or incomplete\n' >&2
  status=1
fi
if rg -q '^.+ [0-9]+ refusal .*retiredCell' "$evidence/absent-refuses.out"; then
  printf 'REFUSAL-PLANT detected\n'
else
  printf 'REFUSAL-PLANT blind\n' >&2
  status=1
fi
printf '[]\n' >"$evidence/empty.json"
if systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 \
    "$runner" "$evidence/empty.json" >"$evidence/empty.out" 2>"$evidence/empty.err"; then
  rc=0
else
  rc=$?
fi
printf 'EMPTY exit %s\n' "$rc"
if [[ $rc != 1 ]]; then status=1; fi
cat "$evidence/empty.out"
cat "$evidence/empty.err" >&2
exit "$status"
