#!/usr/bin/env bash
# Remove only run.sh's binary verification in a TEMP COPY; M7's tamper step must go red.
set -euo pipefail
here=$(cd "$(dirname "$0")/../.." && pwd)
source=${1:?built candidate}
out=${2:?new evidence directory}
[ ! -e "$out" ]
mkdir -p "$out"
c=$(mktemp -d "$out/operator.XXXXXX")
# Preserve evidence of the temporary mutation; never edit the original candidate.
cp -a --reflink=auto "$source/bin" "$c/bin"
for f in run.sh lib.sh genesis.sh genesis-params.example.json provenance.json manifest.json; do cp "$source/$f" "$c/$f"; done
chmod u+w "$c/run.sh"
python3 - "$c/run.sh" <<'PY'
import pathlib,sys
p=pathlib.Path(sys.argv[1]);s=p.read_text();call='  candidate_verify_outputs "$CANDIDATE_MANIFEST"'
assert s.count(call)==2,s.count(call)
p.write_text(s.replace(call,'  : # planted: output verification removed'))
PY
[ "$(grep -c 'planted: output verification removed' "$c/run.sh")" = 2 ]
if grep -q 'candidate_verify_outputs' "$c/run.sh"; then echo 'plant: verification survived' >&2; exit 1; fi
# The manifest still refers to source; check-tamper relocates from the original root.
python3 - "$source" "$c" <<'PY'
import json,pathlib,sys
old,new=sys.argv[1:];p=pathlib.Path(new)/'manifest.json'
def move(v):
 if isinstance(v,str) and v.startswith(old+'/'):return new+v[len(old):]
 if isinstance(v,dict):return {k:move(x) for k,x in v.items()}
 return v
p.write_text(json.dumps(move(json.loads(p.read_text())))+'\n')
PY
if "$here/deploy/candidate/check-tamper.sh" "$c" "$out/check" >"$out/check.log" 2>&1; then
  echo 'plant: M7 tamper check accepted removed verification' >&2; exit 1
fi
grep -Fx 'M7: tamper init accepted binary grain-runtime' "$out/check.log"
echo 'plant-m7-no-verification: M7 tamper check went red as required'
