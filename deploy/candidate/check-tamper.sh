#!/usr/bin/env bash
# Exercise the same run.sh refusal M7 requires. Candidate stays untouched.
# Usage: check-tamper.sh CANDIDATE NEW_EVIDENCE_DIR
set -euo pipefail
candidate=$(realpath "${1:?candidate}")
work=${2:?new evidence directory}
[ ! -e "$work" ]
mkdir -p "$work/candidate"
work=$(realpath "$work")
c=$work/candidate
cp -a --reflink=auto "$candidate/bin" "$c/bin"
for f in run.sh lib.sh genesis.sh genesis-params.example.json provenance.json manifest.json; do
  cp "$candidate/$f" "$c/$f"
done
# Relocate only absolute runtime references; outputs retain their relative paths and pins.
python3 - "$candidate" "$c" <<'PY'
import json,sys,pathlib
old,new=sys.argv[1:];p=pathlib.Path(new)/'manifest.json'
def relocate(v):
 if isinstance(v,str) and v.startswith(old+'/'):return new+v[len(old):]
 if isinstance(v,dict):return {k:relocate(x) for k,x in v.items()}
 if isinstance(v,list):return [relocate(x) for x in v]
 return v
p.write_text(json.dumps(relocate(json.loads(p.read_text())),indent=2)+'\n')
PY
# Use a non-core binary: removing whole-family verification must be observable
# even when the four Store-role pins and the state's Host pin still agree.
binary=$c/bin/grain-runtime
before=$(sha256sum "$binary" | cut -d' ' -f1)
chmod u+w "$binary"
python3 - "$binary" <<'PY'
import sys
with open(sys.argv[1],'r+b') as f:
 f.seek(64);b=f.read(1);assert len(b)==1
 f.seek(64);f.write(bytes([b[0]^1]))
PY
after=$(sha256sum "$binary" | cut -d' ' -f1)
[ "$before" != "$after" ] || { echo 'tamper mutation did not change sha256' >&2; exit 1; }
printf 'binary grain-runtime sha256 mismatch: manifest %s, file %s\n' "$before" "$after" >"$work/expected.txt"
# A state descriptor is sufficient: refusal must precede mini serve / Store I/O.
s=$work/state
mkdir -p "$s/deployment" "$s/public" "$s/tmp"
jq -n --arg m "$c/manifest.json" --arg h "$(jq -r .sha256.host "$c/manifest.json")" \
  '{type:"minidregg-candidate-state-v1",manifest:$m,hostSha256:$h}' >"$s/state.json"
jq -n --arg store "$c/bin/minidregg-link-sqlite-store" --arg verifier "$c/bin/minidregg-credential-signature-verifier" \
  '{storageBinary:$store,signatureBinary:$verifier}' >"$s/deployment/pinned-config.json"
for verb in init serve; do
  args=(--state "$s")
  if [ "$verb" = init ]; then args=(--manifest "$c/manifest.json" --params "$c/genesis-params.example.json" --state "$work/new-state"); fi
  if timeout 20 "$c/run.sh" "$verb" "${args[@]}" >"$work/$verb.log" 2>&1; then
    echo "M7: tamper $verb accepted binary grain-runtime" >&2; exit 1
  fi
  if ! grep -F -f "$work/expected.txt" "$work/$verb.log"; then
    echo "M7: tamper $verb did not refuse binary grain-runtime with named sha256 mismatch" >&2; exit 1
  fi
done
[ ! -e "$work/new-state" ] || { echo 'M7: tamper init created state before refusing' >&2; exit 1; }
echo 'M7: tamper init and serve refused binary grain-runtime'
