#!/usr/bin/env bash
# Audit the candidate workspace resolution before accepting a shared lock.
set -euo pipefail
work=${1:?new audit directory}
repo=$(git rev-parse --show-toplevel)
[ ! -e "$work" ]
mkdir -p "$work/src"
git archive "${2:-e0a8ba21a39d92b470cc331fd16ea0408f608b1f}" >"$work/source.tar"
tar -xf "$work/source.tar" -C "$work/src"
python3 - "$work/src" <<'PY'
import sys,pathlib,tomllib,json
s=pathlib.Path(sys.argv[1])
names=['resource-client','hyperdocument-link-sqlite-store','credential-signature-verifier','grain-runtime','inference-scheduler','spk-host','discord-entrance','pay-watcher','mini-keys','mini-sdk','compatible-upgrade-custody','signed-api-path','spk-rpc']
(s/'Cargo.toml').write_text('[workspace]\nresolver = "2"\nmembers = '+json.dumps(['native/'+n for n in names])+'\n')
# Most comprehensive old lock, so Cargo preserves existing versions when possible.
p=s/'native/hyperdocument-link-sqlite-store/Cargo.toml'
p.write_text(p.read_text().replace('libc = "=0.2.186"','libc = "=0.2.189"'))
p=s/'native/resource-client/Cargo.toml'
p.write_text(p.read_text().replace('sha3 = "=0.10.8"','sha3 = "=0.10.9"'))
(s/'Cargo.lock').write_bytes((s/'native/resource-client/Cargo.lock').read_bytes())
PY
cd "$work/src"
rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
cargo "+$rust" metadata --offline --format-version 1 >"$work/metadata.json"
cargo "+$rust" update --offline -p sha3 --precise 0.10.9
python3 - "$work" <<'PY'
import sys,pathlib,tomllib,json
w=pathlib.Path(sys.argv[1]);s=w/'src'
new=tomllib.loads((s/'Cargo.lock').read_text())['package']
ids=lambda ps:{(p['name'],p['version'],p.get('source','')) for p in ps}
newids=ids(new); rows=[]
for member in tomllib.loads((s/'Cargo.toml').read_text())['workspace']['members']:
 p=s/member/'Cargo.lock'
 if not p.exists():continue
 oldids=ids(tomllib.loads(p.read_text())['package'])
 for n,v,source in sorted(oldids-newids):
  rows.append({'member':member,'name':n,'old':v,'new':sorted(p['version'] for p in new if p['name']==n and p.get('source','')==source)})
(w/'drift.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2));print('workspace-lock-audit: '+str(len(rows))+' old package identities absent from root lock')
PY
