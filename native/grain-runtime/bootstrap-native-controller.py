#!/usr/bin/env python3
"""Fresh native manager qualification setup; no controller/provider/worker launch.

Uses the source jpay6 genesis/birth/delegation segment, not a copied genesis codec.
Leaves all services stopped. Run as the intended service UID; ROOT must not exist.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def write(path, value):
    with open(path, 'x') as f:
        json.dump(value, f, indent=2)
        f.write('\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ('root', 'repo', 'host', 'mini', 'store', 'verifier', 'runtime'):
        parser.add_argument('--' + flag, required=True, type=Path)
    parser.add_argument('--base', required=True)
    parser.add_argument('--tool-workspace', action='store_true')
    a = parser.parse_args()
    if not a.base.isdecimal() or str(int(a.base)) != a.base or int(a.base) <= 12:
        parser.error('--base must be canonical decimal above reserved fixture IDs 0..12')
    for flag in ('root', 'repo', 'host', 'mini', 'store', 'verifier', 'runtime'):
        path = getattr(a, flag)
        if not path.is_absolute() or '..' in path.parts or str(path) != os.path.normpath(str(path)):
            parser.error('--' + flag + ' must be canonical absolute path')
    if a.root.exists() or a.root.is_symlink():
        parser.error('ROOT must not exist; retained state is never overwritten')
    # Linux sockaddr_un includes the terminating NUL; leave room for all retained
    # controller sockets, not only the Host socket used during bootstrap.
    if len(os.fsencode(a.root / 'controller/state/control.sock')) >= 100:
        parser.error('ROOT is too long for native Unix sockets; choose a shorter owned path')
    source = a.repo / 'native/resource-client/journey.d/jpay6.sh'
    raw = source.read_text()
    begin = 'python3 - "$DIR" <<\'PY\'\n'
    end = '# ---------------------------------------------------------------- Host plumbing'
    if raw.count(begin) != 1 or raw.count(end) != 1:
        parser.error('source jpay6 extraction seam changed; inspect rather than guess')
    code = raw.split(begin, 1)[1].split(end, 1)[0]
    # Current native genesis declares clock enrollment and retained tail bound.
    # Keep the source birth/codec path; retain the exact transformed code hash.
    anchor = 'json.dump(genesis, open(path("genesis.json"), "w"), indent=1)'
    if code.count(anchor) != 1:
        parser.error('source genesis publication seam changed; inspect rather than guess')
    code = code.replace(anchor, 'genesis["clockTickers"] = []\ngenesis["tailBound"] = "256"\n' + anchor, 1)
    artifacts = {name: {'path': str(getattr(a, name)), 'sha256': digest(getattr(a, name))}
                 for name in ('host', 'mini', 'store', 'verifier', 'runtime')}
    for name in artifacts:
        if not os.access(getattr(a, name), os.X_OK):
            parser.error(name + ' must be executable')
    source_sha = digest(source)
    os.umask(0o077)
    a.root.mkdir(mode=0o700)
    (a.root / 'bootstrap-extracted.py').write_text(code)
    write(a.root / 'bootstrap-source.json', {
        'type': 'mini-native-controller-fixture-source-v1', 'source': str(source),
        'sourceSha256': source_sha, 'extractedSha256': digest(a.root / 'bootstrap-extracted.py'),
        'artifacts': artifacts, 'base': a.base, 'serviceUid': os.geteuid(),
        'providerCalls': 0, 'controllerStarted': False,
        'scope': 'jpay6 genesis, native birth and four delegations only; unused provider grain exists'})
    os.environ.update(HOST=str(a.host), MINI=str(a.mini), STORE=str(a.store), VERIFIER=str(a.verifier),
                      GRAIN=str(a.runtime), REPO=str(a.repo), JPAY6_BASE=a.base,
                      TEST_PROVIDER='UNUSED', HERMES_STANDIN='UNUSED', LAUNCH_GATE='UNUSED')
    sys.argv = [str(a.root / 'bootstrap-extracted.py'), str(a.root)]
    ns = {'__name__': '__native_controller_fixture__'}
    exec(compile(code, str(a.root / 'bootstrap-extracted.py'), 'exec'), ns)
    if ns['born'].get('type') != 'confirmed' or any(x.get('type') != 'confirmed' for x in ns['delegations']):
        raise SystemExit('native birth/delegation refused; retained exact artifacts, no retry')
    state = a.root / 'controller/state'
    state.mkdir(parents=True, mode=0o700)
    cfg = {'mini': str(a.mini), 'host': str(a.host), 'hostConfig': ns['CONFIG'], 'hostSocket': ns['SOCKET'],
           'controlSocket': str(state / 'control.sock'), 'custodyKey': str(a.root / 'keys/7.key'),
           'stateDir': str(state), 'cwd': str(a.root), 'task': a.base, 'subject': '7',
           'capability': '71', 'queryCapability': '71', 'policyControlCapability': '72',
           'toolTask': {'task': str(int(a.base) + 1), 'subject': '8', 'capability': '81',
                        'queryCapability': '81', 'custodyKey': str(a.root / 'keys/8.key'),
                        'parentCapability': '73', 'parentObserveCapability': '73',
                        'reserve': '2', 'charge': '1', 'allowedPublications': []}, 'commands': []}
    if a.tool_workspace:
        ws = state / 'resource-workspace'
        command = [str(a.mini), 'workspace', '--action', 'init', '--host', str(a.host),
                   '--config', ns['CONFIG'], '--socket', ns['SOCKET'], '--key', str(a.root / 'keys/8.key'),
                   '--subject', '8', '--dir', str(ws)]
        result = subprocess.run(command, capture_output=True)
        (a.root / 'workspace.stdout').write_bytes(result.stdout)
        (a.root / 'workspace.stderr').write_bytes(result.stderr)
        if result.returncode:
            raise SystemExit('tool workspace init failed; inspect retained workspace.stderr')
        cfg['toolTask']['resourceWorkspace'] = str(ws)
    config = a.root / 'controller.json'
    write(config, cfg)
    write(a.root / 'host-profile.json', ns['profile'])
    for item in artifacts.values():
        if digest(item['path']) != item['sha256']:
            raise SystemExit('pinned binary changed during bootstrap; refuse ready publication')
    if digest(source) != source_sha:
        raise SystemExit('source changed during bootstrap; refuse ready publication')
    ready = {'type': 'mini-native-controller-fixture-ready-v1', 'root': str(a.root),
             'controllerConfig': str(config), 'stateDir': str(state), 'task': a.base,
             'toolTask': str(int(a.base) + 1), 'keys': str(a.root / 'keys'),
             'hostConfig': ns['CONFIG'], 'hostSocket': ns['SOCKET'],
             'hostProfile': str(a.root / 'host-profile.json'), 'source': str(a.root / 'bootstrap-source.json'),
             'hostCommand': [str(a.mini), 'serve', '--host', str(a.host), '--config', ns['CONFIG'], '--socket', ns['SOCKET']],
             'controllerCommand': [str(a.runtime), 'serve', str(config)],
             'controllerUnit': 'mini-grain-controller@' + a.base + '.service',
             'providerConfigured': False, 'allServicesStopped': True}
    write(a.root / 'ready.json', ready)
    print(json.dumps(ready))


if __name__ == '__main__':
    main()
