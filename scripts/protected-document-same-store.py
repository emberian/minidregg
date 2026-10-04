#!/usr/bin/env python3
"""Run protected document receiving on supplied, existing member custody."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess

def check(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def validate(binding):
    check(binding['protocol'] == 'mini-protected-same-store-v1', 'binding validation failed')
    manifest_path = Path(binding['manifestPath']).resolve(strict=True)
    check(digest(manifest_path) == binding['manifestSha256'], 'manifest changed')
    manifest = read(manifest_path)
    for role in ('host', 'mini'):
        executable = Path(manifest[role]).resolve(strict=True)
        check(digest(executable) == manifest['sha256'][role], f'{role} changed')
        check(os.access(executable, os.X_OK), f'{role} is not executable')
    config = Path(binding['configPath']).resolve(strict=True)
    socket = Path(binding['socketPath'])
    check(socket.is_socket(), 'supplied service socket missing')
    store = Path(binding['storePath']).resolve(strict=True)
    check(store.is_dir(), 'supplied Store missing')
    actors = {}
    roles = ('owner', 'member') + tuple((role for role in ('reader', 'reviewer') if role in binding))
    for role in roles:
        selected = binding[role]
        workspace = Path(selected['workspace']).resolve(strict=True)
        home = Path(selected['home']).resolve(strict=True)
        state = read(workspace / 'workspace.json')
        check(Path(state['config']).resolve(strict=True) == config, f'{role} config differs')
        check(state['socket'] == str(socket), f'{role} socket differs')
        check(Path(state['host']).resolve(strict=True) == Path(manifest['host']).resolve(strict=True), f'{role} Host differs')
        # workspace.json names its Host by path only (no hash field); the pin is
        # checked on the bytes that path resolves to.
        check(digest(Path(state['host']).resolve(strict=True)) == manifest['sha256']['host'], f'{role} Host pin differs')
        # Optional room-key cache input belongs to other receiving consumers;
        # protected documents use their native private storage.key.
        password = selected.get('cachePassphraseFile')
        if password:
            password = Path(password).resolve(strict=True)
            check(password.stat().st_mode & 0o077 == 0, f'{role} passphrase permissions')
            check(password.read_text().strip(), f'{role} empty passphrase')
        actors[role] = (workspace, home, state['subject'], password)
    check(len({a[2] for a in actors.values()}) == len(actors), 'members must be distinct')
    check(len({a[0] for a in actors.values()}) == len(actors), 'workspaces must be distinct')
    return (manifest, config, socket, store, actors)

def run(binding_path, output, script):
    binding_bytes = binding_path.read_bytes()
    binding = json.loads(binding_bytes)
    manifest, config, socket, store, actors = validate(binding)
    # Retained local names fence a failed invocation against fresh reauthoring.
    for workspace, home, _, _ in actors.values():
        for name in ('pd-paper', 'pd-paper-catalog'):
            check(not (workspace / 'refs' / f'{name}.json').exists(), f'protected receiving reference already present: {name}')
        for directory in (workspace / 'proposals', workspace / 'attempts', home / 'requests'):
            if directory.exists():
                check(not any((p.name.startswith('pd-') for p in directory.iterdir())), f'protected receiving names already present: {directory}')
    output.mkdir(mode=0o700, parents=True, exist_ok=True)
    check(output.stat().st_mode & 0o077 == 0, 'receiving output must be private')
    with (output / 'receiving.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        saved = output / 'binding.json'
        if saved.exists():
            check(saved.read_bytes() == binding_bytes, 'receiving binding changed')
        else:
            with saved.open('xb') as stream:
                stream.write(binding_bytes)
            saved.chmod(0o600)
        env = os.environ.copy()
        env.update(MINI=manifest['mini'], HOST=manifest['host'], CONFIG=str(config), SOCKET=str(socket), JOURNEY_RUN=str(output), JOURNEY_STEP_DIR=str(output / 'protected'), JOURNEY_WORLD=str(store.parent), PD_STORE_DIR=str(store), PD_DOCUMENT='pd-paper', PD_CATALOG='pd-paper-catalog')
        # Only native commands create the protected device keys and journal.
        paths = []
        subjects = {}
        for role in ('owner', 'member'):
            workspace, home, subject, password = actors[role]
            env.update({f'PD_{role.upper()}_WS': str(workspace), f'PD_{role.upper()}_HOME': str(home)})
            paths.extend([str(workspace / 'protected-documents'), str(home / 'requests')])
            subjects[role] = subject
        (output / 'protected').mkdir(mode=0o700, exist_ok=True)
        report = {'protocol': 'mini-protected-same-store-result-v1', 'manifestSha256': binding['manifestSha256'], 'bindingSha256': hashlib.sha256(binding_bytes).hexdigest(), 'runnerSha256': digest(script), 'subjects': subjects, 'configPath': str(config), 'socketPath': str(socket), 'storePath': str(store), 'statePaths': paths, 'nativeCliOnly': True, 'restrictedSshUnlockQualified': False, 'bootstrap': False, 'serviceRestart': False, 'state': 'running'}
        report_path = output / 'result.json'
        report_path.write_text(json.dumps(report, indent=2) + '\n')
        with (output / 'receiving.log').open('w') as log:
            result = subprocess.run([str(script)], env=env, stdout=log, stderr=subprocess.STDOUT)
        report.update(state='passed' if result.returncode == 0 else 'failed', exitCode=result.returncode)
        report_path.write_text(json.dumps(report, indent=2) + '\n')
        return result.returncode
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binding', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    os.umask(0o077)
    script = Path(__file__).resolve().with_name('protected-document-journey.sh')
    raise SystemExit(run(args.binding, args.output, script))
