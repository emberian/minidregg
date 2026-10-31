#!/usr/bin/env python3
"""Untrusted physical stage adapter. Mini retains admission and authority.

Consumes a verified legacy source-map stage and one pinned Rust distribution;
creates a fresh stage for the existing signer and independent package inspector.
No source stage, shared dataset, private state or signing key is modified.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile

_spec = importlib.util.spec_from_file_location('oracle_stage', Path(__file__).with_name('stage.py'))
stage = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(stage)

LAUNCH = '''#!/usr/bin/python3.12
"""Untrusted process supervisor; Mini owns fd3 and authority."""
import os, socket, sys
from lifecycle import supervise
if len(sys.argv) != 1:
    raise SystemExit("launcher accepts no arguments")
with socket.fromfd(3, socket.AF_UNIX, socket.SOCK_STREAM) as connection:
    if connection.getsockopt(socket.SOL_SOCKET, socket.SO_TYPE) != socket.SOCK_STREAM or not isinstance(connection.getpeername(), (str, bytes)):
        raise SystemExit("fd3 must be the supervisor Unix stream")
os.chdir("/var")
os.umask(0o077)
sys.exit(supervise(
    ["/usr/bin/python3.12", "-I", "-B", "-S", "/opt/oracle-host/bin/oracle-host",
     "--state-root", "/var/oracle-host", "--port", "7070"],
    ["/opt/oracle-bin/minidregg-oracle-appliance", "--port", "7070"]))
'''


def relocate(value, mappings):
    if isinstance(value, dict):
        return {k: relocate(v, mappings) for k, v in value.items()}
    if isinstance(value, list):
        return [relocate(v, mappings) for v in value]
    if isinstance(value, str):
        for old, new in sorted(mappings.items(), key=lambda row: -len(row[0])):
            if value == old or value.startswith(old + '/'):
                return new + value[len(old):]
    return value


def adapt(source, source_sha, payload, payload_sha, mappings, target, resources=()):
    if target.exists() or target.is_symlink():
        raise ValueError('target must be new')
    receipt = stage.pinned_json(source / 'STAGE.json', source_sha)
    if stage.verify_stage(source) != receipt:
        raise ValueError('stage changed')
    manifest = stage.pinned_json(payload / 'MANIFEST.json', payload_sha)
    if manifest.get('schema') != 'oracle-host-distribution-v1':
        raise ValueError('expected coherent Rust distribution')
    entries = stage.inventory(payload)
    files = {p: e for p, e in entries.items() if e['kind'] == 'file' and p != 'MANIFEST.json'}
    if set(files) != set(manifest['files']) or any(e['kind'] == 'symlink' for e in entries.values()):
        raise ValueError('payload has extra, missing or symlink files')
    for p, e in files.items():
        stage.name(p)
        if (e['sha256'], e['size']) != (manifest['files'][p]['sha256'], manifest['files'][p]['bytes']):
            raise ValueError('payload changed: ' + p)
    stage.linux_binary(payload / 'lib/oracle-host')
    if not files.get('lib/oracle-host', {}).get('executable'):
        raise ValueError('Rust host must be executable')
    for old, new in mappings.items():
        if not old.startswith('/') or not new.startswith('/') or '..' in Path(new).parts:
            raise ValueError('mapping must use absolute non-traversing paths')
    manifest = relocate(manifest, mappings)
    config = relocate(json.loads((payload / 'host.template.json').read_text()), mappings)
    # External files must already be signed members or the pinned public dataset.
    expected = dict(receipt['expected_package_entries'])
    admitted_resources = []
    for resource in resources:
        source_path = Path(resource['path'])
        destination_path = resource['destination']
        if not destination_path.startswith('/opt/oracle-resources/'):
            raise ValueError('resource destination must be under /opt/oracle-resources/')
        relative = stage.name(destination_path.lstrip('/'))
        if relative in expected:
            raise ValueError('resource collides with existing signed member')
        stage.pinned(source_path, resource['sha256'])
        entry = {'kind': 'file', 'sha256': resource['sha256'],
                 'size': source_path.stat().st_size, 'executable': False}
        expected[relative] = entry
        admitted_resources.append((source_path, relative, resource['sha256']))
    shared = {row['path']: row for row in (receipt.get('shared_data') or {}).get('files', [])}
    for row in manifest['external_files']:
        path = row['path']
        entry = expected.get(path.lstrip('/'))
        if path.startswith('/opt/oracle-data/'):
            entry = shared.get(path[len('/opt/oracle-data/'):])
        if not entry or entry.get('sha256') != row['sha256']:
            raise ValueError('external file is not admitted by base stage: ' + path)
        if row.get('invocation') and row['invocation'] != path:
            raise ValueError('use the signed regular interpreter path, not a venv alias')
    with tempfile.TemporaryDirectory(prefix='.oracle-rust-stage-', dir=target.parent) as temporary:
        output = Path(temporary) / 'stage'
        shutil.copytree(source, output, symlinks=True)
        image = output / 'image'
        destination = image / 'opt/oracle-host'
        if destination.exists():
            raise ValueError('Rust payload already present')
        shutil.copytree(payload, destination)
        (destination / 'host.template.json').write_text(json.dumps(config, sort_keys=True, indent=2) + '\n')
        manifest['files']['host.template.json']['sha256'] = stage.digest(destination / 'host.template.json')
        manifest['files']['host.template.json']['bytes'] = (destination / 'host.template.json').stat().st_size
        (destination / 'MANIFEST.json').write_text(json.dumps(manifest, sort_keys=True, indent=2) + '\n')
        binary = image / 'opt/oracle-bin'
        shutil.copyfile(binary / 'launch.py', binary / 'lifecycle.py')
        (binary / 'launch.py').write_text(LAUNCH)
        for source_path, relative, sha256 in admitted_resources:
            resource_path = image / relative
            resource_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source_path, resource_path)
            resource_path.chmod(0o444)
            stage.pinned(resource_path, sha256)
        generated = stage.inventory(image)
        stage.require_spk_members(generated)
        receipt['expected_package_entries'].update(generated)
        receipt['package_sources'].update({p: {'root': 'image', 'path': p} for p in generated})
        (output / 'files.list').write_text('\n'.join(sorted(receipt['expected_package_entries'])) + '\n')
        receipt['rust_host'] = {'manifest_sha256': payload_sha, 'path_mappings': mappings,
                                'source_stage_sha256': source_sha, 'private_state': '/var/oracle-host',
                                'resources': list(resources)}
        receipt['generated_files'] = stage.inventory(output)
        receipt['generated_files'].pop('STAGE.json', None)
        (output / 'STAGE.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
        stage.publish(output, target)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for key in ('stage', 'payload', 'path-map', 'target'):
        ap.add_argument('--' + key, type=Path, required=True)
    for key in ('stage-sha256', 'payload-sha256'):
        ap.add_argument('--' + key, required=True)
    ap.add_argument('--resources', type=Path, help='JSON list of explicit path/sha256/destination inputs')
    a = ap.parse_args()
    adapt(a.stage, a.stage_sha256, a.payload, a.payload_sha256,
          json.loads(a.path_map.read_text()), a.target,
          json.loads(a.resources.read_text()) if a.resources else ())
    print(json.dumps({'stage': str(a.target), 'signed': False, 'receiving_qualified': False}))


if __name__ == '__main__':
    main()
