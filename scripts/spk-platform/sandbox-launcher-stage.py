#!/usr/bin/env python3
"""Stage a source-pinned launcher for one declared app UID; never launch an SPK.

Root FRAME MANIFEST APP_UID stages immutable bytes, a narrow AppArmor attachment,
and runs only an isolated /usr/bin/true namespace probe as that exact app user.
Profile/candidate admission and failed START reconciliation are separate steps.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import pwd
import re
import secrets
import stat
import subprocess

def require(value, message):
    if not value:
        raise RuntimeError(message)
def digest(data):
    return hashlib.sha256(data).hexdigest()
def root_path(path, directory=False):
    p = Path(path)
    require(p.is_absolute() and p.resolve() == p, 'root path must be canonical')
    for entry in [p, *p.parents]:
        m = entry.lstat()
        require(m.st_uid == 0 and not m.st_mode & 0o022 and not stat.S_ISLNK(m.st_mode), 'root custody differs')
    require(p.is_dir() if directory else p.is_file(), 'root object kind differs')
    if not directory:
        require(p.stat().st_nlink == 1, 'root file must have one link')
    return p

def selected(frame, manifest, broker, uid, account):
    require(frame.is_absolute() and re.fullmatch(r'/var/lib/mini-[A-Za-z0-9_-]+', str(frame)), 'isolated Mini frame required')
    require(uid in broker['appUids'] and account.pw_uid == uid and account.pw_gid == uid and uid != 0,
            'exact declared app UID/GID required')
    source = Path(manifest['bwrap'])
    launcher = frame / 'usr/local/libexec' / ('app-' + str(uid)) / 'mini-grain-bwrap'
    name = 'mini-frame-bwrap-' + digest(str(frame).encode())[:12] + '-' + str(uid)
    policy = Path('/etc/apparmor.d') / name
    text = ('# Exact source-pinned isolated Mini app launcher.\nabi <abi/4.0>,\ninclude <tunables/global>\n\n'
            + 'profile ' + name + ' ' + str(launcher) + ' flags=(unconfined) {\n  userns,\n}\n')
    return source, launcher, policy, text.encode()

def publish(path, data, mode, gid=0):
    if path.exists() or path.is_symlink():
        root_path(path)
        m = path.stat()
        require(path.read_bytes() == data and stat.S_IMODE(m.st_mode) == mode and m.st_gid == gid,
                'retained launcher artifact differs; preserve original')
        return
    temporary = path.parent / ('.' + path.name + '.stage-' + secrets.token_hex(8))
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, mode)
    with os.fdopen(fd, 'wb') as out:
        os.fchown(out.fileno(), 0, gid)
        os.fchmod(out.fileno(), mode)
        out.write(data); out.flush(); os.fsync(out.fileno())
    os.link(temporary, path)
    temporary.unlink()
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)

def run(frame, manifest_path, uid):
    require(os.geteuid() == 0, 'root staging required')
    root_path(frame, True)
    manifest_path = root_path(manifest_path)
    require(manifest_path.is_relative_to(frame / 'var/lib/mini/candidate'), 'manifest outside isolated frame candidate')
    broker_path = root_path(frame / 'etc/mini/spk-broker.json')
    manifest, broker = [json.loads(p.read_text()) for p in (manifest_path, broker_path)]
    account = pwd.getpwuid(uid)
    source, launcher, policy, policy_bytes = selected(frame, manifest, broker, uid, account)
    binary = root_path(source).read_bytes()
    require(digest(binary) == manifest['sha256']['bwrap'] and binary.startswith(b'\x7fELF'), 'source launcher bytes differ')
    lock = frame / 'etc/mini/.sandbox-launcher-stage.lock'
    fd = os.open(lock, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'r+') as held:
        root_path(lock)
        fcntl.flock(held.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        for directory in (frame / 'usr/local/libexec', launcher.parent, frame / 'etc/mini/sandbox-launchers'):
            if not directory.exists():
                directory.mkdir(mode=0o755)
                directory.chmod(0o755)  # root staging runs with a private umask
            root_path(directory, True)
            require(stat.S_IMODE(directory.stat().st_mode) == 0o755, 'launcher directory traversal mode differs')
        # Operator opens read-only before drop; only this app group executes.
        publish(launcher, binary, 0o754, uid)
        publish(policy, policy_bytes, 0o644)
        subprocess.run(['/sbin/apparmor_parser', '-r', str(policy)], check=True, timeout=30)
        argv = ['/usr/bin/setpriv', '--reuid=' + str(uid), '--regid=' + str(uid),
                '--clear-groups', '--no-new-privs', '--inh-caps=-all', '--ambient-caps=-all', '--bounding-set=-all',
                '--', str(launcher), '--unshare-all', '--die-with-parent', '--ro-bind', '/', '/', '--', '/usr/bin/true']
        probe = subprocess.run(argv, capture_output=True, text=True, timeout=30)
        result = {'protocol': 'mini-app-sandbox-launcher-stage-v2', 'frame': str(frame), 'uid': uid, 'gid': uid,
                  'source': str(source), 'bwrap': str(launcher), 'bwrapSha256': digest(binary),
                  'manifest': str(manifest_path), 'manifestSha256': digest(manifest_path.read_bytes()),
                  'brokerSha256': digest(broker_path.read_bytes()), 'policy': str(policy), 'policySha256': digest(policy_bytes),
                  'probe': {'argv': argv, 'exitCode': probe.returncode, 'stderr': probe.stderr[-1000:]},
                  'profileAdmission': 'pending; no profile/candidate or lifecycle operation changed'}
        require(probe.returncode == 0, 'app namespace/exec probe failed; original source claim remains untouched: ' + probe.stderr[-1000:])
        receipt = frame / 'etc/mini/sandbox-launchers' / (str(uid) + '-nnp.json')
        publish(receipt, (json.dumps(result, sort_keys=True, indent=2) + '\n').encode(), 0o600)
        return dict(result, receipt=str(receipt))

if __name__ == '__main__':
    os.umask(0o077)
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('frame', type=Path); p.add_argument('manifest', type=Path); p.add_argument('uid', type=int)
    a = p.parse_args()
    print(json.dumps(run(a.frame, a.manifest, a.uid)))
