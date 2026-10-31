#!/usr/bin/python3
"""Fixed root setup for a world's isolated test controller, never Store admission.

Invoked only by install-user-world. Supplied programs execute in fixed systemd
units as the operator/controller, never as root. Failed inputs stay where they
were supplied; receipts and immutable configuration revisions remain inspectable.
"""
import base64
import contextlib
import fcntl
import grp
import hashlib
import json
import os
from pathlib import Path
import pwd
import re
import resource
import selectors
import shutil
import signal
import socket
import stat
import struct
import subprocess
import sys
import time

WORLDS = Path('/var/lib/mini-spk-worlds')
REGISTRY = Path('/etc/mini-spk-volumes')
UNITS = Path('/etc/systemd/system')
HISTORY = Path('/var/lib/mini-spk-controller-history')
TOOLS = {'mini_create_application_session', 'mini_oracle_discover', 'mini_oracle_call', 'mini_grain_status'}
# A typed application attachment's tools (and its hidden qualify tool): the controller checks that the
# attachment, its declaration digest and its route exist before it runs anything.
TYPED_TOOL = re.compile('mini_app_[a-z0-9][a-z0-9_]{0,63}')


def allowed_tool(name):
    return name in TOOLS or TYPED_TOOL.fullmatch(name) is not None
FILES = {'controller.json': 524288, 'host-config.json': 1048576,
         **{f'custody/{role}.key': 32 for role in ('controller', 'tool', 'dispatch', 'provider')},
         'state/shared-app-refs/app-birth.bin': 1048576,
         'state/shared-app-refs/bootstrap-ticket.bin': 1048576}
FINAL_FILES = {'state/shared-app-refs/agent-ticket.bin': 1048576,
               **{f'state/oracle-grant/{n}': 1048576 for n in ('seal.json', 'call.bin', 'submit-marker.json', 'receipt.json')}}
BINS = ('grain-runtime', 'mini', 'minidregg-host')
CONSENT_BIN = 'minidregg-client-consent'
ENV = {'PATH': '/usr/sbin:/usr/bin:/sbin:/bin', 'LANG': 'C.UTF-8'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def canonical(value):
    require(isinstance(value, str) and re.fullmatch(r'/[A-Za-z0-9_./-]+', value)
            and all(p not in ('', '.', '..') for p in value[1:].split('/')), 'noncanonical setup path')
    return Path(value)


def run(args, **kwargs):
    return subprocess.run(args, check=True, env=ENV, timeout=60, **kwargs)


def metadata(path, owner=None, mode=None):
    m = path.lstat()
    require(not stat.S_ISLNK(m.st_mode), f'symlink refused: {path}')
    if owner is not None:
        require(m.st_uid == owner, f'owner refused: {path}')
    if mode is not None:
        require(stat.S_IMODE(m.st_mode) == mode, f'mode refused: {path}')
    return m


def ancestry(path, owners):
    for p in reversed((path, *path.parents)):
        m = metadata(p)
        require(stat.S_ISDIR(m.st_mode) and m.st_uid in owners and not m.st_mode & 0o022,
                f'ancestor custody refused: {p}')


def fingerprint(m):
    return (m.st_dev, m.st_ino, m.st_uid, m.st_gid, m.st_mode, m.st_size, m.st_mtime_ns, m.st_ctime_ns)


def read_file(path, owner, maximum, executable=False, allow_empty=False, required_mode=None):
    ancestry(path.parent, {0, owner})
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    try:
        before = os.fstat(fd)
        require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1 and before.st_uid == owner,
                f'regular source custody refused: {path}')
        require(required_mode is None or stat.S_IMODE(before.st_mode) == required_mode,
                f'private source mode refused: {path}')
        require(not before.st_mode & 0o7022 and (allow_empty or before.st_size > 0) and before.st_size <= maximum,
                f'source mode/size refused: {path}')
        require(not executable or before.st_mode & 0o111, f'nonexecutable binary: {path}')
        require('security.capability' not in os.listxattr(fd), f'file capabilities refused: {path}')
        chunks, left = [], maximum + 1
        while left:
            chunk = os.read(fd, min(left, 1024 * 1024))
            if not chunk:
                break
            chunks.append(chunk)
            left -= len(chunk)
        data = b''.join(chunks)
        require(len(data) == before.st_size and fingerprint(before) == fingerprint(os.fstat(fd))
                and fingerprint(before) == fingerprint(path.lstat()), f'source changed while copying: {path}')
        return data
    finally:
        os.close(fd)


def write_new(path, data, uid=0, gid=0, mode=0o600):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, mode)
    try:
        os.fchown(fd, uid, gid)
        os.fchmod(fd, mode)
        with os.fdopen(os.dup(fd), 'wb') as out:
            out.write(data)
            out.flush()
        os.fsync(fd)
    finally:
        os.close(fd)
    d = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(d)
    finally:
        os.close(d)


def sync_directory(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def publish_exact(path, data, uid=0, gid=0, mode=0o600, bound=65536):
    """Publish exact bytes under the held lifecycle lock; retain partial stages.

    A final conflicting file is never overwritten. An unfinished private stage
    can only grow from the exact prefix of these already-bound expected bytes.
    """
    require(len(data) <= bound, 'exact publication exceeds bound')
    maximum = max(1, len(data))
    if path.exists() or path.is_symlink():
        require(read_file(path, uid, maximum, allow_empty=not data, required_mode=mode) == data,
                'exact publication final bytes differ')
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)
        sync_directory(path.parent)
        return
    temporary = path.with_name('.' + path.name + '-publishing')
    if not temporary.exists() and not temporary.is_symlink():
        write_new(temporary, data, uid, gid, mode)
    else:
        prefix = read_file(temporary, uid, maximum, allow_empty=True, required_mode=mode)
        require(data.startswith(prefix), 'exact publication orphan stage conflicts')
        access = os.O_RDONLY if len(prefix) == len(data) else os.O_WRONLY | os.O_APPEND
        fd = os.open(temporary, access | os.O_NOFOLLOW | os.O_CLOEXEC)
        try:
            m = os.fstat(fd); named = temporary.lstat()
            require(stat.S_ISREG(m.st_mode) and m.st_uid == uid and m.st_nlink == 1
                    and stat.S_IMODE(m.st_mode) == mode and m.st_size == len(prefix)
                    and (m.st_dev, m.st_ino) == (named.st_dev, named.st_ino), 'exact publication stage changed')
            offset = len(prefix)
            while offset < len(data):
                written = os.write(fd, data[offset:offset + 65536])
                require(written > 0, 'exact publication made no progress')
                offset += written
            os.fsync(fd)
        finally:
            os.close(fd)
    require(read_file(temporary, uid, maximum, allow_empty=not data, required_mode=mode) == data,
            'exact publication stage differs')
    # Root-private archives, or a stopped controller's private directory, have
    # a single writer under the lifecycle lock. Preserve any unexpected final.
    require(not path.exists() and not path.is_symlink(), 'exact publication final appeared during write')
    os.replace(temporary, path)
    sync_directory(path.parent)


def mkdir(path, uid=0, gid=0, mode=0o700):
    path.mkdir(mode=mode)
    os.chown(path, uid, gid)
    os.chmod(path, mode)


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


# Permanent reservations are intentionally separate from removable controller
# resources. Old resident namespaces can retain a mapping after account removal.
RESERVATIONS = Path('/etc/mini-spk-controller-reservations')
MAX_IDENTITIES = 4096
MAX_ID = 2**32 - 1


def strict_json(data):
    def pairs(items):
        value = {}
        for key, item in items:
            require(key not in value, 'duplicate root identity field')
            value[key] = item
        return value
    return json.loads(data, object_pairs_hook=pairs)


def ident(value, subordinate=False):
    return type(value) is int and (65536 if subordinate else 1) <= value < MAX_ID


def registry_record(path):
    r = strict_json(read_file(path, 0, 65536, required_mode=0o644))
    keys = {'protocol', 'store', 'deploymentId', 'hostId', 'grainsRoot', 'operatorUid', 'operatorGid', 'appUids', 'helper', 'helperSha256'}
    require(isinstance(r, dict) and set(r) == keys and r['protocol'] == 'mini-spk-volume-registry-v1', 'root world registry schema refused')
    require(isinstance(r['store'], str) and re.fullmatch('[0-9a-f]{16}', r['store'])
            and path.name == r['store'] + '.json' and r['grainsRoot'] == str(WORLDS / r['store']), 'world registry path differs')
    require(all(isinstance(r[k], str) and re.fullmatch('[0-9a-f]{64}', r[k]) for k in ('deploymentId', 'hostId', 'helperSha256'))
            and ident(r['operatorUid']) and ident(r['operatorGid']), 'world registry identity malformed')
    require(isinstance(r['helper'], str) and re.fullmatch(r'/usr/local/libexec/mini-spk-volume-helper(?:-[0-9a-f]{16})?', r['helper']), 'world helper path malformed')
    app = r['appUids']
    require(isinstance(app, list) and 1 <= len(app) <= 64 and all(ident(i, True) for i in app)
            and len(set(app)) == len(app) and not set(app) & {r['operatorUid'], r['operatorGid']}, 'world app identity set malformed')
    return r


def namespace_record(r):
    fields = {'protocol', 'store', 'deploymentId', 'hostId', 'operatorUid', 'operatorGid', 'controllerUid', 'controllerGid', 'account'}
    require(isinstance(r, dict) and set(r) == fields and r['protocol'] == 'mini-spk-controller-namespace-v1', 'controller reservation schema refused')
    require(isinstance(r['store'], str) and re.fullmatch('[0-9a-f]{16}', r['store'])
            and r['account'] == 'mini-c-' + r['store'], 'controller reservation name malformed')
    require(all(isinstance(r[k], str) and re.fullmatch('[0-9a-f]{64}', r[k]) for k in ('deploymentId', 'hostId'))
            and all(ident(r[k]) for k in ('operatorUid', 'operatorGid'))
            and all(ident(r[k], True) for k in ('controllerUid', 'controllerGid'))
            and not {r['operatorUid'], r['operatorGid']} & {r['controllerUid'], r['controllerGid']}, 'controller reservation identity malformed')
    return r


def bounded_json_paths(directory):
    try:
        ancestry(directory, {0})
    except FileNotFoundError:
        # Missing fixed directory is the legacy empty case; a dangling symlink
        # or inaccessible existing directory never gets that interpretation.
        require(not directory.exists() and not directory.is_symlink(), 'identity directory custody refused')
        return []
    found = []
    for entry in directory.iterdir():
        if entry.name.endswith('.json'):
            found.append(entry)
            require(len(found) <= MAX_IDENTITIES, 'root identity registry count exceeds bound')
    return sorted(found)


def occupied_ids():
    occupied, reservations = set(), {}
    for path in bounded_json_paths(REGISTRY):
        r = registry_record(path)
        require(not occupied.intersection(r['appUids']), 'root app registries overlap')
        occupied.update(r['appUids'])
        occupied.update((r['operatorUid'], r['operatorGid']))
    for path in bounded_json_paths(RESERVATIONS):
        r = namespace_record(strict_json(read_file(path, 0, 4096, required_mode=0o644)))
        require(path.name == r['store'] + '.json', 'controller reservation filename differs')
        ids = {r['controllerUid'], r['controllerGid']}
        require(not occupied.intersection(ids), 'controller reservation overlaps a world or another reservation')
        occupied.update(ids); reservations[r['store']] = r
    # Existing removed-controller evidence is also a reservation, including
    # receipts from the earlier system-account allocator. Never reclaim it.
    for path in bounded_json_paths(HISTORY):
        h = strict_json(read_file(path, 0, 65536, required_mode=0o600))
        require(isinstance(h, dict) and h.get('removed') is True and isinstance(h.get('receipt'), dict), 'removed controller receipt malformed')
        r = h['receipt']; store = r.get('store')
        require(isinstance(store, str) and re.fullmatch('[0-9a-f]{16}', store) and path.name == store + '.json'
                and r.get('protocol') in ('mini-spk-controller-v1', 'mini-spk-controller-v2') and r.get('name') == 'mini-c-' + store
                and ident(r.get('uid')) and ident(r.get('gid')), 'removed controller identity malformed')
        if store in reservations:
            require((r['uid'], r['gid']) == (reservations[store]['controllerUid'], reservations[store]['controllerGid']), 'removed controller reservation changed')
        else:
            require(not occupied.intersection((r['uid'], r['gid'])), 'removed controller identity overlaps live allocation')
            occupied.update((r['uid'], r['gid']))
    # A pending create has a permanent reservation before any account creation.
    # Older allocations without one must not silently disappear from scanning.
    for path in bounded_json_paths(REGISTRY):
        r = registry_record(path); directory = WORLDS / r['store'] / 'controller'
        if directory.exists() or directory.is_symlink():
            ancestry(directory, {0})
            require(r['store'] in reservations, 'existing/pending controller lacks permanent identity reservation')
    return occupied


def merged(ranges):
    out = []
    for start, end in sorted(ranges):
        if out and start <= out[-1][1]: out[-1] = (out[-1][0], max(out[-1][1], end))
        else: out.append((start, end))
    return out


def subordinate_ranges(path, operator_uid):
    data = read_file(path, 0, 1024 * 1024, allow_empty=True, required_mode=0o644).decode('ascii')
    own, other = [], []
    lines = data.splitlines(); require(len(lines) <= 16384, 'subordinate delegation line bound exceeded')
    for line in lines:
        if not line or line.startswith('#'): continue
        parts = line.split(':')
        require(len(parts) == 3 and re.fullmatch('[A-Za-z0-9_.-]{1,256}', parts[0])
                and re.fullmatch('[0-9]+', parts[1]) and re.fullmatch('[0-9]+', parts[2]), 'subordinate delegation row malformed')
        owner, first, count = parts[0], int(parts[1]), int(parts[2])
        require(0 <= first < MAX_ID and 0 < count <= MAX_ID and first + count <= MAX_ID, 'subordinate delegation range overflows')
        if owner.isascii() and owner.isdecimal(): owner_uid = int(owner)
        else:
            try: owner_uid = pwd.getpwnam(owner).pw_uid
            except KeyError: owner_uid = None
        (own if owner_uid == operator_uid else other).append((first, first + count))
    return merged(own), merged(other)


def intersection(left, right):
    out = []; i = j = 0
    while i < len(left) and j < len(right):
        first, end = max(left[i][0], right[j][0], 65536), min(left[i][1], right[j][1])
        if first < end: out.append((first, end))
        if left[i][1] < right[j][1]: i += 1
        else: j += 1
    return out


def delegated(operator_uid):
    uids, foreign_uids = subordinate_ranges(Path('/etc/subuid'), operator_uid)
    gids, foreign_gids = subordinate_ranges(Path('/etc/subgid'), operator_uid)
    return intersection(uids, gids), merged(foreign_uids + foreign_gids)


def in_ranges(identity, ranges):
    return any(first <= identity < end for first, end in ranges)


def nss_ids():
    users, groups = pwd.getpwall(), grp.getgrall()
    require(len(users) <= 16384 and len(groups) <= 16384, 'NSS identity snapshot bound exceeded')
    return {i for p in users for i in (p.pw_uid, p.pw_gid)} | {g.gr_gid for g in groups}


def nss_free(identity, enumerated=None):
    try: pwd.getpwuid(identity)
    except KeyError: pass
    else: return False
    try: grp.getgrgid(identity)
    except KeyError: pass
    else: return False
    return identity not in (nss_ids() if enumerated is None else enumerated)


def delegation_owners():
    names, ids = set(), set()
    for path in (Path('/etc/subuid'), Path('/etc/subgid')):
        data = read_file(path, 0, 1024 * 1024, allow_empty=True, required_mode=0o644).decode('ascii')
        require(len(data.splitlines()) <= 16384, 'subordinate delegation line bound exceeded')
        for line in data.splitlines():
            if not line or line.startswith('#'): continue
            parts = line.split(':')
            require(len(parts) == 3 and re.fullmatch('[A-Za-z0-9_.-]{1,256}', parts[0]), 'subordinate delegation owner malformed')
            if parts[0].isascii() and parts[0].isdecimal(): ids.add(int(parts[0]))
            else: names.add(parts[0])
    return names, ids


def allocate_identity(operator_uid, account):
    occupied = occupied_ids(); own, foreign = delegated(operator_uid); accounts = nss_ids()
    delegated_names, delegated_ids = delegation_owners()
    require(account not in delegated_names, 'new controller name already has subordinate grants')
    examined = 0
    for first, end in own:
        for identity in range(first, end):
            examined += 1
            require(examined <= 65536, 'controller allocation candidate bound exhausted; no range truncated or reclaimed')
            if identity not in occupied and identity not in delegated_ids and not in_ranges(identity, foreign) and nss_free(identity, accounts):
                return identity
    raise ValueError('no unused controller identity in exclusive delegated UID/GID intersection')


def check_app_allocation(store, helper, op_text, first_text, count_text):
    require(re.fullmatch('[0-9a-f]{16}', store) and re.fullmatch(r'/usr/local/libexec/mini-spk-volume-helper(?:-[0-9a-f]{16})?', helper), 'app allocation coordinates malformed')
    require(all(re.fullmatch('[1-9][0-9]*', s) for s in (op_text, first_text, count_text)), 'app allocation decimal malformed')
    operator, first, count = map(int, (op_text, first_text, count_text))
    require(ident(operator) and ident(first, True) and 2 <= count <= 64 and first + count <= MAX_ID
            and str(operator) == os.environ.get('SUDO_UID', str(operator)), 'app allocation identity/bound refused')
    occupied = occupied_ids(); own, foreign = delegated(operator); accounts = nss_ids()
    def free(start):
        return all(in_ranges(i, own) and not in_ranges(i, foreign) and i not in occupied and nss_free(i, accounts)
                   for i in range(start, start + count))
    # START is where the caller would like the range. Several worlds (and their
    # controller accounts) share one operator's delegated range, so a taken START
    # moves to the next free COUNT-aligned range of the delegation, at or after
    # START first, then from the delegation's beginning; the registry records the
    # range actually allocated. Only a delegation with no free range refuses.
    if not free(first):
        candidates = [c for low, end in own for c in range(low, end - count + 1, count)]
        later = [c for c in candidates if c >= first]
        chosen = next((c for c in later + [c for c in candidates if c < first] if free(c)), None)
        require(chosen is not None, 'app range exhausted: no free %d-identity range in the operator delegated UID/GID intersection' % count)
        first_requested, first = first, chosen
    else:
        first_requested = first
    return {'store': store, 'appRangeRequested': [first_requested, first_requested + count], 'appRangeChecked': [first, first + count]}


def store_context(store, helper):
    require(re.fullmatch('[0-9a-f]{16}', store), 'invalid Store')
    require(re.fullmatch(r'/usr/local/libexec/mini-spk-volume-helper(?:-[0-9a-f]{16})?', helper), 'invalid helper')
    r = registry_record(REGISTRY / (store + '.json'))
    require(r['protocol'] == 'mini-spk-volume-registry-v1' and r['store'] == store and r['helper'] == helper,
            'registered Store/helper differs')
    require(str(r['operatorUid']) == os.environ.get('SUDO_UID', str(r['operatorUid'])), 'caller is not Store operator')
    require(r['operatorUid'] != 0 and pwd.getpwuid(r['operatorUid']).pw_gid == r['operatorGid'], 'operator account differs')
    root = WORLDS / store
    require(r['grainsRoot'] == str(root), 'registered world path differs')
    ancestry(root, {0})
    base = root / 'controller'
    return r, base


def names(store, consent=False, task=None):
    units = [f'mini-grain-controller@{task}.service' if task else f'mini-spk-controller-{store}.service', f'mini-spk-controller-proxy-{store}.socket',
             f'mini-spk-controller-proxy-{store}.service']
    return units + ([f'mini-spk-controller-consent-{store}.socket',
                     f'mini-spk-controller-consent-{store}.service'] if consent else [])


def has_consent(r):
    return r.get('protocol') == 'mini-spk-controller-v2'


def binary_names(r):
    return (*BINS, CONSENT_BIN) if has_consent(r) else BINS


def consent_environment(r, base, pins):
    if not has_consent(r):
        return {}
    home = Path(r['home'])
    return {'MINI_LOCAL_HOST': str(home / 'bin/minidregg-host'),
            'MINI_CONSENT_HOST': str(base / 'bin' / CONSENT_BIN),
            'MINI_CONSENT_CONFIG': str(home / 'host-config.json'),
            'MINI_CONSENT_SOCKET': str(home / 'consent/peer.sock'),
            'MINI_CONSENT_PEER_UID': '0',
            'MINI_CONSENT_SHA256': pins['providerSha256'],
            'MINI_CONSENT_CONFIG_SHA256': pins['configSha256']}



def consent_dependencies(config_bytes, operator):
    """Snapshot the two configured executables; expose only those files through ProtectHome."""
    config = strict_json(config_bytes)
    result = {}
    for role in ('signatureBinary', 'storageBinary'):
        path = canonical(config.get(role))
        owner = metadata(path).st_uid
        require(owner in (0, operator), 'consent dependency owner refused')
        data = read_file(path, owner, 256 * 1024 * 1024, executable=True)
        result[role] = {'path': str(path), 'sha256': sha(data)}
    return result


def consent_storage(config_bytes, operator):
    config = strict_json(config_bytes)
    root = canonical(config.get('storageRoot'))
    require(len(str(root)) <= 4096 and len(root.parts) <= 64, 'consent Store path exceeds bound')
    parent = root.parent
    ancestry(root, {0, operator})
    metadata(parent, operator, 0o700); metadata(root, operator, 0o700)
    require(root.resolve(strict=True) == root, 'consent Store path is not canonical')
    def pin(path):
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC | os.O_NONBLOCK)
        try:
            m = os.fstat(fd)
            require(stat.S_ISREG(m.st_mode) and m.st_nlink == 1 and m.st_uid == operator
                    and stat.S_IMODE(m.st_mode) == 0o600, 'consent Store object custody differs')
            require((m.st_dev, m.st_ino) == (path.lstat().st_dev, path.lstat().st_ino), 'consent Store path changed')
            return {'path': str(path), 'dev': m.st_dev, 'ino': m.st_ino, 'uid': m.st_uid,
                    'gid': m.st_gid, 'mode': 0o600}
        finally:
            os.close(fd)
    directories = []
    for path in reversed((root, *root.parents)):
        m = path.lstat()
        require(stat.S_ISDIR(m.st_mode) and m.st_uid in (0, operator) and not m.st_mode & 0o022,
                'consent Store ancestor changed while pinning')
        directories.append({'path': str(path), 'dev': m.st_dev, 'ino': m.st_ino,
                            'uid': m.st_uid, 'gid': m.st_gid, 'mode': stat.S_IMODE(m.st_mode)})
    database = pin(root / 'forward-link.sqlite3')
    lock_path = Path(str(root) + '.head-anchor.lock')
    lock = pin(lock_path)
    require(lock_path.stat().st_size == 0, 'consent Store anchor lock is not empty')
    anchor = read_file(Path(str(root) + '.head-anchor'), operator, 120, required_mode=0o600)
    require(len(anchor) == 120 and anchor.startswith(b'MINIANC2'), 'consent Store anchor format differs')
    # Source reads legitimately replace this inode when the retained head
    # advances. Pin its private parent and validate its custody/format each use.
    result = {'protocol': 'mini-spk-consent-storage-v1', 'root': str(root),
              'writableParent': str(parent), 'directories': directories,
              'database': database, 'lock': lock, 'replaceableAnchor': str(root) + '.head-anchor'}
    require(len(encoded(result)) <= 32768, 'consent Store custody pins exceed bound')
    return result


def manager_properties(name):
    output = run(['/usr/bin/systemctl', 'show', name, '--property=LoadState,FragmentPath,Transient,User,ActiveState,MainPID,ControlPID,InvocationID'],
                 stdout=subprocess.PIPE).stdout.decode()
    return dict(line.split('=', 1) for line in output.splitlines() if '=' in line)


def load(store, helper):
    registry, base = store_context(store, helper)
    ancestry(base, {0})
    receipt = json.loads(read_file(base / 'receipt.json', 0, 65536))
    require(receipt['protocol'] in ('mini-spk-controller-v1', 'mini-spk-controller-v2') and receipt['store'] == store
            and receipt['operatorUid'] == registry['operatorUid'], 'controller receipt differs')
    require(receipt['name'] == 'mini-c-' + store and receipt['home'] == str(base / 'home')
            and receipt['units'] == names(store, has_consent(receipt), receipt.get('workerTask')), 'controller layout differs')
    account = pwd.getpwnam(receipt['name'])
    require((account.pw_uid, account.pw_gid, account.pw_dir, account.pw_shell) ==
            (receipt['uid'], receipt['gid'], receipt['home'], '/usr/sbin/nologin'), 'controller account changed')
    group = grp.getgrgid(receipt['gid'])
    require(group.gr_name == receipt['name'] and not group.gr_mem, 'controller private group changed')
    require(sum(p.pw_uid == receipt['uid'] for p in pwd.getpwall()) == 1, 'controller UID aliases refused')
    require(receipt['uid'] not in [0, registry['operatorUid'], *registry['appUids']], 'controller UID collision')
    reserved = namespace_record(strict_json(read_file(RESERVATIONS / (store + '.json'), 0, 4096, required_mode=0o644)))
    actual = namespace_record(strict_json(read_file(base / 'namespace.json', 0, 4096, required_mode=0o644)))
    require(reserved == actual and (actual['controllerUid'], actual['controllerGid']) == (receipt['uid'], receipt['gid'])
            and actual['operatorUid'] == registry['operatorUid'] and actual['operatorGid'] == registry['operatorGid']
            and actual['deploymentId'] == registry['deploymentId'] and actual['hostId'] == registry['hostId'], 'controller allocation reservation differs')
    m = metadata(base / 'home', receipt['uid'], 0o700)
    require([m.st_dev, m.st_ino] == receipt['homeIdentity'], 'controller home replaced')
    return registry, base, receipt


def account_defaults():
    # CREATE_MAIL_SPOOL is a useradd defaults-file setting, not a login.defs
    # key accepted by -K. Never change host defaults to provision one account.
    raw = run(['/usr/sbin/useradd', '-D'], stdout=subprocess.PIPE).stdout
    require(len(raw) <= 16384, 'useradd defaults exceed bound')
    defaults = {}
    for line in raw.decode('utf-8').splitlines():
        if not line or line.startswith('#'): continue
        key, separator, value = line.partition('=')
        require(separator and key not in defaults, 'useradd defaults malformed')
        defaults[key] = value
    require(defaults.get('CREATE_MAIL_SPOOL') == 'no' and defaults.get('GROUPS', '') == '',
            'useradd must disable mail spool and implicit supplementary groups')


def create_account(base, name, identity):
    # --system does not grant subuids/subgids; never pass --add-subids-for-system.
    run(['/usr/sbin/useradd', '--system', '--uid', str(identity), '--gid', str(identity),
         '--no-user-group', '--no-create-home', '--no-log-init',
         '--home-dir', str(base / 'home'), '--shell', '/usr/sbin/nologin', name])
    delegated_names, delegated_ids = delegation_owners()
    require(name not in delegated_names and identity not in delegated_ids,
            'created controller unexpectedly has subordinate grants')


def create(store, helper):
    registry, base = store_context(store, helper)
    name = 'mini-c-' + store
    require(not base.exists() and not base.is_symlink(), 'controller resources already exist')
    require(not (HISTORY / (store + '.json')).exists(), 'removed controller identity cannot be silently reused')
    require(not any(p.pw_name == name for p in pwd.getpwall()) and not any(g.gr_name == name for g in grp.getgrall()),
            'controller account/group name already exists')
    account_defaults()
    identity = allocate_identity(registry['operatorUid'], name)
    namespace = {'protocol': 'mini-spk-controller-namespace-v1', 'store': store,
                 'deploymentId': registry['deploymentId'], 'hostId': registry['hostId'],
                 'operatorUid': registry['operatorUid'], 'operatorGid': registry['operatorGid'],
                 'controllerUid': identity, 'controllerGid': identity, 'account': name}
    namespace_record(namespace)
    if not RESERVATIONS.exists(): mkdir(RESERVATIONS, mode=0o755)
    ancestry(RESERVATIONS, {0})
    # Written before either group/account creation. Never deleted on failure or
    # removal: old resident namespaces can retain this mapping indefinitely.
    write_new(RESERVATIONS / (store + '.json'), encoded(namespace), mode=0o644)
    mkdir(base, mode=0o755)
    write_new(base / 'lifecycle.lock', b'controller lifecycle lock\n')
    write_new(base / 'pending.json', encoded({'store': store, 'name': name, 'operatorUid': registry['operatorUid']}))
    run(['/usr/sbin/groupadd', '--system', '--gid', str(identity), name])
    create_account(base, name, identity)
    return finish_create(registry, base, namespace)


def finish_create(registry, base, namespace):
    store, name, identity = namespace['store'], namespace['account'], namespace['controllerUid']
    a = pwd.getpwnam(name)
    require((a.pw_uid, a.pw_gid) == (identity, identity) and a.pw_uid not in [0, registry['operatorUid'], *registry['appUids']], 'allocated controller UID/GID collision')
    require(not any(g.gr_mem and name in g.gr_mem for g in grp.getgrall()), 'controller supplemental groups refused')
    mkdir(base / 'home', a.pw_uid, a.pw_gid)
    mkdir(base / 'listener', registry['operatorUid'], registry['operatorGid'])
    mkdir(base / 'reverse', a.pw_uid, a.pw_gid, 0o711)
    m = (base / 'home').stat()
    receipt = {'protocol': 'mini-spk-controller-v2', 'store': store, 'name': name, 'uid': a.pw_uid, 'gid': a.pw_gid,
               'operatorUid': registry['operatorUid'], 'operatorGid': registry['operatorGid'],
               'home': str(base / 'home'), 'homeIdentity': [m.st_dev, m.st_ino], 'units': names(store, True),
               'activationPeerUid': 0, 'proxyServiceUid': registry['operatorUid'],
               'controllerHome': str(base / 'home'), 'controllerUid': a.pw_uid,
               'listenerSocket': str(base / 'listener/api.sock'), 'reverseSocket': str(base / 'reverse/custody.sock'),
               'operatorSocket': str(base / 'home/operator/mini.sock'), 'operatorPeerUid': 0,
               'consentSocket': str(base / 'home/consent/peer.sock'), 'consentPeerUid': 0}
    write_new(base / 'receipt.json', encoded(receipt))
    write_new(base / 'namespace.json', encoded(namespace), mode=0o644)
    return receipt


def pending_create_identity(registry, base):
    store = registry['store']; name = 'mini-c-' + store
    ancestry(base, {0}); metadata(base, 0, 0o755)
    require(set(p.name for p in base.iterdir()) == {'pending.json', 'lifecycle.lock'},
            'pending controller layout differs; no completed or partial account adoption')
    require(read_file(base / 'lifecycle.lock', 0, 64, required_mode=0o600) == b'controller lifecycle lock\n',
            'pending controller lifecycle lock differs')
    pending = strict_json(read_file(base / 'pending.json', 0, 4096, required_mode=0o600))
    require(pending == {'store': store, 'name': name, 'operatorUid': registry['operatorUid']},
            'pending controller intent differs')
    namespace = namespace_record(strict_json(read_file(RESERVATIONS / (store + '.json'), 0, 4096, required_mode=0o644)))
    require(namespace['store'] == store and namespace['account'] == name
            and all(namespace[key] == registry[key] for key in ('deploymentId', 'hostId', 'operatorUid', 'operatorGid')),
            'pending controller reservation differs from world')
    identity = namespace['controllerUid']
    require(identity == namespace['controllerGid'], 'pending controller UID/GID differ')
    require(not (HISTORY / (store + '.json')).exists(), 'removed controller cannot resume creation')
    occupied_ids()  # Validate all app/reservation records, including collisions.
    own, foreign = delegated(registry['operatorUid'])
    delegated_names, delegated_ids = delegation_owners()
    require(in_ranges(identity, own) and not in_ranges(identity, foreign)
            and name not in delegated_names and identity not in delegated_ids,
            'pending controller delegation changed')
    users, groups = pwd.getpwall(), grp.getgrall()
    require(len(users) <= 16384 and len(groups) <= 16384, 'NSS identity snapshot bound exceeded')
    require(not any(p.pw_name == name or identity in (p.pw_uid, p.pw_gid) for p in users),
            'pending controller account or UID/GID already used')
    for lookup, key in ((pwd.getpwnam, name), (pwd.getpwuid, identity)):
        try: lookup(key)
        except KeyError: pass
        else: raise ValueError('pending controller account already exists')
    matches = [g for g in groups if g.gr_name == name or g.gr_gid == identity]
    require(len(matches) == 1 and matches[0].gr_name == name and matches[0].gr_gid == identity
            and not matches[0].gr_mem, 'pending controller group identity differs')
    for group in (grp.getgrnam(name), grp.getgrgid(identity)):
        require(group.gr_name == name and group.gr_gid == identity and not group.gr_mem,
                'pending controller NSS group differs')
    require(not any(name in g.gr_mem for g in groups), 'pending controller supplemental group refused')
    no_processes(identity)
    for unit in names(store, True):
        require(not (UNITS / unit).exists() and not (UNITS / unit).is_symlink()
                and manager_properties(unit).get('LoadState') == 'not-found', 'pending controller unit already exists')
    return namespace


def resume_create(store, helper):
    registry, base = store_context(store, helper)
    namespace = pending_create_identity(registry, base)
    account_defaults()
    create_account(base, namespace['account'], namespace['controllerUid'])
    result = finish_create(registry, base, namespace)
    return {**result, 'resumedPendingCreation': True}


def no_processes(uid):
    live = []
    for p in Path('/proc').iterdir():
        if p.name.isdecimal():
            try:
                if p.stat().st_uid == uid:
                    live.append(int(p.name))
            except FileNotFoundError:
                pass
    require(not live, f'controller still has processes; preserve resources: {live}')


def unit_bytes(r, base, upstream, consent=None, public=None):
    home = Path(r['home'])
    stem = 'mini-spk-controller-proxy-' + r['store']
    common = ('\nNoNewPrivileges=yes\nPrivateTmp=yes\nProtectSystem=strict\nProtectHome=yes\n'
              'MemoryMax=2G\nMemorySwapMax=0\nCPUQuota=100%\nTasksMax=128\nRuntimeMaxSec=10800\n'
              'TimeoutStopSec=30\nKillMode=control-group\nUMask=0077\n')
    runtime = (f'[Unit]\nDescription=Mini isolated controller {r["store"]}\n[Service]\n'
               f'User={r["uid"]}\nGroup={r["gid"]}\n'
               f'ExecStart={base}/bin/grain-runtime serve {worker_config(r)}\n'
               f'Environment=HOME={home}\nEnvironment=MINI_CONSENT_ANCHOR_DIR={home}/a\nWorkingDirectory={worker_layout(r) if r.get("workerTask") else home / "workspace"}\nReadWritePaths={home} {base}/reverse\n' + common)
    if r.get('workerTask'):
        runtime = worker_runtime_access(runtime.encode(), r).decode()
        runtime += ''.join(f'Environment={key}={value}\n' for key, value in worker_environment(base, r).items())
    if public is not None:
        # The controller may connect to its public relay and provider broker.
        # Bind their private socket directory, preserving each endpoint's UID/ACL.
        runtime = runtime.replace('ProtectHome=yes\n', 'ProtectHome=tmpfs\n')
        runtime += f'BindReadOnlyPaths={public.parent}\n'
    sock = (f'[Unit]\nDescription=Mini controller operator activation {r["store"]}\n[Socket]\n'
            f'ListenStream={home}/operator/mini.sock\n' +
            (f'ListenStream={home}/operator/mini.control\n' if r.get('workerTask') else '') +
            f'SocketUser={r["uid"]}\nSocketGroup={r["gid"]}\n'
            f'SocketMode=0600\nDirectoryMode=0700\nRemoveOnStop=yes\nAccept=no\nService={stem}.service\n')
    proxy = (f'[Unit]\nDescription=Mini fixed operator proxy {r["store"]}\nRequires={stem}.socket\n'
             f'[Service]\nUser={r["operatorUid"]}\nGroup={r["operatorGid"]}\n'
             f'ExecStart={base}/bin/mini serve-agent-operator-proxy --socket {home}/operator/mini.sock '
             f'--upstream {upstream} --config {base}/proxy/config.json --controller-uid {r["uid"]}\n'
             f'BindReadOnlyPaths={upstream.parent}\n' + common.replace('ProtectHome=yes\n', 'ProtectHome=tmpfs\n'))
    values = [runtime, sock, proxy]
    if has_consent(r):
        require(consent is not None, 'consent service pins missing')
        environment = consent_environment(r, base, consent)
        # Values are fixed canonical paths, decimal identities and exact hashes.
        runtime += ''.join(f'Environment={key}={value}\n' for key, value in environment.items())
        values[0] = runtime
        consent_stem = 'mini-spk-controller-consent-' + r['store']
        # An empty home tmpfs permits explicit bind exceptions. ProtectHome=yes
        # mounts inaccessible ancestors: ReadWritePaths cannot unhide the Store,
        # and a verifier can be read through a file bind while exec still fails.
        consent_common = common.replace('ProtectHome=yes\n', 'ProtectHome=tmpfs\n')
        values.append(f'[Unit]\nDescription=Mini controller consent activation {r["store"]}\n[Socket]\n'
                      f'ListenStream={home}/consent/peer.sock\nSocketUser={r["uid"]}\nSocketGroup={r["gid"]}\n'
                      f'SocketMode=0600\nDirectoryMode=0700\nRemoveOnStop=yes\nAccept=no\nService={consent_stem}.service\n')
        values.append(f'[Unit]\nDescription=Mini independent full consent {r["store"]}\nRequires={consent_stem}.socket\n'
                      f'[Service]\nUser={r["operatorUid"]}\nGroup={r["operatorGid"]}\n'
                      f'ExecStart={base}/bin/mini serve-controller-consent --socket {home}/consent/peer.sock '
                      f'--consent {base}/bin/{CONSENT_BIN} --config {base}/consent/config.json '
                      f'--consent-sha256 {consent["providerSha256"]} --config-sha256 {consent["configSha256"]} '
                      f'--controller-uid {r["uid"]} --anchors {base}/consent/anchors\n'
                      f'Environment=HOME={base}/consent\nReadWritePaths={base}/consent/anchors'
                      f' {consent["storage"]["writableParent"]}\n'
                      f'BindPaths={consent["storage"]["writableParent"]}\n' +
                      ''.join(f'BindReadOnlyPaths={base}/consent-dependencies/{role}:{pin["path"]}\n'
                              for role, pin in consent.get('dependencies', {}).items()) + consent_common)
    require(len(values) == len(r['units']), 'controller service layout differs')
    return dict(zip(r['units'], (value.encode() for value in values)))


def acl_text(path):
    return run(['/usr/bin/getfacl', '-c', '-p', '-n', '--', str(path)], stdout=subprocess.PIPE).stdout.decode()


def grant_acl(path, uid, permission, operator, receipt_path=None):
    m = metadata(path)
    require(m.st_uid in (0, operator), 'public socket ancestry owner refused')
    before = acl_text(path)
    require(not any(line.startswith(f'user:{uid}:') for line in before.splitlines()), 'controller ACL already exists')
    # Refuse extended ACLs instead of widening their masks or changing other users.
    require(not any(line.startswith(('mask:', 'default:')) or re.match(r'(user|group):[^:]+:', line)
                    for line in before.splitlines()), 'public socket ancestry has extended ACL; explicit operator preparation required')
    entry = {'path': str(path), 'dev': m.st_dev, 'ino': m.st_ino, 'before': before}
    if receipt_path is not None:
        write_new(receipt_path, encoded(entry))
    run(['/usr/bin/setfacl', '-m', f'u:{uid}:{permission}', '--', str(path)])
    entry['after'] = acl_text(path)
    if receipt_path is not None:
        write_new(receipt_path.with_suffix('.after.json'), encoded(entry))
    return entry


def world_root(public, store_root):
    """The owner-controlled boundary: the Store's own tree when the public endpoint lies in it,
    otherwise the directory that holds the endpoint. Nothing above it is this world's to change."""
    return store_root if store_root in public.parents else public.parent


def traversable(path, uid):
    """Search permission for UID on a directory without any change: the other bit, or an existing
    user entry for UID that grants x under the mask."""
    m = metadata(path)
    if m.st_mode & 0o001:
        return True
    mask = 'rwx'
    text = acl_text(path).splitlines()
    for line in text:
        if line.startswith('mask::'):
            mask = line.split('::', 1)[1]
    return any(line.startswith(f'user:{uid}:') and 'x' in line.split(':')[2] and 'x' in mask for line in text)


def acl_grants(public, uid, store_root):
    """(path, permission) pairs the controller needs: traversal of private ancestors and access to the
    public socket. Above the world root an ancestor must already be traversable (refused by name
    otherwise): worlds share those directories, and a grant there makes the next world refuse the
    first one's entry and lets teardown order matter. At and below the root the grant is made."""
    root = world_root(public, store_root)
    grants = []
    for p in reversed((public.parent, *public.parent.parents)):
        inside = p == root or root in p.parents
        if inside:
            if not metadata(p).st_mode & 0o001:
                grants.append((p, '--x'))
        else:
            require(traversable(p, uid), f'public socket ancestry {p} above the world root {root} is not '
                    f'traversable (--x) for controller uid {uid}; operator preparation required')
    return grants + [(public, '-w-')]


def worker_layout(r):
    home = Path(r['home'])
    return home / 'grain' if r.get('workerTask') else home


def worker_state(r):
    return worker_layout(r) / 'state'


def worker_config(r):
    return worker_layout(r) / 'controller.json'


def worker_relative(value):
    require(isinstance(value, str) and re.fullmatch(r'[A-Za-z0-9_./-]{1,512}', value)
            and all(p not in ('', '.', '..') for p in value.split('/')), 'worker relative path refused')
    return Path(value)


def worker_inputs(request, operator):
    require(isinstance(request, dict) and set(request) ==
            {'protocol', 'task', 'files', 'directories', 'launcherDirectory', 'runtimeRoot'}
            and request['protocol'] == 'mini-controller-worker-prepare-v1'
            and isinstance(request['task'], str) and re.fullmatch('[1-9][0-9]{0,19}', request['task']),
            'worker preparation schema refused')
    require(isinstance(request['files'], list) and 1 <= len(request['files']) <= 256
            and isinstance(request['directories'], list) and len(request['directories']) <= 256,
            'worker input count refused')
    data = {}; total = 0
    for entry in request['files']:
        require(isinstance(entry, dict) and set(entry) == {'source', 'destination'}, 'worker file entry refused')
        rel = worker_relative(entry['destination'])
        require(str(rel) == 'host-config.json' or rel.parts[0] in ('keys', 'bootstrap', 'requests'),
                'worker input destination refused')
        require(str(rel) not in data, 'duplicate worker input destination')
        content = read_file(canonical(entry['source']), operator, 8 * 1024 * 1024, required_mode=0o600)
        total += len(content); require(total <= 32 * 1024 * 1024, 'worker input bytes exceed bound')
        data[str(rel)] = content
    require('host-config.json' in data, 'worker Host configuration absent')
    directories = {'keys', 'bootstrap', 'requests', 'worker-work', 'grain'}
    for name in request['directories']:
        rel = worker_relative(name)
        require(rel.parts[0] in ('keys', 'bootstrap', 'requests', 'worker-work'), 'worker directory destination refused')
        directories.add(str(rel))
    for name in data:
        directories.update(str(p) for p in Path(name).parents if str(p) != '.')
    for name in tuple(directories):
        directories.update(str(p) for p in Path(name).parents if str(p) != '.')
    require(not (set(data) & directories), 'worker file/directory collision')
    return data, directories


def runtime_relative(value):
    """Runtime data names are filenames, never shell or systemd expressions."""
    require(isinstance(value, str) and 0 < len(value.encode('utf-8')) <= 4096
            and all(p not in ('', '.', '..') and len(p.encode('utf-8')) <= 255 for p in value.split('/'))
            and all(ord(c) >= 32 and ord(c) != 127 for c in value), 'runtime relative path refused')
    return Path(value)


def worker_tree_inventory(source, operator):
    """Validate the complete unprivileged tree before publishing any stage."""
    ancestry(source, {0, operator})
    inventory = {}; total = 0; directories = []
    for directory, dirs, files in os.walk(source, followlinks=False):
        rel = Path(directory).relative_to(source)
        require(len(directories) <= 20000 and len(rel.parts) <= 32, 'worker runtime directory bound exceeded')
        for name in dirs:
            src = Path(directory) / name
            relative = str(src.relative_to(source)); runtime_relative(relative)
            m = metadata(src, operator)
            require(stat.S_ISDIR(m.st_mode) and not m.st_mode & 0o7022, 'worker runtime directory custody refused')
            directories.append(relative)
        for name in files:
            src = Path(directory) / name
            relative = str(src.relative_to(source)); runtime_relative(relative)
            require(len(inventory) < 100000, 'worker runtime file count exceeded')
            data = read_file(src, operator, 256 * 1024 * 1024, allow_empty=True)
            total += len(data); require(total <= 4 * 1024 * 1024 * 1024, 'worker runtime byte bound exceeded')
            mode = 0o555 if src.lstat().st_mode & 0o111 else 0o444
            inventory[relative] = {'sha256': sha(data), 'mode': mode, 'size': len(data)}
    return {'directories': sorted(directories), 'files': inventory}


def mkdir_exact(path, uid=0, gid=0, mode=0o700):
    if path.exists() or path.is_symlink():
        m = metadata(path, uid, mode)
        require(stat.S_ISDIR(m.st_mode) and m.st_gid == gid, 'retained stage directory differs')
    else:
        mkdir(path, uid, gid, mode)


def validate_retained_runtime(destination, expected):
    if destination.exists() or destination.is_symlink():
        metadata(destination, 0, 0o755)
        # An interrupted copy may contain only exact members of this inventory.
        for directory, dirs, files in os.walk(destination, followlinks=False):
            for name in dirs + files:
                path = Path(directory) / name; rel = str(path.relative_to(destination))
                m = metadata(path, 0)
                if name in dirs:
                    require(rel in expected['directories'] and stat.S_ISDIR(m.st_mode), 'retained runtime directory differs')
                else:
                    require(rel in expected['files'], 'unrecorded retained runtime file')
                    pin = expected['files'][rel]
                    require(sha(read_file(path, 0, max(1, pin['size']), allow_empty=True, required_mode=pin['mode'])) == pin['sha256'],
                            'retained runtime bytes differ')


def copy_worker_tree(source, destination, operator, expected=None, resume=False):
    """Bounded regular-file snapshot; never dereference caller symlinks as root."""
    actual = worker_tree_inventory(source, operator)
    require(expected is None or actual == expected, 'worker runtime changed after preflight')
    expected = actual
    if resume: validate_retained_runtime(destination, expected)
    make = mkdir_exact if resume else mkdir
    make(destination, mode=0o755)
    for relative in sorted(expected['directories'], key=lambda v: (len(Path(v).parts), v)):
        make(destination / relative, mode=0o755)
    for relative, pin in expected['files'].items():
        data = read_file(source / relative, operator, 256 * 1024 * 1024, allow_empty=True)
        require(len(data) == pin['size'] and sha(data) == pin['sha256'], 'worker runtime source changed during copy')
        if resume:
            publish_exact(destination / relative, data, mode=pin['mode'], bound=256 * 1024 * 1024)
        else:
            write_new(destination / relative, data, mode=pin['mode'])
    return expected['files']


def worker_manager(base, r, action):
    if not r.get('workerTask'):
        return
    path = base / ('stage.json' if (base / 'stage.json').exists() else 'stage-pending.json')
    stage = strict_json(read_file(path, 0, 65536))
    unit = stage['worker']['userManager']
    require(unit == f'user@{r["uid"]}.service', 'worker manager identity differs')
    run(['/usr/bin/systemctl', action, unit])


def worker_environment(base, r):
    if not r.get('workerTask'):
        return {}
    return {'XDG_RUNTIME_DIR': f'/run/user/{r["uid"]}',
            'DBUS_SESSION_BUS_ADDRESS': f'unix:path=/run/user/{r["uid"]}/bus',
            'MINI_GRAIN_CONTROLLER_MANAGER': 'system', 'MINI_GRAIN_WORKER_MANAGER': 'user',
            'MINI_GRAIN_CONTROLLER_UNIT': r['units'][0],
            'MINI_GRAIN_CONTROLLER_REGISTRATION': str(base / 'registrations' / (r['workerTask'] + '.json'))}


def validate_worker_config(value, base, r, previous=None):
    home = Path(r['home']); root = worker_layout(r)
    require(value.get('task') == r['workerTask'] and value.get('stateDir') == str(root / 'state')
            and value.get('controlSocket') == str(root / 'state/control.sock') and value.get('cwd') == str(root)
            and value.get('hostConfig') == str(home / 'host-config.json'), 'worker config layout differs')
    for field, name in (('mini', 'mini'), ('host', 'minidregg-host')):
        require(value.get(field) in (str(home / 'bin' / name), str(base / 'bin' / name)), 'worker native binary path refused')
    commands = value.get('commands')
    require(isinstance(commands, list) and len(commands) == 1, 'one fixed Hermes command required')
    command = commands[0]
    require(set(command) == {'name', 'program', 'args', 'systemdScope', 'wallTimeSeconds', 'reserve', 'charge'}
            and command['name'] == 'hermes-acp' and command['program'] == str(base / 'worker/launcher/bwrap')
            and command['systemdScope'] is True and type(command['wallTimeSeconds']) is int
            and 1 <= command['wallTimeSeconds'] <= 1800
            and command['args'] in (["--workspace", str(home / 'worker-work'), "--runtime-root", str(base / 'worker/runtime-root'),
                                     "--network", network, "--", "/agent/hermes-acp"] for network in ('none', 'host')),
            'worker command differs from staged fixed launcher/runtime/workspace')
    for field in ('reserve', 'charge'):
        require(isinstance(command[field], str) and re.fullmatch('0|[1-9][0-9]{0,19}', command[field]), 'worker charge shape refused')
    for role in (None, 'toolTask', 'providerTask', 'dispatchTask'):
        task = value if role is None else value.get(role)
        if task is None: continue
        key = canonical(task.get('custodyKey'))
        require(key.parent == home / 'keys', 'worker custody key outside staged role directory')
        require(len(read_file(key, r['uid'], 32, required_mode=0o600)) == 32, 'worker custody key shape refused')
        if previous is not None:
            old = previous if role is None else previous.get(role)
            require(isinstance(old, dict) and all(task.get(k) == old.get(k) for k in
                ('task', 'subject', 'custodyKey', 'capability', 'queryCapability', 'parentCapability', 'parentObserveCapability')),
                'worker role or custody identity changed')
    if previous is not None:
        require(all(value.get(k) == previous.get(k) for k in ('commands', 'mini', 'host', 'hostConfig', 'hostSocket',
                'policyControlCapability', 'providerTask', 'dispatchTask')),
                'worker command, transport or service authority changed')


def unchanged_worker_config(previous, current, state):
    """Permit the first bounded foreground session allowance before native runtime custody."""
    old = {k:v for k,v in previous.items() if k != 'toolTask'}
    new = {k:v for k,v in current.items() if k != 'toolTask'}
    if old == new:
        return
    if previous.get('foregroundTool') is None and current.get('foregroundTool') == {'reserve': '1', 'charge': '0'}:
        journal = state / 'journal.json'
        require(not journal.exists() and not journal.is_symlink(),
                'initial foreground allowance requires no native controller journal')
        new = dict(new)
        if 'foregroundTool' in old: new['foregroundTool'] = old['foregroundTool']
        else: del new['foregroundTool']
    require(old == new, 'worker non-tool config changed')


def unchanged_worker_tool(previous, current):
    """Allow one initial account reference selection; native handoff still grants access."""
    allowed = {'registeredSharedApplications', 'allowedSessionFamilies', 'currentBirthHostSha256',
               'allowedApplicationLifetimeRoutes', 'lifetimeApiHostSha256', 'applicationServices',
               'typedApplications'}
    old = {k:v for k,v in previous.items() if k not in allowed}
    new = {k:v for k,v in current.items() if k not in allowed}
    if old == new:
        return
    old_room, new_room = old.get('room'), new.get('room')
    if isinstance(old_room, dict) and isinstance(new_room, dict) and old_room.get('account') == 'unsummoned':
        account = new_room.get('account')
        # Same syntactic boundary as native workspace::validate_ref_name. This
        # selects a reference, never proves its ownership, funding or room grant.
        valid = (isinstance(account, str) and account != 'unsummoned' and 0 < len(account) <= 128
                 and all(re.fullmatch('[A-Za-z0-9-]{1,64}', part) for part in account.split('/')))
        if valid:
            new = {**new, 'room': {**new_room, 'account': 'unsummoned'}}
    require(old == new, 'worker non-attachment tool config changed or room account already bound')


def publish_worker_config(store, helper):
    _, base, r = load(store, helper)
    stage = checked_units(base, r)
    require(r.get('workerTask'), 'worker mode required')
    worker_manager(base, r, 'stop'); no_processes(r['uid'])
    data = read_file(worker_config(r), r['uid'], 524288, required_mode=0o600)
    value = strict_json(data); validate_worker_config(value, base, r)
    require(value.get('hostSocket') == stage['publicSocket'], 'worker participant socket changed')
    archive = base / 'configs' / (sha(data) + '.json')
    publish_exact(archive, data, bound=524288)
    registration = {'protocol': 'mini-controller-registration-v1', 'task': r['workerTask'],
                    'config': str(worker_config(r)), 'manager': 'system', 'workerManager': 'user',
                    'serviceUid': r['uid'], 'residentConfig': None}
    publish_exact(base / 'registrations' / (r['workerTask'] + '.json'), encoded(registration), mode=0o644)
    publish_exact(base / 'worker-published.json', encoded({'configSha256': sha(data)}))
    return {'store': store, 'configurationSha256': sha(data), 'config': value,
            'controllerHome': str(worker_layout(r)), 'controllerUid': r['uid']}


def controller_run(store, helper, request_arg):
    _, base, r = load(store, helper)
    stage = checked_units(base, r)
    require(r.get('workerTask'), 'worker mode required')
    request = strict_json(read_file(canonical(request_arg), r['operatorUid'], 65536, required_mode=0o600))
    require(isinstance(request, dict) and set(request) in ({'program', 'args'}, {'program', 'args', 'inputs'})
            and request['program'] in ('mini', 'grain-runtime') and isinstance(request['args'], list)
            and 1 <= len(request['args']) <= 128 and all(isinstance(a, str) and '\0' not in a and len(a) <= 4096
                                                        for a in request['args']), 'worker command schema refused')
    allowed = {'mini': {'shell', 'hermes-handoff', 'workspace', 'credit', 'context'},
               'grain-runtime': {'create', 'hermes-room', 'controller-launch', 'tool-result', 'tool-ack'}}
    require(request['args'][0] in allowed[request['program']], 'worker command is outside fixed native verbs')
    if request['args'][0] == 'create':
        require(request['program'] == 'grain-runtime' and len(request['args']) == 2
                and canonical(request['args'][1]).parent == Path(r['home']) / 'requests',
                'worker create selects one staged request, never operator birth')
    inputs = request.get('inputs', [])
    require(isinstance(inputs, list) and len(inputs) <= 32, 'worker command input count refused')
    copies = {}
    for entry in inputs:
        require(isinstance(entry, dict) and set(entry) == {'source', 'destination'}
                and isinstance(entry['destination'], str)
                and re.fullmatch(r'requests/(?:registrations/)?[A-Za-z0-9_-]+\.json', entry['destination']),
                'worker command input destination refused')
        require(entry['destination'] not in copies, 'duplicate worker command input')
        copies[entry['destination']] = read_file(canonical(entry['source']), r['operatorUid'], 262144, required_mode=0o600)
    def setup():
        for name, data in copies.items():
            path = Path(r['home']) / name
            ancestry(path.parent, {0, r['uid']})
            write_new(path, data, r['uid'], r['gid'])
    r['_consentEnvironment'] = {**consent_environment(r, base, stage['consent']), **worker_environment(base, r)}
    worker_manager(base, r, 'start')
    return controller_child(r, [str(base / 'bin' / request['program']), *request['args']], setup, timeout=1800)


def export_config(store, helper):
    _, base, r = load(store, helper)
    checked_units(base, r)
    return strict_json(read_file(worker_config(r), r['uid'], 524288, required_mode=0o600))


def transfer_birth_tree(root, before_uid, uid, gid):
    """Only bounded owned regular birth artifacts; chown descriptors, never follow links."""
    ancestry(root.parent, {0, uid, before_uid})
    entries = []; total = 0
    for directory, dirs, files in os.walk(root, followlinks=False):
        require(len(entries) <= 4096 and len(Path(directory).relative_to(root).parts) <= 16,
                'birth transfer directory bound exceeded')
        for path in [Path(directory), *[Path(directory) / n for n in files]]:
            m = metadata(path, before_uid)
            require(stat.S_ISDIR(m.st_mode) or (stat.S_ISREG(m.st_mode) and m.st_nlink == 1),
                    'birth transfer requires owned regular files and directories')
            total += m.st_size if stat.S_ISREG(m.st_mode) else 0
            require(total <= 64 * 1024 * 1024, 'birth transfer byte bound exceeded')
            entries.append((path, fingerprint(m)))
        for name in dirs:
            require(stat.S_ISDIR(metadata(Path(directory) / name, before_uid).st_mode), 'birth transfer linked directory refused')
    for path, expected in reversed(entries):
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
        try:
            m = os.fstat(fd)
            require(fingerprint(m) == expected and fingerprint(path.lstat()) == expected, 'birth transfer path changed')
            os.fchown(fd, uid, gid)
            os.fchmod(fd, 0o700 if stat.S_ISDIR(m.st_mode) else 0o600)
            os.fsync(fd)
        finally:
            os.close(fd)


def worker_birth(store, helper, source_arg):
    _, base, r = load(store, helper)
    stage = checked_units(base, r)
    require(r.get('workerTask') and not (base / 'worker-published.json').exists(), 'birth only before worker publication')
    service(store, helper, 'stop'); no_processes(r['uid'])
    raw = read_file(canonical(source_arg), r['operatorUid'], 524288, required_mode=0o600)
    spec = strict_json(raw); home = Path(r['home']); root = worker_layout(r)
    require(spec.get('root') == str(root) and spec.get('task') == r['workerTask']
            and spec.get('mini') == str(base / 'bin/mini') and spec.get('host') == str(base / 'bin/minidregg-host')
            and spec.get('hostConfig') == str(home / 'host-config.json')
            and spec.get('genesis') == str(home / 'bootstrap/genesis.json')
            and spec.get('namespaceRoot') == str(home / 'bootstrap/namespace'), 'worker birth layout refused')
    sponsor = canonical(spec['sponsor']['key'])
    require(not sponsor.is_relative_to(home) and len(read_file(sponsor, r['operatorUid'], 32, required_mode=0o600)) == 32,
            'sponsor key must remain operator-private outside controller home')
    retained = base / 'worker-birth-spec.json'
    publish_exact(retained, raw, bound=524288)
    # The same bytes are handed to Whole; root never changes the native spec.
    publish_exact(home / 'requests/create.json', raw, r['uid'], r['gid'], bound=524288)
    owner = metadata(root).st_uid
    require(owner in (r['uid'], r['operatorUid']), 'birth root ownership differs')
    transfer_birth_tree(root, owner, r['operatorUid'], r['operatorGid'])
    acl_root = base / ('worker-birth-acl-' + str(time.time_ns()))
    mkdir(acl_root)
    paths = [(home, '--x'), (home / 'host-config.json', 'r--')]
    for directory, dirs, files in os.walk(home / 'bootstrap', followlinks=False):
        paths.append((Path(directory), 'r-x'))
        paths.extend((Path(directory) / name, 'r--') for name in files)
        for name in dirs:
            require(stat.S_ISDIR(metadata(Path(directory) / name, r['uid']).st_mode), 'bootstrap linked directory refused')
    require(len(paths) <= 512, 'birth bootstrap ACL count exceeded')
    changed = []
    try:
        for index, (path, permission) in enumerate(paths):
            m = metadata(path, r['uid'])
            before = acl_text(path)
            require(not any(line.startswith(('mask:', 'default:')) or re.match(r'(user|group):[^:]+:', line)
                            for line in before.splitlines()), 'birth temporary ACL needs unextended source')
            entry = {'path': str(path), 'dev': m.st_dev, 'ino': m.st_ino, 'before': before}
            write_new(acl_root / f'{index:03}.json', encoded(entry)); changed.append(entry)
            run(['/usr/bin/setfacl', '-m', f'u:{r["operatorUid"]}:{permission}', '--', str(path)])
        operator = {**r, 'uid': r['operatorUid'], 'gid': r['operatorGid'],
                    'home': pwd.getpwuid(r['operatorUid']).pw_dir}
        fd = os.memfd_create('mini-worker-birth-spec', os.MFD_ALLOW_SEALING | os.MFD_CLOEXEC)
        try:
            os.write(fd, raw); os.lseek(fd, 0, os.SEEK_SET)
            os.fchown(fd, r['operatorUid'], r['operatorGid']); os.fchmod(fd, 0o400)
            fcntl.fcntl(fd, fcntl.F_ADD_SEALS, fcntl.F_SEAL_SEAL | fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_GROW | fcntl.F_SEAL_WRITE)
            result = controller_child(operator, [str(base / 'bin/grain-runtime'), 'create', f'/proc/self/fd/{fd}',
                                      '--birth-socket', stage['upstreamSocket']], timeout=1800, pass_fds=(fd,))
        finally:
            os.close(fd)
    finally:
        for entry in reversed(changed):
            path = Path(entry['path']); m = metadata(path, r['uid'])
            require((m.st_dev, m.st_ino) == (entry['dev'], entry['ino']), 'birth ACL object replaced; preserve receipt')
            run(['/usr/bin/setfacl', '--restore=-'], input=(f'# file: {path}\n' + entry['before']).encode())
        transfer_birth_tree(root, r['operatorUid'], r['uid'], r['gid'])
        run(['/usr/bin/systemctl', 'start', r['units'][1], r['units'][3], r['units'][4]])
    return result


def resume_worker_inputs(base, home, r, pending, data, binaries, worker_dirs, runtime_inventory):
    previous = strict_json(read_file(base / 'stage-pending.json', 0, 65536, required_mode=0o600))
    require({k:v for k,v in previous.items() if k != 'upstreamIdentity'} ==
            {k:v for k,v in pending.items() if k != 'upstreamIdentity'}, 'pending stage inputs differ')
    require(not previous['acl'] and not any((base / p).exists() for p in
            ('worker-files.json', 'worker-birth-spec.json', 'worker-published.json', 'proxy/config.json', 'worker/launcher')),
            'worker stage advanced past recoverable copy boundary')
    # Every existing home member is one of the exact planned inputs. No
    # task state or unexpected controller-authored path can be adopted.
    expected_dirs = {'bin', 'operator', 'tool-requests', 'consent'} | worker_dirs
    expected_files = set(data) | {'bin/' + n for n in binaries}
    for directory, dirs, files in os.walk(home, followlinks=False):
        for name in dirs + files:
            path = Path(directory) / name; rel = str(path.relative_to(home))
            m = metadata(path, r['uid'])
            require((name in dirs and rel in expected_dirs and stat.S_ISDIR(m.st_mode)) or
                    (name in files and rel in expected_files and stat.S_ISREG(m.st_mode)), 'unexpected retained controller input')
    for name, content in data.items():
        if (home / name).exists():
            require(read_file(home / name, r['uid'], max(1, len(content)), required_mode=0o600) == content, 'retained worker input changed')
    for name, content in binaries.items():
        for path, uid, mode in ((base / 'bin' / name, 0, 0o755), (home / 'bin' / name, r['uid'], 0o500)):
            if path.exists():
                require(read_file(path, uid, len(content), required_mode=mode) == content, 'retained native binary changed')
    for directory, allowed in ((base / 'worker', {'runtime-root'}), (base / 'proxy', set()),
                               (base / 'configs', set()), (base / 'registrations', set()),
                               (base / 'bin', set(binaries))):
        if directory.exists():
            require(set(p.name for p in directory.iterdir()) <= allowed, 'unrecorded staged publication')
    validate_retained_runtime(base / 'worker/runtime-root', runtime_inventory)
    recovery = {'protocol': 'mini-worker-stage-resume-v1', 'previousSha256': sha(encoded(previous)),
                'current': pending, 'runtimeInventorySha256': sha(encoded(runtime_inventory))}
    write_new(base / ('stage-resume-' + str(time.time_ns()) + '.json'), encoded(recovery))


def stage(store, helper, bundle_arg, bins_arg, upstream_arg, public_arg, worker=False, resume=False):
    registry, base, r = load(store, helper)
    no_processes(r['uid'])
    require(not worker or has_consent(r), 'worker preparation requires version-2 consent services')
    require(not (base / 'stage.json').exists() and (resume or not (base / 'stage-pending.json').exists()), 'controller stage already attempted')
    require(not resume or (worker and not r.get('workerTask')), 'only pre-publication worker staging can resume')
    bundle, bins, upstream, public = map(canonical, (bundle_arg, bins_arg, upstream_arg, public_arg))
    op = registry['operatorUid']
    ancestry(bundle.parent if worker else bundle, {0, op}); ancestry(bins, {0, op})
    request = strict_json(read_file(bundle, op, 65536, required_mode=0o600)) if worker else None
    if worker:
        data, worker_dirs = worker_inputs(request, op)
        r = {**r, 'workerTask': request['task'], 'units': names(store, has_consent(r), request['task'])}
    actual = set()
    if not worker:
        allowed_dirs = {'custody', 'state', 'state/shared-app-refs', 'state/oracle-grant', 'workspace'}
        for directory, dirs, files in os.walk(bundle, followlinks=False):
            require(len(actual) <= len(FILES) + len(FINAL_FILES), 'controller bundle exceeds file bound')
            for n in dirs:
                child = Path(directory) / n
                require(str(child.relative_to(bundle)) in allowed_dirs, 'controller bundle directory outside allowlist')
                metadata(child, op)
            actual.update(str((Path(directory) / n).relative_to(bundle)) for n in files)
        require(set(FILES) <= actual <= set(FILES) | set(FINAL_FILES), 'controller bundle files differ from exact allowlist')
        limits = {**FILES, **FINAL_FILES}
        data = {n: read_file(bundle / n, op, limits[n], required_mode=0o600 if n.startswith('custody/') else None)
                for n in actual}
        require(all(len(data['custody/' + role + '.key']) == 32 for role in ('controller', 'tool', 'dispatch', 'provider')), 'controller key size differs')
    binaries = {n: read_file(bins / n, op, 256 * 1024 * 1024, True) for n in binary_names(r)}
    config = json.loads(data['controller.json']) if not worker else {}; host = json.loads(data['host-config.json'])
    home = Path(r['home'])
    require(worker or (config.get('commands') == [] and config.get('stateDir') == str(home / 'state')
            and config.get('controlSocket') == str(home / 'state/control.sock')
            and config.get('cwd') == str(home / 'workspace') and config.get('hostConfig') == str(home / 'host-config.json')
            and config.get('hostSocket') == str(public)), 'controller configuration layout differs')
    ancestry(upstream.parent, {0, op}); um = metadata(upstream, op, 0o600)
    require(stat.S_ISSOCK(um.st_mode), 'primary operator endpoint is not a socket')
    ancestry(public.parent, {0, op}); pm = metadata(public, op)
    require(stat.S_ISSOCK(pm.st_mode), 'public endpoint is not a socket')
    consent = {'providerSha256': sha(binaries[CONSENT_BIN]), 'configSha256': sha(data['host-config.json']),
               'storage': consent_storage(data['host-config.json'], op),
               'dependencies': consent_dependencies(data['host-config.json'], op)} if has_consent(r) else None
    units = unit_bytes(r, base, upstream, consent, public)
    require(all(not (UNITS / n).exists() and not (UNITS / n).is_symlink() for n in units), 'controller unit already exists')
    require(all(manager_properties(n).get('LoadState') == 'not-found' for n in units),
            'controller unit name already loaded; replacement refused')
    pending = {'sourceBundle': str(bundle), 'files': {n: sha(v) for n, v in data.items()},
               'binaries': {n: sha(v) for n, v in binaries.items()}, 'publicSocket': str(public),
               'upstreamSocket': str(upstream), 'upstreamIdentity': [um.st_dev, um.st_ino], 'acl': [],
               'units': {n: sha(value) for n, value in units.items()}}
    if worker:
        pending['worker'] = {'task': request['task'], 'root': str(worker_layout(r)),
                             'userManager': f'user@{r["uid"]}.service', 'inputSha256': sha(encoded(request))}
    if consent is not None:
        pending['consent'] = consent
    runtime_inventory = worker_tree_inventory(canonical(request['runtimeRoot']), op) if worker else None
    if resume:
        resume_worker_inputs(base, home, r, pending, data, binaries, worker_dirs, runtime_inventory)
    else:
        write_new(base / 'stage-pending.json', encoded(pending))
    if worker:
        publish_exact(base / 'worker-tree-input.json', encoded(runtime_inventory), bound=64 * 1024 * 1024)
    make = mkdir_exact if resume else mkdir
    def put(path, value, uid=0, gid=0, mode=0o600):
        if resume: publish_exact(path, value, uid, gid, mode, bound=256 * 1024 * 1024)
        else: write_new(path, value, uid, gid, mode)
    # Fresh home only; no running controller can redirect the root setup writes.
    require(resume or not list(home.iterdir()), 'controller home is not fresh')
    directories = {'bin', 'operator', 'tool-requests'} | (worker_dirs if worker else {'custody', 'state', 'state/shared-app-refs', 'state/oracle-grant', 'workspace'})
    for rel in sorted(directories, key=lambda p: (len(Path(p).parts), p)):
        make(home / rel, r['uid'], r['gid'])
    if has_consent(r):
        make(home / 'consent', r['uid'], r['gid'])
        make(base / 'consent', op, registry['operatorGid'])
        make(base / 'consent/anchors', op, registry['operatorGid'])
        put(base / 'consent/config.json', data['host-config.json'], op, registry['operatorGid'])
        make(base / 'consent-dependencies', mode=0o755)
        for role, pin in consent['dependencies'].items():
            source = canonical(pin['path'])
            payload = read_file(source, metadata(source).st_uid, 256 * 1024 * 1024, executable=True)
            require(sha(payload) == pin['sha256'], 'consent dependency changed during staging')
            put(base / 'consent-dependencies' / role, payload, mode=0o755)
    make(base / 'bin', mode=0o755); make(base / 'configs'); make(base / 'proxy', op, registry['operatorGid'])
    for n, value in data.items():
        put(home / n, value, r['uid'], r['gid'])
    for n, value in binaries.items():
        put(base / 'bin' / n, value, mode=0o755)
        put(home / 'bin' / n, value, r['uid'], r['gid'], 0o500)
    if not worker:
        put(base / 'configs' / (sha(data['controller.json']) + '.json'), data['controller.json'])
    else:
        make(base / 'worker', mode=0o755); make(base / 'registrations', mode=0o755)
        runtime = copy_worker_tree(canonical(request['runtimeRoot']), base / 'worker/runtime-root', op, runtime_inventory, resume)
        launcher = canonical(request['launcherDirectory']); ancestry(launcher, {0, op})
        require(set(p.name for p in launcher.iterdir()) == {'bwrap', 'launch-gate'}, 'fixed launcher files differ')
        make(base / 'worker/launcher', mode=0o755)
        pins = {}
        for name in ('bwrap', 'launch-gate'):
            content = read_file(launcher / name, op, 256 * 1024 * 1024, True)
            put(base / 'worker/launcher' / name, content, mode=0o555)
            pins['launcher/' + name] = sha(content)
        for name in ('hermes-acp', 'grain-runtime', 'grain-provider-bridge'):
            require(name in runtime and runtime[name]['mode'] == 0o555, 'worker runtime entrypoint absent')
            pins['runtime-root/' + name] = runtime[name]['sha256']
        put(base / 'worker-files.json', encoded(runtime))
        pending['worker']['binaries'] = pins
        replace_root_record(base / 'receipt.json', encoded(r), 0o600)
    put(base / 'proxy/config.json', data['host-config.json'], op, registry['operatorGid'])
    # Only traversal of private ancestors and access to the PUBLIC socket. The
    # operator's private listener and Store files receive no controller ACL.
    for p, perm in acl_grants(public, r['uid'], WORLDS / store):
        pending['acl'].append(grant_acl(p, r['uid'], perm, op, base / f'acl-{len(pending["acl"]) + 1:03}.json'))
    if has_consent(r):
        # The authorized public-listener traversal ACL may change mode-mask
        # bits on a shared ancestor. Retain the completed setup's path custody.
        pending['consent']['storage'] = consent_storage(data['host-config.json'], op)
    for n, value in units.items():
        write_new(UNITS / n, value, mode=0o644)
    pending['units'] = {n: sha(value) for n, value in units.items()}
    write_new(base / 'stage.json', encoded(pending))
    run(['/usr/bin/systemctl', 'daemon-reload'])
    if worker:
        run(['/usr/bin/loginctl', 'enable-linger', r['name']])
        run(['/usr/bin/systemctl', 'start', r['units'][1], r['units'][3], r['units'][4]])
    return {**r, 'stage': str(base / 'stage.json'), **({'consent': consent_record(base, r, pending)} if has_consent(r) else {})}


def checked_units(base, r, partial=False, consent_upgrade_hashes=(), runtime_upgrade_hashes=(), proxy_upgrade_hashes=(), socket_upgrade_hashes=(), mini_upgrade_hashes=(), controller_upgrade_hashes=()):
    stage_path = base / 'stage.json'
    if partial and not stage_path.exists():
        stage_path = base / 'stage-pending.json'
        if not stage_path.exists():
            require(not any((UNITS / n).exists() for n in r['units']), 'unrecorded controller units exist')
            return {'units': {}, 'binaries': {}}
    stage = json.loads(read_file(stage_path, 0, 65536))
    for n in r['units']:
        if partial and not (UNITS / n).exists() and not (UNITS / n).is_symlink():
            continue
        actual = sha(read_file(UNITS / n, 0, 16384))
        require(actual == stage['units'][n] or (has_consent(r) and n == r['units'][4]
                and actual in consent_upgrade_hashes) or (n == r['units'][2] and actual in proxy_upgrade_hashes)
                or (n == r['units'][1] and actual in socket_upgrade_hashes)
                or (n == r['units'][0] and actual in controller_upgrade_hashes), 'controller unit changed')
    if 'statusProxy' in stage:
        pin = stage['statusProxy']
        require(isinstance(pin, dict) and set(pin) == {'binary', 'sha256'}
                and isinstance(pin['sha256'], str) and re.fullmatch('[0-9a-f]{64}', pin['sha256'])
                and pin['binary'] == 'mini-status-' + pin['sha256'], 'status proxy pin malformed')
        require(sha(read_file(base / 'bin' / pin['binary'], 0, 256 * 1024 * 1024,
                              executable=True, required_mode=0o755)) == pin['sha256'], 'status proxy binary changed')
    for n in binary_names(r):
        if partial and not (base / 'bin' / n).exists() and not (base / 'bin' / n).is_symlink():
            continue
        digest = sha(read_file(base / 'bin' / n, 0, 256 * 1024 * 1024, True))
        require(digest == stage['binaries'][n] or (n == 'grain-runtime' and digest in runtime_upgrade_hashes)
                or (n == 'mini' and digest in mini_upgrade_hashes),
                'controller binary changed')
    if stage.get('worker') and not partial:
        for name, digest in stage['worker']['binaries'].items():
            require(sha(read_file(base / 'worker' / name, 0, 256 * 1024 * 1024, True)) == digest, 'worker binary changed')
    if has_consent(r) and not partial:
        pins = stage['consent']
        require(pins['providerSha256'] == stage['binaries'][CONSENT_BIN], 'consent provider pin differs')
        for path, owner in ((base / 'consent/config.json', r['operatorUid']),
                            (Path(r['home']) / 'host-config.json', r['uid'])):
            require(sha(read_file(path, owner, 1048576, required_mode=0o600)) == pins['configSha256'],
                    'consent configuration bytes differ')
        metadata(base / 'consent/anchors', r['operatorUid'], 0o700)
        for role, pin in pins.get('dependencies', {}).items():
            require(role in ('signatureBinary', 'storageBinary'), 'unknown consent dependency')
            require(sha(read_file(base / 'consent-dependencies' / role, 0, 256 * 1024 * 1024,
                                  executable=True, required_mode=0o755)) == pin['sha256'],
                    'consent dependency snapshot changed')
        if 'storage' in pins:
            require(consent_storage(read_file(base / 'consent/config.json', r['operatorUid'], 1048576,
                                             required_mode=0o600), r['operatorUid']) == pins['storage'],
                    'consent Store directory or persistent inode pins differ')
    return stage


def consent_record(base, r, stage):
    return {**stage['consent'], 'transportSha256': stage['binaries']['mini'], 'socket': str(Path(r['home']) / 'consent/peer.sock'),
            'socketUnit': r['units'][3], 'serviceUnit': r['units'][4],
            'serviceUid': r['operatorUid'], 'controllerUid': r['uid'], 'activationPeerUid': 0,
            'provider': str(base / 'bin' / CONSENT_BIN), 'config': str(base / 'consent/config.json'),
            'anchors': str(base / 'consent/anchors')}


def consent_readiness(base, r, stage):
    # Observation only: the authenticated first request still has to complete
    # native independent admission. Never report process readiness as consent.
    record = consent_record(base, r, stage)
    observed = manager_properties(record['serviceUnit'])
    require(observed.get('ActiveState') == 'active' and observed.get('MainPID', '0').isdigit()
            and int(observed['MainPID']) > 0, 'consent service is not active')
    require(re.fullmatch('[0-9a-f]{32}', observed.get('InvocationID', '')) is not None, 'consent invocation identity missing')
    pid = int(observed['MainPID'])
    proc = Path('/proc') / str(pid)
    require(proc.stat().st_uid == r['operatorUid'], 'consent process UID differs')
    executable = (proc / 'exe').stat(); expected = (base / 'bin/mini').stat()
    require((executable.st_dev, executable.st_ino) == (expected.st_dev, expected.st_ino), 'consent process executable differs')
    raw_stat = (proc / 'stat').read_text()
    ticks = int(raw_stat[raw_stat.rfind(')') + 2:].split()[19])
    m = metadata(Path(record['socket']), r['uid'], 0o600)
    require(stat.S_ISSOCK(m.st_mode), 'consent endpoint is not a socket')
    again = (proc / 'stat').read_text()
    require(int(again[again.rfind(')') + 2:].split()[19]) == ticks, 'consent process start changed')
    after = manager_properties(record['serviceUnit'])
    require(after.get('MainPID') == str(pid) and after.get('InvocationID') == observed.get('InvocationID')
            and after.get('ActiveState') == 'active', 'consent process changed during readiness')
    return {**record, 'mainPid': pid, 'processStartTicks': ticks, 'invocationId': observed.get('InvocationID'),
            'processExecutableIdentity': [executable.st_dev, executable.st_ino],
            'socketUid': m.st_uid, 'socketMode': '0600', 'socketIdentity': [m.st_dev, m.st_ino],
            'readiness': 'process-and-socket-only', 'independentAdmissionObserved': False}


def stopped_controller_units(r):
    no_processes(r['uid'])
    for unit in r['units']:
        value = manager_properties(unit)
        require(value.get('LoadState') == 'loaded' and value.get('Transient') == 'no'
                and value.get('FragmentPath') == str(UNITS / unit), 'stopped controller unit identity differs')
        # A failed unit can be physically stopped; keep its diagnostic state.
        require(value.get('ActiveState') in ('inactive', 'failed') and value.get('MainPID', '0') == '0'
                and value.get('ControlPID', '0') == '0', 'controller units must be stopped before storage upgrade')
        if unit.endswith('.service'):
            require(value.get('User') == str(r['uid'] if unit == r['units'][0] else r['operatorUid']),
                    'stopped controller unit user differs')


def replace_root_record(path, data, mode):
    temporary = path.with_name('.' + path.name + '-storage-next')
    publish_exact(temporary, data, mode=mode)
    os.replace(temporary, path)
    sync_directory(path.parent)


def consent_storage_upgrade(store, helper):
    _, base, r = load(store, helper)
    require(has_consent(r), 'storage upgrade requires a version-2 controller')
    stopped_controller_units(r)
    intent_path = base / 'consent-storage-upgrade.json'
    unit_path, stage_path = UNITS / r['units'][4], base / 'stage.json'
    def archive(digest, kind):
        require(isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest), 'storage upgrade digest malformed')
        return base / 'configs' / ('consent-storage-' + digest + '.' + kind)
    if not intent_path.exists() and not intent_path.is_symlink():
        old_stage = checked_units(base, r)
        if 'storage' in old_stage['consent']:
            return {'store': store, 'alreadyConfigured': True, 'consent': consent_record(base, r, old_stage)}
        old_stage_raw = read_file(stage_path, 0, 65536, required_mode=0o600)
        require(strict_json(old_stage_raw) == old_stage, 'stage changed before storage upgrade')
        old_unit = read_file(unit_path, 0, 16384, required_mode=0o644)
        old_line = f'ReadWritePaths={base}/consent/anchors\n'.encode()
        require(old_unit.count(old_line) == 1, 'original consent writable paths differ')
        settings = read_file(base / 'consent/config.json', r['operatorUid'], 1048576, required_mode=0o600)
        storage = consent_storage(settings, r['operatorUid'])
        new_unit = old_unit.replace(old_line, old_line[:-1] + b' ' + storage['writableParent'].encode() + b'\n')
        new_stage = strict_json(old_stage_raw)
        new_stage['consent']['storage'] = storage
        new_stage['units'][r['units'][4]] = sha(new_unit)
        new_stage_raw = encoded(new_stage)
        require(len(new_stage_raw) <= 65536, 'storage upgrade stage exceeds bound')
        intent = {'protocol': 'mini-spk-consent-storage-upgrade-v1', 'store': store,
                  'oldStageSha256': sha(old_stage_raw), 'newStageSha256': sha(new_stage_raw),
                  'oldUnitSha256': sha(old_unit), 'newUnitSha256': sha(new_unit)}
        for raw, kind in ((old_stage_raw, 'stage'), (new_stage_raw, 'stage'), (old_unit, 'service'), (new_unit, 'service')):
            path = archive(sha(raw), kind)
            publish_exact(path, raw)
        publish_exact(intent_path, encoded(intent))
    intent = strict_json(read_file(intent_path, 0, 4096, required_mode=0o600))
    require(set(intent) == {'protocol', 'store', 'oldStageSha256', 'newStageSha256', 'oldUnitSha256', 'newUnitSha256'}
            and intent['protocol'] == 'mini-spk-consent-storage-upgrade-v1' and intent['store'] == store,
            'storage upgrade intent differs')
    archives = {}
    for key, kind in (('oldStage', 'stage'), ('newStage', 'stage'), ('oldUnit', 'service'), ('newUnit', 'service')):
        digest = intent[key + 'Sha256']
        archives[key] = read_file(archive(digest, kind), 0, 65536, required_mode=0o600)
        require(sha(archives[key]) == digest, 'storage upgrade archived hash differs')
    old_stage, new_stage = (strict_json(archives[key]) for key in ('oldStage', 'newStage'))
    settings = read_file(base / 'consent/config.json', r['operatorUid'], 1048576, required_mode=0o600)
    require(sha(settings) == old_stage['consent']['configSha256'], 'storage upgrade config changed')
    storage = consent_storage(settings, r['operatorUid'])
    expected = strict_json(archives['oldStage'])
    expected['consent']['storage'] = storage
    expected['units'][r['units'][4]] = intent['newUnitSha256']
    old_line = f'ReadWritePaths={base}/consent/anchors\n'.encode()
    require(archives['oldUnit'].count(old_line) == 1 and archives['newUnit'] == archives['oldUnit'].replace(
            old_line, old_line[:-1] + b' ' + storage['writableParent'].encode() + b'\n')
            and expected == new_stage, 'storage upgrade exceeds exact filesystem change')
    require(sha(read_file(stage_path, 0, 65536, required_mode=0o600)) in
            (intent['oldStageSha256'], intent['newStageSha256']), 'current stage is outside storage upgrade')
    checked_units(base, r, consent_upgrade_hashes=(intent['oldUnitSha256'], intent['newUnitSha256']))
    # Either exact old/new byte state is recoverable after interruption; no
    # unrelated unit or pin is overwritten. Old bytes and intent stay retained.
    replace_root_record(unit_path, archives['newUnit'], 0o644)
    replace_root_record(stage_path, archives['newStage'], 0o600)
    run(['/usr/bin/systemctl', 'daemon-reload'])
    checked_units(base, r)
    return {'store': store, 'storageUpgrade': str(intent_path),
            'previousStageSha256': intent['oldStageSha256'], 'stageSha256': intent['newStageSha256'],
            'consent': consent_record(base, r, new_stage)}


def runtime_upgrade(store, helper, source_arg):
    return controller_binary_upgrade(store, helper, source_arg, 'grain-runtime')


def controller_binary_upgrade(store, helper, source_arg, binary_name):
    require(binary_name in ('grain-runtime', 'mini'), 'controller binary upgrade name refused')
    label = 'runtime' if binary_name == 'grain-runtime' else 'mini'
    _, base, r = load(store, helper)
    stopped_controller_units(r)
    source = read_file(canonical(source_arg), r['operatorUid'], 256 * 1024 * 1024, executable=True)
    source_sha = sha(source)
    intent_path = base / (label + '-upgrade-' + source_sha + '.json')
    root_binary, home_binary = base / 'bin' / binary_name, Path(r['home']) / 'bin' / binary_name
    stage_path = base / 'stage.json'
    def archive(digest, kind):
        require(isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest), 'runtime upgrade digest malformed')
        return base / 'configs' / (label + '-upgrade-' + digest + '.' + kind)
    if not intent_path.exists() and not intent_path.is_symlink():
        stage = checked_units(base, r)
        old = read_file(root_binary, 0, 256 * 1024 * 1024, executable=True, required_mode=0o755)
        require(sha(old) == stage['binaries'][binary_name] and
                read_file(home_binary, r['uid'], 256 * 1024 * 1024, executable=True, required_mode=0o500) == old,
                'controller runtime copies differ from retained stage')
        if old == source:
            return {'store': store, 'alreadyConfigured': True, label + 'Sha256': source_sha}
        old_stage = read_file(stage_path, 0, 65536, required_mode=0o600)
        require(strict_json(old_stage) == stage, 'stage changed before runtime upgrade')
        stage['binaries'][binary_name] = source_sha
        new_stage = encoded(stage)
        require(len(new_stage) <= 65536, 'runtime upgrade stage exceeds bound')
        intent = {'protocol': 'mini-spk-controller-' + label + '-upgrade-v1', 'store': store,
                  'oldBinarySha256': sha(old), 'newBinarySha256': source_sha,
                  'oldStageSha256': sha(old_stage), 'newStageSha256': sha(new_stage)}
        for raw, kind in ((old, 'binary'), (source, 'binary'), (old_stage, 'stage'), (new_stage, 'stage')):
            path = archive(sha(raw), kind)
            publish_exact(path, raw, bound=256 * 1024 * 1024 if kind == 'binary' else 65536)
        publish_exact(intent_path, encoded(intent))
    intent = strict_json(read_file(intent_path, 0, 4096, required_mode=0o600))
    require(set(intent) == {'protocol', 'store', 'oldBinarySha256', 'newBinarySha256', 'oldStageSha256', 'newStageSha256'}
            and intent['protocol'] == 'mini-spk-controller-' + label + '-upgrade-v1' and intent['store'] == store
            and intent['newBinarySha256'] == source_sha, 'runtime upgrade intent differs')
    archives = {}
    for key, kind in (('oldBinary', 'binary'), ('newBinary', 'binary'), ('oldStage', 'stage'), ('newStage', 'stage')):
        digest = intent[key + 'Sha256']
        archives[key] = read_file(archive(digest, kind), 0, 256 * 1024 * 1024 if kind == 'binary' else 65536, required_mode=0o600)
        require(sha(archives[key]) == digest, 'runtime upgrade archived hash differs')
    expected = strict_json(archives['oldStage'])
    require(expected['binaries'][binary_name] == intent['oldBinarySha256'], 'runtime upgrade original pin differs')
    expected['binaries'][binary_name] = source_sha
    require(expected == strict_json(archives['newStage']) and archives['newBinary'] == source,
            'runtime upgrade exceeds exact binary change')
    require(sha(read_file(stage_path, 0, 65536, required_mode=0o600)) in
            (intent['oldStageSha256'], intent['newStageSha256']), 'stage is outside runtime upgrade')
    allowed = (intent['oldBinarySha256'], source_sha)
    checked_units(base, r, **{label + '_upgrade_hashes': allowed})
    for path, owner, mode in ((root_binary, 0, 0o755), (home_binary, r['uid'], 0o500)):
        require(sha(read_file(path, owner, 256 * 1024 * 1024, executable=True, required_mode=mode)) in allowed,
                'runtime copy is outside exact upgrade')
    for path, owner, group, mode in ((root_binary, 0, 0, 0o755), (home_binary, r['uid'], r['gid'], 0o500)):
        temporary = path.with_name('.' + binary_name + '-' + source_sha + '-next')
        publish_exact(temporary, source, owner, group, mode, 256 * 1024 * 1024)
        os.replace(temporary, path)
        sync_directory(path.parent)
    replace_root_record(stage_path, archives['newStage'], 0o600)
    checked_units(base, r)
    return {'store': store, label + 'Upgrade': str(intent_path), label + 'Sha256': source_sha,
            'previous' + label.title() + 'Sha256': intent['oldBinarySha256'], 'stageSha256': intent['newStageSha256']}


def checked_consent_memory(mib):
    require(type(mib) is int and 256 <= mib <= 16384 and mib % 256 == 0,
            'consent memory must be 256 through 16384 MiB in 256 MiB steps')
    return mib


def worker_runtime_access(service, r):
    """Hide all home trees while exposing only this controller's user manager."""
    require(r.get('workerTask') and type(r['uid']) is int and r['uid'] > 0, 'worker runtime identity refused')
    own = f'BindPaths=/run/user/{r["uid"]}\n'.encode()
    protections = re.findall(rb'^ProtectHome=.*$', service, re.MULTILINE)
    binds = [line+b'\n' for line in service.splitlines() if line.startswith(b'BindPaths=')]
    require((protections == [b'ProtectHome=yes'] and not binds)
            or (protections == [b'ProtectHome=tmpfs'] and binds == [own]), 'worker runtime mounts differ')
    if protections == [b'ProtectHome=tmpfs']:
        return service
    return service.replace(b'ProtectHome=yes\n', b'ProtectHome=tmpfs\n'+own)


def worker_runtime_access_upgrade(store, helper):
    _, base, r = load(store, helper)
    stopped_controller_units(r)
    require(r.get('workerTask'), 'worker runtime access requires a worker controller')
    unit = r['units'][0]; path = UNITS / unit; stage_path = base/'stage.json'
    intent_path = base/'worker-runtime-access.json'
    def archive(digest, kind):
        require(isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest), 'worker runtime archive hash malformed')
        return base/'configs'/('worker-runtime-access-'+digest+'.'+kind)
    if not intent_path.exists() and not intent_path.is_symlink():
        stage = checked_units(base, r)
        old_stage = read_file(stage_path, 0, 65536, required_mode=0o600)
        require(strict_json(old_stage) == stage, 'worker runtime stage changed')
        old_unit = read_file(path, 0, 16384, required_mode=0o644)
        new_unit = worker_runtime_access(old_unit, r)
        stage['units'][unit] = sha(new_unit)
        intent = {'protocol':'mini-controller-worker-runtime-access-v1', 'store':store, 'uid':r['uid']}
        for name,kind,raw in (('oldStage','stage',old_stage),('newStage','stage',encoded(stage)),
                              ('oldUnit','service',old_unit),('newUnit','service',new_unit)):
            intent[name+'Sha256'] = sha(raw)
            publish_exact(archive(sha(raw),kind),raw)
        publish_exact(intent_path,encoded(intent))
    intent = strict_json(read_file(intent_path,0,4096,required_mode=0o600))
    require(set(intent) == {'protocol','store','uid','oldStageSha256','newStageSha256','oldUnitSha256','newUnitSha256'}
            and intent['protocol'] == 'mini-controller-worker-runtime-access-v1' and intent['store'] == store
            and intent['uid'] == r['uid'], 'worker runtime access intent differs')
    kept = {}
    for name,kind in (('oldStage','stage'),('newStage','stage'),('oldUnit','service'),('newUnit','service')):
        digest = intent[name+'Sha256']; kept[name] = read_file(archive(digest,kind),0,65536,required_mode=0o600)
        require(sha(kept[name]) == digest,'worker runtime archive differs')
    expected = strict_json(kept['oldStage']); expected['units'][unit] = sha(kept['newUnit'])
    require(encoded(expected) == kept['newStage'] and worker_runtime_access(kept['oldUnit'],r) == kept['newUnit'],
            'worker runtime revision exceeds own runtime access')
    require(sha(read_file(stage_path,0,65536,required_mode=0o600)) in
            (intent['oldStageSha256'],intent['newStageSha256']),'stage is outside worker runtime access revision')
    checked_units(base,r,controller_upgrade_hashes=(intent['oldUnitSha256'],intent['newUnitSha256']))
    replace_root_record(path,kept['newUnit'],0o644)
    replace_root_record(stage_path,kept['newStage'],0o600)
    run(['/usr/bin/systemctl','daemon-reload']); checked_units(base,r)
    return {'store':store,'workerRuntimeAccessUpgrade':str(intent_path),'runtimeDirectory':f'/run/user/{r["uid"]}',
            'stageSha256':intent['newStageSha256'],'nativeOperationSubmitted':False}


def consent_memory_transition(stage, service, service_name, mib):
    mib = checked_consent_memory(mib)
    matches = list(re.finditer(rb'^MemoryMax=[0-9]+[MG]$', service, re.MULTILINE))
    require(len(matches) == 1, 'consent service memory setting differs')
    match = matches[0]
    new_service = service[:match.start()] + f'MemoryMax={mib}M'.encode() + service[match.end():]
    changed = strict_json(encoded(stage))
    changed['consentMemoryMiB'] = mib
    changed['consentMemoryRevision'] = 'consent-memory-' + str(mib) + '-' + sha(encoded(stage))
    changed['units'][service_name] = sha(new_service)
    return changed, new_service


def consent_memory_upgrade(store, helper, mib_arg):
    """Change an operator resource limit with all native authority pins intact."""
    require(re.fullmatch('[1-9][0-9]{2,4}', mib_arg), 'consent memory argument malformed')
    mib = checked_consent_memory(int(mib_arg))
    _, base, r = load(store, helper)
    require(has_consent(r), 'consent memory revision requires version-2 provisioning')
    stopped_controller_units(r)
    stage_path = base / 'stage.json'
    current = strict_json(read_file(stage_path, 0, 65536, required_mode=0o600))
    prefix = (current.get('consentMemoryRevision') if current.get('consentMemoryMiB') == mib
              else 'consent-memory-' + str(mib) + '-' + sha(encoded(current)))
    require(isinstance(prefix, str) and re.fullmatch('consent-memory-' + str(mib) + '-[0-9a-f]{64}', prefix),
            'consent memory revision malformed')
    intent_path = base / (prefix + '.json')
    unit = r['units'][4]; unit_path = UNITS / unit
    if current.get('consentMemoryMiB') == mib:
        checked_units(base, r)
        service = read_file(unit_path, 0, 16384, required_mode=0o644)
        require(re.findall(rb'^MemoryMax=.*$', service, re.MULTILINE) == [f'MemoryMax={mib}M'.encode()],
                'recorded consent memory differs from unit')
        # Other exact upgrades may have followed this resource revision. Do not
        # replay an old stage over their pins; the current verified unit suffices.
        run(['/usr/bin/systemctl', 'daemon-reload'])
        return {'store': store, 'consentMemoryUpgrade': str(intent_path), 'memoryMiB': mib,
                'stageSha256': sha(encoded(current)), 'nativeOperationSubmitted': False, 'alreadyConfigured': True}
    def archive(digest, kind):
        require(isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest), 'consent memory archive hash malformed')
        return base / 'configs' / (prefix + '-' + digest + '.' + kind)
    if not intent_path.exists() and not intent_path.is_symlink():
        stage = checked_units(base, r)
        old_stage = read_file(stage_path, 0, 65536, required_mode=0o600)
        require(strict_json(old_stage) == stage, 'consent memory stage changed')
        old_unit = read_file(unit_path, 0, 16384, required_mode=0o644)
        next_stage, next_unit = consent_memory_transition(stage, old_unit, unit, mib)
        intent = {'protocol': 'mini-controller-consent-memory-v1', 'store': store, 'memoryMiB': mib}
        for name, kind, raw in (('oldStage', 'stage', old_stage), ('newStage', 'stage', encoded(next_stage)),
                                ('oldUnit', 'service', old_unit), ('newUnit', 'service', next_unit)):
            intent[name + 'Sha256'] = sha(raw)
            publish_exact(archive(sha(raw), kind), raw)
        publish_exact(intent_path, encoded(intent))
    intent = strict_json(read_file(intent_path, 0, 4096, required_mode=0o600))
    require(set(intent) == {'protocol', 'store', 'memoryMiB', 'oldStageSha256', 'newStageSha256', 'oldUnitSha256', 'newUnitSha256'}
            and intent['protocol'] == 'mini-controller-consent-memory-v1' and intent['store'] == store
            and intent['memoryMiB'] == mib, 'consent memory intent differs')
    kept = {}
    for name, kind in (('oldStage', 'stage'), ('newStage', 'stage'), ('oldUnit', 'service'), ('newUnit', 'service')):
        digest = intent[name + 'Sha256']
        kept[name] = read_file(archive(digest, kind), 0, 65536, required_mode=0o600)
        require(sha(kept[name]) == digest, 'consent memory archived bytes differ')
    expected_stage, expected_unit = consent_memory_transition(strict_json(kept['oldStage']), kept['oldUnit'], unit, mib)
    require(expected_stage['consentMemoryRevision'] == prefix and encoded(expected_stage) == kept['newStage']
            and expected_unit == kept['newUnit'], 'consent memory change exceeds resource setting')
    require(sha(read_file(stage_path, 0, 65536, required_mode=0o600)) in
            (intent['oldStageSha256'], intent['newStageSha256']), 'stage is outside consent memory revision')
    checked_units(base, r, consent_upgrade_hashes=(intent['oldUnitSha256'], intent['newUnitSha256']))
    replace_root_record(unit_path, kept['newUnit'], 0o644)
    replace_root_record(stage_path, kept['newStage'], 0o600)
    run(['/usr/bin/systemctl', 'daemon-reload'])
    checked_units(base, r)
    return {'store': store, 'consentMemoryUpgrade': str(intent_path), 'memoryMiB': mib,
            'stageSha256': intent['newStageSha256'], 'nativeOperationSubmitted': False}


def status_proxy_transition(stage, r, base, service, sock, digest):
    """Add only the status listener and a pinned auxiliary transport executable."""
    require(r.get('workerTask'), 'status proxy upgrade requires a worker controller')
    require(re.fullmatch('[0-9a-f]{64}', digest), 'status proxy digest malformed')
    old_name = stage.get('statusProxy', {}).get('binary', 'mini')
    require(old_name == 'mini' or re.fullmatch('mini-status-[0-9a-f]{64}', old_name), 'old status proxy name malformed')
    name = 'mini-status-' + digest
    old = f'ExecStart={base}/bin/{old_name} serve-agent-operator-proxy '.encode()
    new = f'ExecStart={base}/bin/{name} serve-agent-operator-proxy '.encode()
    require(service.count(old) == 1, 'status proxy service command differs')
    next_service = service.replace(old, new)
    first = f'ListenStream={r["home"]}/operator/mini.sock\n'.encode()
    second = f'ListenStream={r["home"]}/operator/mini.control\n'.encode()
    listeners = [line + b'\n' for line in sock.splitlines() if line.startswith(b'ListenStream=')]
    require(listeners in ([first], [first, second]), 'status proxy listener layout differs')
    next_socket = sock.replace(first, first + second) if listeners == [first] else sock
    changed = strict_json(encoded(stage))
    changed['statusProxy'] = {'binary': name, 'sha256': digest}
    changed['units'][r['units'][1]] = sha(next_socket)
    changed['units'][r['units'][2]] = sha(next_service)
    return changed, next_service, next_socket


def status_proxy_upgrade(store, helper, source_arg):
    """Stopped, resumable transport-only publication; native bindings stay fixed."""
    _, base, r = load(store, helper)
    stopped_controller_units(r)
    require(r.get('workerTask'), 'status proxy upgrade requires a worker controller')
    source = read_file(canonical(source_arg), r['operatorUid'], 256 * 1024 * 1024, executable=True)
    digest = sha(source)
    prefix = 'status-proxy-upgrade-' + digest
    intent_path = base / (prefix + '.json')
    stage_path = base / 'stage.json'
    service_path, socket_path = UNITS / r['units'][2], UNITS / r['units'][1]
    def archive(value, kind):
        require(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value), 'status proxy archive hash malformed')
        return base / 'configs' / (prefix + '-' + value + '.' + kind)
    if not intent_path.exists() and not intent_path.is_symlink():
        stage = checked_units(base, r)
        old_stage = read_file(stage_path, 0, 65536, required_mode=0o600)
        require(strict_json(old_stage) == stage, 'status proxy stage changed')
        old_service = read_file(service_path, 0, 16384, required_mode=0o644)
        old_socket = read_file(socket_path, 0, 16384, required_mode=0o644)
        next_stage, next_service, next_socket = status_proxy_transition(stage, r, base, old_service, old_socket, digest)
        new_stage = encoded(next_stage)
        intent = {'protocol': 'mini-controller-status-proxy-upgrade-v1', 'store': store, 'binarySha256': digest}
        for name, kind, raw in (('oldStage', 'stage', old_stage), ('newStage', 'stage', new_stage),
                                ('oldService', 'service', old_service), ('newService', 'service', next_service),
                                ('oldSocket', 'socket', old_socket), ('newSocket', 'socket', next_socket)):
            intent[name + 'Sha256'] = sha(raw)
            publish_exact(archive(sha(raw), kind), raw)
        publish_exact(intent_path, encoded(intent))
    intent = strict_json(read_file(intent_path, 0, 4096, required_mode=0o600))
    fields = {'protocol', 'store', 'binarySha256'} | {name + 'Sha256' for name in
              ('oldStage', 'newStage', 'oldService', 'newService', 'oldSocket', 'newSocket')}
    require(set(intent) == fields and intent['protocol'] == 'mini-controller-status-proxy-upgrade-v1'
            and intent['store'] == store and intent['binarySha256'] == digest, 'status proxy upgrade intent differs')
    kept = {}
    for name, kind in (('oldStage', 'stage'), ('newStage', 'stage'), ('oldService', 'service'),
                       ('newService', 'service'), ('oldSocket', 'socket'), ('newSocket', 'socket')):
        value = intent[name + 'Sha256']
        kept[name] = read_file(archive(value, kind), 0, 65536, required_mode=0o600)
        require(sha(kept[name]) == value, 'status proxy archived bytes differ')
    expected_stage, expected_service, expected_socket = status_proxy_transition(
        strict_json(kept['oldStage']), r, base, kept['oldService'], kept['oldSocket'], digest)
    require(encoded(expected_stage) == kept['newStage'] and expected_service == kept['newService']
            and expected_socket == kept['newSocket'], 'status proxy upgrade exceeds transport change')
    require(sha(read_file(stage_path, 0, 65536, required_mode=0o600)) in
            (intent['oldStageSha256'], intent['newStageSha256']), 'stage is outside status proxy upgrade')
    checked_units(base, r,
                  proxy_upgrade_hashes=(intent['oldServiceSha256'], intent['newServiceSha256']),
                  socket_upgrade_hashes=(intent['oldSocketSha256'], intent['newSocketSha256']))
    binary = base / 'bin' / ('mini-status-' + digest)
    publish_exact(binary, source, mode=0o755, bound=256 * 1024 * 1024)
    replace_root_record(service_path, kept['newService'], 0o644)
    replace_root_record(socket_path, kept['newSocket'], 0o644)
    replace_root_record(stage_path, kept['newStage'], 0o600)
    run(['/usr/bin/systemctl', 'daemon-reload'])
    checked_units(base, r)
    return {'store': store, 'statusProxyUpgrade': str(intent_path), 'binarySha256': digest,
            'stageSha256': intent['newStageSha256'], 'nativeOperationSubmitted': False}


def relocated_operator_stage(stage, unit, proxy_unit, upstream, identity):
    old = f'--upstream {stage["upstreamSocket"]} --config '.encode()
    new = f'--upstream {upstream} --config '.encode()
    require(unit.count(old) == 1, 'operator proxy does not have one exact upstream argument')
    changed_unit = unit.replace(old, new)
    changed = strict_json(encoded(stage))
    changed['upstreamSocket'] = str(upstream)
    changed['upstreamIdentity'] = identity
    changed['units'][proxy_unit] = sha(changed_unit)
    return changed, changed_unit


def operator_endpoint_upgrade(store, helper, socket_arg):
    """Stopped transport relocation; Store/config/custody/native intents stay fixed."""
    _, base, r = load(store, helper)
    stopped_controller_units(r)
    upstream = canonical(socket_arg); op = r['operatorUid']
    ancestry(upstream.parent, {0, op}); metadata(upstream.parent, op, 0o700)
    endpoint = metadata(upstream, op, 0o600)
    require(stat.S_ISSOCK(endpoint.st_mode), 'operator successor is not a private socket')
    settings = read_file(base / 'proxy/config.json', op, 1048576, required_mode=0o600)
    require(read_file(upstream.with_suffix('.config'), op, 1048576, required_mode=0o600) == settings,
            'operator successor has different Store settings')
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as peer:
        peer.settimeout(2); peer.connect(str(upstream))
        _, uid, _ = struct.unpack('3i', peer.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))
        require(uid == op, 'operator successor peer identity differs')
    stage_path = base / 'stage.json'; unit_path = UNITS / r['units'][2]
    name = 'operator-endpoint-' + sha(str(upstream).encode())
    intent_path = base / (name + '.json')
    def archive(digest, kind):
        require(re.fullmatch('[0-9a-f]{64}', digest), 'operator endpoint archive hash malformed')
        return base / 'configs' / (name + '-' + digest + '.' + kind)
    if not intent_path.exists() and not intent_path.is_symlink():
        stage = checked_units(base, r)
        old_stage = read_file(stage_path, 0, 65536, required_mode=0o600)
        require(strict_json(old_stage) == stage, 'operator endpoint stage changed')
        old_unit = read_file(unit_path, 0, 16384, required_mode=0o644)
        next_stage, next_unit = relocated_operator_stage(stage, old_unit, r['units'][2], upstream,
                                                        [endpoint.st_dev, endpoint.st_ino])
        new_stage = encoded(next_stage)
        intent = {'protocol': 'mini-controller-operator-endpoint-v1', 'store': store, 'upstream': str(upstream),
                  'oldStageSha256': sha(old_stage), 'newStageSha256': sha(new_stage),
                  'oldUnitSha256': sha(old_unit), 'newUnitSha256': sha(next_unit)}
        for raw, kind in ((old_stage, 'stage'), (new_stage, 'stage'), (old_unit, 'service'), (next_unit, 'service')):
            publish_exact(archive(sha(raw), kind), raw)
        publish_exact(intent_path, encoded(intent))
    intent = strict_json(read_file(intent_path, 0, 4096, required_mode=0o600))
    require(set(intent) == {'protocol', 'store', 'upstream', 'oldStageSha256', 'newStageSha256', 'oldUnitSha256', 'newUnitSha256'}
            and intent['protocol'] == 'mini-controller-operator-endpoint-v1' and intent['store'] == store
            and intent['upstream'] == str(upstream), 'operator endpoint intent differs')
    kept = {}
    for key, kind in (('oldStage', 'stage'), ('newStage', 'stage'), ('oldUnit', 'service'), ('newUnit', 'service')):
        digest = intent[key + 'Sha256']; kept[key] = read_file(archive(digest, kind), 0, 65536, required_mode=0o600)
        require(sha(kept[key]) == digest, 'operator endpoint archive differs')
    old_stage, new_stage = strict_json(kept['oldStage']), strict_json(kept['newStage'])
    expected_stage, expected_unit = relocated_operator_stage(old_stage, kept['oldUnit'], r['units'][2], upstream,
                                                            new_stage['upstreamIdentity'])
    require(expected_stage == new_stage and expected_unit == kept['newUnit'], 'operator endpoint change exceeds transport coordinates')
    require(sha(read_file(stage_path, 0, 65536, required_mode=0o600)) in
            (intent['oldStageSha256'], intent['newStageSha256']), 'stage is outside operator endpoint transition')
    checked_units(base, r, proxy_upgrade_hashes=(intent['oldUnitSha256'], intent['newUnitSha256']))
    replace_root_record(unit_path, kept['newUnit'], 0o644)
    replace_root_record(stage_path, kept['newStage'], 0o600)
    run(['/usr/bin/systemctl', 'daemon-reload']); checked_units(base, r)
    return {'store': store, 'operatorEndpointUpgrade': str(intent_path), 'operatorSocket': str(upstream),
            'previousOperatorSocket': old_stage['upstreamSocket'], 'stageSha256': intent['newStageSha256'],
            'observedSocketIdentity': [endpoint.st_dev, endpoint.st_ino]}


def enroll(store, helper, source_arg):
    _, base, r = load(store, helper)
    require(has_consent(r), 'native controller enrollment requires version-2 provisioning')
    stage = checked_units(base, r)
    require('storage' in stage['consent'], 'native enrollment requires qualified consent storage access')
    no_processes(r['uid'])
    runtime = manager_properties(r['units'][0])
    require(runtime.get('LoadState') == 'loaded' and runtime.get('Transient') == 'no'
            and runtime.get('FragmentPath') == str(UNITS / r['units'][0]) and runtime.get('User') == str(r['uid'])
            and runtime.get('ActiveState') == 'inactive' and runtime.get('MainPID', '0') == '0'
            and runtime.get('ControlPID', '0') == '0', 'controller runtime must be stopped for native enrollment')
    raw = read_file(canonical(source_arg), r['operatorUid'], 8192, required_mode=0o600)
    request = strict_json(raw)
    require(isinstance(request, dict) and set(request) in ({'protocol', 'mode', 'expectedBindingSha256', 'targetConfigSha256'},
                {'protocol', 'mode', 'expectedBindingSha256', 'targetConfigSha256', 'residentState'})
            and request['protocol'] == 'mini-controller-application-enrollment-v1'
            and request['mode'] in ('bootstrap-dispatch', 'application')
            and all(isinstance(request[key], str) and re.fullmatch('[0-9a-f]{64}', request[key])
                    for key in ('expectedBindingSha256', 'targetConfigSha256')), 'native enrollment request shape refused')
    home = Path(r['home'])
    config = read_file(worker_config(r), r['uid'], 524288, required_mode=0o600)
    require(sha(config) == request['targetConfigSha256']
            and read_file(base / 'configs' / (sha(config) + '.json'), 0, 524288, required_mode=0o600) == config,
            'native enrollment config differs from retained revision')
    if 'residentState' in request:
        state = strict_json(config).get('stateDir')
        resident = request['residentState']
        require(isinstance(state, str) and isinstance(resident, str)
                and str(Path(resident)) == resident and Path(resident).is_absolute()
                and Path(resident).parent == Path(state) and Path(resident).name not in ('.', '..'),
                'native enrollment resident state must be an exact direct child of stateDir')
    # Source reads need the separately pinned operator services. The controller
    # runtime remains stopped; no background controller work is launched.
    prior = {}
    for unit in r['units'][1:]:
        value = manager_properties(unit)
        require(value.get('LoadState') == 'loaded' and value.get('Transient') == 'no'
                and value.get('FragmentPath') == str(UNITS / unit), 'enrollment prerequisite unit differs')
        require(value.get('ActiveState') in ('active', 'inactive'), 'enrollment prerequisite unit is transitioning or failed')
        prior[unit] = value['ActiveState']
        if unit.endswith('.service'):
            require(value.get('User') == str(r['operatorUid']), 'enrollment prerequisite service user differs')
    r['_consentEnvironment'] = consent_environment(r, base, stage['consent'])
    path = home / 'enroll-requests' / (sha(raw) + '.json')
    def setup():
        if not path.parent.exists() and not path.parent.is_symlink():
            mkdir(path.parent, r['uid'], r['gid'])
        ancestry(path.parent, {0, r['uid']}); metadata(path.parent, r['uid'], 0o700)
        publish_exact(path, raw, r['uid'], r['gid'], bound=8192)
    try:
        run(['/usr/bin/systemctl', 'start', r['units'][1], r['units'][3], r['units'][4]])
        return controller_child(r, [str(base / 'bin/grain-runtime'), 'application-enroll', 'stopped',
                                   str(worker_config(r)), str(path)], setup, timeout=1800)
    finally:
        # Socket activation may also have started the operator proxy service.
        # Restore only helpers observed inactive, including after native refusal;
        # never undo enrollment or erase its retained request/record.
        inactive = [unit for unit, state in prior.items() if state == 'inactive']
        if inactive:
            run(['/usr/bin/systemctl', 'stop', *inactive])


def service(store, helper, action):
    _, base, r = load(store, helper)
    stage = checked_units(base, r, partial=(action == 'stop'))
    for name in r['units']:
        observed = manager_properties(name)
        if observed.get('LoadState') == 'not-found' and action == 'stop':
            continue
        require(observed.get('FragmentPath') == str(UNITS / name) and observed.get('Transient') == 'no',
                'controller manager unit identity differs')
        if name.endswith('.service'):
            expected = r['uid'] if name == r['units'][0] else r['operatorUid']
            require(observed.get('User') == str(expected), 'controller manager unit user differs')
    if action == 'start':
        if r.get('workerTask'):
            require((base / 'worker-published.json').exists(), 'worker configuration has not been published')
            worker_manager(base, r, 'start')
        if has_consent(r):
            require('storage' in stage['consent'], 'consent Store sandbox needs explicit stopped storage upgrade')
            run(['/usr/bin/systemctl', 'start', r['units'][3], r['units'][4]])
        run(['/usr/bin/systemctl', 'start', r['units'][1], r['units'][0]])
        ready = worker_state(r) / 'control.sock'
        deadline = time.monotonic() + 180
        while True:
            observed = manager_properties(r['units'][0])
            require(observed.get('ActiveState') in ('active', 'activating'),
                    'controller unit exited before control readiness; inspect its journal')
            try:
                m = metadata(ready, r['uid'], 0o600)
                require(stat.S_ISSOCK(m.st_mode), 'controller control endpoint is not a socket')
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as connection:
                    connection.settimeout(1)
                    connection.connect(str(ready))
                    pid, uid, _ = struct.unpack('3i', connection.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))
                    require(uid == r['uid'] and str(pid) == observed.get('MainPID'),
                            'controller control peer differs from exact manager process')
                break
            except (FileNotFoundError, ConnectionRefusedError, TimeoutError):
                require(time.monotonic() < deadline, 'controller control readiness timed out; no tool was sent')
                time.sleep(.2)
    else:
        present = [n for n in r['units'] if (UNITS / n).exists()]
        if present:
            run(['/usr/bin/systemctl', 'stop', *present])
        worker_manager(base, r, 'stop')
        no_processes(r['uid'])
    return {'store': store, 'action': action, 'units': r['units'],
            **({'consent': consent_readiness(base, r, stage)} if action == 'start' and has_consent(r) else {})}


def worker_attachment_limit(relative):
    # Declarations are inert input to the native typed-tool validator. The
    # installer admits only bounded files in this private attachment directory.
    if re.fullmatch(r'state/shared-app-refs/[A-Za-z0-9_-]+\.declaration\.json', relative):
        return 1024 * 1024
    require(re.fullmatch(r'state/shared-app-refs/[A-Za-z0-9-]+\.bin|state/attachments/[A-Za-z0-9-]+/grant/(?:seal\.json|call\.bin|submit-marker\.json|receipt\.json)', relative),
            'worker proof file refused')
    return 12_102_760


def config_update(store, helper, source_arg):
    _, base, r = load(store, helper)
    checked_units(base, r); worker_manager(base, r, 'stop'); no_processes(r['uid'])
    source = canonical(source_arg)
    worker = bool(r.get('workerTask'))
    limits = dict(FINAL_FILES)
    proof = {}
    if stat.S_ISDIR(source.lstat().st_mode):
        actual = set()
        allowed_dirs = {'state', 'state/shared-app-refs', 'state/oracle-grant'}
        for directory, dirs, files in os.walk(source, followlinks=False):
            for n in dirs:
                p = Path(directory) / n; metadata(p, r['operatorUid'])
                relative = str(p.relative_to(source))
                require(relative in allowed_dirs or (worker and re.fullmatch(r'state/(?:attachments(?:/[A-Za-z0-9-]+(?:/grant)?)?|shared-app-refs)', relative)), 'config bundle directory refused')
            actual.update(str((Path(directory) / n).relative_to(source)) for n in files)
            require(len(actual) <= (65 if worker else 1 + len(FINAL_FILES)), 'config bundle exceeds file bound')
        if worker:
            for relative in actual - {'controller.json'}:
                limits[relative] = worker_attachment_limit(relative)
        require('controller.json' in actual and actual <= {'controller.json'} | set(limits), 'config bundle files refused')
        data = read_file(source / 'controller.json', r['operatorUid'], 524288)
        proof = {n: read_file(source / n, r['operatorUid'], limits[n]) for n in actual - {'controller.json'}}
    else:
        data = read_file(source, r['operatorUid'], 524288)
    value = json.loads(data); home = Path(r['home'])
    require(sum(map(len, proof.values())) <= 32 * 1024 * 1024, 'config proof bytes exceed bound')
    if not worker:
        require(value.get('commands') == [] and value.get('stateDir') == str(home / 'state')
                and value.get('controlSocket') == str(home / 'state/control.sock'), 'controller config layout differs')
        if has_consent(r):
            require(value.get('hostConfig') == str(home / 'host-config.json')
                    and value.get('cwd') == str(home / 'workspace'), 'consent-bound controller config layout differs')
    old = read_file(worker_config(r), r['uid'], 524288, required_mode=0o600)
    require(read_file(base / 'configs' / (sha(old) + '.json'), 0, 524288, required_mode=0o600) == old,
            'current config differs from retained revision')
    if worker:
        validate_worker_config(value, base, r, strict_json(old))
        previous = strict_json(old)
        unchanged_worker_config(previous, value, worker_state(r))
        unchanged_worker_tool(previous['toolTask'], value['toolTask'])
    root = worker_layout(r)
    for name, content in proof.items():
        path = root / name
        if path.exists() or path.is_symlink():
            require(read_file(path, r['uid'], limits[name]) == content, 'retained grant evidence differs')
    target = base / 'configs' / (sha(data) + '.json')
    intent_path = base / 'configs' / ('config-publication-' + sha(data) + '.json')
    if not intent_path.exists() and not intent_path.is_symlink():
        require(not target.exists() or old == data, 'retained noncurrent config lacks a publication intent')
        intent = {'protocol': 'mini-spk-controller-config-publication-v1', 'store': store,
                  'previousSha256': sha(old), 'configurationSha256': sha(data),
                  'proofSha256': {name: sha(content) for name, content in proof.items()}}
        publish_exact(intent_path, encoded(intent))
    intent = strict_json(read_file(intent_path, 0, 65536 if worker else 4096, required_mode=0o600))
    require(isinstance(intent, dict) and set(intent) ==
            {'protocol', 'store', 'previousSha256', 'configurationSha256', 'proofSha256'}
            and intent['protocol'] == 'mini-spk-controller-config-publication-v1' and intent['store'] == store
            and isinstance(intent['previousSha256'], str) and re.fullmatch('[0-9a-f]{64}', intent['previousSha256'])
            and intent['configurationSha256'] == sha(data)
            and intent['proofSha256'] == {name: sha(content) for name, content in proof.items()}
            and sha(old) in (intent['previousSha256'], sha(data)), 'config publication is outside exact old/new intent')
    previous = read_file(base / 'configs' / (intent['previousSha256'] + '.json'), 0, 524288, required_mode=0o600)
    require(sha(previous) == intent['previousSha256'], 'config publication original revision differs')
    publish_exact(target, data, bound=524288)
    for name, content in proof.items():
        path = root / name
        for parent in reversed(path.parent.relative_to(root).parents):
            directory = root / parent
            if not directory.exists() and not directory.is_symlink(): mkdir(directory, r['uid'], r['gid'])
            metadata(directory, r['uid'], 0o700)
        if not path.parent.exists() and not path.parent.is_symlink(): mkdir(path.parent, r['uid'], r['gid'])
        ancestry(path.parent, {0, r['uid']})
        publish_exact(path, content, r['uid'], r['gid'], bound=limits[name])
    pending = root / '.controller-next.json'
    publish_exact(pending, data, r['uid'], r['gid'], bound=524288)
    os.replace(pending, worker_config(r))
    sync_directory(root)
    return {'store': store, 'configurationSha256': sha(data), 'previousSha256': intent['previousSha256'],
            'publication': str(intent_path), 'replayed': old == data}


def controller_child(r, argv, setup=None, timeout=1200, pass_fds=()):
    def identity():
        os.setsid(); os.setgroups([]); os.setgid(r['gid']); os.setuid(r['uid']); os.umask(0o077)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        resource.setrlimit(resource.RLIMIT_NOFILE, (256, 256))
        if setup:
            setup()
    proc = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            preexec_fn=identity, pass_fds=pass_fds, env={**ENV, 'HOME': r['home'], **r.get('_consentEnvironment', {}),
                                 'MINI_CONSENT_ANCHOR_DIR': str(Path(r['home']) / 'a'),
                                 'MINI_CODEC_RESIDENT': '0', 'MINI_CONSENT_RESIDENT': '0'})
    try:
        total = 0; deadline = time.monotonic() + timeout
        sel = selectors.DefaultSelector()
        sel.register(proc.stdout, selectors.EVENT_READ, sys.stdout.buffer)
        sel.register(proc.stderr, selectors.EVENT_READ, sys.stderr.buffer)
        while sel.get_map():
            require(time.monotonic() < deadline, 'controller command timed out; retain request ID, do not resend')
            for key, _ in sel.select(1):
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    sel.unregister(key.fileobj); continue
                total += len(chunk); require(total <= 16 * 1024 * 1024, 'controller output exceeds bound')
                key.data.write(chunk); key.data.flush()
        return proc.wait(timeout=10)
    finally:
        if proc.poll() is None:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait(timeout=10)


def tool(store, helper, verb, request_id, extra):
    _, base, r = load(store, helper)
    stage = checked_units(base, r)
    if has_consent(r):
        r['_consentEnvironment'] = consent_environment(r, base, stage['consent'])
    require(re.fullmatch('[0-9a-f]{32}', request_id), 'request ID must be 32 lowercase hex')
    home = Path(r['home']); runtime = str(base / 'bin/grain-runtime'); socket = str(worker_state(r) / 'control.sock')
    if verb == 'tool':
        require(len(extra) == 2 and allowed_tool(extra[0]), 'unsupported controller tool')
        data = read_file(canonical(extra[1]), r['operatorUid'], 262144)
        require(isinstance(json.loads(data), dict), 'tool arguments must be an object')
        path = home / 'tool-requests' / (request_id + '.args.json')
        def setup():
            ancestry(path.parent, {0, r['uid']})
            write_new(path, data, r['uid'], r['gid'])
        return controller_child(r, [runtime, 'tool', socket, 'soft', request_id, extra[0], str(path)], setup)
    require(not extra and verb in ('tool-result', 'tool-ack'), 'unsupported controller result operation')
    return controller_child(r, [runtime, verb, socket, request_id])


def recover_session(store, helper, request_id):
    """One fixed private admin operation; no attach, resend, or result ACK."""
    _, base, r = load(store, helper)
    checked_units(base, r)
    require(re.fullmatch('[0-9a-f]{32}', request_id), 'request ID must be 32 lowercase hex')
    return controller_child(r, [str(base / 'bin/grain-runtime'), 'admin',
        str(worker_state(r) / 'admin.sock'), 'recover foreground session ' + request_id], timeout=1800)


def recover_api_unreserved(store, helper, request_id):
    """Ask native custody to audit an API intent which has no dispatch reservation."""
    require(isinstance(request_id, str) and re.fullmatch('[0-9a-f]{32}', request_id),
            'request ID must be 32 lowercase hex')
    return controller_admin_fixed(store, helper, 'recover foreground api-unreserved ' + request_id)


def reconcile_controller(store, helper, selector):
    commands = {'parent': 'reconcile parent', 'effects': 'reconcile effects',
                'parent-audited': 'reconcile parent audited', 'worker-audited': 'reconcile worker audited',
                'foreground-audited': 'reconcile foreground audited'}
    require(selector in commands, 'unsupported controller reconciliation')
    return controller_admin_fixed(store, helper, commands[selector])


def reconcile_prompt(store, helper, operation):
    require(isinstance(operation,str) and re.fullmatch('[1-9][0-9]{0,19}',operation)
            and int(operation) < 2**64, 'prompt operation ID must be canonical nonzero u64')
    return controller_admin_fixed(store,helper,'reconcile prompt audited '+operation)


def worker_unit_observation(store, helper):
    """Observe only the exact retained worker through its registered manager."""
    _, base, r = load(store, helper)
    stage = checked_units(base, r)
    stopped_controller_units(r)
    require(r.get('workerTask'), 'worker observation requires a worker controller')
    raw = read_file(worker_state(r)/'journal.json',r['uid'],8*1024*1024,required_mode=0o600)
    child = strict_json(raw).get('child')
    require(isinstance(child,dict) and type(child.get('operationId')) is int and child['operationId'] > 0,
            'retained worker operation absent')
    stem = f'mini-grain-t{r["workerTask"]}-o{child["operationId"]}'
    require(child.get('unit') == stem, 'retained worker unit differs from task and operation')
    unit = stem + '.service'
    manager = stage['worker']['userManager']
    require(manager == f'user@{r["uid"]}.service','worker manager differs')
    before = manager_properties(manager)
    require(before.get('ActiveState') in ('active','inactive','failed'), 'worker manager is transitioning')
    started = before['ActiveState'] != 'active'
    def identity():
        os.setgroups([]); os.setgid(r['gid']); os.setuid(r['uid']); os.umask(0o077)
    if started: worker_manager(base,r,'start')
    try:
        observed = subprocess.run(['/usr/bin/systemctl','--user','show',unit,
            '--property=Id,LoadState,ActiveState,SubState,MainPID,ControlPID,ControlGroup,InvocationID'],
            stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30,
            preexec_fn=identity,env={**ENV,'HOME':r['home'],**worker_environment(base,r)})
        require(observed.returncode in (0,4) and len(observed.stdout)+len(observed.stderr) <= 65536,
                'worker manager observation failed')
        fields = {}
        for line in observed.stdout.decode().splitlines():
            key, sep, value = line.partition('=')
            require(sep and key not in fields and key in {'Id','LoadState','ActiveState','SubState','MainPID',
                    'ControlPID','ControlGroup','InvocationID'},'worker manager output malformed')
            fields[key] = value
        require(fields.get('Id') == unit and fields.get('LoadState') in ('loaded','not-found','masked','error'),
                'worker manager returned another unit')
        require(read_file(worker_state(r)/'journal.json',r['uid'],8*1024*1024,required_mode=0o600) == raw,
                'retained worker changed during observation')
        return {'protocol':'mini-controller-worker-observation-v1','store':store,'unit':unit,
                'journalSha256':sha(raw),'manager':manager,'managerStarted':started,'properties':fields,
                'nativeOperationSubmitted':False}
    finally:
        if started: worker_manager(base,r,'stop')


def controller_admin_fixed(store, helper, command):
    _, base, r = load(store, helper)
    checked_units(base, r)
    return controller_child(r, [str(base / 'bin/grain-runtime'), 'admin',
        str(worker_state(r) / 'admin.sock'), command], timeout=1800)


def controller_quiescence(store, helper):
    """Inspect fixed native resident custody; no caller command or path selection."""
    _, base, r = load(store, helper)
    checked_units(base, r)
    require(r.get('workerTask'), 'resident quiescence requires worker mode')
    state = worker_state(r)
    return controller_child(r, [str(base / 'bin/grain-runtime'), 'quiescence', 'inspect',
        str(state / 'admin.sock'), str(state / 'resident')], timeout=1800)


def export_state(store, helper, scope='all'):
    require(scope in ('all', 'application'), 'controller evidence scope refused')
    _, base, r = load(store, helper)
    checked_units(base, r)
    root = worker_state(r); files = {}; total = 0; directories = 0
    for directory, dirs, entries in os.walk(root, followlinks=False):
        if scope == 'application':
            relative = Path(directory).relative_to(root)
            dirs[:] = [name for name in dirs if relative == Path('.') and name == 'resident']
            entries = [name for name in entries if
                       (relative == Path('.') and (name == 'journal.json' or re.fullmatch(
                           r'provider-[0-9]{16}\.controller-request|application-api-(?:reply-)?[0-9]{16}\.json', name)))
                       or (relative == Path('resident') and name == 'resident.json')]
        directories += 1
        require(directories <= 1024 and len(Path(directory).relative_to(root).parts) <= 16, 'controller evidence directory bound exceeded')
        for name in dirs:
            metadata(Path(directory) / name, r['uid'])
        for name in entries:
            path = Path(directory) / name
            if stat.S_ISSOCK(path.lstat().st_mode):
                continue
            require(len(files) < 4096, 'controller evidence file bound exceeded')
            data = read_file(path, r['uid'], 8 * 1024 * 1024, allow_empty=True)
            total += len(data); require(total <= 32 * 1024 * 1024, 'controller evidence byte bound exceeded')
            files[str(path.relative_to(root))] = {'sha256': sha(data), 'base64': base64.b64encode(data).decode()}
    return {'protocol': 'mini-spk-controller-evidence-v1', 'store': store, 'files': files,
            **({'scope': scope} if scope != 'all' else {})}


def reserve_export(store, helper, attempt_text):
    _, base, r = load(store, helper)
    require(re.fullmatch('0|[1-9][0-9]{0,19}', attempt_text) and int(attempt_text) < 2**64,
            'dispatch attempt ID must be canonical decimal u64')
    prefix = f'agent-lifetime-reserve-{int(attempt_text):016}'
    root = worker_state(r) / prefix
    files = {}; total = 0
    for name in ('source.json', 'pin.json', 'request.bin', 'plan.bin', 'plan.frame',
                 'call.bin', 'receipt.json', 'submit-marker.json'):
        data = read_file(root / name, r['uid'], 12_102_760, required_mode=0o600)
        total += len(data)
        require(total <= 32 * 1024 * 1024, 'selected reserve evidence exceeds byte bound')
        files[prefix + '/' + name] = {'sha256': sha(data), 'base64': base64.b64encode(data).decode()}
    return {'protocol': 'mini-spk-controller-evidence-v1', 'store': store, 'files': files}


def bounded_service_journal(unit, invocation):
    args = ['/usr/bin/journalctl', '--quiet', '--no-pager', '--lines=256',
            '--output=short-iso-precise', '--unit=' + unit]
    if invocation:
        require(re.fullmatch('[0-9a-f]{32}', invocation) is not None, 'service invocation identity malformed')
        args.append('_SYSTEMD_INVOCATION_ID=' + invocation)
    proc = subprocess.Popen(args, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, env=ENV, start_new_session=True)
    output = bytearray(); deadline = time.monotonic() + 20
    try:
        with selectors.DefaultSelector() as ready:
            ready.register(proc.stdout, selectors.EVENT_READ)
            while ready.get_map():
                require(time.monotonic() < deadline, 'service journal read exceeded deadline')
                for key, _ in ready.select(min(1, max(0, deadline - time.monotonic()))):
                    chunk = os.read(key.fileobj.fileno(), 65536)
                    if not chunk:
                        ready.unregister(key.fileobj)
                    else:
                        output.extend(chunk)
                        require(len(output) <= 1024 * 1024, 'service journal output exceeds 1 MiB bound')
        require(proc.wait(timeout=max(.1, deadline - time.monotonic())) == 0, 'service journal query failed')
        return bytes(output)
    finally:
        if proc.poll() is None:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait(timeout=10)
        proc.stdout.close()


def service_logs(store, helper):
    _, base, r = load(store, helper)
    stage = checked_units(base, r, partial=True)
    result = []
    # Names come exclusively from the checked root receipt/stage. No caller
    # unit, invocation, path, executable, or journal expression is accepted.
    for unit in r['units']:
        if not unit.endswith('.service') or unit not in stage['units']:
            continue
        observed = manager_properties(unit)
        require(observed.get('LoadState') == 'loaded'
                and observed.get('FragmentPath') == str(UNITS / unit) and observed.get('Transient') == 'no',
                'service journal manager identity differs')
        expected = r['uid'] if unit == r['units'][0] else r['operatorUid']
        require(observed.get('User') == str(expected), 'service journal unit user differs')
        invocation = observed.get('InvocationID', '')
        raw = bounded_service_journal(unit, invocation)
        after = manager_properties(unit)
        require(after.get('InvocationID', '') == invocation and after.get('FragmentPath') == observed['FragmentPath'],
                'service invocation changed while reading journal')
        result.append({'unit': unit, 'invocationId': invocation or None,
                       'selection': 'observed-invocation' if invocation else 'fixed-unit-recent-history',
                       'sha256': sha(raw), 'bytes': len(raw), 'base64': base64.b64encode(raw).decode()})
    return {'protocol': 'mini-spk-controller-service-logs-v1', 'store': store,
            'maximumLinesPerService': 256, 'maximumBytesPerService': 1024 * 1024,
            'services': result, 'privateEvidence': True}


def preserve_consent_state(base, r):
    if not has_consent(r):
        return None
    source = base / 'consent/anchors'
    if not source.exists():
        require(not source.is_symlink(), 'consent anchor directory is a dangling link')
        return {'notCreated': True}
    metadata(source, r['operatorUid'], 0o700)
    limits = {'binding': 1024, 'frontier': 12_103_784, 'lock': 1}
    children = list(source.iterdir())
    require(len(children) <= 3 and all(p.name in limits for p in children), 'unexpected consent anchor files')
    # Also retain partial initialization (binding without frontier); never turn a
    # failed verifier into a fresh unanchored verifier by discarding its bytes.
    data = {p.name: read_file(p, r['operatorUid'], limits[p.name], allow_empty=p.name == 'lock', required_mode=0o600)
            for p in children}
    require(not data.get('lock'), 'consent lock contents differ')
    target = HISTORY / (r['store'] + '-consent')
    if not target.exists():
        mkdir(target)
    ancestry(target, {0}); metadata(target, 0, 0o700)
    require(set(p.name for p in target.iterdir()) <= set(data), 'retained consent archive differs')
    for name, content in data.items():
        path = target / name
        if path.exists() or path.is_symlink():
            require(read_file(path, 0, limits[name], allow_empty=name == 'lock', required_mode=0o600) == content,
                    'retained consent archive bytes differ')
        else:
            write_new(path, content)
    return {'directory': str(target), 'files': {name: {'sha256': sha(content), 'size': len(content)}
                                               for name, content in data.items()}}


def listener_pin(r):
    return f'MINI-PUBLIC-CONTROLLER/v1\n{r["uid"]}\n'.encode()


@contextlib.contextmanager
def stopped_public_listener(stage, r):
    public = canonical(stage['publicSocket'])
    ancestry(public.parent, {0, r['operatorUid']})
    path = public.with_suffix('.lock')
    fd = os.open(path, os.O_RDWR | os.O_NOFOLLOW | os.O_CLOEXEC)
    try:
        m = os.fstat(fd)
        require(stat.S_ISREG(m.st_mode) and m.st_uid == r['operatorUid'] and m.st_nlink == 1
                and stat.S_IMODE(m.st_mode) == 0o600, 'public listener lock custody refused')
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        require(fingerprint(m) == fingerprint(path.lstat()), 'public listener lock replaced')
        require(not public.exists() and not public.is_symlink(), 'public listener must be stopped with its socket absent')
        yield public
    finally:
        os.close(fd)


def public_acl_receipts(base, stage, r, public):
    entries = []
    for path in sorted(base.glob('acl-[0-9][0-9][0-9].json')):
        require(len(entries) < 64, 'public ACL receipt count exceeds bound')
        raw = read_file(path, 0, 16384, required_mode=0o600)
        intent = strict_json(raw)
        after = read_file(path.with_suffix('.after.json'), 0, 16384, required_mode=0o600)
        entry = strict_json(after)
        require({k: entry[k] for k in intent} == intent and entry in stage['acl'], 'public ACL receipt differs from stage')
        target = canonical(intent['path'])
        require(target == public or target in public.parents, 'public ACL target outside registered ancestry')
        if target != public:
            m = metadata(target)
            require(stat.S_ISDIR(m.st_mode) and m.st_uid in (0, r['operatorUid'])
                    and (m.st_dev, m.st_ino) == (intent['dev'], intent['ino'])
                    and acl_text(target) == entry['after'], 'public ancestor ACL or identity changed')
        entries.append({'receipt': path.name, 'sha256': sha(raw), 'afterSha256': sha(after), 'path': str(target)})
    require(len(entries) == len(stage['acl']) and sum(e['path'] == str(public) for e in entries) == 1,
            'public ACL receipt set differs')
    return entries


def public_listener_record(base, stage, r, public):
    raw = read_file(base / 'public-listener.json', 0, 16384, required_mode=0o600)
    value = strict_json(raw)
    require(set(value) == {'protocol', 'store', 'socket', 'controllerUid', 'operatorUid', 'binary',
                          'binarySha256', 'parentIdentity', 'aclReceipts', 'pinSha256'}
            and value['protocol'] == 'mini-spk-controller-public-listener-v1' and value['store'] == r['store']
            and value['socket'] == str(public) and value['controllerUid'] == r['uid']
            and value['operatorUid'] == r['operatorUid'] and value['binary'] == str(base / 'public-listener/mini')
            and value['pinSha256'] == sha(listener_pin(r)), 'public listener registration differs')
    m = metadata(public.parent, r['operatorUid'], 0o710)
    require(value['parentIdentity'] == [m.st_dev, m.st_ino]
            and value['aclReceipts'] == public_acl_receipts(base, stage, r, public), 'public listener custody differs')
    require(sha(read_file(base / 'public-listener/mini', 0, 256 * 1024 * 1024, True,
                          required_mode=0o555)) == value['binarySha256'], 'registered public listener binary changed')
    require(read_file(public.with_suffix('.controller'), r['operatorUid'], 128, required_mode=0o600)
            == listener_pin(r), 'public listener controller pin changed')
    return value


def controller_status(store, helper):
    _, base, r = load(store, helper)
    stage = checked_units(base, r)
    stopped_controller_units(r)
    raw = read_file(base / 'stage.json', 0, 65536, required_mode=0o600)
    require(strict_json(raw) == stage, 'stage changed during observation')
    home = Path(r['home'])
    config = read_file(worker_config(r), r['uid'], 524288, required_mode=0o600)
    require(read_file(base / 'configs' / (sha(config) + '.json'), 0, 524288, required_mode=0o600) == config,
            'controller configuration is not an exact retained revision')
    runtime = read_file(home / 'bin/grain-runtime', r['uid'], 256 * 1024 * 1024, True, required_mode=0o500)
    require(sha(runtime) == stage['binaries']['grain-runtime'], 'controller runtime copy differs')
    result = {'store': store, 'controllerUid': r['uid'], 'stageSha256': sha(raw),
              'runtimeSha256': sha(runtime), 'controllerConfigSha256': sha(config),
              'stopped': True, 'stoppedUnits': list(r['units']), 'consent': stage.get('consent')}
    if (base / 'public-listener.json').exists() or (base / 'public-listener.json').is_symlink():
        with stopped_public_listener(stage, r) as public:
            result['publicListener'] = public_listener_record(base, stage, r, public)
    return result


def register_public_listener(store, helper, binary_arg):
    registry, base, r = load(store, helper)
    stage = checked_units(base, r)
    stopped_controller_units(r)
    source = canonical(binary_arg)
    data = read_file(source, r['operatorUid'], 256 * 1024 * 1024, True)
    with stopped_public_listener(stage, r) as public:
        receipts = public_acl_receipts(base, stage, r, public)
        m = metadata(public.parent, r['operatorUid'], 0o710)
        require(acl_text(public.parent).splitlines() ==
                ['user::rwx', f'user:{r["uid"]}:--x', 'group::---', 'mask::--x', 'other::---', ''],
                'public parent must have only exact controller traversal ACL')
        value = {'protocol': 'mini-spk-controller-public-listener-v1', 'store': store,
                 'socket': str(public), 'controllerUid': r['uid'], 'operatorUid': r['operatorUid'],
                 'binary': str(base / 'public-listener/mini'), 'binarySha256': sha(data),
                 'parentIdentity': [m.st_dev, m.st_ino], 'aclReceipts': receipts, 'pinSha256': sha(listener_pin(r))}
        # Publish the immutable intent first. Explicit retries accept only the
        # same binary and policy after interruption; never adopt a new socket.
        publish_exact(base / 'public-listener.json', encoded(value), bound=16384)
        destination = base / 'public-listener'
        if not destination.exists(): mkdir(destination, mode=0o755)
        metadata(destination, 0, 0o755)
        publish_exact(destination / 'mini', data, mode=0o555, bound=256 * 1024 * 1024)
        publish_exact(public.with_suffix('.controller'), listener_pin(r), r['operatorUid'], registry['operatorGid'])
        public_listener_record(base, stage, r, public)
    return controller_status(store, helper)


def upgrade_public_listener(store, helper, binary_arg, old_sha, new_sha):
    """Stopped exact binary succession, preserving the original registration."""
    _, base, r = load(store, helper)
    stage = checked_units(base, r)
    stopped_controller_units(r)
    require(all(re.fullmatch('[0-9a-f]{64}', digest) for digest in (old_sha, new_sha))
            and old_sha != new_sha, 'listener upgrade requires distinct exact old/new digests')
    data = read_file(canonical(binary_arg), r['operatorUid'], 256 * 1024 * 1024, True)
    require(sha(data) == new_sha, 'listener candidate digest differs')
    directory = base / 'public-listener'
    binary, record_path = directory / 'mini', base / 'public-listener.json'
    intent_path = directory / ('upgrade-' + new_sha + '.json')
    with stopped_public_listener(stage, r) as public:
        if not intent_path.exists() and not intent_path.is_symlink():
            old_record = public_listener_record(base, stage, r, public)
            require(old_record['binarySha256'] == old_sha, 'listener predecessor digest differs')
            old_binary = read_file(binary, 0, 256 * 1024 * 1024, True, required_mode=0o555)
            before = read_file(record_path, 0, 16384, required_mode=0o600)
            after = encoded({**old_record, 'binarySha256': new_sha})
            for raw, kind, bound in ((old_binary, 'binary', 256*1024*1024), (data, 'binary', 256*1024*1024),
                                     (before, 'record', 16384), (after, 'record', 16384)):
                publish_exact(directory / (sha(raw) + '.' + kind), raw, bound=bound)
            publish_exact(intent_path, encoded({'protocol':'mini-spk-public-listener-upgrade-v1', 'store':store,
                'oldBinarySha256':old_sha, 'newBinarySha256':new_sha,
                'oldRecordSha256':sha(before), 'newRecordSha256':sha(after)}))
        intent = strict_json(read_file(intent_path, 0, 4096, required_mode=0o600))
        require(set(intent) == {'protocol','store','oldBinarySha256','newBinarySha256','oldRecordSha256','newRecordSha256'}
                and intent['protocol'] == 'mini-spk-public-listener-upgrade-v1' and intent['store'] == store
                and intent['oldBinarySha256'] == old_sha and intent['newBinarySha256'] == new_sha,
                'listener upgrade intent differs')
        retained = {}
        for key, kind, bound in (('oldBinary','binary',256*1024*1024),('newBinary','binary',256*1024*1024),
                                 ('oldRecord','record',16384),('newRecord','record',16384)):
            digest = intent[key+'Sha256']
            require(isinstance(digest,str) and re.fullmatch('[0-9a-f]{64}',digest), 'listener archive hash malformed')
            retained[key] = read_file(directory/(digest+'.'+kind), 0, bound, required_mode=0o600)
            require(sha(retained[key]) == digest, 'listener archived bytes changed')
        old_record, new_record = map(strict_json, (retained['oldRecord'],retained['newRecord']))
        require(new_record == {**old_record,'binarySha256':new_sha} and old_record['binarySha256'] == old_sha
                and retained['newBinary'] == data, 'listener upgrade changes more than exact binary')
        # All namespace/ACL/UID pins remain exact even on partial publication.
        m = metadata(public.parent,r['operatorUid'],0o710)
        require(old_record['store'] == store and old_record['socket'] == str(public)
                and old_record['binary'] == str(binary) and old_record['controllerUid'] == r['uid']
                and old_record['operatorUid'] == r['operatorUid']
                and old_record['parentIdentity'] == [m.st_dev,m.st_ino]
                and old_record['aclReceipts'] == public_acl_receipts(base,stage,r,public)
                and old_record['pinSha256'] == sha(listener_pin(r))
                and read_file(public.with_suffix('.controller'),r['operatorUid'],128,required_mode=0o600) == listener_pin(r),
                'listener upgrade custody changed')
        require(sha(read_file(binary,0,256*1024*1024,True,required_mode=0o555)) in (old_sha,new_sha)
                and read_file(record_path,0,16384,required_mode=0o600) in (retained['oldRecord'],retained['newRecord']),
                'listener is outside exact upgrade states')
        temporary = directory / ('.mini-' + new_sha + '-next')
        publish_exact(temporary,data,mode=0o555,bound=256*1024*1024)
        os.replace(temporary,binary); sync_directory(directory)
        replace_root_record(record_path,retained['newRecord'],0o600)
        public_listener_record(base,stage,r,public)
    return {**controller_status(store,helper),'publicListenerUpgrade':str(intent_path)}


@contextlib.contextmanager
def public_listener_teardown(base, stage, r):
    if not (base / 'public-listener.json').exists() and not (base / 'public-listener.json').is_symlink():
        yield None
        return
    with stopped_public_listener(stage, r) as public:
        record = public_listener_record(base, stage, r, public)
        # Hold the same native lock until ancestor ACLs are restored and the
        # explicit controller pin is gone. No listener can bind in between.
        yield record
        pin = public.with_suffix('.controller')
        require(read_file(pin, r['operatorUid'], 128, required_mode=0o600) == listener_pin(r),
                'public listener pin changed during teardown')
        pin.unlink()
        sync_directory(pin.parent)


def remove(store, helper):
    _, base, r = load(store, helper)
    stage = checked_units(base, r, partial=True)
    service(store, helper, 'stop')
    if not HISTORY.exists():
        mkdir(HISTORY)
    ancestry(HISTORY, {0})
    consent_archive = preserve_consent_state(base, r)
    with public_listener_teardown(base, stage, r) as listener:
        # Only restore ACLs on the exact recorded objects and exact unchanged ACL.
        for path in sorted(base.glob('acl-[0-9][0-9][0-9].json'), reverse=True):
            intent = json.loads(read_file(path, 0, 16384))
            target = canonical(intent['path'])
            if listener is not None and str(target) == listener['socket']:
                continue  # Original absent socket identity remains in the registration history.
            # A stopped legacy public proxy unlinks its socket. There is then no
            # object whose ACL needs restoring; never accept a replacement inode.
            if str(target) == stage.get('publicSocket') and not target.exists() and not target.is_symlink():
                continue
            m = metadata(target)
            require((m.st_dev, m.st_ino) == (intent['dev'], intent['ino']), 'public ACL object replaced; cleanup refused')
            after_path = path.with_suffix('.after.json')
            if after_path.exists():
                entry = json.loads(read_file(after_path, 0, 16384))
                require(entry['before'] == intent['before'] and acl_text(target) == entry['after'], 'public ACL changed; cleanup refused')
                run(['/usr/bin/setfacl', '--restore=-'], input=(f'# file: {target}\n' + intent['before']).encode())
            else:
                require(acl_text(target) == intent['before'], 'incomplete ACL mutation; preserve intent receipt for operator repair')
    mounts = Path('/proc/self/mountinfo').read_text().splitlines()
    require(not any(line.split()[4].startswith(str(base) + '/') or line.split()[4] == str(base) for line in mounts), 'controller subtree has mounts')
    for n in r['units']:
        if (UNITS / n).exists():
            (UNITS / n).unlink()
    run(['/usr/bin/systemctl', 'daemon-reload'])
    no_processes(r['uid'])
    if r.get('workerTask'):
        run(['/usr/bin/loginctl', 'disable-linger', r['name']])
    run(['/usr/sbin/userdel', r['name']])
    try:
        group = grp.getgrnam(r['name'])
    except KeyError:
        pass
    else:
        require(group.gr_gid == r['gid'] and not group.gr_mem, 'controller group changed')
        run(['/usr/sbin/groupdel', r['name']])
    if not HISTORY.exists():
        mkdir(HISTORY)
    ancestry(HISTORY, {0})
    write_new(HISTORY / (store + '.json'), encoded({'receipt': r, 'stage': stage, 'removed': True, 'consentArchive': consent_archive, 'publicListener': listener}))
    shutil.rmtree(base)
    return {'store': store, 'removedController': r['name'], 'receipt': str(HISTORY / (store + '.json'))}


def main(args):
    require(os.geteuid() == 0, 'controller setup requires root installer')
    require(len(args) >= 3, 'controller verb requires STORE HELPER')
    action, store, helper, *extra = args
    # Same global allocator lock as ordinary world setup; no nested installer call.
    if action == 'controller-check-app-allocation':
        require(len(extra) == 3, 'app allocation check requires operator/start/count')
        held = os.fstat(8); named = os.stat('/run/mini-spk-world-install.lock', follow_symlinks=False)
        require(stat.S_ISREG(held.st_mode) and held.st_uid == 0 and held.st_nlink == 1
                and not held.st_mode & 0o022 and (held.st_dev, held.st_ino) == (named.st_dev, named.st_ino),
                'inherited global allocator lock differs')
        fcntl.flock(8, fcntl.LOCK_EX | fcntl.LOCK_NB)
        print(json.dumps(check_app_allocation(store, helper, *extra), sort_keys=True))
        return 0
    with open('/run/mini-spk-world-install.lock', 'a') as lock, contextlib.ExitStack() as held_locks:
        fcntl.flock(lock, fcntl.LOCK_EX)
        held = None
        if action != 'controller-create':
            _, base = store_context(store, helper)
            ancestry(base, {0})
            held = os.open(base / 'lifecycle.lock', os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC)
            held_locks.callback(os.close, held)
            m = os.fstat(held)
            require(stat.S_ISREG(m.st_mode) and m.st_uid == 0 and m.st_nlink == 1
                    and stat.S_IMODE(m.st_mode) == 0o600, 'controller lifecycle lock custody refused')
            shared = action in ('controller-tool', 'controller-tool-result', 'controller-tool-ack', 'controller-recover-session',
                                'controller-journal', 'controller-export', 'controller-reserve-export',
                                'controller-service-logs', 'controller-status', 'controller-quiescence', 'controller-run', 'controller-config-export', 'controller-host-config-export')
            # Lock order is global allocator, then controller. Never wait on a
            # controller while holding the allocator: an active call gets a
            # visible busy refusal, not account/config deletion underneath it.
            fcntl.flock(held, (fcntl.LOCK_SH if shared else fcntl.LOCK_EX) | fcntl.LOCK_NB)
        if action == 'controller-create' and not extra: result = create(store, helper)
        elif action == 'controller-resume-create' and not extra: result = resume_create(store, helper)
        elif action == 'controller-stage' and len(extra) == 4: result = stage(store, helper, *extra)
        elif action == 'controller-worker-prepare' and len(extra) == 4: result = stage(store, helper, *extra, worker=True)
        elif action == 'controller-worker-prepare-resume' and len(extra) == 4: result = stage(store, helper, *extra, worker=True, resume=True)
        elif action == 'controller-worker-birth' and len(extra) == 1:
            fcntl.flock(lock, fcntl.LOCK_UN)
            return worker_birth(store, helper, extra[0])
        elif action == 'controller-worker-publish' and not extra: result = publish_worker_config(store, helper)
        elif action == 'controller-config-export' and not extra: result = export_config(store, helper)
        elif action == 'controller-host-config-export' and not extra:
            _, base, r = load(store, helper)
            checked_units(base, r)
            result = strict_json(read_file(Path(r['home']) / 'host-config.json', r['uid'], 1048576, required_mode=0o600))
        elif action == 'controller-run' and len(extra) == 1:
            fcntl.flock(lock, fcntl.LOCK_UN)
            return controller_run(store, helper, extra[0])
        elif action in ('controller-start', 'controller-stop') and not extra: result = service(store, helper, action[11:])
        elif action == 'controller-config' and len(extra) == 1: result = config_update(store, helper, extra[0])
        elif action in ('controller-tool', 'controller-tool-result', 'controller-tool-ack') and extra:
            # A long controller call must not monopolize the host installation lock.
            fcntl.flock(lock, fcntl.LOCK_UN)
            return tool(store, helper, action[11:], extra[0], extra[1:])
        elif action == 'controller-recover-session' and len(extra) == 1:
            fcntl.flock(lock, fcntl.LOCK_UN)
            return recover_session(store,helper,extra[0])
        elif action == 'controller-recover-api-unreserved' and len(extra) == 1:
            fcntl.flock(lock, fcntl.LOCK_UN)
            return recover_api_unreserved(store, helper, extra[0])
        elif action == 'controller-quiescence' and not extra:
            fcntl.flock(lock, fcntl.LOCK_UN)
            return controller_quiescence(store, helper)
        elif action == 'controller-prepare-idle' and not extra:
            fcntl.flock(lock, fcntl.LOCK_UN)
            return controller_admin_fixed(store, helper, 'prepare idle')
        elif action == 'controller-reconcile' and len(extra) == 1:
            fcntl.flock(lock, fcntl.LOCK_UN)
            return reconcile_controller(store, helper, extra[0])
        elif action == 'controller-reconcile-prompt' and len(extra) == 1:
            fcntl.flock(lock, fcntl.LOCK_UN)
            return reconcile_prompt(store,helper,extra[0])
        elif action == 'controller-export' and extra in ([], ['application']):
            result = export_state(store, helper, extra[0] if extra else 'all')
        elif action == 'controller-reserve-export' and len(extra) == 1: result = reserve_export(store, helper, extra[0])
        elif action == 'controller-service-logs' and not extra: result = service_logs(store, helper)
        elif action == 'controller-status' and not extra: result = controller_status(store, helper)
        elif action == 'controller-public-listener' and len(extra) == 1: result = register_public_listener(store, helper, extra[0])
        elif action == 'controller-public-listener-upgrade' and len(extra) == 3:
            result = upgrade_public_listener(store,helper,*extra)
        elif action == 'controller-consent-storage' and not extra: result = consent_storage_upgrade(store, helper)
        elif action == 'controller-runtime-upgrade' and len(extra) == 1: result = runtime_upgrade(store, helper, extra[0])
        elif action == 'controller-mini-upgrade' and len(extra) == 1: result = controller_binary_upgrade(store, helper, extra[0], 'mini')
        elif action == 'controller-consent-memory' and len(extra) == 1: result = consent_memory_upgrade(store, helper, extra[0])
        elif action == 'controller-worker-runtime-access' and not extra: result = worker_runtime_access_upgrade(store, helper)
        elif action == 'controller-worker-observe' and not extra: result = worker_unit_observation(store, helper)
        elif action == 'controller-status-proxy-upgrade' and len(extra) == 1: result = status_proxy_upgrade(store, helper, extra[0])
        elif action == 'controller-operator-endpoint' and len(extra) == 1: result = operator_endpoint_upgrade(store, helper, extra[0])
        elif action == 'controller-enroll' and len(extra) == 1:
            fcntl.flock(lock, fcntl.LOCK_UN)
            return enroll(store, helper, extra[0])
        elif action == 'controller-journal' and not extra:
            _, base, r = load(store, helper)
            result = json.loads(read_file(worker_state(r) / 'journal.json', r['uid'], 8 * 1024 * 1024))
        elif action == 'controller-remove' and not extra: result = remove(store, helper)
        else: raise ValueError('unsupported controller installer arguments')
        print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main(sys.argv[1:]))
    except (ValueError, OSError, KeyError, subprocess.SubprocessError) as error:
        print(f'controller setup refused: {error}', file=sys.stderr)
        sys.exit(1)
