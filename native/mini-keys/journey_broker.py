"""A same-account key broker for a journey (sandbox, one uid).

The production broker runs as its own account with a root-owned config; a
journey runs every process as one account, so its config says singleAccount
and names this account in every role. Everything else is the production
binary and the production checks.

    import journey_broker
    proc, client = journey_broker.start(root, mini, providers=..., host=..., host_config=..., public_socket=...)
    # client: the mini-keys client config; give it to `mini key --broker`,
    # a controller's providerTask.credentialBroker, or mini-socket-proxy's third argument.
"""
import json
import os
import pathlib
import subprocess
import time


def _private_dir(path):
    path.mkdir(mode=0o700, parents=True, exist_ok=True)
    os.chmod(path, 0o700)


def binary(mini):
    """mini-keys beside the selected mini (a candidate's bin/), or $MINI_KEYS."""
    explicit = os.environ.get('MINI_KEYS')
    path = pathlib.Path(explicit) if explicit else pathlib.Path(mini).resolve().parent / 'mini-keys'
    if not os.access(path, os.X_OK):
        raise RuntimeError(f'mini-keys is not executable at {path} (set MINI_KEYS)')
    return path


def start(root, mini, *, providers, host, host_config, public_socket, seal_key=None, credentials=None,
          discord_mirror=None, timeout=20):
    root = pathlib.Path(root)
    keys = root / 'mini-keys'
    for sub in ('', 'run', 'state'):
        _private_dir(keys / sub)
    credentials = pathlib.Path(credentials) if credentials else root / 'credentials'
    _private_dir(credentials)
    seal_key = pathlib.Path(seal_key) if seal_key else keys / 'credentials.key'
    if not seal_key.exists():
        seal_key.write_bytes(os.urandom(32))
    os.chmod(seal_key, 0o600)
    uid, gid = os.geteuid(), os.getegid()
    config = {'type': 'mini-keys-broker-v1', 'socket': str(keys / 'run/broker.sock'),
              'audit': str(keys / 'state/audit.jsonl'), 'spool': str(keys / 'state/spool'),
              'singleAccount': True,
              'peers': [{'role': 'member', 'gids': [gid]}, {'role': 'provider', 'uids': [uid]},
                        {'role': 'discord', 'uids': [uid]}, {'role': 'operator', 'uids': [uid]}],
              'credentials': {'host': str(host), 'hostConfig': str(host_config), 'publicSocket': str(public_socket),
                              'providers': str(providers), 'root': str(credentials), 'key': str(seal_key)}}
    if discord_mirror:
        config['discord'] = {'mirror': str(discord_mirror)}
    (keys / 'broker.json').write_text(json.dumps(config))
    os.chmod(keys / 'broker.json', 0o644)
    client = keys / 'client.json'
    client.write_text(json.dumps({'type': 'mini-keys-client-v1', 'socket': config['socket'], 'uid': uid}))
    os.chmod(client, 0o644)
    log = open(keys / 'state/broker.log', 'ab')
    proc = subprocess.Popen([str(binary(mini)), 'serve', '--config', str(keys / 'broker.json')],
                            stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT)
    deadline = time.time() + timeout
    while not pathlib.Path(config['socket']).exists():
        if proc.poll() is not None:
            raise RuntimeError('mini-keys exited: ' + (keys / 'state/broker.log').read_text()[-500:])
        if time.time() > deadline:
            proc.kill()
            raise RuntimeError('mini-keys did not bind its socket')
        time.sleep(0.05)
    return proc, client


def pool_set(mini, client, provider, secret_file):
    """The operator's pool key, through the broker (the journey's account holds the operator role)."""
    subprocess.run([str(binary(mini)), 'pool', '--action', 'set', '--provider', provider, '--secret', str(secret_file),
                    '--client-config', str(client)], check=True, capture_output=True)
