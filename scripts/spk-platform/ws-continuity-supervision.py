#!/usr/bin/env python3
"""Root-only scoped supervisor override for a fresh, source-bound test fixture."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import pwd
import re
import stat
import subprocess

BODY=b'[Unit]\nOnFailure=\n[Service]\nRestart=no\n'


def require(value,message):
    if not value: raise RuntimeError(message)


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(path, owner=None, private=False):
    p=Path(path)
    require(p.is_absolute() and '..' not in p.parts, 'absolute canonical path required')
    for ancestor in [p,*p.parents]:
        s=ancestor.lstat()
        require(not stat.S_ISLNK(s.st_mode) and not s.st_mode & 0o022, 'unsafe path component')
        require(s.st_uid in ({0} if owner is None else {0,owner}), 'unexpected path owner')
    require(p.is_file(), 'regular file required')
    if private: require(not p.stat().st_mode & 0o077, 'private file required')
    return p


def read(path): return json.loads(path.read_text())


def sync_parent(path):
    fd=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    try: os.fsync(fd)
    finally: os.close(fd)


def exclusive(path,data):
    fd=os.open(path,os.O_CREAT|os.O_EXCL|os.O_WRONLY|os.O_NOFOLLOW,0o600)
    with os.fdopen(fd,'wb') as out:
        out.write(data); out.flush(); os.fsync(out.fileno())
    sync_parent(path)


def restore_owned(record,override,reload_and_observe):
    """Caller validates root ownership/coordinates. Preserve unknown files on any mismatch."""
    data=read(record)
    expected=hashlib.sha256(BODY).hexdigest()
    require(data['override']==str(override) and data['overrideSha256']==expected, 'recorded override differs')
    restored=record.with_suffix('.restored.json')
    if restored.exists():
        prior=read(restored)
        require(prior.get('restored') is True and prior.get('recordSha256')==sha(record)
                and not override.exists() and not override.is_symlink(), 'restored evidence differs or override reappeared')
        return
    if override.exists() or override.is_symlink():
        require(not override.is_symlink() and override.read_bytes()==BODY and sha(override)==expected,
                'override changed; refusing removal')
        override.unlink()
        sync_parent(override)
    # Missing override is valid after interrupted install before create_new, or
    # interrupted restore after unlink. Rerun reload; do not recreate anything.
    properties=reload_and_observe()
    exclusive(restored,(json.dumps({'restored':True,'recordSha256':sha(record),'properties':properties})+'\n').encode())


def systemctl(*args):
    result=subprocess.run(['/usr/bin/systemctl',*args],capture_output=True,check=True,timeout=30)
    return result.stdout.decode()


def main():
    os.umask(0o077)
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('action',choices=['install','restore'])
    for key in ['fixture','expected-app','expected-unit','expected-resident-sha256','broker-config','broker-config-sha256']:
        p.add_argument('--'+key,required=True)
    args=p.parse_args()
    require(os.getuid()==0, 'root-controlled invocation required')
    broker_path=checked(args.broker_config,private=True)
    require(sha(broker_path)==args.broker_config_sha256, 'broker config pin differs')
    broker=read(broker_path)
    operator=pwd.getpwnam(broker['operatorUser']).pw_uid
    fp=checked(args.fixture,operator,True); f=read(fp)
    require(f.get('schema')=='spk-ws-continuity-fixture-v1' and f.get('enableSealRecovery') is True,
            'fresh continuity seal fixture required')
    require(fp==Path(f['root'])/'fixture.json' and (fp.parent/'input.json').is_file(), 'fixture root mismatch')
    setup=read(checked(fp.parent/'input.json',operator,True))
    require(setup.get('root')==str(fp.parent) and setup.get('enableSealRecovery') is True, 'fixture original input mismatch')
    require(re.fullmatch('[1-9][0-9]*',args.expected_app) is not None and f['app']==args.expected_app, 'app pin differs')
    require(broker['grainsRoot']==f['grainsRoot'], 'broker belongs to another grains root')
    # Derive the old generation from the explicitly pinned exact generated unit:
    # restore remains possible after fixture.json advances to its new generation.
    match=re.fullmatch(r'mini-spk-a([1-9][0-9]*)-g([1-9][0-9]*)\.service',args.expected_unit)
    require(match and match[1]==args.expected_app, 'source-generated resident unit required')
    generation=match[2]
    if args.action=='install': require(f['generation']==generation, 'setup requires current fixture generation')
    grains=Path(f['grainsRoot']); state=Path(f['state'])
    require(state.is_relative_to(grains) and state.name=='host', 'fixture state not a native host root')
    profile=read(checked(Path(f['profilePath']),operator,True))
    require(profile['stateRoot']==str(state) and profile['grainsRoot']==str(grains), 'profile fixture mismatch')
    resident=checked(state/f'apps/{f["app"]}/g{generation}/resident.json',operator,True)
    require(sha(resident)==args.expected_resident_sha256, 'resident pin differs')
    config=read(resident)
    store=config['store']
    require(re.fullmatch('[0-9a-f]{16}',store) is not None and state==grains/store/'host', 'native Store root differs')
    require(config['unit']==args.expected_unit and config['grainsRoot']==str(grains)
            and config['journalDir']==str(resident.parent), 'resident coordinates differ')
    tag=checked(grains/'broker/units'/args.expected_unit,private=True)
    require(tag.read_text()==store+'\n', 'root broker custody tag belongs to another Store')
    # Require the root-rendered base unit to name this exact config, not an alias.
    base=checked(Path('/run/systemd/system')/args.expected_unit)
    text=base.read_text()
    require(f'store={store} app={f["app"]} generation={generation}' in text
            and f' resident-run {resident}\n' in text, 'root unit is not this native fixture incarnation')
    name='90-mini-continuity-seal-'+hashlib.sha256(str(fp).encode()).hexdigest()[:16]+'.conf'
    directory=base.with_name(base.name+'.d')
    override=directory/name
    records=grains/'broker/fixture-supervision'
    if not records.exists():
        records.mkdir(mode=0o700); sync_parent(records)
    require(records.is_dir() and not records.is_symlink() and records.stat().st_uid==0 and not records.stat().st_mode & 0o077, 'unsafe root evidence directory')
    record=records/(args.expected_unit+'-'+name+'.json')
    if args.action=='install':
        before=systemctl('show',args.expected_unit,'--property=OnFailure,Restart,ActiveState,ExecStart')
        require('ActiveState=active\n' in before, 'fixture unit is not active')
        if not directory.exists():
            directory.mkdir(mode=0o755); sync_parent(directory)
        require(directory.is_dir() and not directory.is_symlink() and directory.stat().st_uid==0 and not directory.stat().st_mode & 0o022,'unsafe drop-in directory')
        record_data={'protocol':'mini-spk-fixture-supervision-v1','fixture':str(fp),'app':f['app'],'unit':args.expected_unit,
                     'residentSha256':args.expected_resident_sha256,'brokerConfig':str(broker_path),'brokerConfigSha256':args.broker_config_sha256,
                     'override':str(override),'overrideSha256':hashlib.sha256(BODY).hexdigest(),'previousProperties':before,
                     'previousUnit':systemctl('cat',args.expected_unit)}
        exclusive(record,(json.dumps(record_data,indent=2)+'\n').encode())
        exclusive(override,BODY)
        systemctl('daemon-reload')
        after=systemctl('show',args.expected_unit,'--property=OnFailure,Restart')
        require('OnFailure=\n' in after and 'Restart=no\n' in after,'override not effective; retain root evidence for recovery')
    else:
        if not record.exists():
            require(not record.is_symlink() and not override.exists() and not override.is_symlink(), 'missing record cannot authorize existing override cleanup')
            print(json.dumps({'protocol':'mini-spk-fixture-supervision-result-v1','action':'restore','notInstalled':True,'unit':args.expected_unit}))
            return
        record=checked(record,private=True); data=read(record)
        require(data['fixture']==str(fp) and data['unit']==args.expected_unit and data['residentSha256']==args.expected_resident_sha256
                and data['brokerConfigSha256']==args.broker_config_sha256 and data['override']==str(override), 'root setup record differs')
        if override.exists() or override.is_symlink(): checked(override,private=True)
        restored=record.with_suffix('.restored.json')
        if restored.exists() or restored.is_symlink(): checked(restored,private=True)
        def reload_and_observe():
            systemctl('daemon-reload')
            return systemctl('show',args.expected_unit,'--property=OnFailure,Restart')
        restore_owned(record,override,reload_and_observe)
    print(json.dumps({'protocol':'mini-spk-fixture-supervision-result-v1','action':args.action,'record':str(record),'unit':args.expected_unit,'override':str(override)}))


if __name__=='__main__': main()
