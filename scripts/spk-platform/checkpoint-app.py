#!/usr/bin/env python3
"""Operator callback for source-coordinated same-generation SPK checkpointing.
Static config is root-owned; capture/quiesce/resume accept the retained checkpoint ID.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import socket
import stat
import struct
import subprocess
import sys
import time

PROTOCOL='mini-spk-checkpoint-control-v1'
def require(ok,why):
    if not ok:raise RuntimeError(why)
def load(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def sync_parent(path):
    parent=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    try:os.fsync(parent)
    finally:os.close(parent)
def private_file(path):
    meta=path.lstat();require(stat.S_ISREG(meta.st_mode) and meta.st_uid==os.getuid() and meta.st_nlink==1 and not meta.st_mode&0o077,'checkpoint file custody differs')
    return path
def private_directory(path):
    require(path.is_absolute() and '..' not in path.parts,'canonical state path required')
    for item in [path,*path.parents]:
        meta=item.lstat();require(stat.S_ISDIR(meta.st_mode) and meta.st_uid in (0,os.getuid()) and not meta.st_mode&0o022,'checkpoint directory custody differs')
    require(path.stat().st_uid==os.getuid() and not path.stat().st_mode&0o077,'private operator state required')
def save(path,value):
    encoded=(json.dumps(value,sort_keys=True,indent=2)+'\n').encode()
    if path.exists() or path.is_symlink():
        require(private_file(path).read_bytes()==encoded,'checkpoint retry differs');sync_parent(path);return
    temporary=path.parent/('.'+path.name+'.stage-'+secrets.token_hex(8))
    fd=os.open(temporary,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
    with os.fdopen(fd,'wb') as out:out.write(encoded);out.flush();os.fsync(out.fileno())
    # Operator callbacks are serialized by the root checkpoint runner. Refuse
    # conflicting existing final bytes; a private interrupted stage is retained.
    require(not path.exists() and not path.is_symlink(),'checkpoint path appeared')
    os.rename(temporary,path)
    sync_parent(path)
def root_config(path):
    path=Path(path);require(path.is_absolute() and '..' not in path.parts,'canonical config path required')
    for item in [path,*path.parents]:
        meta=item.lstat();require(not stat.S_ISLNK(meta.st_mode) and meta.st_uid==0 and not meta.st_mode&0o022,'root config custody required')
    meta=path.lstat();require(stat.S_ISREG(meta.st_mode) and meta.st_nlink==1,'root config file required')
    return load(path)
def exact(stream,size):
    parts=[]
    while size:
        data=stream.recv(size);require(bool(data),'checkpoint response EOF; retain exact request');parts.append(data);size-=len(data)
    return b''.join(parts)
def invoke(request):
    path=Path(request['binding']['journalDir'])/'checkpoint-control.sock'
    with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as stream:
        stream.settimeout(15);stream.connect(str(path));peer=struct.unpack('3i',stream.getsockopt(socket.SOL_SOCKET,socket.SO_PEERCRED,12));require(peer[1]==os.getuid(),'checkpoint peer differs')
        data=json.dumps(request).encode();stream.sendall(struct.pack('<I',len(data))+data)
        size=struct.unpack('<I',exact(stream,4))[0];require(0<size<=16384,'checkpoint response exceeds bound');return json.loads(exact(stream,size))
def run(action,config_path,checkpoint_id):
    require(os.getuid()!=0,'checkpoint callback runs as Store operator')
    require(re.fullmatch('[A-Za-z0-9_-]{1,128}',checkpoint_id) is not None,'checkpoint ID invalid')
    c=root_config(config_path);require(c['protocol']=='mini-spk-checkpoint-app-config-v1','unknown checkpoint config')
    require(sha(c['spkHost'])==c['spkHostSha256'],'checkpoint image pin differs')
    state_root=Path(c['stateRoot']);private_directory(state_root)
    state=state_root/'checkpoints'/checkpoint_id
    state.parent.mkdir(mode=0o700,exist_ok=True);private_directory(state.parent)
    state.mkdir(mode=0o700,exist_ok=True);private_directory(state)
    plan=state/'plan.json'
    if not plan.exists():
        require(action=='capture','capture exact checkpoint intent first')
        status=json.loads(subprocess.check_output([c['spkHost'],'grain','status',c['profilePath'],c['app']],timeout=30))
        require(status['protocol']=='mini-spk-grain-status-v2' and status['app']==c['app'],'native status binding differs')
        running=[run for run in status['runs'] if run['state']=='running'];require(len(running)==1,'exact running generation required')
        require(not any(run['state'].startswith('uncertain') for run in status['runs']),'prior generation requires exact recovery')
        gen=running[0]['generation'];journal=Path(c['stateRoot'])/f'apps/{c["app"]}/g{gen}';resident=journal/'resident.json';r=load(resident)
        require(r['journalDir']==str(journal) and r['unit']==running[0]['unit'],'resident coordinate differs')
        request={'protocol':PROTOCOL,'action':'pause','nonceHex':secrets.token_hex(32),'binding':{'app':c['app'],'generation':gen,'journalDir':str(journal),
            'residentConfig':str(resident),'residentConfigSha256':sha(resident),'miniConfigSha256':r['miniConfigSha256']}}
        save(plan,{'configPath':str(config_path),'configSha256':sha(config_path),'request':request,'store':status['store'],'unit':running[0]['unit']})
    p=load(private_file(plan));require(p['configPath']==str(config_path) and p['configSha256']==sha(config_path),'callback config changed since capture')
    request=dict(p['request'])
    if action!='capture':
        request['action']='pause' if action=='quiesce' else 'resume'
        result=invoke(request);save(state/(action+'-response-'+str(time.time_ns())+'.json'),result)
        require(result['protocol']==PROTOCOL and result['status']==('paused' if action=='quiesce' else 'resumed'),'source resident checkpoint refused; preserve exact phase')
        require(result['intent']['request']==p['request'],'resident checkpoint reply differs from retained request')
        save(state/(action+'-result.json'),result)
    value={'type':'mini-service-app-checkpoint-result-v1','checkpointId':checkpoint_id,'action':action,'ready':True,'plan':str(plan),'planSha256':sha(plan)}
    if action=='quiesce':
        inventory=state/'pause-inventory.json';save(inventory,{'protocol':'mini-spk-checkpoint-pause-inventory-v1','apps':[{'store':p['store'],'request':p['request']}]})
        value.update(pauseInventory=str(inventory),pausedUnits=[p['unit']])
    return value

def main():
    os.umask(0o077);p=argparse.ArgumentParser(description=__doc__);p.add_argument('action',choices=['capture','quiesce','resume']);p.add_argument('config');p.add_argument('--checkpoint-id',required=True);a=p.parse_args();print(json.dumps(run(a.action,a.config,a.checkpoint_id)))
if __name__=='__main__':
    try:main()
    except (RuntimeError,OSError,ValueError,KeyError,subprocess.SubprocessError) as error:print('SPK checkpoint: '+str(error),file=sys.stderr);sys.exit(1)
