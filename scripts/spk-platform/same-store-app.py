#!/usr/bin/env python3
"""Provision SPK apps in a supplied existing Mini world. Never initializes Store.
All births/share/enrollment use supplied owner/member authority and pinned sockets.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('continuity_fixture',HERE/'ws-continuity-fixture.py')
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
load,save,require,sha,absolute=f.load,f.save,f.require,f.sha,f.absolute

def decimal(value): return isinstance(value,str) and re.fullmatch(r'0|[1-9][0-9]*',value) is not None

def validate(c):
    require(c.get('protocol')=='mini-spk-same-store-attach-v1','unknown attach protocol')
    for key in ['root','manifest','miniConfig','publicSocket','privateSocket','workspace','genesis','profileResult','initStoreResult','grainsRoot','spk']:
        absolute(c[key])
    require(c['publicSocket']!=c['privateSocket'],'one public relay and distinct private Store owner required')
    require(sha(c['miniConfig'])==c['miniConfigSha256'],'supplied Mini config pin differs')
    m=load(c['manifest']);require(m['sourceCommit']==c['expectedSourceCommit'],'manifest source pin differs')
    artifacts={}
    for role in ['host','mini','store','verifier','spkHost']:
        p=absolute(m[role]);require(p.is_file() and not p.is_symlink() and os.access(p,os.X_OK) and sha(p)==m['sha256'][role],'candidate artifact differs: '+role)
        artifacts[role]={'path':str(p),'sha256':m['sha256'][role]}
    require(sha(c['spk'])==c['spkSha256'],'package pin differs')
    a=c['authority'];require(decimal(a['owner']) and a['owner'] in c['keys'] and a.get('creator',a['owner']) in c['keys'],'owner signer missing')
    for subject,key in c['keys'].items():
        require(decimal(subject) and decimal(key['keyId']) and decimal(key['keyEpoch']),'key selector invalid')
        seed=absolute(key['seedPath']);pub=absolute(key['publicKeyPath'])
        f.protected_parent(seed.parent);f.protected_parent(pub.parent)
        meta=seed.lstat();require(seed.is_file() and not seed.is_symlink() and meta.st_uid==os.getuid() and not meta.st_mode&0o077 and len(seed.read_bytes())==32,'private participant seed required')
        require(pub.is_file() and not pub.is_symlink() and len(pub.read_bytes())==32,'public key file required')
    app=c['application']
    app_fields=['app','packageManifest','snapshotManifest','appOwnerCapability','appControlCapability','packageOwnerCapability','packageControlCapability','snapshotOwnerCapability','snapshotControlCapability']
    require(all(decimal(app[k]) for k in app_fields),'app coordinates invalid')
    resources=[app[k] for k in ['app','packageManifest','snapshotManifest']]
    capabilities=[app[k] for k in app_fields[3:]]
    require(1<=len(c['delegates'])<=64,'explicit route capacity is 64')
    session_fields=['session','descriptor','cap','sessionControlCapability','descriptorOwnerCapability','descriptorControlCapability','ticket','appObserve','pkgObserve','ticketOwner','ticketControl','ticketObserve']
    subjects=[]
    for label,d in c['delegates'].items():
        require(re.fullmatch('[a-z][a-z0-9-]{0,47}',label) is not None,'route label invalid')
        require(d['subject'] in c['keys'] and decimal(d['subject']),'participant signer missing')
        require(all(decimal(d[k]) for k in session_fields),'session coordinates invalid')
        resources.extend(d[k] for k in ['session','descriptor','ticket'])
        capabilities.extend(d[k] for k in session_fields if k not in ['session','descriptor','ticket'])
        require('expectedHost' in d and d['expectedHost'],'route host required')
        subjects.append(d['subject'])
    require(len(set(resources))==len(resources) and len(set(capabilities))==len(capabilities),'resource or capability allocations overlap')
    require(decimal(a.get('creatorAccountCapability',a.get('ownerAccountCapability'))),'account capability invalid')
    for name in ['tool','parent']:
        require(all(decimal(a[name][k]) for k in ['task','capability','observeCapability']),'task authority invalid')
    require(all(decimal(a['factory'][k]) for k in ['target','capability']),'factory authority invalid')
    require(all(decimal(a['template'][k]) for k in ['issuer','ownerBudget','lifetime']),'birth template invalid')
    require(all(decimal(a['tariff'][k]) for k in ['base','perBirth']),'birth tariff invalid')
    return m,artifacts

def birth_app(x):
    x.reserve(int(x.authority['tariff']['base'])+3*int(x.authority['tariff']['perBirth']))
    observations=[x.query(x.creator,t['task'],t['observeCapability']) for t in [x.tool,x.parent]]
    nonce=x.n()
    def witness(q,t):
        return dict(t,targetRoot=q['view']['cell']['root'],before={k:q['view']['cell']['grain'][k] for k in ['generation','status','remaining','reserved']})
    app=dict(x.f['application'],owner=x.owner)
    spec={'genesis':load(x.genesis),'template':x.authority['template'],'creator':x.creator,'nonce':nonce,
          'sourceCapabilities':[x.accountcap],'funding':[],'feePayer':x.creator,'application':app}
    factory=x.authority['factory']
    source=x.fresh('application-source.json')
    save(source,{'subject':x.creator,'nonce':nonce,'grants':[f.grant(factory['target'],factory['capability']),
        f.grant(x.creator,x.accountcap,'account'),*[f.grant(t['task'],cap) for t in [x.tool,x.parent] for cap in dict.fromkeys([t['capability'],t['observeCapability']])]],
        'applicationGrainBirth':{'tariff':x.authority['tariff'],'applicationBirth':spec,
           'tool':witness(observations[0],x.tool),'parent':witness(observations[1],x.parent)}})
    author=x.fresh('application-author');attempt=x.fresh('application-birth')
    x.mini('current-application-intent','--source',source,'--dir',author)
    x.mini('submit','--intent',author/'intent.bin','--intent-kind','binary','--key',x.key(x.creator),'--dir',attempt)
    outcome=load(attempt/'outcome.json');require(outcome.get('type')=='confirmed' and outcome.get('confirmation')=='installed','app birth uncertain; inspect exact retained attempt')
    x.f.update(applicationSource=str(author/'source.json'),applicationReceipt=str(attempt/'outcome.json'))
    x.write_state()

def attach(path):
    require(os.getuid()!=0,'run with Store operator authority')
    c=load(path);m,artifacts=validate(c)
    root=absolute(c['root']);require(not root.exists() and not root.is_symlink(),'fresh attachment evidence root required')
    f.protected_parent(root.parent)
    # Validate native Store/profile provenance before creating any app or member.
    state,profile,profile_value=f.discover_profile(root,absolute(c['miniConfig']),absolute(c['grainsRoot']),artifacts,c.get('brokerSocket','/run/mini-spk-broker.sock'),absolute(c['profileResult']),absolute(c['initStoreResult']))
    require(profile_value['miniOperatorSocket']==c['privateSocket'],'profile points at a different private Store owner')
    root.mkdir(mode=0o700);(root/'hooks').mkdir(mode=0o700)
    save(root/'input.json',c);save(root/'manifest.json',m)
    save(root/'source-inputs.json',{str(HERE/name):sha(HERE/name) for name in ['same-store-app.py','ws-continuity-fixture.py']})
    value={'schema':f.SCHEMA,'root':str(root),'app':c['application']['app'],'application':c['application'],
        'authority':c['authority'],'keys':c['keys'],'artifacts':artifacts,'state':str(state),'profilePath':str(profile),
        'grainsRoot':c['grainsRoot'],'brokerSocket':c.get('brokerSocket','/run/mini-spk-broker.sock'),'candidateSource':m['sourceCommit'],
        'attachment':{k:c[k] for k in ['workspace','miniConfig','miniConfigSha256','publicSocket','privateSocket','genesis','profileResult','initStoreResult']},
        'delegates':c['delegates'],'leaseSeconds':profile_value.get('wsAuthorityLeaseSeconds',120)}
    save(root/'fixture.json',value);x=f.Fixture(root/'fixture.json')
    # Signed current observations bind the supplied world identity before writes.
    q=x.query(x.creator,x.creator,x.accountcap,kind='account')
    require(all(q['challenge'][k]==c['namespace'][k] for k in ['domain','semantics']),'signed source namespace differs from harness deployment')
    save(root/'source-namespace.json',q['challenge'])
    room=x.query(x.owner,c['room']['target'],c['room']['capability'])
    require(all(room['challenge'][k]==c['namespace'][k] for k in ['domain','semantics']),'room authority belongs to another namespace')
    save(root/'source-room.json',{'target':c['room']['target'],'authorityEvidence':str(room['dir']),'challenge':room['challenge']})
    birth_app(x)
    x.run([artifacts['spkHost']['path'],'grain','install',x.profile,x.f['applicationSource'],x.f['applicationReceipt'],c['spk'],'--class',c.get('sizeClass','S')])
    for label,d in x.f['delegates'].items():
        x.birth_session(d);x.delegate(x.app,x.appcap,d['appObserve'],d['subject']);x.delegate(x.package_manifest,x.pkgcap,d['pkgObserve'],d['subject'])
        x.issue(d);x.route('member-'+label,d);x.write_state()
    x.run([artifacts['spkHost']['path'],'grain','start',x.profile,x.app])
    for d in x.f['delegates'].values(): x.enroll(d);x.write_state()
    q=x.query(x.owner,x.app,x.appcap);require(f.entries(q['view'])['1']=='4','app is not source serving')
    x.f['generation']=f.entries(q['view'])['0'];x.write_state()
    result={'protocol':'mini-spk-same-store-attached-v1','appId':x.app,'fixture':str(x.path),'generation':x.f['generation'],
        'namespace':c['namespace'],'miniConfig':c['miniConfig'],'miniConfigSha256':c['miniConfigSha256'],
        'subjects':{label:d['subject'] for label,d in x.f['delegates'].items()},
        'inventory':{'app':x.app,'stateRoot':str(x.state),'profilePath':str(x.profile),'journalDir':str(x.state/f'apps/{x.app}/g{x.f["generation"]}'),
            'residentConfig':str(x.state/f'apps/{x.app}/g{x.f["generation"]}/resident.json'),'unit':f'mini-spk-a{x.app}-g{x.f["generation"]}.service',
            'delegates':x.f['delegates']},'receiving':'provisioned; actual shared editing/revoke/restart still required'}
    save(root/'attachment-result.json',result);return result

def main():
    os.umask(0o077);p=argparse.ArgumentParser(description=__doc__);p.add_argument('input');args=p.parse_args()
    print(json.dumps(attach(args.input)))
if __name__=='__main__':
    try: main()
    except (RuntimeError,ValueError,KeyError,OSError) as error:
        print('same-Store app: '+str(error),file=sys.stderr);sys.exit(1)
