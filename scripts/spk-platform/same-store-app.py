#!/usr/bin/env python3
"""Provision SPK apps in a supplied existing Mini world. Never initializes Store.
All births/share/enrollment use supplied owner/member authority and pinned sockets.

  same-store-app.py INPUT                       attach, or continue the same attachment
  same-store-app.py status INPUT                retained step ledger; no native call
  same-store-app.py settle INPUT STEP absent|confirmed EVIDENCE REASON
  same-store-app.py adopt-adapter INPUT REASON  pin repaired adapter bytes for this root

An attachment is a ledger of single-effect steps under one evidence root. A
completed step never repeats. Install, lifecycle delegation and START re-enter
their own native journals. Any other interrupted step fences the attachment
until its retained attempt is settled from evidence.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import secrets
import stat
import subprocess
import sys

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('continuity_fixture',HERE/'ws-continuity-fixture.py')
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
load,save,require,sha,absolute=f.load,f.save,f.require,f.sha,f.absolute

def route_name(label): return 'm'+hashlib.sha256(label.encode()).hexdigest()[:12]
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
    subjects=[];route_names=[]
    for label,d in c['delegates'].items():
        require(re.fullmatch('[A-Za-z0-9][A-Za-z0-9_-]{0,63}',label) is not None,'route label invalid')
        require(d['subject'] in c['keys'] and decimal(d['subject']),'participant signer missing')
        require(all(decimal(d[k]) for k in session_fields),'session coordinates invalid')
        resources.extend(d[k] for k in ['session','descriptor','ticket'])
        capabilities.extend(d[k] for k in session_fields if k not in ['session','descriptor','ticket'])
        require('expectedHost' in d and d['expectedHost'],'route host required')
        subjects.append(d['subject']);route_names.append(route_name(label))
    require(len(set(route_names))==len(route_names),'route name hash collision; choose distinct inventory keys')
    state=Path(c['grainsRoot'])/c['miniConfigSha256'][:16]/'host'/'apps'/app['app']
    # INSTALL is generation 1 and each START takes the next; bound two digits.
    sockets=[state/'g99/checkpoint-control.sock',*[state/'routes'/name/'http.sock' for name in route_names]]
    require(all(len(os.fsencode(path))<=107 for path in sockets),'Linux socket pathname exceeds bound; shorten grains root or app ID')
    require(len(set(resources))==len(resources) and len(set(capabilities))==len(capabilities),'resource or capability allocations overlap')
    require(decimal(a.get('creatorAccountCapability',a.get('ownerAccountCapability'))),'account capability invalid')
    for name in ['tool','parent']:
        require(all(decimal(a[name][k]) for k in ['task','capability','observeCapability']),'task authority invalid')
    require(all(decimal(a['factory'][k]) for k in ['target','capability']),'factory authority invalid')
    require(all(decimal(a['template'][k]) for k in ['issuer','ownerBudget','lifetime']),'birth template invalid')
    require(all(decimal(a['tariff'][k]) for k in ['base','perBirth']),'birth tariff invalid')
    validate_lifecycle(c,artifacts)
    return m,artifacts

def validate_lifecycle(c, artifacts):
    delegation=c.get('lifecycleDelegation')
    if delegation is None:return None
    require(isinstance(delegation,dict) and set(delegation)=={'ownerWorkspace','manager','requestId'},'lifecycle delegation input must name ownerWorkspace, manager, requestId')
    require(decimal(delegation['manager']) and isinstance(delegation['requestId'],str) and re.fullmatch('[A-Za-z0-9][A-Za-z0-9_-]{0,39}',delegation['requestId']) is not None,'lifecycle manager/request ID invalid')
    workspace=absolute(delegation['ownerWorkspace']);f.protected_parent(workspace)
    pin=load(workspace/'workspace.json')
    require(pin['subject']==c['authority']['owner'] and pin['config']==c['miniConfig'] and pin['socket']==c['publicSocket'],'lifecycle workspace belongs to a different owner/world')
    require(pin['key']==c['keys'][pin['subject']]['seedPath'] and sha(pin['host'])==artifacts['host']['sha256'],'lifecycle owner workspace key/Host pin differs')
    return delegation

def delegate_lifecycle(x,c):
    delegation=c['lifecycleDelegation'];workspace=absolute(delegation['ownerWorkspace'])
    application=c['application'];prefix='spk-'+hashlib.sha256(x.app.encode()).hexdigest()[:12]
    names=[prefix+'-'+kind for kind in ['app','package','snapshot']]
    resources=[('app','appOwnerCapability','appControlCapability'),('packageManifest','packageOwnerCapability','packageControlCapability'),('snapshotManifest','snapshotOwnerCapability','snapshotControlCapability')]
    provenance=x.fresh('owner-root-provenance.json')
    save(provenance,{'type':'mini-spk-source-owner-roots-v1','authority':'hint-only-requires-current-source','subject':x.owner,'applicationSource':x.f['applicationSource'],'applicationSourceSha256':sha(x.f['applicationSource']),'applicationReceipt':x.f['applicationReceipt'],'applicationReceiptSha256':sha(x.f['applicationReceipt'])})
    for name,(resource,capability,control) in zip(names,resources):
        expected={'name':name,'kind':'object','target':application[resource],'observeCapability':application[capability],'operationCapability':application[capability],'controlCapability':application[control]}
        retained=workspace/'refs'/(name+'.json')
        if retained.exists():
            prior=load(retained);require(all(prior.get(k)==v for k,v in expected.items()),'existing owner root reference differs')
        else:
            x.run([x.m['mini']['path'],'workspace','--action','import','--dir',workspace,'--name',name,'--kind','object','--target',expected['target'],'--observe-capability',expected['observeCapability'],'--operation-capability',expected['operationCapability'],'--control-capability',expected['controlCapability'],'--provenance',provenance])
    common=[x.m['mini']['path'],'workspace','--action','app-lifecycle','--dir',workspace,'--request-id',delegation['requestId']]
    for phase in ['app-policy','package-policy','snapshot-policy','app-grant','package-grant','snapshot-grant']:
        _,prepared,_=x.run([*common,'--op','prepare','--name',names[0],'--package-name',names[1],'--snapshot-name',names[2],'--manager',delegation['manager']])
        before=load(prepared)
        require(before.get('type')=='mini-member-app-lifecycle-result-v1' and before.get('owner')==x.owner and before.get('manager')==delegation['manager'],'owner lifecycle preparation identity differs')
        if before.get('complete') is True:result=before;break
        # The owner module alone classifies phases and retains exact calls.
        # An uncertain submit fails here with its attempt intact; it is never
        # replaced by a fresh source request or a manager signature.
        _,submitted,_=x.run([*common,'--op','submit'])
        result=load(submitted)
        require(result.get('type')=='mini-member-app-lifecycle-result-v1' and result.get('owner')==x.owner and result.get('manager')==delegation['manager'],'owner lifecycle submission identity differs')
        if result.get('complete') is True:break
        require(result.get('phase')!=before.get('phase'),'owner lifecycle phase did not confirm; retain exact call for recovery')
    require(result.get('complete') is True,'owner lifecycle workflow incomplete; retain exact workspace request')
    selector=absolute(result['managementSelector']);selected=load(selector)
    require(selected['appOwner']==x.owner and selected['managementSubject']==delegation['manager'] and all(selected['selector'][k]==application[k] for k in ['app','packageManifest','snapshotManifest']),'owner lifecycle selector differs from app/manager')
    x.f['lifecycleDelegation']={'request':delegation,'result':result,'selectorSha256':sha(selector)};x.write_state()
    return selector

# The Host replays history inside INSTALL and START; these bound a hung helper,
# not an ordinary slow one. An interrupted INSTALL preparation cannot be
# repeated, so its bound is far above any measured run (1605 s on the first
# shared host). START's own completion wait is 1800 s.
INSTALL_TIMEOUT=4*3600
START_TIMEOUT=1800+600

def check_task_readiness(x):
    parent=x.query(x.creator,x.parent['task'],x.parent['observeCapability'])
    tool=x.query(x.creator,x.tool['task'],x.tool['observeCapability'])
    p,t=[q['view']['cell']['grain'] for q in [parent,tool]]
    require(all(decimal(g[k]) for g in [p,t] for k in ['generation','status','remaining','reserved']),'task readiness fields invalid')
    require(int(p['generation'])>0 and p['status'] in ['3','4'] and int(p['reserved'])>0,'birth parent is not reserved; prepare its ordinary owner task or recover exact retained attempt before attachment')
    require(int(t['generation'])>0 and t['status'] in ['1','2'] and t['reserved']=='0','birth tool is not attached and settled; prepare its ordinary owner task or recover exact retained attempt before attachment')
    x.f['taskReadiness']={'parent':str(parent['dir']),'tool':str(tool['dir'])};x.write_state()

def app_reserve(x):
    return int(x.authority['tariff']['base'])+3*int(x.authority['tariff']['perBirth'])

def birth_app(x):
    # The reservation is its own retained step; this authors exactly one birth.
    observations=[x.query(x.creator,x.tool['task'],x.tool['observeCapability']),x.query(x.creator,x.parent['task'],x.parent['observeCapability'])]
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

def observe_world(x,c):
    # Signed current observations bind the supplied world identity before writes.
    q=x.query(x.creator,x.creator,x.accountcap,kind='account')
    require(all(q['challenge'][k]==c['namespace'][k] for k in ['domain','semantics']),'signed source namespace differs from harness deployment')
    room=x.query(x.owner,c['room']['target'],c['room']['capability'])
    require(all(room['challenge'][k]==c['namespace'][k] for k in ['domain','semantics']),'room authority belongs to another namespace')
    x.f['sourceObservation']={'namespace':q['challenge'],'namespaceEvidence':str(q['dir']),'room':{'target':c['room']['target'],'authorityEvidence':str(room['dir']),'challenge':room['challenge']}}
    x.write_state()

def runtime_ready(x):
    # INSTALL and START load this profile and START refuses unless the root
    # broker runs its exact pinned SPK runtime. Establish both before the first
    # source write instead of after an app is born and installed.
    profile=load(x.profile)
    for role in ['bwrap','spkHost']:
        meta=os.lstat(profile[role])
        require(stat.S_ISREG(meta.st_mode) and meta.st_uid==0 and not meta.st_mode&0o022 and sha(profile[role])==profile[role+'Sha256'],'native profile pins a '+role+' outside root custody')
    _,out,_=x.run([x.m['spkHost']['path'],'grain','runtime-status',x.profile],timeout=120)
    status=load(out)
    require(status.get('protocol')=='mini-spk-runtime-status-v1' and status.get('brokerProtocol')=='mini-spk-broker-runtime-v1'
        and status.get('store')==x.state.parent.name and status.get('state') in ('baseline','ready')
        and status.get('spkHost')==profile['spkHost'] and status.get('spkHostSha256')==profile['spkHostSha256'],
        'root broker runtime is not ready for this profile; no app was born')
    x.f['runtimeStatus']=str(out);x.write_state()

def install_app(x,c):
    install=[x.m['spkHost']['path'],'grain','install',x.profile,x.f['applicationSource'],x.f['applicationReceipt'],c['spk'],'--class',c.get('sizeClass','S')]
    if c.get('lifecycleDelegation') is not None:
        selector=absolute(x.f['lifecycleDelegation']['result']['managementSelector'])
        require(sha(selector)==x.f['lifecycleDelegation']['selectorSha256'],'retained lifecycle selector changed before installation')
        install+=['--management-selector',selector]
    x.run(install,timeout=INSTALL_TIMEOUT)

def serving(x):
    q=x.query(x.owner,x.app,x.appcap);require(f.entries(q['view'])['1']=='4','app is not source serving')
    x.f['generation']=f.entries(q['view'])['0'];x.write_state()

def enter(path):
    """Bind a fresh evidence root to this exact input, or re-enter that root."""
    require(os.getuid()!=0,'run with Store operator authority')
    c=load(path);m,artifacts=validate(c)
    root=absolute(c['root']);f.protected_parent(root.parent)
    # Validate native Store/profile provenance before creating any app or member.
    state,profile,profile_value=f.discover_profile(root,absolute(c['miniConfig']),absolute(c['grainsRoot']),artifacts,c.get('brokerSocket','/run/mini-spk-broker.sock'),absolute(c['profileResult']),absolute(c['initStoreResult']))
    require(profile_value['miniOperatorSocket']==c['privateSocket'],'profile points at a different private Store owner')
    if c.get('lifecycleDelegation') is not None:require(c['lifecycleDelegation']['manager']==profile_value['managementSubject'],'lifecycle delegated manager differs from native profile')
    elif c['authority']['owner']!=profile_value['managementSubject']:raise RuntimeError('member-owned hosting requires explicit lifecycleDelegation before app birth')
    if root.exists() or root.is_symlink():
        require(root.is_dir() and not root.is_symlink(),'attachment evidence root is not a directory')
        f.protected_parent(root)
        require(load(root/'input.json')==c and load(root/'manifest.json')==m,'retained attachment input differs; a changed attachment needs a fresh evidence root')
        return c,root,f.Fixture(root/'fixture.json')
    # Publish the bound root in one rename; a crash before it leaves no root.
    staging=root.parent/('.'+root.name+'.'+secrets.token_hex(8))
    staging.mkdir(mode=0o700);(staging/'hooks').mkdir(mode=0o700)
    save(staging/'input.json',c);save(staging/'manifest.json',m)
    save(staging/'source-inputs.json',{str(HERE/name):sha(HERE/name) for name in ['same-store-app.py','ws-continuity-fixture.py']})
    value={'schema':f.SCHEMA,'root':str(root),'app':c['application']['app'],'application':c['application'],
        'authority':c['authority'],'keys':c['keys'],'artifacts':artifacts,'state':str(state),'profilePath':str(profile),
        'grainsRoot':c['grainsRoot'],'brokerSocket':c.get('brokerSocket','/run/mini-spk-broker.sock'),'candidateSource':m['sourceCommit'],
        'attachment':{k:c[k] for k in ['workspace','miniConfig','miniConfigSha256','publicSocket','privateSocket','genesis','profileResult','initStoreResult']},
        'delegates':c['delegates'],'leaseSeconds':profile_value.get('wsAuthorityLeaseSeconds',120)}
    save(staging/'fixture.json',value)
    os.rename(staging,root)
    return c,root,f.Fixture(root/'fixture.json')

def attach(path):
    c,root,x=enter(path)
    retained=root/'attachment-result.json'
    if retained.exists():return load(retained)
    host=x.m['spkHost']['path']
    x.step('observe-world',lambda:observe_world(x,c),reentrant=True)
    x.step('runtime-ready',lambda:runtime_ready(x),reentrant=True)
    x.step('task-readiness',lambda:check_task_readiness(x),reentrant=True)
    x.step('app:reserve',lambda:x.reserve(app_reserve(x)),effect_only=True)
    x.step('app:birth',lambda:birth_app(x))
    if c.get('lifecycleDelegation') is not None:x.step('lifecycle',lambda:delegate_lifecycle(x,c),reentrant=True)
    x.step('install',lambda:install_app(x,c),reentrant=True)
    for label,d in x.f['delegates'].items():
        k='member:'+label+':'
        x.step(k+'session-reserve',lambda:x.reserve(x.session_reserve()),effect_only=True)
        x.step(k+'session',lambda d=d:x.birth_session(d,reserve=False))
        x.step(k+'app-observe',lambda d=d:x.delegate(x.app,x.appcap,d['appObserve'],d['subject']),effect_only=True)
        x.step(k+'package-observe',lambda d=d:x.delegate(x.package_manifest,x.pkgcap,d['pkgObserve'],d['subject']),effect_only=True)
        x.step(k+'ticket-reserve',lambda:x.reserve(3),effect_only=True)
        x.step(k+'ticket',lambda d=d:x.issue(d,reserve=False,observe=False))
        x.step(k+'ticket-observe',lambda d=d:x.delegate(d['ticket'],d['ticketOwner'],d['ticketObserve'],d['subject']),effect_only=True)
        x.step(k+'route',lambda label=label,d=d:x.route(route_name(label),d))
    x.step('start',lambda:x.run([host,'grain','start',x.profile,x.app],timeout=START_TIMEOUT),reentrant=True)
    for label,d in x.f['delegates'].items():
        x.step('member:'+label+':enrollment',lambda d=d:x.enroll(d))
    x.step('serving',lambda:serving(x),reentrant=True)
    result={'protocol':'mini-spk-same-store-attached-v1','appId':x.app,'fixture':str(x.path),'generation':x.f['generation'],
        'namespace':c['namespace'],'miniConfig':c['miniConfig'],'miniConfigSha256':c['miniConfigSha256'],
        'subjects':{label:d['subject'] for label,d in x.f['delegates'].items()},
        'inventory':{'app':x.app,'stateRoot':str(x.state),'profilePath':str(x.profile),'journalDir':str(x.state/f'apps/{x.app}/g{x.f["generation"]}'),
            'residentConfig':str(x.state/f'apps/{x.app}/g{x.f["generation"]}/resident.json'),'unit':f'mini-spk-a{x.app}-g{x.f["generation"]}.service',
            'delegates':x.f['delegates']},'receiving':'provisioned; actual shared editing/revoke/restart still required'}
    save(retained,result);return result

def retained_fixture(path):
    c=load(path);root=absolute(c['root']);f.protected_parent(root)
    require(load(root/'input.json')==c,'retained attachment input differs')
    return root

def status(path):
    # Reads retained files only: no Fixture, no hook directory, no native call.
    root=retained_fixture(path);value=load(root/'fixture.json')
    ledger=value.get('steps',{'done':[],'pending':None,'settled':[]})
    return {'protocol':'mini-spk-same-store-attach-status-v1','root':str(root),'app':value['app'],'done':ledger['done'],'pending':ledger['pending'],
        'settled':ledger['settled'],'complete':(root/'attachment-result.json').exists()}

def main():
    os.umask(0o077);p=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('words',nargs='+');words=p.parse_args().words
    if words[0]=='status' and len(words)==2:result=status(words[1])
    elif words[0]=='settle' and len(words)==6:
        result=f.Fixture(retained_fixture(words[1])/'fixture.json').settle(words[2],words[3],words[4],words[5])
    elif words[0]=='adopt-adapter' and len(words)==3:result=f.adopt_adapter(retained_fixture(words[1]),words[2])
    elif len(words)==1:result=attach(words[0])
    else:p.error('unknown command')
    print(json.dumps(result))
if __name__=='__main__':
    try: main()
    except (RuntimeError,ValueError,KeyError,OSError,subprocess.TimeoutExpired) as error:
        print('same-Store app: '+str(error),file=sys.stderr);sys.exit(1)
