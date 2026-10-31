#!/usr/bin/env python3
"""Untrusted orchestration for a fresh Hermes + Oracle receiving journey.

Every transition uses native Mini; the fixed installer handles cross-UID
transport. Retained command outputs and exact native attempts survive failure.
"""
import base64
import hashlib
import fcntl
import importlib.util
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import signal
import stat
import socket
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
PHASES=['world','prepare_platform','prepare_application','publish_data','worker','room','attach','probe']
RESUMABLE={'prepare_platform','prepare_application','publish_data','worker'}
spec=importlib.util.spec_from_file_location('inputs',HERE/'j14-oracle-inputs.py')
inputs=importlib.util.module_from_spec(spec);spec.loader.exec_module(inputs)
read,write,sha=inputs.read,inputs.write,inputs.sha

def available_port():
    with socket.socket() as listener:
        listener.bind(('127.0.0.1',0))
        return listener.getsockname()[1]

def need(name):
    value=os.environ.get(name)
    if not value:raise ValueError('J14 Oracle requires '+name)
    return str(Path(value).resolve(strict=True))

class Journey:
    PROVIDER_FIXTURE=True
    DATA_PUBLICATION=True
    # Hooks a derived journey (j14-apps.py) replaces; the Oracle journey uses these defaults.
    MODEL='mini-hermes-protocol-fixture'

    def start_provider(self,port):
        """The provider table rows and the process behind them (default: the loopback fixture)."""
        write(self.table,{'type':'mini-provider-table-v2','providers':[{'name':'friendkey','kind':'openai-compatible',
            'endpoint':f'http://127.0.0.1:{port}/v1/chat/completions','models':[self.MODEL],'credential':'user'}]})
        self.provider_process=self.spawn('provider',[self.provider,f'127.0.0.1:{port}',self.root/'provider.log','--room-librarian'])
        deadline=time.monotonic()+30
        while f'http://127.0.0.1:{port}/v1' not in self.provider_process.journey_stdout.read_text():
            if self.provider_process.poll() is not None or time.monotonic()>=deadline:raise RuntimeError('selected provider did not bind its loopback port')
            time.sleep(.1)

    def gateway_config(self,port,base):
        return {'providers':str(base/'worker/runtime-root/providers.json'),'credentialBroker':str(base/'worker/runtime-root/keys-client.json'),
            'gatewayBind':f'127.0.0.1:{available_port()}','model':self.MODEL,'provider':'friendkey',
            'onBehalfOf':{'subject':self.subjects['alice'],'publicKey':(self.homes/'alice/keys/mini.key.pub').read_bytes().hex()},
            'reserve':'30000','maxInputTokens':131072,'maxOutputTokens':64,'maxRequestBytes':1048576,'maxResponseBytes':8388608,
            'timeoutSeconds':600,'localFixtureHostNetwork':False}

    def set_provider_keys(self,keyclient):
        secret=self.root/'provider-key.secret';secret.write_text('j14-fixture-key\n');secret.chmod(0o600)
        self.run('provider-key',[self.mini,'key','--action','set','--dir',self.workspaces/'alice','--provider','friendkey','--secret',secret,'--broker',keyclient]);secret.unlink()
        self.run('provider-key-grant',[self.mini,'key','--action','grant','--dir',self.workspaces/'alice','--provider','friendkey',
            '--runner',self.subjects['hprov'],'--per-call','64','--per-day','200','--until','1000000000','--broker',keyclient])

    def __init__(self):
        os.umask(0o077)
        self.root=Path(os.environ['JOURNEY_STEP_DIR'])/'oracle'
        self.root.mkdir(mode=0o700)
        self.lock_root()
        self.logs=self.root/'commands';self.logs.mkdir()
        self.processes=[];self.daemons=[];self.counter=0;self.controller=False
        # A separate fresh private root avoids sharing controller traversal ACLs
        # with another preserved world (including /run/user/UID).
        socket_parent=Path(os.environ.get('J14_ORACLE_SOCKET_PARENT','/build/lanes'))
        # The socket directory is the controller world's root; the ACL grant stops there, so its parent
        # lies above the root and only needs to be traversable (--x) for the controller uid. Add that
        # traverse bit (never read or write) to a parent this user owns, so no caller needs operator prep.
        parent_stat=socket_parent.stat()
        if parent_stat.st_uid==os.getuid() and stat.S_IMODE(parent_stat.st_mode)&0o011!=0o011:
            socket_parent.chmod(stat.S_IMODE(parent_stat.st_mode)|0o011)
        self.sockets=socket_parent/('j14-o7-s-'+secrets.token_hex(4));self.sockets.mkdir(mode=0o700)
        self.bins=Path(need('J14_ORACLE_BIN'))
        self.mini=need('MINI');self.host=need('HOST');self.runtime=need('GRAIN_RUNTIME')
        self.provider=need('TEST_PROVIDER') if self.PROVIDER_FIXTURE else None;self.hermes_root=need('J14_HERMES_ROOT')
        self.candidate_manifest=need('J14_ORACLE_CANDIDATE_MANIFEST')
        self.spk=need('J14_ORACLE_SPK');self.data=need('J14_ORACLE_DATA_SOURCE');self.inventory=need('J14_ORACLE_INVENTORY')
        for name in (['spk-data-publish'] if self.DATA_PUBLICATION else [])+['spk-host','spk-ingest','mini-spk-broker','mini-spk-volume-helper',
                     'mini','minidregg-host','grain-runtime','minidregg-client-consent','mini-keys','grain-provider-bridge','launch-gate']:
            if not os.access(self.bins/name,os.X_OK):raise ValueError('missing selected executable '+name)
        for name,path in [('mini',self.mini),('minidregg-host',self.host),('grain-runtime',self.runtime)]:
            if sha(path)!=sha(self.bins/name):raise ValueError('selected binary cohort differs: '+name)
        self.installer=REPO/'deploy/spk-host/install-user-world'
        self.c={'root':str(self.root),'repo':str(REPO),'mini':self.mini,'host':self.host,'spkHost':str(self.bins/'spk-host'),'spk':self.spk,'taskBase':str(1000000000000+secrets.randbelow(1000000000000))}
        self.c['socketDirectory']=str(self.sockets)
        write(self.root/'allocation-context.json',self.c)
        self.homes=self.root/'homes';self.homes.mkdir();self.workspaces=self.root/'workspaces';self.workspaces.mkdir()
        (self.root/'subjects').mkdir()
        self.subjects={}
        self.pin_candidate()

    @classmethod
    def resume_transport(cls, checkpoint=None):
        """Resume only the proved pre-provision transport cutover boundary.

        No genesis, enrollment, provision, room write or application attempt is
        repeated. Other failure phases need their exact native recovery path.
        """
        os.umask(0o077)
        j=cls.__new__(cls);j.root=Path(os.environ['JOURNEY_STEP_DIR'])/'oracle';j.logs=j.root/'commands';j.lock_root()
        if checkpoint is None:
            failure=read(j.root/'failure.json')
            if failure['phase']!='world' or (j.root/'context-after-world.json').exists() or (j.root/'broker').exists():
                raise ValueError('transport continuation requires the uncompleted world cutover boundary')
            last=failure['lastCommand'];result=j.logs/f'{last:04d}-lifetime-target.result.json'
            if not result.is_file() or read(result)!={'exitCode':0}:
                raise ValueError('transport continuation requires retained successful target metadata rendering')
            j.c=read(j.root/'allocation-context.json')
        else:
            # The first reusable checkpoint is before physical registration or
            # native app attempts. Later uncertain phases use their native exact
            # lookup APIs; an arbitrary phase replay is deliberately unavailable.
            if checkpoint!=j.root/'context-after-world.json' or (j.root/'application').exists():
                raise ValueError('only the pre-application world checkpoint can resume here')
            failures=[read(p) for p in j.root.glob('failure*.json')]
            failure=max(failures,key=lambda f:f['lastCommand']);last=failure['lastCommand']
            command=j.logs/f'{last:04d}-broker-world'
            if failure['phase']!='application' or read(command.with_suffix('.result.json'))!={'exitCode':1}:
                raise ValueError('checkpoint refuses replay after an unclassified native attempt')
            # A refused sudo invocation submitted nothing. Require its retained
            # evidence instead of treating any installer error as safe to retry.
            argv=read(command.with_suffix('.argv.json'));prior=Path(argv[-1])
            if 'sudo: a password is required' not in (prior/'root-setup.log').read_text() or (prior/'broker.json').exists():
                raise ValueError('registration refusal is not proved; inspect exact physical state')
            j.c=read(checkpoint)
        j.c['manifest']=str(j.root/'candidate.json')
        if Path(j.c['root'])!=j.root:raise ValueError('retained root differs')
        j.bins=Path(need('J14_ORACLE_BIN'));j.mini=need('MINI');j.host=need('HOST');j.runtime=need('GRAIN_RUNTIME')
        j.provider=need('TEST_PROVIDER');j.hermes_root=need('J14_HERMES_ROOT');j.spk=need('J14_ORACLE_SPK')
        j.data=need('J14_ORACLE_DATA_SOURCE');j.inventory=need('J14_ORACLE_INVENTORY')
        candidate=read(j.c['manifest'])
        for role,path in [('mini',j.mini),('host',j.host),('spkHost',str(j.bins/'spk-host')),('store',need('STORE')),('verifier',need('VERIFIER'))]:
            if sha(path)!=candidate['sha256'][role]:raise ValueError('continuation binary pin changed: '+role)
        if sha(j.runtime)!=candidate['overlays']['grainRuntime'] or sha(j.provider)!=candidate['overlays']['testProvider']:
            raise ValueError('continuation runtime/provider changed before explicit release')
        j.installer=REPO/'deploy/spk-host/install-user-world';j.sockets=Path(j.c['socketDirectory'])
        j.homes=j.root/'homes';j.workspaces=j.root/'workspaces'
        j.subjects={name:read(j.root/'subjects'/f'{name}.json')['subject'] for name in ['alice','bob','hermes','hhost','hprov','hdisp']}
        w=j.root/'world';h=read(w/'handoff.json');j.sponsor=str(read(w/'genesis-params.json')['sponsor']['subject'])
        initial=Path(j.c.get('initialOperatorSocket',str(j.sockets/('private/operator.sock' if (j.sockets/'private/operator.config').exists() else 'operator.sock'))))
        j.c['initialOperatorSocket']=str(initial)
        j.c.update(repo=str(REPO),world=str(w),hostConfig=h['config'],sponsorWorkspace=h['sponsorWorkspace'],
                   operatorSocket=str(initial.with_name('operator-v2.sock')),publicSocket=str(j.sockets/'participant.sock'),allocation=str(j.root/'allocation.json'))
        room=read(Path(j.c['sponsorWorkspace'])/'refs/oracle-room.json');j.c['room']={'target':room['target'],'capability':room['observeCapability']}
        if read(j.c['allocation'])!=inputs.allocation(j.c) or sha(j.c['hostConfig'])!=sha(j.root/'operator-with-oracle.json'):
            raise ValueError('continuation allocation or installed metadata differs')
        j.counter=last;j.processes=[];j.daemons=[];j.controller=False;j.world_pid=None
        record=j.root/(f'checkpoint-continuation-{last:04d}.json' if checkpoint else 'transport-continuation.json')
        if record.exists():raise ValueError('transport continuation already attempted; inspect its retained commands')
        write(record,{'previousSource':candidate['orchestrationSource'],'sourceCommit':os.environ.get('J14_ORACLE_ORCHESTRATION_COMMIT'),
            'driverSha256':sha(HERE/'j14-oracle.py'),'installerSha256':sha(j.installer),'helperSha256':sha(REPO/'deploy/spk-host/controller-world.py'),
            'previousOperatorSocket':str(initial),'operatorSocket':j.c['operatorSocket'],
            'hostConfigSha256':sha(j.c['hostConfig']),'lastCompletedCommand':last})
        return j

    def restart_transport(self):
        self.spawn('operator-restart-'+str(self.counter),[self.mini,'serve-operator','--host',self.host,'--config',self.c['hostConfig'],'--socket',self.c['operatorSocket']])
        self.wait_socket(self.c['operatorSocket'])
        self.spawn('participant-restart-'+str(self.counter),[self.mini,'serve-public-proxy','--socket',self.c['publicSocket'],'--upstream',self.c['operatorSocket'],'--config',self.c['hostConfig']])
        self.wait_socket(self.c['publicSocket'])

    def resume_world(self):
        self.restart_transport()
        self.migrate_workspace_transport()
        self.c['nativeProfile']=str(self.run('native-profile',[self.host,self.c['hostConfig'],'profile']))

    def __del__(self):
        lock=getattr(self,'_lock',None)
        if lock is not None:lock.close()

    def lock_root(self):
        fd=os.open(self.root/'journey.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600)
        m=os.fstat(fd)
        if m.st_uid!=os.getuid() or m.st_mode&0o077 or m.st_nlink!=1:
            os.close(fd);raise ValueError('journey lock custody differs')
        self._lock=os.fdopen(fd,'r+')
        try:fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:
            self._lock.close();raise ValueError('another journey owns this evidence root')

    def frontier(self):
        rows=[(int(p.name.split('-',1)[0]),p) for p in self.logs.glob('*.argv.json') if re.match(r'^\d+-',p.name)]
        if not rows:return 0,[]
        number,path=max(rows)
        result=path.with_name(path.name.replace('.argv.json','.result.json'))
        if not result.is_file():raise ValueError('last command has no retained result; exact recovery required')
        return number,[{'path':str(p),'sha256':sha(p)} for p in [path,result]]

    def checkpoint(self,next_phase,basis=None,adjudication=None):
        """Retain orchestration coordinates, never fabricate native state."""
        if next_phase not in RESUMABLE:raise ValueError('post-worker recovery requires native application lineage recovery')
        frontier,proof=self.frontier()
        if frontier!=self.counter:raise ValueError('checkpoint counter differs from actual command frontier')
        if proof and read(proof[-1]['path'])!={'exitCode':0} and not adjudication:
            raise ValueError('failed command requires explicit no-submission or exact-recovery adjudication')
        path_fields={'root','logs','sockets','bins','installer','homes','workspaces','contract'}
        omit={'processes','world_pid','_lock'}
        state={k:str(v) if k in path_fields else v for k,v in vars(self).items() if k not in omit}
        live={p.pid for p in self.processes if p.poll() is None}
        state['daemons']=[{k:v for k,v in d.items() if k!='pid'} for d in self.daemons if d.get('pid') in live]
        pins={str(p):sha(p) for p in [self.mini,self.host,self.runtime,self.provider,self.bins/'spk-host',self.installer,
            REPO/'deploy/spk-host/controller-world.py',self.c['hostConfig']]}
        value={'protocol':'mini-j14-checkpoint-v1','nextPhase':next_phase,'state':state,'pins':pins,
            'basis':(basis or [])+proof,'adjudication':adjudication,'sourceCommit':os.environ.get('J14_ORACLE_ORCHESTRATION_COMMIT')}
        path=self.root/f'checkpoint-{self.counter:04d}-{next_phase}.json';write(path,value)
        return path

    @classmethod
    def from_checkpoint(cls,path):
        os.umask(0o077)
        expected=Path(os.environ['JOURNEY_STEP_DIR'])/'oracle'
        if path.parent!=expected or path.is_symlink():raise ValueError('checkpoint must be a retained direct child of the journey root')
        meta=path.stat()
        if meta.st_uid!=os.getuid() or meta.st_mode&0o077:raise ValueError('checkpoint must be private operator custody')
        value=read(path)
        preparation=(value.get('protocol')=='mini-j14-worker-preparation-checkpoint-v1' and value.get('nextPhase')=='worker_preparation')
        birth=(value.get('protocol')=='mini-j14-worker-birth-checkpoint-v1' and value.get('nextPhase')=='worker_birth')
        if not (preparation or birth) and (value.get('protocol')!='mini-j14-checkpoint-v1' or value['nextPhase'] not in RESUMABLE):
            raise ValueError('unsupported journey checkpoint phase')
        if preparation or birth:
            source=Path(value['workerPreparation'])
            required={str(expected/'worker-prepare.json'),str(expected/'grain-spec.json')}
            if (source!=expected/'worker-prepare.json' or bool(value['state'].get('controller'))!=birth
                    or not required <= {p['path'] for p in value['basis']}):
                raise ValueError('worker continuation lacks its exact retained preparation/spec boundary')
        for name,digest in value['pins'].items():
            if sha(name)!=digest:raise ValueError('checkpoint input changed: '+name)
        for proof in value['basis']:
            if sha(proof['path'])!=proof['sha256']:raise ValueError('checkpoint native basis changed')
        j=cls.__new__(cls)
        for name,data in value['state'].items():
            setattr(j,name,Path(data) if name in {'root','logs','sockets','bins','installer','homes','workspaces','contract','keyroot'} else data)
        if j.root!=expected:raise ValueError('checkpoint root differs')
        # A source update is explicit in the successor receipt. Native artifacts,
        # transports and controller custody stay pinned to the retained world.
        j.c['repo']=str(REPO);j.installer=REPO/'deploy/spk-host/install-user-world'
        for rel in ['deploy/spk-host/install-user-world','deploy/spk-host/controller-world.py']:
            selected=[digest for source,digest in value['pins'].items() if source.endswith('/'+rel)]
            if len(selected)!=1 or sha(REPO/rel)!=selected[0]:raise ValueError('checkpoint installer custody changed')
        j.processes=[];j.world_pid=None;j.resume_phase=value['nextPhase'];j.lock_root()
        if j.frontier()[0]!=j.counter:raise ValueError('newer command exists after this checkpoint; exact phase recovery required')
        prior_daemons=j.daemons;j.daemons=[]
        record=j.root/f'checkpoint-resume-{j.counter:04d}-{j.resume_phase}.json'
        if record.exists():raise ValueError('checkpoint continuation already attempted; inspect its exact retained outputs')
        write(record,{'checkpoint':str(path),'sha256':sha(path),'priorSource':value['sourceCommit'],
            'sourceCommit':os.environ.get('J14_ORACLE_ORCHESTRATION_COMMIT'),'driverSha256':sha(HERE/'j14-oracle.py')})
        j.restart_daemons=prior_daemons
        return j

    @classmethod
    def adopt_checkpoint_source(cls,path,reason):
        """Explicit reviewed helper update before first controller staging."""
        os.umask(0o077)
        expected=Path(os.environ['JOURNEY_STEP_DIR'])/'oracle'
        if path.parent!=expected or path.is_symlink():raise ValueError('source adoption needs retained checkpoint')
        metadata=path.stat()
        if metadata.st_uid!=os.getuid() or metadata.st_mode&0o077:raise ValueError('source adoption requires private checkpoint custody')
        value=read(path)
        if value.get('protocol')!='mini-j14-checkpoint-v1' or value.get('nextPhase') not in RESUMABLE:
            raise ValueError('source adoption is limited to pre-worker checkpoints')
        if value['state'].get('controller') or (expected/'worker').exists() or any(p.is_dir() for p in expected.glob('worker-*')):
            raise ValueError('source adoption cannot replace staged controller custody')
        if not isinstance(reason,str) or not 1<=len(reason)<=400:raise ValueError('source adoption requires a bounded explanation')
        j=cls.__new__(cls);j.root=expected;j.logs=expected/'commands';j.lock_root()
        if j.frontier()[0]!=value['state']['counter']:raise ValueError('source adoption refuses newer native work')
        for source,digest in value['pins'].items():
            if sha(source)!=digest:raise ValueError('prior source/native input changed before adoption')
        for proof in value['basis']:
            if sha(proof['path'])!=proof['sha256']:raise ValueError('prior checkpoint evidence changed')
        roles=['deploy/spk-host/install-user-world','deploy/spk-host/controller-world.py']
        pins=dict(value['pins']);changed={}
        for rel in roles:
            old=[source for source in pins if source.endswith('/'+rel)]
            if len(old)!=1:raise ValueError('source adoption role is ambiguous')
            source=old[0];new=str(REPO/rel);digest=sha(new)
            changed[rel]={'previousPath':source,'previousSha256':pins.pop(source),'path':new,'sha256':digest}
            pins[new]=digest
        value['pins']=pins;value['state']['installer']=str(REPO/'deploy/spk-host/install-user-world');value['state']['c']['repo']=str(REPO)
        value['basis']=[*value['basis'],{'path':str(path),'sha256':sha(path)}]
        value['sourceAdoption']={'previousCheckpoint':str(path),'sha256':sha(path),'reason':reason,'roles':changed}
        value['sourceCommit']=os.environ.get('J14_ORACLE_ORCHESTRATION_COMMIT')
        output=expected/f"checkpoint-{value['state']['counter']:04d}-source-successor.json"
        write(output,value);return output

    def restore_services(self):
        for item in self.restart_daemons:
            if sha(item['argv'][0])!=item['executableSha256']:raise ValueError('checkpoint daemon executable changed')
            argv=self.controller_public_args(item['argv']) if 'serve-public-proxy' in item['argv'] and self.controller else item['argv']
            self.spawn(item['label']+'-resume-'+str(self.counter),argv)
            if item.get('socket'):self.wait_socket(item['socket'])
            if 'serve-public-proxy' in item['argv'] and getattr(self,'controller',False):
                self.restore_public_socket_access(item['socket'])
        del self.restart_daemons

    def controller_public_args(self,args):
        argv=list(args);uid=self.layout['controllerUid']
        if type(uid) is not int or uid in (0,os.getuid()) or '--socket-gid' in argv:
            raise ValueError('controller public relay identity differs')
        for field,expected in [('--socket',self.c['publicSocket']),('--upstream',self.c['operatorSocket']),('--config',self.c['hostConfig'])]:
            if argv.count(field)!=1 or argv[argv.index(field)+1]!=expected:
                raise ValueError('controller public relay transport differs')
        if '--controller-uid' in argv:
            if argv.count('--controller-uid')!=1 or argv[argv.index('--controller-uid')+1]!=str(uid):
                raise ValueError('controller public relay recipient differs')
        else:argv.extend(['--controller-uid',str(uid)])
        return argv

    def ensure_controller_public_proxy(self):
        live={p.pid:p for p in self.processes if p.poll() is None}
        matches=[d for d in self.daemons if d.get('pid') in live and 'serve-public-proxy' in d['argv']]
        if len(matches)!=1:raise ValueError('one owned public relay must be running before controller birth')
        daemon=matches[0];argv=self.controller_public_args(daemon['argv'])
        if argv==daemon['argv']:return
        # Native controller ingress accepts the exact installer traversal ACL
        # and recreates this UID's connect ACL whenever the inode is rebound.
        process=live[daemon['pid']];process.terminate();process.wait(timeout=15)
        self.spawn('participant-controller',argv);self.wait_socket(self.c['publicSocket'])

    def private_operator_socket(self,name='operator.sock'):
        directory=self.sockets/'private'
        directory.mkdir(mode=0o700,exist_ok=True)
        metadata=directory.lstat()
        if (not stat.S_ISDIR(metadata.st_mode) or directory.is_symlink()
                or metadata.st_uid!=os.getuid() or stat.S_IMODE(metadata.st_mode)!=0o700):
            raise ValueError('operator socket parent must remain private operator custody')
        return directory/name

    @staticmethod
    def private_metadata_bytes(path):
        path=Path(path);metadata=path.lstat()
        if (path.resolve()!=path or not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink!=1
                or metadata.st_uid!=os.getuid() or metadata.st_mode&0o077 or metadata.st_size>1048576):
            raise ValueError('transport metadata requires private regular operator custody: '+str(path))
        return path.read_bytes()

    @staticmethod
    def retain_transport_bytes(path,data):
        if path.exists():
            if Journey.private_metadata_bytes(path)!=data:raise ValueError('retained transport evidence changed')
            return
        fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
        with os.fdopen(fd,'wb') as out:out.write(data);out.flush();os.fsync(out.fileno())

    def prepare_operator_relocation(self):
        selected=os.environ.get('J14_ORACLE_OPERATOR_RELOCATION')
        if not selected:return
        if not Path(selected).is_absolute():raise ValueError('operator relocation request path must be absolute')
        request=json.loads(self.private_metadata_bytes(Path(selected)))
        expected={'protocol','previousSocket','socket','hostConfigSha256'}
        if (set(request)!=expected or request['protocol']!='mini-j14-operator-relocation-v1'
                or request['socket']!=str(self.sockets/'private/operator.sock')
                or request['previousSocket'] not in (str(self.sockets/'operator-v2.sock'),str(self.sockets/'operator.sock'))
                or request['hostConfigSha256']!=sha(self.c['hostConfig'])
                or self.c['operatorSocket'] not in (request['previousSocket'],request['socket'])):
            raise ValueError('operator transport relocation identity differs')
        if (self.resume_phase!='worker_birth' or not self.controller or getattr(self,'application_unit',None)
                or (self.root/'attachment').exists()):
            raise ValueError('operator transport relocation requires the pre-birth, pre-START boundary')
        old,new=request['previousSocket'],request['socket']
        # The old listener's retained sidecar binds the unchanged native Store.
        if self.private_metadata_bytes(Path(old).with_suffix('.config'))!=self.private_metadata_bytes(Path(self.c['hostConfig'])):
            raise ValueError('operator relocation requires identical native Store settings')
        result=read(self.c['profileResult']);profile=Path(result['profilePath'])
        state=Path(result['stateRoot'])
        if profile!=state/'grain-host.json' or (state/'active-profile.json').exists():
            raise ValueError('operator relocation cannot alter an active successor profile')
        workspaces=[Path(self.c['sponsorWorkspace'])/'workspace.json',*sorted(self.workspaces.glob('*/workspace.json'))]
        broker=self.sockets/'provider/broker.json'
        paths=[(profile,'profile'),*[(path,'workspace') for path in workspaces],(broker,'provider')]
        operator=public=0
        for item in self.restart_daemons:
            argv=item['argv']
            if 'serve-operator' in argv:
                index=argv.index('--socket')+1
                if argv[index] not in (old,new):raise ValueError('retained operator daemon endpoint differs')
                argv[index]=new;item['socket']=new;operator+=1
            elif 'serve-public-proxy' in argv:
                index=argv.index('--upstream')+1
                if argv[index] not in (old,new):raise ValueError('retained public upstream differs')
                argv[index]=new;public+=1
            elif old in argv:raise ValueError('unclassified daemon still selects old operator endpoint')
        if operator!=1 or public!=1:raise ValueError('operator relocation requires one recorded operator and public proxy')
        self.private_operator_socket()
        archive=self.root/'operator-transport';archive.mkdir(mode=0o700,exist_ok=True)
        metadata=archive.lstat()
        if (not stat.S_ISDIR(metadata.st_mode) or metadata.st_uid!=os.getuid()
                or stat.S_IMODE(metadata.st_mode)!=0o700):
            raise ValueError('operator transport archive custody differs')
        plan_path=archive/'transition.json'
        if plan_path.exists():
            plan=json.loads(self.private_metadata_bytes(plan_path))
            if plan['request']!=request or [(row['path'],row['kind']) for row in plan['files']]!=[(str(path),kind) for path,kind in paths]:
                raise ValueError('operator relocation inventory differs from retained transition')
        else:
            rows=[]
            for index,(path,kind) in enumerate(paths):
                before=self.private_metadata_bytes(path);value=json.loads(before)
                if kind=='profile':
                    if (value.get('miniOperatorSocket')!=old or value.get('miniConfig')!=self.c['hostConfig']
                            or value.get('miniConfigSha256')!=request['hostConfigSha256']
                            or value.get('miniHost')!=self.host or value.get('miniHostSha256')!=sha(self.host)
                            or value.get('stateRoot')!=str(state) or value.get('genesisConfigSha256') is not None):
                        raise ValueError('baseline profile transport pins differ')
                    value['miniOperatorSocket']=new
                elif kind=='workspace':
                    if (value.get('socket')!=old or value.get('config')!=self.c['hostConfig']
                            or value.get('host')!=self.host or value.get('hostSha256')!=sha(self.host)):
                        raise ValueError('workspace transport pins differ')
                    value['socket']=new
                else:
                    credentials=value.get('credentials',{})
                    if (credentials.get('publicSocket')!=old or credentials.get('hostConfig')!=self.c['hostConfig']
                            or credentials.get('host')!=self.host or credentials.get('hostSha256')!=sha(self.host)
                            or credentials.get('publicSocketUid')!=os.getuid()):
                        raise ValueError('provider transport pins differ')
                    credentials['publicSocket']=new
                after=(json.dumps(value,indent=2)+'\n').encode()
                before_path=archive/f'{index:02d}-before.json';after_path=archive/f'{index:02d}-after.json'
                self.retain_transport_bytes(before_path,before);self.retain_transport_bytes(after_path,after)
                rows.append({'path':str(path),'kind':kind,'before':str(before_path),'after':str(after_path),
                             'beforeSha256':sha(before_path),'afterSha256':sha(after_path)})
            plan={'protocol':'mini-j14-operator-transport-transition-v1','request':request,'files':rows}
            self.retain_transport_bytes(plan_path,(json.dumps(plan,indent=2)+'\n').encode())
        # Persist the whole transition before replacing the first metadata file.
        directory=os.open(archive,os.O_RDONLY)
        try:os.fsync(directory)
        finally:os.close(directory)
        for row in plan['files']:
            path=Path(row['path']);before=self.private_metadata_bytes(Path(row['before']));after=self.private_metadata_bytes(Path(row['after']))
            if hashlib.sha256(before).hexdigest()!=row['beforeSha256'] or hashlib.sha256(after).hexdigest()!=row['afterSha256']:
                raise ValueError('operator relocation archived bytes changed')
            current=self.private_metadata_bytes(path)
            if current==after:continue
            if current!=before:raise ValueError('transport metadata changed outside retained transition')
            temporary=path.with_name(path.name+'.operator-transport-next')
            self.retain_transport_bytes(temporary,after);os.replace(temporary,path)
            directory=os.open(path.parent,os.O_RDONLY)
            try:os.fsync(directory)
            finally:os.close(directory)
        self.c['operatorSocket']=new
        self.c['operatorTransportTransition']=str(plan_path)
        self.operator_relocation=request

    def restore_public_socket_access(self,path):
        if str(path)!=self.c['publicSocket']:raise ValueError('public ACL restore selected another socket')
        metadata=Path(path).lstat()
        uid=self.layout['controllerUid']
        if (not stat.S_ISSOCK(metadata.st_mode) or metadata.st_uid!=os.getuid()
                or type(uid) is not int or uid==0 or uid==os.getuid()):
            raise ValueError('public socket ACL recipient or custody differs')
        self.run('public-socket-acl',['setfacl','-m',f'u:{uid}:-w-','--',path])
        after=Path(path).lstat()
        if (metadata.st_dev,metadata.st_ino)!=(after.st_dev,after.st_ino):
            raise ValueError('public socket changed during ACL restoration')

    def finish_operator_relocation(self):
        request=getattr(self,'operator_relocation',None)
        if request is None:return
        self.fixed('controller-stop')
        receipt=self.fixed('controller-operator-endpoint',request['socket'])
        self.c['operatorEndpointReceipt']=str(receipt)

    def pin_candidate(self):
        candidate=read(self.candidate_manifest)
        source_files=[HERE/'j14-oracle.py',HERE/'j14-oracle-inputs.py',HERE/'j14-oracle-evidence.py',
            REPO/'scripts/application-attachment.py',REPO/'scripts/spk-platform/same-store-app.py',
            REPO/'scripts/spk-platform/same-store-profile.py',REPO/'scripts/spk-platform/ws-continuity-fixture.py',
            REPO/'scripts/spk-platform/broker-world-up.sh',REPO/'deploy/spk-host/install-user-world',
            REPO/'deploy/spk-host/controller-world.py',REPO/'native/resource-client/newparticipant-acceptance.sh']
        m={'sourceCommit':candidate['sourceCommit'],'sha256':{},'candidateManifest':self.candidate_manifest,
           'candidateManifestSha256':sha(self.candidate_manifest),'overlays':{'grainRuntime':sha(self.runtime),**({'testProvider':sha(self.provider)} if self.provider else {})},
           'orchestrationSource':{'commit':os.environ.get('J14_ORACLE_ORCHESTRATION_COMMIT'),
                                  'files':{str(p.relative_to(REPO)):sha(p) for p in source_files}}}
        for role,path in [('host',self.host),('mini',self.mini),('store',need('STORE')),('verifier',need('VERIFIER')),('spkHost',str(self.bins/'spk-host'))]:
            digest=sha(path)
            if digest!=candidate['sha256'][role]:raise ValueError('selected candidate artifact differs: '+role)
            m[role]=path;m['sha256'][role]=digest
        manifest=self.root/'candidate.json';write(manifest,m);self.c['manifest']=str(manifest)

    def task(self,role):
        return str(int(self.c['taskBase'])+['controller','tool','provider','dispatch'].index(role)+1)

    def run(self,label,args,env=None,timeout=1800):
        self.counter+=1;stem=self.logs/f'{self.counter:04d}-{label}'
        argv=list(map(str,args));write(stem.with_suffix('.argv.json'),argv)
        with stem.with_suffix('.stdout').open('w') as out,stem.with_suffix('.stderr').open('w') as err:
            result=subprocess.run(argv,stdout=out,stderr=err,env=env,timeout=timeout)
        write(stem.with_suffix('.result.json'),{'exitCode':result.returncode})
        if result.returncode:raise RuntimeError(f'{label} failed ({result.returncode}); retained {stem}')
        return stem.with_suffix('.stdout')

    def spawn(self,label,args):
        stem=self.logs/label;generation=0
        while any(Path(str(stem)+suffix).exists() for suffix in ['.stdout','.stderr','.process.json']):
            generation+=1;stem=self.logs/f'{label}-{generation:02d}'
        output=Path(str(stem)+'.stdout');error=Path(str(stem)+'.stderr')
        with output.open('x') as out,error.open('x') as err:
            p=subprocess.Popen(list(map(str,args)),stdout=out,stderr=err)
        self.processes.append(p);p.journey_stdout=output
        argv=list(map(str,args))
        write(Path(str(stem)+'.process.json'),{'pid':p.pid,'argv':argv})
        daemon={'label':stem.name,'argv':argv,'executableSha256':sha(argv[0]),'pid':p.pid}
        if '--socket' in argv:daemon['socket']=argv[argv.index('--socket')+1]
        self.daemons.append(daemon)
        return p

    def wait_socket(self,path):
        deadline=time.monotonic()+120
        while time.monotonic()<deadline:
            # A stopped endpoint can leave its socket inode behind. Readiness
            # requires a listener, not merely a filesystem entry.
            try:
                with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as client:
                    client.settimeout(.2);client.connect(str(path))
                if getattr(self,'daemons',[]):self.daemons[-1]['socket']=str(path)
                return
            except (OSError,TimeoutError):pass
            time.sleep(.1)
        raise RuntimeError('socket did not appear: '+str(path))

    def shell(self,who,line):
        ws=self.c['sponsorWorkspace'] if who=='sponsor' else str(self.workspaces/who)
        return self.run('shell-'+who,[self.mini,'shell','--socket',self.c['operatorSocket'],'--host',self.host,
            '--config',self.c['hostConfig'],'--workspace',ws,'--home',self.homes/who,'--line',line])

    def fixed(self,verb,*args,timeout=1800):
        return self.run(verb,['sudo','-n',self.installer,verb,self.broker['store'],self.broker['helper'],*args],timeout=timeout)

    def controller_run(self,program,args,files=None):
        request=self.root/f'controller-request-{self.counter+1:04d}.json';write(request,{'program':program,'args':list(map(str,args)),**({'inputs':files} if files else {})})
        return self.fixed('controller-run',request)

    def world(self):
        tariff=self.root/'provider-services.json';write(tariff,[{'providerResourceId':int(self.task('provider')),'tariff':{
            'version':'1','model':self.MODEL,'routes':{'user':{'perOp':'5'},
            'pool':{'perOp':'7','inputMicroPerMillion':'100000','outputMicroPerMillion':'200000'},
            'homelab':{'perOp':'3','inputMicroPerMillion':'0','outputMicroPerMillion':'0'}}}}])
        w=self.root/'world';sock=self.private_operator_socket('operator.sock');self.c['initialOperatorSocket']=str(sock)
        # Each run needs a distinct Store tag for its registered physical world.
        env=dict(os.environ,NEWPARTICIPANT_GRAIN_PLATFORM='1',NEWPARTICIPANT_SERVE='serve-operator',
                 NEWPARTICIPANT_TEMPLATE_DIR='',NEWPARTICIPANT_PROVIDER_SERVICES=str(tariff),NEWPARTICIPANT_SPONSOR_BALANCE='1000000')
        self.run('world',[REPO/'native/resource-client/newparticipant-acceptance.sh',self.host,self.mini,need('STORE'),need('VERIFIER'),w,sock],env=env)
        h=read(w/'handoff.json');self.c.update(world=str(w),hostConfig=h['config'],sponsorWorkspace=h['sponsorWorkspace'],operatorSocket=str(sock),publicSocket=str(self.sockets/'participant.sock'))
        self.world_pid=int((w/'public/server.pid').read_text())
        params=read(w/'genesis-params.json');self.sponsor=str(params['sponsor']['subject'])
        (self.homes/'sponsor/keys').mkdir(parents=True)
        self.run('app-tasks',[self.mini,'apps','bootstrap','--dir',self.c['sponsorWorkspace'],'--budget','20000'])
        permit=self.root/'permit-all.json';write(permit,{'type':'all','predicates':[]})
        for who,funding in [('alice',5000),('bob',100),('hermes',10000),('hhost',0),('hprov',0),('hdisp',0)]:
            (self.homes/who).mkdir()
            self.shell(who,'keygen mini.key')
            key=self.homes/who/'keys/mini.key';copy=self.homes/'sponsor/keys'/f'j14-{who}.key'
            shutil.copyfile(key,copy)
            self.shell('sponsor',f'enroll plan j14-{who} j14-{who}.key --no-prerotation')
            self.shell('sponsor',f'enroll seal j14-{who}')
            enrolled=read(self.shell('sponsor',f'enroll submit j14-{who}'))
            write(self.root/'subjects'/f'{who}.json',enrolled);self.subjects[who]=enrolled['subject'];copy.unlink()
            self.run('provision-'+who,[self.mini,'workspace','--action','provision','--dir',self.c['sponsorWorkspace'],
                '--name','j14-'+who,'--holder',enrolled['subject'],'--funding',funding,'--account-predicate',permit,'--factory-ref','factory'])
            (self.homes/who/'provision').mkdir()
            shutil.copyfile(Path(self.c['sponsorWorkspace'])/'provisions'/('j14-'+who)/'birth-context.json',self.homes/who/'provision/birth-context.json')
            if who in ['alice','bob']:self.shell(who,f'init mini.key {enrolled["subject"]} --no-prerotation')
        self.shell('alice','chat new lab');self.shell('alice',f"doc new lab-index 'any [ not (verb == write), subject == {self.subjects['alice']} ]' --in lab")
        self.shell('alice','tariff lab set hermes/turn 10')
        self.shell('alice',f"chat invite lab {self.subjects['bob']} bob --verbs observe,place,append")
        (self.homes/'bob/requests').mkdir(exist_ok=True)
        shutil.copyfile(self.homes/'alice/chat/invites'/f"lab-{self.subjects['bob']}.json",self.homes/'bob/requests/lab-invite.json')
        self.shell('bob','chat join lab @lab-invite.json')
        # The app issuer observes this actual room through the founder's grant.
        self.shell('alice',f'room invite oracle-host lab {self.sponsor} --verbs observe')
        for line in ['submit oracle-host','publish oracle-host']:self.shell('alice',line)
        reference=self.shell('alice','export oracle-host').read_text().strip()
        self.shell('sponsor','import oracle-room '+reference)
        room=read(Path(self.c['sponsorWorkspace'])/'refs/oracle-room.json')
        self.c['room']={'target':room['target'],'capability':room['observeCapability']}
        allocation=self.root/'allocation.json';write(allocation,inputs.allocation(self.c));self.c['allocation']=str(allocation)
        fresh=self.root/'operator-with-oracle.json'
        self.run('lifetime-target',['python3',REPO/'scripts/application-attachment.py','render-host-config',self.c['hostConfig'],allocation,fresh])
        os.kill(self.world_pid,signal.SIGTERM)
        deadline=time.monotonic()+60
        while Path('/proc',str(self.world_pid)).exists() and time.monotonic()<deadline:time.sleep(.1)
        if Path('/proc',str(self.world_pid)).exists():raise RuntimeError('own operator did not stop before settings update')
        shutil.copyfile(fresh,self.c['hostConfig'])
        # Retained endpoint config pins are immutable. Preserve the old pin
        # and expose revised transport metadata on a fresh same-Store endpoint.
        sock=self.private_operator_socket('operator-v2.sock');self.c['operatorSocket']=str(sock)
        self.spawn('operator-v2',[self.mini,'serve-operator','--host',self.host,'--config',self.c['hostConfig'],'--socket',sock]);self.world_pid=None
        self.wait_socket(sock)
        self.spawn('participant',[self.mini,'serve-public-proxy','--socket',self.c['publicSocket'],'--upstream',sock,'--config',self.c['hostConfig']]);self.wait_socket(self.c['publicSocket'])
        self.migrate_workspace_transport()
        native=self.run('native-profile',[self.host,self.c['hostConfig'],'profile']);self.c['nativeProfile']=str(native)

    def migrate_workspace_transport(self):
        """Explicit same-Store routing change; preserve every authority field."""
        old=Path(self.c.get('initialOperatorSocket',str(self.sockets/'operator.sock')));new=self.c['operatorSocket']
        if str(old)==new:return
        old_config=old.with_suffix('.config');before_config=read(old_config);after_config=read(self.c['hostConfig'])
        semantic=lambda value:{k:v for k,v in value.items() if k!='agentLifetimeDispatchTargets'}
        if semantic(before_config)!=semantic(after_config):raise ValueError('workspace migration requires identical native Store settings')
        archive=self.root/'workspace-transport';archive.mkdir(mode=0o700,exist_ok=True)
        for index,path in enumerate([Path(self.c['sponsorWorkspace'])/'workspace.json',*sorted(self.workspaces.glob('*/workspace.json'))]):
            record=archive/f'{index:02d}.json'
            if record.exists():
                pins=read(record)
                if str(path)!=pins['workspace']:raise ValueError('workspace routing inventory changed')
                before=Path(pins['before']).read_bytes();after=Path(pins['after']).read_bytes()
                if hashlib.sha256(before).hexdigest()!=pins['beforeSha256'] or hashlib.sha256(after).hexdigest()!=pins['afterSha256']:
                    raise ValueError('retained workspace routing bytes changed')
            else:
                if path.is_symlink() or path.stat().st_uid!=os.getuid() or path.stat().st_mode&0o077:
                    raise ValueError('workspace routing requires private operator custody')
                before=path.read_bytes();value=json.loads(before)
                if value['socket']!=str(old) or value['config']!=self.c['hostConfig'] or value['host']!=self.host or value['hostSha256']!=sha(self.host):
                    raise ValueError('workspace routing source pins differ')
                value['socket']=new;after=(json.dumps(value,indent=2)+'\n').encode()
                previous=archive/f'{index:02d}-before.json';successor=archive/f'{index:02d}-after.json'
                for target,data in [(previous,before),(successor,after)]:
                    with target.open('xb') as out:out.write(data);out.flush();os.fsync(out.fileno())
                write(record,{'workspace':str(path),'before':str(previous),'after':str(successor),
                    'beforeSha256':sha(previous),'afterSha256':sha(successor),'oldSocket':str(old),'newSocket':new,
                    'oldConfig':str(old_config),'oldConfigSha256':sha(old_config),'newConfigSha256':sha(self.c['hostConfig'])})
            current=path.read_bytes()
            if current==after:continue
            if current!=before:raise ValueError('workspace changed outside retained routing transition')
            temporary=path.with_name('workspace.transport-next.json')
            with temporary.open('xb') as out:out.write(after);out.flush();os.fsync(out.fileno())
            os.replace(temporary,path)
            directory=os.open(path.parent,os.O_RDONLY)
            try:os.fsync(directory)
            finally:os.close(directory)

    def prepare_platform(self):
        # The resident broker checks a concrete inventory for any home paths.
        # These are the native transport/custody inputs, never a whole home tree.
        w=Path(self.c['world'])
        paths=[Path(self.host),Path(self.c['hostConfig']),Path(self.c['operatorSocket']).parent,
               w/'keys/completion.seed',w/'sponsor.key',
               *[self.homes/name/'keys/mini.key' for name in ('hhost','hermes','hprov','hdisp')]]
        inventory=self.root/'resident-home-paths.json'
        write(inventory,sorted({str(p) for p in paths if p.is_relative_to('/home') or p.is_relative_to('/root')}))
        env=dict(os.environ,MINI_IMPORT_PROFILE='operator-appliance-v1',MINI_RESIDENT_HOME_PATHS=str(inventory))
        broker=self.root/f'broker-{self.counter+1:04d}'
        self.run('broker-world',[REPO/'scripts/spk-platform/broker-world-up.sh',self.bins,self.c['hostConfig'],broker],env=env)
        self.broker=read(broker/'broker.json')
        self.layout=read(self.fixed('controller-create'));self.c['controllerRoot']=str(Path(self.layout['controllerHome'])/'grain')
        params=read(Path(self.c['world'])/'genesis-params.json')
        manifest=Path(self.c['manifest']);m=read(manifest)
        w=Path(self.c['world']);p={'protocol':'mini-spk-same-store-profile-input-v1','manifest':str(manifest),'expectedSourceCommit':m['sourceCommit'],
            'miniConfig':self.c['hostConfig'],'miniConfigSha256':sha(self.c['hostConfig']),
            'management':{'subject':self.sponsor,'keyId':str(params['sponsor']['keyId']),'keyEpoch':str(params['sponsor']['keyEpoch']),'publicKeyPath':str(w/'sponsor.pub'),'seedPath':str(w/'sponsor.key')},
            'completionPublicKey':str(w/'keys/completion.pub'),'completionSeed':str(w/'keys/completion.seed'),
            'semantics':str(read(self.c['nativeProfile'])['semantics']),'root':str(self.root/'profile'),
            'grainsRoot':self.broker['grainsRoot'],'brokerSocket':self.broker['brokerSocket'],'privateSocket':self.c['operatorSocket'],
            'bwrap':self.run('bwrap',['sh',REPO/'deploy/grain-host/resolve-bwrap']).read_text().strip(),'importProfile':'operator-appliance-v1'}
        path=self.root/'profile-input.json';write(path,p)
        result=read(self.run('profile',['python3',REPO/'scripts/spk-platform/same-store-profile.py',path]));self.c['profileResult']=result['profileResult']

    def application_input(self):
        return inputs.provision(self.c)

    def prepare_application(self):
        path=self.root/'application-input.json'
        expected=self.application_input()
        if path.exists():
            if read(path)!=expected:raise ValueError('retained application input differs')
        else:write(path,expected)
        prepared=self.run('application-prepare',['python3',REPO/'scripts/spk-platform/same-store-app.py','prepare',path],timeout=14400)
        self.c['preparedApplication']=str(prepared)

    def publish_data(self):
        self.run('publish-data',[self.bins/'spk-data-publish','publish','--store',Path(self.broker['grainsRoot'])/'spk/public-data','--source',self.data,'--inventory',self.inventory],timeout=3600)

    def cleanup(self):
        if self.controller:
            try:self.fixed('controller-stop',timeout=120)
            except Exception:pass
        for p in reversed(self.processes):
            if p.poll() is None:
                p.terminate()
                try:p.wait(timeout=30)
                except subprocess.TimeoutExpired:pass
        if getattr(self,'world_pid',None):
            try:os.kill(self.world_pid,signal.SIGTERM)
            except ProcessLookupError:pass

    def await_worker_release(self):
        selected=os.environ.get('J14_ORACLE_WORKER_RELEASE')
        if not selected:return
        if Path(self.runtime)!=self.bins/'grain-runtime':
            raise ValueError('worker release may update only the selected owned bin overlay')
        path=Path(selected)
        if not path.is_absolute():raise ValueError('worker release path must be absolute')
        successor=self.root/'worker-runtime-successor.json'
        prior=read(successor) if successor.exists() else None
        previous=prior['previousRuntimeSha256'] if prior else sha(self.runtime)
        deadline=time.monotonic()+1800
        wait_record={'releasePath':str(path),'previousRuntimeSha256':previous,'maximumWaitSeconds':1800}
        retained=self.root/'worker-wait.json'
        if retained.exists():
            if read(retained)!=wait_record:raise ValueError('retained worker release wait differs')
        else:write(retained,wait_record)
        while not path.exists():
            if time.monotonic()>=deadline:raise TimeoutError('worker release not supplied; native Store and application attempts retained')
            time.sleep(1)
        metadata=path.lstat()
        if path.is_symlink() or not path.is_file() or metadata.st_uid!=os.getuid() or metadata.st_mode&0o077:
            raise ValueError('worker release must be an operator-private regular file')
        release=read(path)
        if set(release)!={'runtime','sha256','sourceCommit'} or re.fullmatch('[0-9a-f]{64}',release['sha256']) is None or re.fullmatch('[0-9a-f]{40}',release['sourceCommit']) is None:
            raise ValueError('worker release pin contract differs')
        source=Path(release['runtime'])
        if not source.is_absolute() or source.is_symlink() or not source.is_file() or not os.access(source,os.X_OK) or sha(source)!=release['sha256']:
            raise ValueError('released runtime differs from selected pin')
        expected={'protocol':'mini-j14-runtime-successor-v1','previousRuntimeSha256':previous,
                  'initialCandidateManifest':self.c['manifest'],'release':release}
        if prior is not None and prior!=expected:raise ValueError('runtime successor differs from retained release')
        if prior is not None and sha(self.runtime)==release['sha256']:return
        if sha(self.runtime)!=previous:raise ValueError('initial runtime changed while preparation was running')
        temporary=self.bins/('grain-runtime-release-'+secrets.token_hex(6))
        shutil.copyfile(source,temporary);temporary.chmod(0o755)
        if sha(temporary)!=release['sha256']:raise ValueError('runtime changed during release copy')
        if prior is None:write(successor,expected)
        os.replace(temporary,self.runtime)

    def worker(self):
        home=Path(self.layout['controllerHome']);base=home.parent;grain=home/'grain'
        staged=self.root/f'worker-{self.counter+1:04d}';staged.mkdir();launcher=staged/'launcher';launcher.mkdir()
        physical=self.run('bwrap',['sh',REPO/'deploy/grain-host/resolve-bwrap']).read_text().strip()
        self.run('launcher',['python3',REPO/'deploy/grain-host/materialize-bwrap.py','--physical-bwrap',physical,'--physical-sha256',sha(physical),'--output',launcher/'bwrap'])
        shutil.copyfile(self.bins/'launch-gate',launcher/'launch-gate');os.chmod(launcher/'launch-gate',0o700)
        runtime=staged/'runtime-root'
        # Dereference the selected source once as the ordinary operator. The
        # root installer only accepts the resulting bounded regular tree.
        shutil.copytree(self.hermes_root,runtime,symlinks=False)
        for name in ['grain-runtime','grain-provider-bridge']:
            shutil.copyfile(self.bins/name,runtime/name);os.chmod(runtime/name,0o755)
        pins=read(runtime/'pins.json')
        pins.update(grainRuntimeSha256=sha(runtime/'grain-runtime'),grainProviderBridgeSha256=sha(runtime/'grain-provider-bridge'),
                    candidateManifest=self.candidate_manifest,candidateManifestSha256=sha(self.candidate_manifest),
                    runtimeOverlay={'path':self.runtime,'sha256':sha(self.runtime)})
        (runtime/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
        self.table=runtime/'providers.json';port=int(os.environ['J14_PROVIDER_PORT']) if 'J14_PROVIDER_PORT' in os.environ else available_port()
        self.start_provider(port)
        self.keyroot=self.sockets/'provider';self.keyroot.mkdir(mode=0o711);self.keyroot.chmod(0o711)
        keysocket=self.keyroot/'keys.sock';keyclient=runtime/'keys-client.json'
        write(keyclient,{'type':'mini-keys-client-v1','socket':str(keysocket),'uid':os.getuid()})
        (self.keyroot/'credentials').mkdir(mode=0o700)
        key=self.keyroot/'credentials.key';key.write_bytes(secrets.token_bytes(32));key.chmod(0o600)
        brokerconfig=self.keyroot/'broker.json'
        write(brokerconfig,{'type':'mini-keys-broker-v1','socket':str(keysocket),'audit':str(self.keyroot/'audit.jsonl'),
            'spool':str(self.keyroot/'spool'),'singleAccount':True,
            'peers':[{'role':'member','gids':[os.getgid()]},{'role':'provider','uids':[self.layout['controllerUid']]},
                     {'role':'operator','uids':[os.getuid()]}],
            'credentials':{'host':self.host,'hostSha256':sha(self.host),'hostConfig':self.c['hostConfig'],
                'publicSocket':self.c['operatorSocket'],'publicSocketUid':os.getuid(),'providers':str(base/'worker/runtime-root/providers.json'),
                'root':str(self.keyroot/'credentials'),'key':str(key)}})
        params=read(Path(self.c['world'])/'genesis-params.json');cfg=read(self.c['hostConfig'])
        role=lambda name:{'key':str(home/'keys'/f'{name}.key'),'subject':self.subjects[name],'noPrerotation':True}
        spec={'type':'mini-grain-create-v1','mini':str(base/'bin/mini'),'host':str(base/'bin/minidregg-host'),
            'hostConfig':str(home/'host-config.json'),'hostSocket':str(home/'operator/mini.sock'),
            'genesis':str(home/'bootstrap/genesis.json'),'namespaceRoot':str(home/'bootstrap/namespace'),'root':str(grain),'nonce':'987000',
            'sponsor':{'key':str(Path(self.c['world'])/'sponsor.key'),'subject':self.sponsor,
                'accountCapability':str(params['sponsor']['spendCapabilityId']),
                'grants':read(Path(self.c['world'])/'sponsor-birth-context.json')['grants']},
            'template':{k:str(cfg[k]) for k in ['issuer','ownerBudget','lifetime']},'owner':role('hhost'),'workerKey':role('hermes'),
            'task':self.task('controller'),'toolTask':self.task('tool'),'capabilities':{'parentObserve':'9870011','parentControl':'9870012','toolObserve':'9870013','toolControl':'9870014'},
            'budgets':{'parent':'20000','tool':'20000','witnessMaxCost':'50000'},
            'worker':{'launcher':str(base/'worker/launcher/bwrap'),'runtimeRoot':str(base/'worker/runtime-root'),
                'workspace':str(home/'worker-work'),'network':'none','wallTimeSeconds':1800,'reserve':'3','charge':'1'},
            'toolCharges':{'reserve':'5','charge':'1'},
            'provider':{'key':role('hprov'),'task':self.task('provider'),'observeCapability':'9870015','controlCapability':'9870016','budget':'50000',
                'gateway':self.gateway_config(port,base)},
            'dispatch':{'key':role('hdisp'),'task':self.task('dispatch'),'observeCapability':'9870017','controlCapability':'9870018','budget':'20000',
                'transport':{'reserve':'1','charge':'1','socketPath':self.layout['reverseSocket'],'hostUid':os.getuid(),
                    'operatorSocket':str(home/'operator/mini.sock'),'operatorPeerUid':0,
                    'reserveSigner':{'role':'4','index':'0','publicKey':(self.homes/'hdisp/keys/mini.key.pub').read_bytes().hex(),
                                     'keyId':read(self.root/'subjects/hdisp.json')['keyId'],'keyEpoch':'1'}}},
            'room':{'mini':str(base/'bin/mini'),'host':str(base/'bin/minidregg-host'),'hostConfig':str(home/'host-config.json'),
                'socket':self.c['publicSocket'],'workspace':str(grain/'state/resource-workspace'),'home':str(grain/'state/room-home'),
                'room':'lab','account':'unsummoned'}}
        # Public Host frames use the public endpoint; reserve authoring uses
        # the separate, controller-only operator proxy.
        spec['hostSocket']=self.c['publicSocket']
        source=self.root/'grain-spec.json';write(source,spec)
        files=[{'source':self.c['hostConfig'],'destination':'host-config.json'},
               {'source':str(Path(self.c['world'])/'genesis.json'),'destination':'bootstrap/genesis.json'},
               {'source':str(source),'destination':'requests/grain-spec.json'}]
        for name in ['hhost','hermes','hprov','hdisp']:
            files.append({'source':str(self.homes/name/'keys/mini.key'),'destination':f'keys/{name}.key'})
        prepare=self.root/'worker-prepare.json';write(prepare,{'protocol':'mini-controller-worker-prepare-v1','task':self.task('controller'),
            'files':files,'directories':['bootstrap/namespace','requests','requests/inbox','requests/registrations','worker-work/.hermes','worker-work/.cache','worker-work/.config','worker-work/.local/share'],
            'launcherDirectory':str(launcher),'runtimeRoot':str(runtime)})
        self.fixed('controller-worker-prepare',prepare,self.bins,self.c['operatorSocket'],self.c['publicSocket'])
        self.finish_worker(source,runtime)

    def worker_preparation(self):
        prepare=self.root/'worker-prepare.json';request=read(prepare)
        self.keyroot=self.sockets/'provider'
        self.fixed('controller-worker-prepare-resume',prepare,self.bins,self.c['operatorSocket'],self.c['publicSocket'])
        self.finish_worker(self.root/'grain-spec.json',Path(request['runtimeRoot']))

    def worker_birth(self):
        # The native installer retains the exact birth spec. Native create
        # resolves any signed attempt by lookup before it can author a new one.
        self.keyroot=self.sockets/'provider'
        self.finish_worker(self.root/'grain-spec.json',Path(read(self.root/'worker-prepare.json')['runtimeRoot']))

    def finish_worker(self,source,runtime):
        home=Path(self.layout['controllerHome'])
        brokerconfig=self.keyroot/'broker.json';keysocket=self.keyroot/'keys.sock';keyclient=runtime/'keys-client.json'
        self.controller=True
        self.ensure_controller_public_proxy()
        successor=os.environ.get('J14_ORACLE_CONTROLLER_UPGRADE')
        if successor:
            release=Path(successor);metadata=release.stat();selected=read(release)
            if metadata.st_uid!=os.getuid() or metadata.st_mode&0o077 or release.is_symlink():
                raise ValueError('controller runtime successor must be private operator custody')
            if (set(selected)!={'runtime','sha256','sourceCommit'} or not re.fullmatch('[0-9a-f]{40}',selected['sourceCommit'])
                    or sha(selected['runtime'])!=selected['sha256']):
                raise ValueError('controller runtime successor pins differ')
            self.fixed('controller-stop')
            receipt=self.fixed('controller-runtime-upgrade',selected['runtime'])
            if read(receipt)['runtimeSha256']!=selected['sha256']:raise ValueError('installed controller successor differs')
            self.c['controllerRuntimeSuccessor']={**selected,'release':str(release),'releaseSha256':sha(release),'receipt':str(receipt)}
        self.fixed('controller-worker-birth',source)
        self.controller_run('grain-runtime',['create',home/'requests/create.json'])
        self.fixed('controller-worker-publish')
        self.c['controllerHostConfigExport']=str(self.fixed('controller-host-config-export'))
        self.controller_config()
        self.spawn('keys',[self.bins/'mini-keys','serve','--config',brokerconfig]);self.wait_socket(keysocket)
        self.run('provider-socket-acl',['setfacl','-m',f"u:{self.layout['controllerUid']}:rw-",keysocket])
        self.set_provider_keys(keyclient)

    def controller_config(self):
        exported=self.fixed('controller-config-export');self.c['controllerConfig']=str(exported)
        return read(exported)

    def room(self):
        home=Path(self.layout['controllerHome']);grain=Path(self.c['controllerRoot'])
        room=read(self.workspaces/'alice/refs/lab.json')
        registration=self.controller_run('mini',['hermes-handoff','--action','registration','--dir',grain/'state/resource-workspace',
            '--task',self.task('controller'),'--room-cell',room['target'],'--inbox',home/'requests/inbox','--socket',self.c['publicSocket']])
        registry=self.controller_run('mini',['hermes-handoff','--action','registry','--registrations',home/'requests/registrations',
            '--socket',self.c['publicSocket']],files=[{'source':str(registration),'destination':'requests/registrations/'+self.task('controller')+'.json'}])
        if not read(registry)['residents']:raise ValueError('native registry found no eligible controller custody')
        (self.homes/'alice/hermes').mkdir(exist_ok=True);shutil.copyfile(registry,self.homes/'alice/hermes/registry.json')
        summoned=self.shell('alice','summon lab as librarian --budget 1000').read_text()
        match=re.search(r'hand-off in (.+)',summoned)
        if not match:raise ValueError('summon did not provide its sealed handoff directory')
        outbox=Path(match.group(1).strip());summon=read(outbox/'summon-lab.json')
        self.shell('alice','tariff lab set hermes/provider '+self.task('provider'))
        config=self.controller_config();config['toolTask']['room']['account']=summon['account']['name']
        update=self.root/'summoned-controller.json';write(update,config)
        self.fixed('controller-config',update);self.controller_config()
        dispatched=self.controller_run('mini',['hermes-handoff','--action','dispatch','--registration',home/'requests/registration.json',
            '--bundle',home/'requests/handoff.json','--socket',self.c['publicSocket']],files=[
                {'source':str(registration),'destination':'requests/registration.json'},
                {'source':str(outbox/'handoff.json'),'destination':'requests/handoff.json'}])
        self.inbox=read(dispatched)['inbox'];self.prompts=0

    def attachment_phase(self,contract,name,*extra):
        helper=REPO/'scripts/application-attachment.py'
        retained=Path(read(contract)['paths']['outputDir'])/'attachment.json'
        if retained.exists():
            pins=read(retained);helper=Path(pins['files']['orchestrator'])
            if not helper.is_absolute() or sha(helper)!=pins['sha256']['orchestrator']:
                raise ValueError('retained attachment orchestrator differs')
        return self.run('attachment-'+name,['python3',helper,contract,name,*extra],timeout=3600)

    def attach(self):
        grain=Path(self.c['controllerRoot'])
        self.controller_run('grain-runtime',['hermes-room','resident-init',grain/'controller.json',grain/'state/resident'])
        contract=self.root/'attachment-input.json';write(contract,inputs.attachment(self.c));self.contract=contract
        # The CLI returns its retained result path, whose JSON is the phase result.
        def result(path):return read(path.read_text().strip())
        prepared=result(self.attachment_phase(contract,'prepare-config'))
        self.fixed('controller-config',prepared['stage'])
        exported=self.controller_config()
        # Preserve the original exported filename selected in the pinned input;
        # the attachment permits only its exact prepared/activated successor.
        shutil.copyfile(self.c['controllerConfig'],read(contract)['paths']['controllerConfig'])
        self.finish_attachment(contract,prepared)

    def start_controller(self):
        self.fixed('controller-start')
        readiness=read(self.fixed('controller-prepare-idle'))
        if (readiness.get('type')!='mini-grain-idle-readiness-v1' or readiness.get('ready') is not True
                or readiness.get('task')!=self.task('controller')):
            raise ValueError('native idle readiness did not identify this controller')

    def finish_attachment(self,contract,prepared):
        """Continue from an installed prepared config without repeating its delegations."""
        self.contract=contract
        self.start_controller()
        request=secrets.token_hex(16);args=self.root/'session-arguments.json';write(args,prepared['nextTool']['arguments'])
        write(self.root/'session-request.json',{'requestId':request,'tool':prepared['nextTool']['name'],'arguments':str(args)})
        session=self.fixed('controller-tool',request,prepared['nextTool']['name'],args)
        self.finish_session_attachment(contract,session,request)

    def finish_session_attachment(self,contract,session,request):
        """Join the exact completed session, including explicit native recovery."""
        self.contract=contract
        def phase(name,*extra):return self.attachment_phase(contract,name,*extra)
        def result(path):return read(path.read_text().strip())
        value=read(session)
        if value.get('requestId')!=request:raise ValueError('session result belongs to another request')
        if (value.get('type')!='tool-complete' or value.get('isError') is not False
                or not isinstance(value.get('result'),dict) or value['result'].get('isError') is not False):
            raise ValueError('session tool not complete; retain request ID for native tool-result')
        retained=self.fixed('controller-tool-result',request)
        if session.read_bytes()!=retained.read_bytes():raise ValueError('session retained result differs')
        self.fixed('controller-tool-ack',request)
        self.fixed('controller-stop')
        phase('issue-grant','--input',session)
        layout=dict(self.layout,controllerHome=self.c['controllerRoot'])
        path=self.root/'attachment-layout.json';write(path,layout)
        phase('prepare-route','--input',path)
        self.profile=read(self.c['profileResult'])['profilePath']
        start=self.run('app-start',[self.bins/'spk-host','grain','start',self.profile,'9890001'],timeout=2400)
        self.application_unit=read(start)['unit']
        activated=result(phase('activate','--input',start))
        self.enroll(activated['bundle'],'application')
        self.start_controller()
        self.application_unit=read(start)['unit']

    def enroll(self,bundle,mode):
        before=read(self.fixed('controller-journal'))
        canonical=json.dumps(before['binding'],sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()
        target=Path(bundle)/'controller.json'
        request=self.root/f'enrollment-{self.counter:04d}.json'
        write(request,{'protocol':'mini-controller-application-enrollment-v1','mode':mode,
            'expectedBindingSha256':hashlib.sha256(canonical).hexdigest(),'targetConfigSha256':sha(target),
            'residentState':str(Path(self.c['controllerRoot'])/'state/resident')})
        self.fixed('controller-config',bundle)
        result=read(self.fixed('controller-enroll',request))
        after=read(self.fixed('controller-journal'))
        if result.get('status')!='enrolled' or {k:v for k,v in before.items() if k!='binding'}!={k:v for k,v in after.items() if k!='binding'}:
            raise ValueError('native enrollment did not preserve settled journal')
        self.controller_config()

    def resident(self,label,completed=None):
        home=Path(self.layout['controllerHome']);grain=Path(self.c['controllerRoot'])
        self.prompts=(self.prompts if completed is None else completed)+1
        # A resumed journey may reuse a test label, but its earlier source and
        # controller-side copy remain evidence. Name each invocation by the
        # retained command frontier instead of overwriting that evidence.
        name=f'resident-{label}-{self.counter+1:04d}.json'
        source=self.root/name;destination=f'requests/{name}'
        write(source,{'type':'mini-hermes-room-resident-v1','controller':str(grain/'controller.json'),'inbox':self.inbox,
            'state':str(grain/'state/resident'),'maxPrompts':self.prompts,'intervalSeconds':5})
        result=self.controller_run('grain-runtime',['hermes-room','resident',home/destination],files=[{'source':str(source),'destination':destination}])
        self.run('certify',[self.mini,'checkpoint','--action','certify','--workspace',self.c['sponsorWorkspace'],
            '--control',str(read(Path(self.c['world'])/'genesis.json')['factoryControllerCapability'])])
        return result

    def paid(self):
        result=read(self.run('paid-turns',[self.mini,'credit','--action','ledger','--dir',self.workspaces/'alice',
            '--account','lab-till','--topic','hermes']))
        return len([e for e in result['entries'] if e.get('subject')==self.subjects['hermes'] and e.get('amount')=='10'])

    def web(self,label,granted):
        p=self.spawn('web-'+label,[self.mini,'web','--dir',self.workspaces/'bob','--home',self.homes/'bob','--listen','127.0.0.1:0'])
        output=p.journey_stdout
        try:
            deadline=time.monotonic()+30;url=None
            while time.monotonic()<deadline:
                match=re.search(r'http://127\.0\.0\.1:[0-9]+/[0-9a-f]+/',output.read_text())
                if match:url=match.group(0);break
                if p.poll() is not None:break
                time.sleep(.1)
            if not url:raise ValueError('resident web face did not open')
            response=self.run('web-page-'+label,['curl','--fail','--silent','--show-error','--max-time','60',url+'room/lab/resident'])
            page=response.read_text();expected='true' if granted else 'false'
            if f'data-tool="oracle" data-granted="{expected}"' not in page:raise ValueError('browser resident grant view differs')
            if not granted and 'data-refusal="oracle-not-granted"' not in page:raise ValueError('browser did not explain the named refusal')
        finally:
            p.terminate();p.wait(timeout=30)

    def stop_qualified_application(self):
        """Retire the test application only after all paid answer rows settled."""
        self.fixed('controller-stop')
        journal=read(self.fixed('controller-journal'))
        fields=('applicationApiAttempt','dispatchAttempt','dispatchHold','dispatchPending',
                'foregroundAttempt','parentHold','toolHold','toolPending','pending','settlementDue',
                'providerAttempt','providerHold','providerPending','child','roomAttempt','workspaceAttempt')
        if any(journal.get(name) is not None for name in fields):
            raise ValueError('application teardown retains unsettled controller custody')
        receipt=self.run('app-stop',[self.bins/'spk-host','grain','stop',self.profile,'9890001'],timeout=2400)
        value=read(receipt)
        if (value.get('protocol')!='mini-spk-grain-stop-v1' or value.get('app')!='9890001'
                or value.get('unit')!=self.application_unit or value.get('activeState') not in ('inactive','failed')):
            raise ValueError('native application STOP did not identify the stopped test unit')
        return receipt

    @staticmethod
    def validate_refusal_resume(value,provider_lines):
        if (not isinstance(value,dict) or set(value)!={'askNumber','paidBefore'}
                or not isinstance(value['askNumber'],str) or not re.fullmatch('[1-9][0-9]*',value['askNumber'])
                or type(value['paidBefore']) is not int or value['paidBefore']<0 or provider_lines):
            raise ValueError('retained refusal continuation requires exact ask and no provider dispatch')

    @staticmethod
    def exported_state(exported,name):
        file=exported.get('files',{}).get(name)
        if file is None:return None
        raw=base64.b64decode(file['base64'],validate=True)
        if hashlib.sha256(raw).hexdigest()!=file['sha256']:
            raise ValueError('resident state export hash differs')
        return json.loads(raw)

    @staticmethod
    def completed_prompts(exported):
        state=Journey.exported_state(exported,'resident/resident.json')
        if state is None:return 0
        if state.get('pending') is not None or state.get('returnPending',False):
            raise ValueError('resident has retained completion custody; drain it before another probe')
        completed=state.get('completed')
        if type(completed) is not int or not 0<=completed<1000:
            raise ValueError('native resident completed count is invalid')
        return completed

    @staticmethod
    def retained_requests(exported):
        queue=Journey.exported_state(exported,'resident/requests.json')
        if queue is None:return []
        selected=queue.get('selected')
        if selected is not None and selected.get('started') is not None:
            raise ValueError('resident has a started retained request; settle its native custody before another probe')
        return ([selected] if selected is not None else [])+queue.get('pending',[])

    @staticmethod
    def unconsumed_asks(exported,rows,author,resident,question):
        queue=Journey.exported_state(exported,'resident/requests.json') or {}
        retained=([queue['selected']] if queue.get('selected') is not None else [])+queue.get('pending',[])
        terminal=[]
        for name in exported.get('files',{}):
            if not name.startswith('resident/request-') or not name.endswith('.json'):continue
            record=Journey.exported_state(exported,name)
            if record.get('type')=='mini-resident-request-outcome-v1' and record.get('status') in ('completed','refused','cancelled','failed-after-admission'):
                terminal.append(record.get('identity'))
        remaining=[]
        for row in rows:
            if not (row.get('author')==author and row.get('to')==resident and row.get('kind')=='say'
                    and question in row.get('text','')):continue
            identity={'binding':queue.get('binding'),'author':row.get('author'),'cell':row.get('cell'),'sequence':row.get('sequence')}
            if identity in terminal:continue
            if any(item.get('identity')==identity for item in retained):
                remaining.append(row);continue
            cursor=queue.get('cursors',{}).get(row.get('cell'),0)
            if type(row.get('sequence')) is not int or type(cursor) is not int:
                raise ValueError('native discovery cursor or signed source sequence is invalid')
            if row['sequence']<=cursor:
                raise ValueError('discovered request lacks retained or terminal native custody; inspect before another ask')
            remaining.append(row)
        return remaining

    @staticmethod
    def selected_ask(call,rows,author,resident,question):
        identity=call.get('selectedRequest',{});entry=call.get('selectedEntry',{})
        if (not isinstance(identity,dict) or not isinstance(entry,dict) or not isinstance(identity.get('binding'),dict)
                or identity.get('author')!=author or entry.get('to')!=resident
                or entry.get('kind')!='say' or question not in entry.get('text','')
                or any(identity.get(k)!=entry.get(k) for k in ('author','cell','sequence'))):
            raise ValueError('provider call lacks the exact native selected request')
        # n and height are presentation coordinates of distinct signed views.
        fields=('author','cell','sequence','text','to','kind')
        matches=[row for row in rows if all(row.get(k)==entry.get(k) for k in fields)]
        if len(matches)!=1:raise ValueError('native selected request does not join exactly one signed room entry')
        return matches[0]

    def probe(self,resume_refusal=None):
        question='Who wrote Leaves of Grass?';oraclelog=self.root/'provider.oracle.jsonl'
        prior_operation=None;asks=set()
        def transcript():
            path=self.shell('alice','tail --in lab --json -n 200')
            return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
        def turn(label,answer,resumed=None):
            nonlocal prior_operation
            old_lines=oraclelog.read_text().splitlines() if oraclelog.exists() else []
            exported=read(self.fixed('controller-export'))
            queued=self.retained_requests(exported)
            completed=self.completed_prompts(exported)
            before_rows=transcript()
            if resumed is None:
                before=self.paid()
                if not queued and not self.unconsumed_asks(exported,before_rows,self.subjects['bob'],self.subjects['hermes'],question):
                    self.shell('bob','ask lab oracle: '+question)
            else:
                self.validate_refusal_resume(resumed,old_lines)
                before=resumed['paidBefore']
            rows=transcript()
            selected=[r for r in rows if r.get('author')==self.subjects['bob'] and r.get('to')==self.subjects['hermes']
                      and question in r.get('text','')]
            if not selected:raise ValueError('selected room ask absent from signed history')
            if resumed is not None and not any(str(row['n'])==resumed['askNumber'] for row in selected):
                raise ValueError('retained refusal ask absent from signed room history')
            self.resident(label,completed)
            all_lines=oraclelog.read_text().splitlines()
            if all_lines[:len(old_lines)]!=old_lines:raise ValueError('provider log prefix changed')
            new_lines=all_lines[len(old_lines):]
            phase_log=self.root/f'oracle-{label}-{self.counter:04d}.jsonl';phase_log.write_text('\n'.join(new_lines)+'\n')
            calls=[json.loads(line) for line in new_lines if json.loads(line).get('id')=='or-call']
            if not calls or calls[-1].get('question')!=question:raise ValueError('fresh provider call did not name selected question')
            if any(call.get('selectedRequest')!=calls[-1].get('selectedRequest') for call in calls):
                raise ValueError('one resident invocation consumed multiple native source requests')
            chosen=self.selected_ask(calls[-1],transcript(),self.subjects['bob'],self.subjects['hermes'],question)
            selected_identity=(chosen['author'],chosen['cell'],chosen['sequence'])
            if selected_identity in asks:raise ValueError('native resident selected an already qualified request')
            asks.add(selected_identity)
            if queued and not any(item.get('identity')==calls[-1]['selectedRequest'] for item in queued):
                raise ValueError('provider selection differs from retained native request custody')
            expected='Whitman' if answer else 'oracle-not-granted'
            replies=[r for r in transcript() if r.get('author')==self.subjects['hermes'] and r.get('to')==self.subjects['bob']
                     and r.get('reCell')==chosen['cell']
                     and r.get('reSequence')==chosen['sequence'] and r.get('kind')=='say']
            if not any(expected in r.get('text','') for r in replies):raise ValueError('fresh room reply lacks expected Oracle outcome')
            if self.paid()<=before:raise ValueError('fresh Oracle room reply was not a paid turn')
            if not answer:
                if expected not in calls[-1].get('content',''):raise ValueError('Oracle refusal did not name missing room grant')
                return
            journal=self.fixed('controller-journal')
            path=self.run('answer-evidence-'+label,['python3',HERE/'j14-oracle-evidence.py',phase_log,journal,
                '--route','oracle-app','--expected',expected,'--question',question])
            operation=read(path)['operationId']
            if operation==prior_operation:raise ValueError('fresh turn reused an earlier native operation')
            prior_operation=operation
            return path
        turn('refused-resumed' if resume_refusal is not None else 'refused',False,resume_refusal);self.web('refused',False)
        self.shell('alice','tariff lab set hermes/tools 8');self.web('granted',True)
        evidence=turn('answered',True)
        self.fixed('controller-stop');self.start_controller()
        turn('controller-restarted',True)
        stopped=self.stop_qualified_application()
        write(self.root/'result.json',{'protocol':'mini-j14-oracle-result-v1','passed':True,
            'store':self.broker['store'],'controllerUid':self.layout['controllerUid'],'operatorUid':os.getuid(),
            'rows':['same-store-provision','native-grain-create-dispatch','room-refusal','resident-page-grant-state',
                    'native-answer-and-settlement','paid-room-reply','controller-restart-answer'],
            'residentPageEvidence':'HTTP/HTML; rendered browser is covered separately',
            'answerEvidence':str(evidence),'applicationUnit':self.application_unit,'applicationStop':str(stopped),
            'applicationRestart':'covered by the separate shared-data lifetime recovery journey'})
        table=self.root/'j14.tsv';table.write_text('step\tverdict\n'+''.join(row+'\tok\n' for row in read(self.root/'result.json')['rows']))
        print(table)


def main():
    resume=os.environ.get('J14_ORACLE_RESUME_WORLD')=='1'
    selected=os.environ.get('J14_ORACLE_RESUME_CHECKPOINT')
    checkpoint=Path(selected) if selected else None
    generic=checkpoint is not None and read(checkpoint).get('protocol') in ('mini-j14-checkpoint-v1','mini-j14-worker-preparation-checkpoint-v1','mini-j14-worker-birth-checkpoint-v1')
    j=Journey.from_checkpoint(checkpoint) if generic else Journey.resume_transport(checkpoint) if checkpoint else Journey.resume_transport() if resume else Journey()
    phase='transport';start_counter=j.counter
    try:
        if generic:
            j.prepare_operator_relocation()
            j.restore_services()
            j.finish_operator_relocation()
        elif checkpoint:j.restart_transport()
        phases=([j.resume_phase,*PHASES[PHASES.index('room'):]] if generic and j.resume_phase in ('worker_preparation','worker_birth')
                else PHASES[PHASES.index(j.resume_phase):] if generic else PHASES[1:] if checkpoint else PHASES)
        for phase in phases:
            if phase=='worker':j.await_worker_release()
            (j.resume_world if resume and phase=='world' else getattr(j,phase))()
            write(j.root/('context-after-'+phase+'.json'),j.c)
            next_index=PHASES.index('worker' if phase in ('worker_preparation','worker_birth') else phase)+1
            if next_index<len(PHASES) and PHASES[next_index] in RESUMABLE:j.checkpoint(PHASES[next_index])
    except Exception as error:
        write(j.root/(f'failure-checkpoint-{start_counter:04d}.json' if checkpoint else 'failure-transport-continuation.json' if resume else 'failure.json'),{'phase':phase,'error':str(error),'passed':False,'lastCommand':j.counter,
            'recovery':'Inspect retained exact native attempts; do not repeat an uncertain submission as new work.'})
        raise
    finally:j.cleanup()

if __name__=='__main__':
    if len(sys.argv)==4 and sys.argv[1]=='adopt-checkpoint-source':
        print(Journey.adopt_checkpoint_source(Path(sys.argv[2]),sys.argv[3]))
    else:main()
