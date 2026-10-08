#!/usr/bin/env python3
"""Materialize a coherent joined candidate and run only its isolated fixture.

Root orchestration runs Mini/traffic as the staged nologin operator. Existing
services are never stopped, replaced, or adopted. No compiler/provider calls.
"""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import pwd
import re
import shutil
import socket
import stat
import subprocess
import tarfile
import time

ROLES={'host':'minidregg-host','mini':'mini','store':'minidregg-link-sqlite-store',
       'verifier':'minidregg-credential-signature-verifier','spkHost':'spk-host','browserProxy':'spk-browser-proxy'}


def require(ok,message):
    if not ok: raise RuntimeError(message)


def load(path): return json.loads(Path(path).read_text())


def sha(path):
    with open(path,'rb') as source: return hashlib.file_digest(source,'sha256').hexdigest()


def save(path,value,mode=0o600):
    with open(path,'x') as out: json.dump(value,out,indent=2);out.write('\n');out.flush();os.fsync(out.fileno())
    os.chmod(path,mode)
    fd=os.open(Path(path).parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    try: os.fsync(fd)
    finally: os.close(fd)


def directory(path,mode=0o755):
    path.mkdir(mode=mode);path.chmod(mode)


def root_file(path):
    path=Path(path)
    require(path.is_absolute() and '..' not in path.parts,'canonical absolute path required')
    for part in [path,*path.parents]:
        info=part.lstat()
        require(not stat.S_ISLNK(info.st_mode) and info.st_uid==0 and not info.st_mode & 0o022,'root custody path required')
    require(path.is_file(),'root regular file required')
    return path


def operator_custody(path,under,uid,kind):
    path,under=Path(path),Path(under)
    require(path.is_absolute() and '..' not in path.parts and path.is_relative_to(under) and path!=under,
            'operator path escapes pinned root')
    for part in [path,*path.parents]:
        info=part.lstat()
        require(not stat.S_ISLNK(info.st_mode) and info.st_uid in (0,uid) and not info.st_mode & 0o022,
                'operator path custody differs')
        if part==under: break
    info=path.lstat()
    require(info.st_uid==uid and not info.st_mode & 0o077 and
            (stat.S_ISDIR(info.st_mode) if kind=='directory' else stat.S_ISREG(info.st_mode)),
            'private operator '+kind+' required')
    return path


def fixture_coordinates(f,expected,plan):
    require(f.get('schema')=='spk-ws-continuity-fixture-v1' and f.get('root')==expected['root']
            and f.get('grainsRoot')==expected['grainsRoot'] and f.get('app')==plan['app']
            and f.get('brokerSocket')==expected['brokerSocket'],'fixture coordinate pin differs')
    require(isinstance(f.get('generation'),str) and re.fullmatch('[1-9][0-9]*',f['generation']) is not None,'generation pin invalid')
    state=Path(f['state']);grains=Path(expected['grainsRoot'])
    require(state.name=='host' and state.parent.parent==grains and re.fullmatch('[0-9a-f]{16}',state.parent.name) is not None
            and f.get('profilePath')==str(state/'grain-host.json'),'fixture native state path differs')
    return state


def candidate_archive(manifest,expected):
    require(manifest['sourceCommit']==expected,'candidate source pin differs')
    if manifest.get('sourceArchive'):
        path=Path(manifest['sourceArchive'])
        require(path.is_absolute() and path.is_file() and not path.is_symlink() and path.stat().st_size<=128*1024*1024,'candidate source archive custody differs')
        archive=path.read_bytes()
        require(hashlib.sha256(archive).hexdigest()==manifest['sourceArchiveSha256'],'candidate source archive pin differs')
        return archive
    source=Path(manifest['sourcePath'])
    actual=subprocess.check_output(['git','-C',str(source),'rev-parse',expected+'^{commit}'],text=True).strip()
    require(actual==expected,'source commit not present in candidate repository')
    return subprocess.check_output(['git','-C',str(source),'archive',expected,'scripts'])


def materialize(plan_path,manifest_path,expected):
    plan=load(root_file(plan_path)); root=Path(plan['root'])
    require(plan['state']=='dependencies-staged-no-candidate-no-services','not a fresh dependency plan')
    require(re.fullmatch('[0-9a-f]{40}',expected) is not None,'exact source commit required')
    original=Path(manifest_path).read_bytes(); manifest=json.loads(original)
    require(manifest['sourceCommit']==expected,'candidate source pin differs')
    require('integration-qualification' in manifest.get('spkHostFeatures',[]),'separately pinned qualification image required')
    for role in ROLES:
        path=Path(manifest[role])
        require(path.is_absolute() and path.is_file() and not path.is_symlink() and os.access(path,os.X_OK)
                and sha(path)==manifest['sha256'][role],'candidate artifact/hash missing: '+role)
    for asset in plan['assets'].values(): require(sha(root_file(asset['path']))==asset['sha256'],'dependency changed')
    account=pwd.getpwnam(plan['operator']['name'])
    require((account.pw_uid,account.pw_gid)==(plan['operator']['uid'],plan['operator']['gid']),'operator identity changed')
    archive=candidate_archive(manifest,expected)
    capsule=root/('candidate-'+expected[:12])
    require(not capsule.exists() and not capsule.is_symlink(),'candidate capsule already staged; inspect, never overwrite')
    directory(capsule);directory(capsule/'bin');directory(capsule/'source')
    with open(capsule/'original-manifest.json','xb') as out: out.write(original)
    os.chmod(capsule/'original-manifest.json',0o444)
    staged=dict(manifest)
    for role,name in ROLES.items():
        target=capsule/'bin'/name
        with open(manifest[role],'rb') as src,open(target,'xb') as out: shutil.copyfileobj(src,out)
        target.chmod(0o755)
        require(sha(target)==manifest['sha256'][role],'artifact changed during copy')
        staged[role]=str(target)
    # Extract only tracked scripts from the exact commit. No symlink traversal,
    # untracked output, or reinterpretation of the original source revision.
    script_hashes={}
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        for item in tar:
            parts=Path(item.name).parts
            if not parts or parts[0]!='scripts': continue
            require(parts and parts[0]=='scripts' and '..' not in parts and not Path(item.name).is_absolute(), 'unsafe source archive path')
            target=capsule/'source'/item.name
            if item.isdir(): directory(target)
            else:
                require(item.isfile(),'only regular tracked scripts may enter capsule')
                with tar.extractfile(item) as src,open(target,'xb') as out: shutil.copyfileobj(src,out)
                target.chmod(0o755 if item.mode & 0o111 else 0o644)
                script_hashes[item.name]=sha(target)
    scripts=capsule/'source/scripts/spk-platform'
    for name in ['ws-continuity-fixture.py','ws-continuity-journey.py','ws-continuity-supervision.py','ws-continuity-regressions.py','ws-continuity-launch.py']:
        require((scripts/name).is_file(),'candidate does not include joined runner: '+name)
    staged['originalManifest']=str(capsule/'original-manifest.json')
    staged['stagedScripts']=str(capsule/'source')
    save(capsule/'manifest.json',staged,0o644)
    save(capsule/'script-sha256.json',script_hashes,0o444)
    broker=dict(plan['brokerConfigTemplate'],spkHost=staged['spkHost'],spkHostSha256=staged['sha256']['spkHost'])
    require(broker['brokerSocket']==str(Path(plan['grainsRoot'])/'broker.sock'),'isolated explicit broker required')
    save(capsule/'broker.json',broker)
    package=plan['assets']['ethercalc.spk']
    fixture=dict(root=plan['fixtureRoot'],grainsRoot=plan['grainsRoot'],brokerSocket=broker['brokerSocket'],
        manifest=str(capsule/'manifest.json'),expectedSourceCommit=expected,spk=package['path'],spkSha256=package['sha256'],
        appPrefix=plan['appPrefix'],leaseSeconds=120,enableHotRegrant=True,enableSameIngressRace=True,enableSealRecovery=True,
        stopAfterJourney=False,delegateHosts={'a':'a.localhost:18447','b':'b.localhost:18448'})
    # Root driver installs the override directly; no operator sudo rule needed.
    save(capsule/'fixture-input.json',fixture,0o644)
    ready=dict(protocol='mini-spk-joined-ready-v1',setupPlan=str(plan_path),setupPlanSha256=sha(plan_path),capsule=str(capsule),
        candidateSourceCommit=expected,manifest=str(capsule/'manifest.json'),manifestSha256=sha(capsule/'manifest.json'),
        originalManifestSha256=hashlib.sha256(original).hexdigest(),scripts=str(scripts),scriptHashes=str(capsule/'script-sha256.json'),
        scriptHashesSha256=sha(capsule/'script-sha256.json'),brokerConfig=str(capsule/'broker.json'),brokerConfigSha256=sha(capsule/'broker.json'),
        fixtureInput=str(capsule/'fixture-input.json'),fixtureInputSha256=sha(capsule/'fixture-input.json'))
    save(capsule/'ready.json',ready,0o444)
    return {'ready':str(capsule/'ready.json'),'staged':True,'launched':False}


class Driver:
    def __init__(self,ready_path):
        self.ready=load(root_file(ready_path)); r=self.ready
        require(r['protocol']=='mini-spk-joined-ready-v1','unknown ready protocol')
        for path_key,hash_key in [('setupPlan','setupPlanSha256'),('manifest','manifestSha256'),('brokerConfig','brokerConfigSha256'),
                                  ('fixtureInput','fixtureInputSha256'),('scriptHashes','scriptHashesSha256')]:
            require(sha(root_file(r[path_key]))==r[hash_key],'staged pin changed: '+path_key)
        self.plan=load(r['setupPlan']); self.manifest=load(r['manifest']); self.broker=load(r['brokerConfig']); self.input=load(r['fixtureInput'])
        require(not self.plan.get('receivingMode'),'same-world plan supports materialize only; use same-store helpers')
        self.root=Path(self.plan['root']); self.capsule=Path(r['capsule']); self.scripts=Path(r['scripts'])
        for role in ROLES: require(sha(root_file(self.manifest[role]))==self.manifest['sha256'][role],'staged executable changed')
        for name,digest in load(r['scriptHashes']).items(): require(sha(root_file(self.capsule/'source'/name))==digest,'staged source changed')
        self.operator=self.plan['operator']['name']; self.fixture=Path(self.input['root'])/'fixture.json'
        self.log=self.capsule/('driver-log-'+str(time.time_ns()));directory(self.log,0o700)
        self.counter=0

    def run_command(self,args,operator=False,okay=True,timeout=14400):
        if operator: args=['/usr/sbin/runuser','-u',self.operator,'--',*args]
        self.counter+=1; prefix=self.log/str(self.counter)
        save(str(prefix)+'.argv.json',[str(x) for x in args])
        started=time.monotonic(); metadata=dict(exit=None,timedOut=False,startedMonotonic=started)
        try:
            with open(str(prefix)+'.stdout','xb') as out,open(str(prefix)+'.stderr','xb') as err:
                p=subprocess.run([str(x) for x in args],stdout=out,stderr=err,timeout=timeout)
            metadata['exit']=p.returncode
            require(not okay or p.returncode==0,'command failed; inspect '+str(prefix)+'.stderr')
            return p.returncode,Path(str(prefix)+'.stdout')
        except BaseException as error:
            metadata.update(timedOut=isinstance(error,subprocess.TimeoutExpired),errorType=type(error).__name__)
            raise
        finally:
            ended=time.monotonic();metadata.update(endedMonotonic=ended,elapsedSeconds=ended-started)
            save(str(prefix)+'.exit.json',metadata)

    def properties(self,unit):
        rc,out=self.run_command(['/usr/bin/systemctl','show',unit,'--property=LoadState,ActiveState,OnFailure,Restart,ExecStart'],okay=False,timeout=30)
        properties=dict(line.split('=',1) for line in out.read_text().splitlines() if '=' in line)
        require(rc==0 or properties.get('LoadState')=='not-found','systemd unit inspection failed')
        return properties

    def new_service(self,unit,args,user=None,group=None):
        require(self.properties(unit).get('LoadState')=='not-found','unit name already exists; no replacement: '+unit)
        command=['/usr/bin/systemd-run','--unit='+unit,'--property=UMask=0077','--property=Type=exec']
        if user: command+=['--uid='+user,'--gid='+group]
        self.run_command([*command,*args],timeout=30)

    def checked_fixture(self):
        uid=self.plan['operator']['uid']
        operator_custody(self.fixture,Path(self.input['root']),uid,'file')
        f=load(self.fixture)
        state=fixture_coordinates(f,self.input,self.plan)
        operator_custody(state,Path(self.input['grainsRoot']),uid,'directory')
        profile=load(operator_custody(state/'grain-host.json',state,uid,'file'))
        require(profile.get('stateRoot')==str(state) and profile.get('grainsRoot')==self.input['grainsRoot']
                and profile.get('brokerSocket')==self.input['brokerSocket'],'native profile pin differs')
        _,name=self.run_command([self.manifest['spkHost'],'grain','unit-name',state.parent.name,f['app'],str(f['generation'])],timeout=30)
        unit=load(name)['unit']
        tag=root_file(Path(self.input['grainsRoot'])/'broker/units'/unit)
        require(tag.read_text()==state.parent.name+'\n','root unit custody tag differs')
        return f

    def override_args(self):
        f=self.checked_fixture()
        resident=Path(f['state'])/f'apps/{f["app"]}/g{f["generation"]}/resident.json'
        config=load(resident)
        _,name=self.run_command([self.manifest['spkHost'],'grain','unit-name',Path(f['state']).parent.name,f['app'],str(f['generation'])],timeout=30)
        require(f['app']==self.plan['app'] and config['unit']==load(name)['unit'],'source incarnation differs')
        return ['--fixture',str(self.fixture),'--expected-app',f['app'],'--expected-unit',config['unit'],
                '--expected-resident-sha256',sha(resident),'--broker-config',self.ready['brokerConfig'],
                '--broker-config-sha256',self.ready['brokerConfigSha256']]

    def restore(self):
        record=self.capsule/'override-request.json'
        if record.exists():
            args=load(root_file(record))['arguments']
            self.run_command(['/usr/bin/python3',str(self.scripts/'ws-continuity-supervision.py'),'restore',*args],timeout=60)
        return {'supervisionRestoreRequested':record.exists(),'evidence':str(self.log)}

    def check_current_policy(self):
        f=self.checked_fixture()
        config=load(Path(f['state'])/f'apps/{f["app"]}/g{f["generation"]}/resident.json')
        current=self.properties(config['unit'])
        expected=self.broker['unitPrefix']+'-spk-supervisor@'+config['store']+'-'+f['app']+'.service'
        require(current.get('OnFailure')==expected and current.get('Restart')=='no','current generation did not retain native supervision policy')
        save(self.log/'current-generation-policy.json',dict(unit=config['unit'],generation=f['generation'],properties=current))

    def browser(self):
        f=self.checked_fixture(); access={}
        uid=self.plan["operator"]["uid"]; state=Path(f["state"])
        for label,port in [('a',18447),('b',18448)]:
            d=f['delegates'][label]; token=Path(d['endpoint']['token']); route=token.parent; host=label+'.localhost'
            require(route.parent==state/f'apps/{f["app"]}/routes' and token.name=='browser.token', 'browser route escapes exact app routes')
            operator_custody(route,state,uid,'directory');operator_custody(token,state,uid,'file')
            operator_custody(route/'custodian.json',state,uid,'file')
            require(d['endpoint']['unix_socket']==str(route/'http.sock'),'browser socket path differs')
            require(d['endpoint']['host']==f'{host}:{port}' and not d.get('revoked',False),'current browser route identity differs')
            for name in ('tls.crt','tls.key'): require(not (route/name).exists() and not (route/name).is_symlink(),'TLS artifact already exists')
            # Loopback ports have not been reserved by some other service.
            with socket.socket(socket.AF_INET,socket.SOCK_STREAM) as probe: probe.bind(('127.0.0.1',port))
            self.run_command(['/usr/bin/openssl','req','-x509','-newkey','rsa:2048','-nodes','-days','2',
                '-subj','/CN='+host,'-addext','subjectAltName=DNS:'+host,'-keyout',str(route/'tls.key'),'-out',str(route/'tls.crt')],operator=True,timeout=60)
            # Mode changes execute only with operator authority; root never
            # follows a mutable operator path for chmod/chown.
            self.run_command(['/usr/bin/chmod','600',str(route/'tls.crt'),str(route/'tls.key')],operator=True,timeout=30)
            for name in ('tls.crt','tls.key'): operator_custody(route/name,state,uid,'file')
            unit=self.broker['unitPrefix']+'-browser-'+label+'.service'
            self.new_service(unit,[self.manifest['browserProxy'],str(route),str(port)],self.operator,self.operator)
            access[label]=dict(subject=d['subject'],session=d['session'],origin=f'https://{host}:{port}',
                tokenFile=d['endpoint']['token'],certificateFile=str(route/'tls.crt'),unit=unit)
        destination=Path(self.input['root'])/'browser-access.json'
        value=dict(protocol='mini-spk-browser-access-v1',app=f['app'],generation=f['generation'],delegates=access,
             browserStatus='pending actual browser edit, sharing/access change and persistence qualification')
        writer="import os,sys; os.umask(0o077); fd=os.open(sys.argv[1],os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600); f=os.fdopen(fd,'w'); f.write(sys.argv[2]+'\\n'); f.flush(); os.fsync(f.fileno()); f.close()"
        self.run_command(['/usr/bin/python3','-c',writer,str(destination),json.dumps(value)],operator=True,timeout=30)
        operator_custody(destination,Path(self.input['root']),uid,'file')
        return str(destination)

    def run(self):
        marker=self.capsule/'run-started.json'
        save(marker,{'startedAtUnix':time.time(),'log':str(self.log),'ready':self.ready})
        require(not Path(self.input['root']).exists(),'fresh operator fixture root required')
        broker_socket=Path(self.broker['brokerSocket'])
        require(not broker_socket.exists() and not broker_socket.is_symlink(),'isolated broker endpoint already exists')
        self.new_service(self.broker['unitPrefix']+'-broker.service',[self.manifest['spkHost'],'broker-serve',self.ready['brokerConfig']])
        deadline=time.monotonic()+15
        while not broker_socket.is_socket():
            require(time.monotonic()<deadline,'isolated broker did not bind; inspect its own unit');time.sleep(.1)
        require(broker_socket.lstat().st_uid==0,'broker endpoint is not root-owned')
        # Native init-store authenticates the actual selected broker identity.
        self.run_command(['/usr/bin/python3',str(self.scripts/'ws-continuity-fixture.py'),'prepare',self.ready['fixtureInput']],operator=True)
        args=self.override_args()
        save(self.capsule/'override-request.json',{'protocol':'mini-spk-root-driver-override-v1','arguments':args})
        failure=None
        try:
            self.run_command(['/usr/bin/python3',str(self.scripts/'ws-continuity-supervision.py'),'install',*args],timeout=60)
            result=Path(self.input['root'])/'journey-result.json'
            self.run_command(['/usr/bin/python3',str(self.scripts/'ws-continuity-journey.py'),str(result.parent/'journey.json'),'--output',str(result)],operator=True)
            require(load(result).get('status')=='passed','native traffic journey failed')
        except BaseException as error:
            failure=error
            raise
        finally:
            try: self.restore()
            except Exception as cleanup:
                if failure is None: raise
                save(self.log/'restore-error.json',{'original':str(failure),'cleanup':str(cleanup),'recovery':'run recover-supervision with this same ready.json'})
        self.check_current_policy()
        access=self.browser()
        outcome=dict(nativeJourney='passed',browserQualification='pending',browserAccess=access,journeyResult=str(result),evidence=str(self.log))
        save(self.capsule/'run-result.json',outcome)
        return outcome


def main():
    os.umask(0o077)
    require(os.getuid()==0,'root controls capsule and exact fixture setup; Mini itself runs as the operator')
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='action',required=True)
    mat=sub.add_parser('materialize');mat.add_argument('setup_plan');mat.add_argument('manifest');mat.add_argument('--expected-source',required=True)
    for name in ('run','recover-supervision'):
        cmd=sub.add_parser(name);cmd.add_argument('ready')
    args=parser.parse_args()
    if args.action=='materialize': result=materialize(args.setup_plan,args.manifest,args.expected_source)
    else:
        driver=Driver(args.ready)
        result=driver.run() if args.action=='run' else driver.restore()
    print(json.dumps(result))


if __name__=='__main__': main()
