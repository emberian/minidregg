#!/usr/bin/env python3
"""Prepare supplied source tasks once; unknown native effects require exact recovery."""
import argparse, fcntl, hashlib, json, os, stat, subprocess, time
from pathlib import Path

def require(ok, message):
    if not ok: raise ValueError(message)
def digest(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path): return json.loads(Path(path).read_text())
def save(path, value):
    path=Path(path); temporary=path.with_suffix(path.suffix+'.pending')
    with open(temporary,'x') as stream:
        json.dump(value,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
    os.chmod(temporary,0o600);os.replace(temporary,path)
    fd=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY)
    try: os.fsync(fd)
    finally: os.close(fd)
def classify(role, grain):
    names=('generation','status','remaining','reserved')
    require(all(type(grain.get(k)) is str and grain[k].isdecimal() and str(int(grain[k]))==grain[k] for k in names),'noncanonical native task state')
    generation,status,reserved=(grain[k] for k in ('generation','status','reserved'))
    if (generation,status,reserved)==('0','0','0'): return 'attach'
    if role=='parent':
        if (generation,status,reserved)==('1','2','0'): return 'reserve'
        if generation=='1' and status in ('3','4') and reserved=='1': return 'ready'
    elif role=='tool':
        if generation=='1' and status in ('1','2') and reserved=='0': return 'ready'
    raise ValueError('task state is held or outside the fresh preparation contract; retain exact attempts')

def exclusive_root_lock(root):
    fd=os.open(Path(root)/'operation.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600)
    try:
        st=os.fstat(fd)
        require(stat.S_ISREG(st.st_mode) and st.st_uid==os.getuid() and st.st_mode&0o077==0,'private regular operation lock required')
        fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BaseException:
        os.close(fd)
        raise
    return fd

class Ready:
    def __init__(self, inputs, root):
        require(os.getuid()!=0,'run as the declared Store operator')
        self.input=Path(inputs).resolve();self.ctx=read(self.input);self.root=Path(root)
        self.manifest=read(self.ctx['manifest'])
        require(digest(self.ctx['manifest'])==self.ctx['identity']['manifestSha256'],'manifest bytes differ')
        require(digest(self.ctx['config'])==self.ctx['identity']['configSha256'],'configuration bytes differ')
        for role in ('mini','host'):
            require(digest(self.manifest[role])==self.manifest['sha256'][role],'native role bytes differ '+role)
        require(not self.root.is_symlink(),'evidence root must not be a symlink')
        contract={'protocol':'mini-platform-task-readiness-input-v1','platformInputs':str(self.input),'platformInputsSha256':digest(self.input),'identity':self.ctx['identity'],'helperSha256':digest(__file__)}
        if not self.root.exists(): self.root.mkdir(mode=0o700)
        st=self.root.stat();require(st.st_uid==os.getuid() and st.st_mode&0o077==0,'private evidence owner required')
        self.lock_fd=exclusive_root_lock(self.root)
        if (self.root/'contract.json').exists():
            require(read(self.root/'contract.json')==contract,'retained preparation contract changed')
        else:
            require(not any(p.name!='operation.lock' for p in self.root.iterdir()),'unbound evidence root is not empty')
            save(self.root/'contract.json',contract)
        # A retained effect without a confirmed decision fences all fresh work.
        for attempt in self.root.glob('*-attempt'):
            require((attempt/'outcome.json').is_file() and read(attempt/'outcome.json').get('type')=='confirmed','unresolved preparation attempt; use exact native retry: '+str(attempt))
        self.serial=len(list(self.root.glob('query-*')))
        self.nonce=int(time.time_ns()%((1<<52)-1000000))+1
    def invoke(self,label,words):
        save(self.root/(label+'.command.json'),[str(x) for x in words])
        before=time.monotonic()
        try: result=subprocess.run([str(x) for x in words],capture_output=True,text=True,timeout=600)
        except subprocess.TimeoutExpired as error:
            save(self.root/(label+'.timeout.json'),{'seconds':600,'retry':'none; retain exact native attempt'})
            raise RuntimeError('native timeout; retain exact attempt '+label) from error
        (self.root/(label+'.stdout')).write_text(result.stdout);(self.root/(label+'.stderr')).write_text(result.stderr)
        save(self.root/(label+'.status.json'),{'returncode':result.returncode,'seconds':time.monotonic()-before})
        require(result.returncode==0,'native command refused/uncertain; retain exact attempt '+label)
        return result.stdout
    def query(self,role):
        self.serial+=1;self.nonce+=2;label='query-'+str(self.serial).zfill(4)+'-'+role
        authority=self.ctx['authority'][role];custody=self.ctx['custody']['owner' if role=='parent' else 'management']
        capability=authority['ownerCapability'] if role=='parent' else authority['managementCapability']
        request={'subject':custody['subject'],'nonce':str(self.nonce),'purpose':{'type':'query','kind':'object','target':authority['task'],'view':'resource'},'grants':[{'kind':'object','target':authority['task'],'capability':capability}]}
        source=self.root/(label+'-intent.json');save(source,request);directory=self.root/label
        m=self.manifest
        self.invoke(label,[m['mini'],'query','--host',m['host'],'--config',self.ctx['config'],'--socket',self.ctx['publicSocket'],'--intent',source,'--key',custody['seed'],'--view','resource','--dir',directory])
        view=read(directory/'view.json');cell=view['cell']
        require(str(cell.get('id',authority['task']))==authority['task'],'native task target differs')
        return authority,custody,capability,cell
    def prepare(self,role):
        actions=[]
        for _ in range(3):
            authority,custody,capability,cell=self.query(role);action=classify(role,cell['grain'])
            if action=='ready': return {'task':authority['task'],'source':cell,'actions':actions}
            label=role+'-'+action;attempt=self.root/(label+'-attempt')
            require(not attempt.exists(),'confirmed preparation did not produce expected state; refuse fresh effect')
            self.nonce+=2;operation={'type':'attach','soft':True} if action=='attach' else {'type':'reserve','amount':'1'}
            request={'grain':{'task':authority['task'],'subject':custody['subject'],'capability':capability,'observeCapability':capability,'schemaVersion':'1','expectedTargetRoot':cell['root'],'context':{'operationId':str(self.nonce),'payload':'supplied Store task readiness'},'before':{k:cell['grain'][k] for k in ('generation','status','remaining','reserved')},'operation':operation,'publications':[]},'grants':[{'kind':'object','target':authority['task'],'capability':capability}],'intentNonce':str(self.nonce)}
            source=self.root/(label+'-intent.json');require(not source.exists(),'retained preparation intent without terminal receipt; recover it before new work');save(source,request);m=self.manifest
            self.invoke(label,[m['mini'],'submit','--host',m['host'],'--config',self.ctx['config'],'--socket',self.ctx['publicSocket'],'--intent',source,'--intent-kind','grain-intent','--key',custody['seed'],'--dir',attempt])
            require(read(attempt/'outcome.json').get('type')=='confirmed','effect is not confirmed; exact retry required')
            actions.append({'action':action,'intent':str(source),'intentSha256':digest(source),'attempt':str(attempt),'outcomeSha256':digest(attempt/'outcome.json')})
        raise ValueError('bounded task readiness exhausted')
    def run(self):
        result={'protocol':'mini-platform-task-readiness-result-v1','identity':self.ctx['identity'],'parent':self.prepare('parent'),'tool':self.prepare('tool'),'confirmed':True}
        output=self.root/('result.json' if not (self.root/'result.json').exists() else 'recheck-'+str(time.time_ns())+'.json');save(output,result);print(json.dumps(result))

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--platform-inputs',required=True);parser.add_argument('--evidence',required=True);a=parser.parse_args()
    os.umask(0o077);ready=Ready(a.platform_inputs,a.evidence)
    try: ready.run()
    finally: os.close(ready.lock_fd)
if __name__=='__main__':main()
