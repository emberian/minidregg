#!/usr/bin/env python3
"""Receiving orchestration and byte-transparent observers; no evaluator.

Every fixed link is admitted by the public cohort roster (`mini mix-live`
MCE2 enrollment): members and operators sign challenge-bound enrollments with
their own native Ed25519 keys and receive under roster-pinned ML-KEM keys. The
orchestrator generates public test identities; it provisions no link secret.

Topologies. `single`: every role on this host, observers on --bind-ip.
`two-host`: the three relays (their workers and links) run on --remote under a
tmux session this run owns; registrar, mailbox, clients and every observer run
here, and every link crosses an observer on --bind-ip, so a relay-to-relay link
crosses the LAN twice. Remote material stays on the remote host except public
keys and the relays' registrar pins (the registrar must hold all four).
"""
import argparse,hashlib,json,os,pathlib,shlex,socket,struct,subprocess,sys,threading,time
os.umask(0o077)

def readn(s,n):
    b=b''
    while len(b)<n:
        v=s.recv(n-len(b))
        if not v:raise RuntimeError('short byte-transparent frame')
        b+=v
    return b
def directory(p):p.mkdir(mode=0o700,parents=True,exist_ok=True);return p
def ip_hex(ip):return ''.join(f'{b:02X}' for b in reversed(socket.inet_aton(ip)))
def owns_listener(pid,ip,port):
    # Qualify startup without connecting: receive accepts exactly one enrolled
    # peer, so a readiness TCP probe would only be dropped, but it would still
    # cost a challenge. Pin the LISTEN socket to the receiver's actual PID.
    try:
        sockets={os.readlink(fd)[8:-1] for fd in pathlib.Path(f'/proc/{pid}/fd').iterdir()
                 if os.readlink(fd).startswith('socket:[')}
        for row in pathlib.Path('/proc/net/tcp').read_text().splitlines()[1:]:
            fields=row.split()
            if fields[1]==f'{ip_hex(ip)}:{port:04X}' and fields[3]=='0A' and fields[9] in sockets:
                return True
    except (FileNotFoundError,ProcessLookupError):pass
    return False
def start_receiver(start,argv,ip,log):
    """Bind-probe an ephemeral port, start the receiver there, wait for its own
    LISTEN. Port choice and child bind are not atomic: retry only an exited
    pre-traffic listener. Returns (process, (ip, port))."""
    for attempt in range(16):
        bound=socket.socket();bound.bind((ip,0));port=bound.getsockname()[1];bound.close()
        p=start(argv+['--endpoint',f'{ip}:{port}'])
        deadline=time.monotonic()+3
        while p.poll() is None and time.monotonic()<deadline:
            if owns_listener(p.pid,ip,port):return p,(ip,port)
            time.sleep(.005)
        if p.poll() is not None:
            log(f'STARTUP RETRY {argv[argv.index("--phase")+1]}/{argv[argv.index("--slot")+1]} attempt{attempt}: exited before owned LISTEN; no traffic.')
            continue
        raise RuntimeError('receiver startup did not qualify its owned LISTEN')
    raise RuntimeError('receiver startup port allocation exhausted')

# ---------------------------------------------------------------- remote agent
# `agent PLAN.json` runs on the remote host inside the run's tmux session. It
# starts its receivers, publishes their endpoints, waits for `go`, starts its
# workers and senders, then records every exit status. It decides nothing.
def agent(plan_path):
    plan=json.loads(pathlib.Path(plan_path).read_text())
    root=pathlib.Path(plan['root']);log=(root/'receiving.log').open('ab',buffering=0)
    def say(m):log.write((m+'\n').encode())
    procs=[]
    def start(argv):
        p=subprocess.Popen(argv,stdout=log,stderr=log);procs.append((p,argv));return p
    ready={}
    for r in plan['receivers']:
        p,ep=start_receiver(start,r['argv'],plan['bind_ip'],say);ready[r['label']]=list(ep)
    tmp=root/'ready.json.tmp';tmp.write_text(json.dumps(ready));tmp.rename(root/'ready.json')
    limit=time.monotonic()+120
    while not (root/'go').exists():
        if time.monotonic()>limit:raise SystemExit('agent: no go')
        time.sleep(.01)
    for argv in plan['workers']+plan['senders']:start(argv)
    codes=[]
    for p,argv in procs:
        try:codes.append([p.wait(timeout=plan['wait_s']),argv])
        except subprocess.TimeoutExpired:p.kill();codes.append([-9,argv])
    tmp=root/'done.json.tmp';tmp.write_text(json.dumps(codes));tmp.rename(root/'done.json')
    say('AGENT DONE '+json.dumps([c for c,_ in codes]))

if len(sys.argv)==3 and sys.argv[1]=='agent':
    agent(sys.argv[2]);sys.exit(0)

parser=argparse.ArgumentParser()
parser.add_argument('--mini',required=True,type=pathlib.Path)
parser.add_argument('--fixture',required=True,type=pathlib.Path)
parser.add_argument('--native-socket',required=True)
parser.add_argument('--evidence',required=True,type=pathlib.Path)
parser.add_argument('--epochs',type=int,default=64)
parser.add_argument('--processing-slots',type=int,default=2)
parser.add_argument('--native-workload',choices=['single','every-eight'],default='single')
parser.add_argument('--payload-bytes',type=int,default=4096)
parser.add_argument('--real-clients',type=int,default=2)
# `file`: fixture/expected-transport-outcome.bin, a read-only lookup known in
# advance. `capture`: a NEW effect, whose exact Host reply exists only once the
# effect happens; the delay proxy keeps the bytes it forwarded (exactly once).
parser.add_argument('--expect',choices=['file','capture'],default='file')
# Optional existing native identities for member slots: SECRET:PUBLIC,... (e.g.
# a participant's own Mini key). Absent slots get fresh test identities.
parser.add_argument('--member-keys',default='')
parser.add_argument('--topology',choices=['single','two-host'],default='single')
parser.add_argument('--bind-ip',default='127.0.0.1')
parser.add_argument('--remote',default='')
parser.add_argument('--remote-ip',default='')
parser.add_argument('--remote-dir',default='')
parser.add_argument('--startup-s',type=int,default=60)
a=parser.parse_args()
mini=a.mini;fixture=a.fixture;e=a.evidence;e.mkdir(mode=0o700)
log=(e/'receiving.log').open('wb',buffering=0)
def say(m):log.write((m+'\n').encode())
request=(fixture/'request.native').read_bytes()
expected=(fixture/'expected-transport-outcome.bin').read_bytes() if a.expect=='file' else None
native=a.native_socket
N=a.epochs;P=a.payload_bytes;W=4;T=1000;G=a.processing_slots;R=a.real_clients
job_epochs=list(range(0,N,8)) if a.native_workload=='every-eight' else [0]
if N<12 or N>256 or N%4 or G<1 or G>32 or not 1<=R<=W:
    raise SystemExit('public test profile requires12..256 epochs divisibleby4, 1..32 processing slots, 1..4 real clients')
if a.expect=='capture' and (R!=1 or len(job_epochs)!=1):
    raise SystemExit('a captured new effect is ONE job from ONE client')
two=a.topology=='two-host'
if two and not (a.remote and a.remote_ip and a.remote_dir and a.bind_ip!='127.0.0.1'):
    raise SystemExit('two-host needs --remote, --remote-ip, --remote-dir and a LAN --bind-ip')
generation=os.urandom(16).hex()
common=e/'common';common.mkdir(mode=0o700)
def run(*args):
    r=subprocess.run([str(mini),*map(str,args)],stdout=log,stderr=log)
    if r.returncode:raise RuntimeError('command failed: '+repr(args))
def ssh(cmd,check=True,capture=False):
    r=subprocess.run(['ssh','-o','BatchMode=yes',a.remote,cmd],stdout=subprocess.PIPE if capture else log,stderr=log)
    if check and r.returncode:raise RuntimeError('remote command failed: '+cmd)
    return r.stdout if capture else r.returncode
def fetch(remote_path):
    r=subprocess.run(['ssh','-o','BatchMode=yes',a.remote,'cat '+shlex.quote(remote_path)],stdout=subprocess.PIPE,stderr=log)
    if r.returncode:raise RuntimeError('remote fetch failed: '+remote_path)
    return r.stdout
def push(local,remote_path):
    r=subprocess.run(['scp','-q','-p',str(local),f'{a.remote}:{remote_path}'],stdout=log,stderr=log)
    if r.returncode:raise RuntimeError('remote push failed: '+remote_path)

# ---------------------------------------------------------------- identities
# Mix layer keys k0..k3 and registrar pins a0..a3: hop i<3 is relay i, hop 3 is
# the mailbox. Operators for links: 0 registrar, 1..3 relays, 4 mailbox.
RD=pathlib.PurePosixPath(a.remote_dir) if two else None
rmini=str(RD/'mini') if two else None
remote_ops={1,2,3} if two else set()
if two:
    ssh(f'mkdir -m 700 {RD} && mkdir -m 700 {RD/"common"}')
    push(mini,rmini);push(pathlib.Path(__file__).resolve(),str(RD/'cohort-native-tcp.py'))
    say('remote mini sha256 '+hashlib.sha256(fetch(rmini)).hexdigest()+' local '+hashlib.sha256(mini.read_bytes()).hexdigest())
def keygen(secret,public,remote=False):
    if remote:ssh(f'{rmini} keygen --secret {secret} --public {public} --no-prerotation >/dev/null')
    else:run('keygen','--secret',secret,'--public',public,'--no-prerotation')
def kemgen(state,secret,public,remote=False):
    if remote:ssh(f'{rmini} mix --action key --state {state} --secret {secret} --public {public}')
    else:run('mix','--action','key','--state',state,'--secret',secret,'--public',public)
def pingen(state,secret,remote=False):
    if remote:ssh(f'{rmini} mix --action registrar-key --state {state} --secret {secret}')
    else:run('mix','--action','registrar-key','--state',state,'--secret',secret)
ident={}   # name -> dict(native=path, native_pub=bytes, link_secret, link_public=path, link_pub=bytes, remote)
def identity(name,remote=False,native=None):
    base=(RD/'common') if remote else common
    i={'remote':remote}
    if native:i['native'],pub=native.split(':');i['native_pub']=pathlib.Path(pub).read_bytes()
    else:
        i['native']=str(base/f'{name}.native');keygen(i['native'],str(base/f'{name}.native.pub'),remote)
        i['native_pub']=fetch(str(base/f'{name}.native.pub')) if remote else pathlib.Path(str(base/f'{name}.native.pub')).read_bytes()
    i['link_secret']=str(base/f'{name}.link.secret');i['link_public']=str(base/f'{name}.link.pub')
    kemgen(str(base/f'{name}.linkgen'),i['link_secret'],i['link_public'],remote)
    i['link_pub']=fetch(i['link_public']) if remote else pathlib.Path(i['link_public']).read_bytes()
    ident[name]=i;return i
supplied=[v for v in a.member_keys.split(',') if v]
members=[identity(f'member{i}',native=supplied[i] if i<len(supplied) else None) for i in range(W)]
operators=[identity(n,remote=k in remote_ops) for k,n in enumerate(['registrar','relay0','relay1','relay2','mailbox'])]
for i in range(4):
    remote=i<3 and two
    base=(RD/'common') if remote else common
    kemgen(str(base/f'kg{i}'),str(base/f'k{i}.secret'),str(base/f'k{i}.pub'),remote)
    pingen(str(base/f'ag{i}'),str(base/f'a{i}.key'),remote)
    if remote:
        for f in [f'k{i}.pub',f'a{i}.key']:
            path=common/f;path.write_bytes(fetch(str(base/f)));path.chmod(0o600)
(common/'roster.json').write_text(json.dumps({
    'type':'minidregg-cohort-roster-v1','generation':generation,'width':W,
    'members':[{'native':m['native_pub'].hex(),'linkKem':m['link_pub'].hex()} for m in members],
    'operators':[{'native':o['native_pub'].hex(),'linkKem':o['link_pub'].hex()} for o in operators]}))
roster=common/'roster.json'
if two:push(roster,str(RD/'common'/'roster.json'))
def roster_for(remote):return str(RD/'common'/'roster.json') if remote else str(roster)
keycsv=','.join(str(common/f'k{i}.pub') for i in range(4))
authcsv=','.join(str(common/f'a{i}.key') for i in range(4))
say('ROSTER sha256 '+hashlib.sha256(roster.read_bytes()).hexdigest()+' generation '+generation)

def frame_size(phase):
    mf=18+160*W+128
    return ([P+4640+160]+[mf+19+W*(P+(5-i)*1160) for i in range(1,5)]+[19+W*P])[phase]+89
# MCE2: receiver challenge (MCE2|nonce32|ephemeral ML-KEM ek), sender response
# (two ML-KEM ciphertexts|Ed25519 signature), receiver acknowledgement.
HANDSHAKE=[(False,4+32+1184),(True,2*1088+64),(False,32)]
def link_parties(phase,slot):
    """(sender identity, receiver identity) of the roster for this link."""
    return (members[slot] if phase==0 else operators[phase-1],
            members[slot] if phase==5 else operators[phase])

def scenario(name,real):
    d=directory(e/name);origin=int(time.time()*1000)+a.startup_s*1000
    rd=(RD/name) if two else None
    if two:ssh(f'mkdir -m 700 {rd}')
    processes=[];observers=[];public=[];errors=[];forwarded=[];replies=[];checks={}
    delay_path=pathlib.Path('/run/user/'+str(os.getuid()))/('mini-cohort-'+str(os.getpid())+'-'+name+'.sock')
    listener=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM);listener.bind(str(delay_path));listener.listen(4)
    listener.settimeout(.1);stop=threading.Event()
    def native_one(client):
        try:
            with client:
                n=struct.unpack('<I',readn(client,4))[0];body=readn(client,n)
                if body!=request:raise RuntimeError('unexpected native source envelope')
                # Public test delay only. Every byte forwarded ONCE; no fake reply.
                time.sleep(2)
                with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as downstream:
                    downstream.connect(native);downstream.sendall(struct.pack('<I',n)+body)
                    size=readn(downstream,4);reply=readn(downstream,struct.unpack('<I',size)[0])
                forwarded.append(hashlib.sha256(body).hexdigest());replies.append(reply)
                client.sendall(size+reply)
        except Exception as err:errors.append(repr(err))
    def native_loop():
        while not stop.is_set():
            try:c,_=listener.accept()
            except socket.timeout:continue
            except OSError:break
            t=threading.Thread(target=native_one,args=(c,));t.start();observers.append(t)
    nt=threading.Thread(target=native_loop);nt.start()
    def base(where):return rd if where else d
    def command(action,state,records,phase,slot=0,*extra,remote=False):
        return [rmini if remote else str(mini),'mix-live','--action',action,'--state',str(state),
            '--generation',generation,'--slot',str(slot),
            '--phase',str(phase),'--width',str(W),'--payload-bytes',str(P),
            '--origin-ms',str(origin),'--tick-ms',str(T),'--processing-slots',str(G),'--epochs',str(N),
            '--records',str(records),*map(str,extra)]
    def mkdirs(*paths,remote=False):
        if remote:ssh('mkdir -p -m 700 '+' '.join(map(str,paths)))
        else:
            for p in paths:directory(pathlib.Path(p))
        return paths
    def start(cmd):
        p=subprocess.Popen(cmd,stdout=log,stderr=log);processes.append((p,cmd));return p
    remote_plan={'root':str(rd) if two else '','bind_ip':a.remote_ip,'receivers':[],'workers':[],'senders':[],'wait_s':a.startup_s+N+5*G+120}
    targets={}
    def observe(label,phase,slot,proxy):
        try:
            with proxy:
                incoming,_=proxy.accept()
                deadline=time.monotonic()+20
                while label not in targets:
                    if time.monotonic()>deadline:raise RuntimeError('receiver endpoint never published')
                    time.sleep(.005)
                with incoming,socket.socket() as outgoing:
                    for _ in range(400):
                        try:outgoing.connect(targets[label]);break
                        except ConnectionRefusedError:time.sleep(.005)
                    else:raise RuntimeError('fixed receiver not listening')
                    incoming.settimeout(240);outgoing.settimeout(240)
                    # Fixed MCE2 startup exchange precedes epochs; the transparent
                    # observer neither supplies nor verifies any enrollment.
                    for from_sender,n in HANDSHAKE:
                        if from_sender:outgoing.sendall(readn(incoming,n))
                        else:incoming.sendall(readn(outgoing,n))
                    for epoch in range(N):
                        wire=readn(incoming,frame_size(phase))
                        at=time.time()*1000-origin
                        if wire[:4]!=b'MCL1' or struct.unpack('<Q',wire[36:44])[0]!=epoch:
                            raise RuntimeError('public link framing changed')
                        public.append({'link':label,'phase':phase,'slot':slot,'epoch':epoch,'bytes':len(wire),'relative_ms':at})
                        outgoing.sendall(wire)
        except Exception as err:errors.append(label+': '+repr(err))
    links=[]
    def edge(label,phase,slot,source,dest):
        sender,receiver=link_parties(phase,slot)
        proxy=socket.socket();proxy.bind((a.bind_ip,0));proxy.listen(1)
        t=threading.Thread(target=observe,args=(label,phase,slot,proxy));t.start();observers.append(t)
        rs=receiver['remote'];ss=sender['remote']
        receive=command('receive',base(rs)/f'{label}-receive-state',dest,phase,slot,
            '--roster',roster_for(rs),'--link-secret',receiver['link_secret'],'--link-public',receiver['link_public'],remote=rs)
        send=command('send',base(ss)/f'{label}-send-state',source,phase,slot,
            '--roster',roster_for(ss),'--native-key',sender['native'],
            '--endpoint',f'{a.bind_ip}:{proxy.getsockname()[1]}',remote=ss)
        links.append((label,rs,receive,ss,send))
    try:
        cdirs=[]
        for i in range(W):
            source=directory(d/f'client{i}-source');out=directory(d/f'client{i}-out')
            if real and i<R:
                for begin in job_epochs:
                    ident16=os.urandom(16);cap=os.urandom(32)
                    (source/f'epoch-{begin}.intent').write_bytes(b'\x01'+ident16+cap+request)
                    # Fixed spare application opportunity: exact same original
                    # body/id/access, fresh outer epoch seal. Native gateway
                    # caches or admits once; never a second semantic dispatch.
                    (source/f'epoch-{begin+1}.intent').write_bytes(b'\x01'+ident16+cap+request)
                    repairs=(begin+3,begin+7) if a.native_workload=='every-eight' else (3,7,N-1)
                    for epoch in set(repairs):
                        (source/f'epoch-{epoch}.intent').write_bytes(b'\x02'+ident16+b'\x00'+hashlib.sha256(request).digest()+cap+os.urandom(32))
            start(command('cover',directory(d/f'client{i}-worker'),out,0,i,'--source',source,'--keys',keycsv))
        # Establish complete cover inventory before public links begin.
        # This is public profile admission, before any cohort connection. Use
        # the fixed startup interval, reserving10s for enrolled links;
        # never start an incomplete inventory or move the original origin.
        while int(time.time()*1000) < origin-10000-(20000 if two else 0):
            if all((d/f'client{i}-out'/f'epoch-{N-1}.cover').exists() for i in range(W)):break
            time.sleep(.005)
        else:raise RuntimeError('cover inventory did not finish before original public startup cutoff')
        registrar_sources=[directory(d/f'client{i}-incoming') for i in range(W)]
        # Stage directories live where their consumer/producer lives.
        def stage_dir(i,kind):  # kind: out (producer of stage i) / incoming (consumer)
            owner=(i>0 if kind=='out' else i<3) and two
            return (rd if owner else d)/f'batch{i}-{kind}',owner
        for i in range(4):
            for kind in ['out','incoming']:
                p,remote=stage_dir(i,kind);mkdirs(p,remote=remote)
        workers=[]
        workers.append((False,command('registrar',directory(d/'registrar-worker'),stage_dir(0,'out')[0],1,0,
            '--source',','.join(map(str,registrar_sources)),'--auth-keys',authcsv,'--roster',roster)))
        for i in range(3):
            remote=two;bd=rd if remote else d;cm=(RD/'common') if remote else common
            if not remote:directory(d/f'relay{i}-worker')
            workers.append((remote,command('relay',bd/f'relay{i}-worker',stage_dir(i+1,'out')[0],i+2,0,
                '--source',stage_dir(i,'incoming')[0],'--hop',i,'--secret',cm/f'k{i}.secret','--auth-key',cm/f'a{i}.key',
                '--roster',roster_for(remote),remote=remote)))
        workers.append((False,command('mailbox',directory(d/'mailbox-worker'),directory(d/'broadcast-out'),5,0,
            '--source',stage_dir(3,'incoming')[0],'--secret',common/'k3.secret','--auth-key',common/'a3.key',
            '--target',delay_path,'--config',fixture/'host.config','--custody-hold-ms',3000,'--roster',roster)))
        for i in range(W):
            workers.append((False,command('scan',directory(d/f'client{i}-scan-worker'),directory(d/f'client{i}-opened'),5,i,
                '--source',directory(d/f'client{i}-broadcast'),'--caps',d/f'client{i}-worker'/'caps','--roster',roster)))
        for i in range(W):edge(f'client{i}-registrar',0,i,d/f'client{i}-out',registrar_sources[i])
        for i in range(4):edge(f'stage{i}',i+1,0,stage_dir(i,'out')[0],stage_dir(i,'incoming')[0])
        for i in range(W):edge(f'broadcast-client{i}',5,i,d/'broadcast-out',d/f'client{i}-broadcast')
        # Order: observers listen (above); local receivers; remote receivers;
        # then workers and senders on both hosts.
        for label,rs,receive,_,_ in links:
            if not rs:
                _,ep=start_receiver(start,receive,a.bind_ip,say);targets[label]=ep
        if two:
            for label,rs,receive,_,_ in links:
                if rs:remote_plan['receivers'].append({'label':label,'argv':receive})
            remote_plan['workers']=[w for remote,w in workers if remote]
            remote_plan['senders']=[s for _,_,_,ss,s in links if ss]
            plan=e/f'{name}-remote-plan.json';plan.write_text(json.dumps(remote_plan,indent=1))
            push(plan,str(rd/'plan.json'))
            session=f'traffic-{os.getpid()}-{name}'
            ssh(f'tmux new-session -d -s {session} python3 {RD/"cohort-native-tcp.py"} agent {rd/"plan.json"}')
            say(f'REMOTE tmux session {session} on {a.remote}')
            deadline=time.monotonic()+60
            while True:
                if ssh(f'test -e {rd/"ready.json"}',check=False)==0:break
                if time.monotonic()>deadline:raise RuntimeError('remote receivers never published readiness')
                time.sleep(.2)
            for label,ep in json.loads(fetch(str(rd/'ready.json'))).items():targets[label]=tuple(ep)
            ssh(f'touch {rd/"go"}')
        for remote,w in workers:
            if not remote:start(w)
        for _,_,_,ss,s in links:
            if not ss:start(s)
        limit=time.monotonic()+a.startup_s+20+N+5*G+(60 if two else 0)
        # Every failure is recorded, then EVERY check runs, so one run yields
        # the whole picture; any failure still refutes the pole at the end.
        for p,cmd in processes:
            try:rc=p.wait(timeout=max(.1,limit-time.monotonic()))
            except subprocess.TimeoutExpired:rc='timeout'
            if rc:errors.append('actor failed '+str(rc)+': '+repr(cmd))
        if two:
            deadline=time.monotonic()+120
            while ssh(f'test -e {rd/"done.json"}',check=False):
                if time.monotonic()>deadline:errors.append('remote actors never finished');break
                time.sleep(.5)
            else:
                for rc,cmd in json.loads(fetch(str(rd/'done.json'))):
                    if rc:errors.append('remote actor failed '+str(rc)+': '+repr(cmd))
        for t in observers:t.join(timeout=3)
        def check(name,fn):
            try:ok=bool(fn());checks[name]=ok if ok else 'FAILED'
            except Exception as err:checks[name]='FAILED: '+repr(err)[:300]
        def read(p):return p.read_bytes() if p.exists() else b''
        check('records_12N',lambda:len(public)==12*N)
        check('every_record_within_100ms',lambda:all(abs(v['relative_ms']-(v['epoch']+v['phase']*G+1)*T)<100 for v in public))
        check('valid_broadcast_every_epoch_every_client',lambda:all(
            len(r)==5+19+W*P and r[0]==1 for i in range(W) for epoch in range(N)
            for r in [read(d/f'client{i}-broadcast'/f'epoch-{epoch}.record')]))
        check('identical_broadcast_to_every_client',lambda:all(
            len({read(d/f'client{i}-broadcast'/f'epoch-{epoch}.record') for i in range(W)})==1 for epoch in range(N)))
        if real:
            check('exactly_once_source_submissions',lambda:len(forwarded)==R*len(job_epochs))
            want=expected
            if a.expect=='capture':
                check('one_captured_reply',lambda:len(replies)==1)
                if replies:
                    want=b'\x00'+replies[0]
                    (d/'captured-native-reply.bin').write_bytes(replies[0])
            def outcomes():
                for i in range(R):
                    for begin in job_epochs:
                        first=read(d/f'client{i}-opened'/f'epoch-{begin}.payload')
                        if first:
                            n=struct.unpack('<I',first[:4])[0]
                            assert n==len(first)-4 and first[4] in (0,3),'not physical continuation/exact reply'
                            if first[4]==0:assert first[4:]==want
                        # Empty is physical response uncertainty/cover, never Native Pending.
                        finish=begin+7 if a.native_workload=='every-eight' else N-1
                        last=read(d/f'client{i}-opened'/f'epoch-{finish}.payload')
                        n=struct.unpack('<I',last[:4])[0]
                        assert n==len(last)-4 and last[4:]==want,'not exact source frame'
                return want is not None
            check('exact_outcomes_after_lost_reply_recovery',outcomes)
        else:check('nothing_forwarded_without_work',lambda:not forwarded)
        failed=[k for k,v in checks.items() if v is not True]
        if errors or failed:raise RuntimeError('; '.join(errors+['check '+k for k in failed]))
        public.sort(key=lambda v:(v['phase'],v['slot'],v['epoch']))
        (d/'public-wire-observation.json').write_text(json.dumps(public,indent=2))
        say('PASS '+name+': '+str(len(public))+' roster-enrolled fixed TCP records, valid broadcast every epoch, '+str(len(forwarded))+' exact original source calls.')
        return [(v['link'],v['phase'],v['slot'],v['epoch'],v['bytes']) for v in public]
    finally:
        for p,_ in processes:
            if p.poll() is None:p.terminate()
        for p,_ in processes:
            if p.poll() is None:
                try:p.wait(timeout=5)
                except subprocess.TimeoutExpired:p.kill();p.wait()
        stop.set();listener.close();nt.join(timeout=2)
        delay_path.unlink(missing_ok=True)
        # Preserve public observations even on a processing refutation. These
        # contain sizes/times only, never packet bodies or native source bytes.
        public.sort(key=lambda v:(v['phase'],v['slot'],v['epoch']))
        (d/'public-wire-observation.json').write_text(json.dumps(public,indent=2))
        def produced(label,remote):
            if remote:
                return int(ssh(f'ls {rd/label} 2>/dev/null | grep -c "^epoch-.*\\.payload$" || true',check=False,capture=True) or 0)
            return sum((d/label/f'epoch-{epoch}.payload').exists() for epoch in range(N))
        counts={'batch0-out':produced('batch0-out',False)}
        for i in range(1,4):counts[f'batch{i}-out']=produced(f'batch{i}-out',two)
        counts['broadcast-out']=produced('broadcast-out',False)
        latencies=[v['relative_ms']-(v['epoch']+v['phase']*G+1)*T for v in public]
        def dist(xs):
            xs=sorted(xs)
            if not xs:return None
            q=lambda f:xs[min(len(xs)-1,int(f*len(xs)))]
            return {'n':len(xs),'min':xs[0],'p50':q(.5),'p90':q(.9),'p99':q(.99),'max':xs[-1],
                    'over_100ms':sum(abs(x)>=100 for x in xs)}
        # Which links cross the LAN (two-host): one leg per remote endpoint.
        crossing={l:(int(rs)+int(ss)) for l,rs,_,ss,_ in links}
        valid_delivery={f'client{i}':sum(
            (d/f'client{i}-broadcast'/f'epoch-{epoch}.record').exists()
            and (d/f'client{i}-broadcast'/f'epoch-{epoch}.record').read_bytes()[0]==1
            for epoch in range(N)) for i in range(W)}
        want_path=lambda i,begin:d/f'client{i}-opened'/f'epoch-{begin+7 if a.native_workload=="every-eight" else N-1}.payload'
        final_want=(b'\x00'+replies[0]) if (a.expect=='capture' and replies) else expected
        (d/'public-run-summary.json').write_text(json.dumps({
            'topology':a.topology,'bind_ip':a.bind_ip,'remote':a.remote or None,'remote_ip':a.remote_ip or None,
            'roster_sha256':hashlib.sha256(roster.read_bytes()).hexdigest(),
            'tick_ms':T,'processing_slots':G,'epochs':N,'width':W,'payload_bytes':P,'epoch_buffer_lengths':N/G,
            'contribution_to_broadcast_schedule_ms':5*G*T,
            'origin_to_first_broadcast_ms':(5*G+1)*T,
            'records_observed':len(public),'records_expected':12*N,
            'min_wire_lateness_ms':min(latencies) if latencies else None,
            'max_wire_lateness_ms':max(latencies) if latencies else None,
            'wire_lateness_ms':dist(latencies),
            'wire_lateness_ms_by_lan_legs':{str(k):dist([v['relative_ms']-(v['epoch']+v['phase']*G+1)*T for v in public if crossing.get(v['link'])==k]) for k in sorted(set(crossing.values()))},
            'wire_lateness_ms_by_phase':{str(ph):dist([v['relative_ms']-(v['epoch']+v['phase']*G+1)*T for v in public if v['phase']==ph]) for ph in range(6)},
            'durable_produced_epoch_counts':counts,'valid_delivered_broadcast_epochs':valid_delivery,'native_workload':a.native_workload,
            'expect':a.expect,'real_clients':R,
            'source_jobs_expected':R*len(job_epochs) if real else 0,
            'exact_native_final_outcomes': [(want_path(i,begin).read_bytes()[4:]==final_want if want_path(i,begin).exists() and final_want else False) for i in range(R) for begin in job_epochs] if real else [],
            'actual_source_submissions':len(forwarded),
            'checks':checks,'errors':errors},indent=2))
# Historical lookup is read-only; preserve BOTH poles even if processing
# refutes baseline. An unsuccessful pole never becomes a qualified comparison.
results={};failures=[]
for name,real in [('all-cover',False),('native-delayed',True)]:
    try:results[name]=scenario(name,real)
    except Exception as error:
        failures.append(name+': '+repr(error))
        say('REFUTED '+failures[-1])
if failures:raise RuntimeError('; '.join(failures))
assert results['all-cover']==results['native-delayed'],'public epoch/slot/phase/record shape changed with hidden work'
say('PASS matched public shapes at 1s: all-cover and delayed actual native work; no missing broadcast, no catch-up burst; retained requests and authorized fresh-cap repair fetch returned exact source outcomes; exactly '+str(R*len(job_epochs))+' source submissions.')
log.close()
