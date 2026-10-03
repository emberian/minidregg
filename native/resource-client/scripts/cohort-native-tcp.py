#!/usr/bin/env python3
"""Receiving orchestration and byte-transparent observers; no evaluator."""
import argparse,hashlib,json,os,pathlib,socket,struct,subprocess,threading,time
os.umask(0o077)
parser=argparse.ArgumentParser()
parser.add_argument('--mini',required=True,type=pathlib.Path)
parser.add_argument('--fixture',required=True,type=pathlib.Path)
parser.add_argument('--native-socket',required=True)
parser.add_argument('--evidence',required=True,type=pathlib.Path)
parser.add_argument('--epochs',type=int,default=64)
parser.add_argument('--processing-slots',type=int,default=2)
a=parser.parse_args()
mini=a.mini;fixture=a.fixture;e=a.evidence;e.mkdir(mode=0o700)
log=(e/'receiving.log').open('wb',buffering=0)
request=(fixture/'request.native').read_bytes();expected=(fixture/'expected-transport-outcome.bin').read_bytes()
native=a.native_socket
N=a.epochs;P=4096;W=4;T=1000;G=a.processing_slots
if N<12 or N>256 or N%4 or G<1 or G>32:
    raise SystemExit('public test profile requires12..256 epochs divisibleby4 and1..32 processing slots')
generation=os.urandom(16).hex()
common=e/'common';common.mkdir(mode=0o700)
def run(*args):
    r=subprocess.run([str(mini),*map(str,args)],stdout=log,stderr=log)
    if r.returncode:raise RuntimeError('command failed: '+repr(args))
for i in range(4):
    run('mix','--action','key','--state',common/f'kg{i}','--secret',common/f'k{i}.secret','--public',common/f'k{i}.pub')
    run('mix','--action','registrar-key','--state',common/f'ag{i}','--secret',common/f'a{i}.key')
(common/'worker.key').write_bytes(os.urandom(32))
keycsv=','.join(str(common/f'k{i}.pub') for i in range(4))
authcsv=','.join(str(common/f'a{i}.key') for i in range(4))
def readn(s,n):
    b=b''
    while len(b)<n:
        v=s.recv(n-len(b))
        if not v:raise RuntimeError('short byte-transparent frame')
        b+=v
    return b
def directory(p):p.mkdir(mode=0o700,parents=True,exist_ok=True);return p
def frame_size(phase):
    mf=18+160*W+128
    return ([P+4640+160]+[mf+19+W*(P+(5-i)*1160) for i in range(1,5)]+[19+W*P])[phase]+89
def scenario(name,real):
    d=directory(e/name);origin=int(time.time()*1000)+60000
    processes=[];observers=[];public=[];errors=[];forwarded=[]
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
                forwarded.append(hashlib.sha256(body).hexdigest())
                client.sendall(size+reply)
        except Exception as err:errors.append(repr(err))
    def native_loop():
        while not stop.is_set():
            try:c,_=listener.accept()
            except socket.timeout:continue
            except OSError:break
            t=threading.Thread(target=native_one,args=(c,));t.start();observers.append(t)
    nt=threading.Thread(target=native_loop);nt.start()
    def command(action,state,records,phase,slot=0,*extra):
        return [str(mini),'mix-live','--action',action,'--state',str(directory(state)),
            '--key',str(common/'worker.key'),'--generation',generation,'--slot',str(slot),
            '--phase',str(phase),'--width',str(W),'--payload-bytes',str(P),
            '--origin-ms',str(origin),'--tick-ms',str(T),'--processing-slots',str(G),'--epochs',str(N),
            '--records',str(directory(records)),*map(str,extra)]
    def start(cmd):
        p=subprocess.Popen(cmd,stdout=log,stderr=log);processes.append((p,cmd));return p
    def edge(label,phase,slot,source,dest):
        key=d/f'{label}.key';key.write_bytes(os.urandom(32))
        bound=socket.socket();bound.bind(('127.0.0.1',0));endpoint=bound.getsockname();bound.close()
        receive=command('receive',d/f'{label}-receive-state',dest,phase,slot,'--endpoint',f'{endpoint[0]}:{endpoint[1]}')
        receive[receive.index('--key')+1]=str(key);start(receive)
        proxy=socket.socket();proxy.bind(('127.0.0.1',0));proxy.listen(1);address=proxy.getsockname()
        def observe():
            try:
                with proxy:
                    incoming,_=proxy.accept()
                    with incoming,socket.socket() as outgoing:
                        for _ in range(200):
                            try:outgoing.connect(endpoint);break
                            except ConnectionRefusedError:time.sleep(.005)
                        else:raise RuntimeError('fixed receiver not listening')
                        incoming.settimeout(120)
                        for epoch in range(N):
                            wire=readn(incoming,frame_size(phase))
                            at=time.time()*1000-origin
                            if wire[:4]!=b'MCL1' or struct.unpack('<Q',wire[36:44])[0]!=epoch:
                                raise RuntimeError('public link framing changed')
                            public.append({'link':label,'phase':phase,'slot':slot,'epoch':epoch,'bytes':len(wire),'relative_ms':at})
                            outgoing.sendall(wire)
            except Exception as err:errors.append(label+': '+repr(err))
        t=threading.Thread(target=observe);t.start();observers.append(t)
        send=command('send',d/f'{label}-send-state',source,phase,slot,'--endpoint',f'{address[0]}:{address[1]}')
        send[send.index('--key')+1]=str(key);start(send)
    try:
        for i in range(W):
            source=directory(d/f'client{i}-source');out=directory(d/f'client{i}-out')
            if real and i<2:
                ident=os.urandom(16);cap=os.urandom(32)
                (source/'epoch-0.intent').write_bytes(b'\x01'+ident+cap+request)
                for epoch in (3,7,N-1):
                    (source/f'epoch-{epoch}.intent').write_bytes(b'\x02'+ident+b'\x00'+hashlib.sha256(request).digest()+cap+os.urandom(32))
            start(command('cover',d/f'client{i}-worker',out,0,i,'--source',source,'--keys',keycsv))
        # Establish complete cover inventory before public links begin.
        for _ in range(6000):
            if all((d/f'client{i}-out'/f'epoch-{N-1}.cover').exists() for i in range(W)):break
            time.sleep(.005)
        else:raise RuntimeError('cover inventory did not finish')
        registrar_sources=[directory(d/f'client{i}-incoming') for i in range(W)]
        start(command('registrar',d/'registrar-worker',d/'batch0-out',1,0,
            '--source',','.join(map(str,registrar_sources)),'--auth-keys',authcsv))
        for i in range(3):
            start(command('relay',d/f'relay{i}-worker',d/f'batch{i+1}-out',i+2,0,
                '--source',d/f'batch{i}-incoming','--hop',i,'--secret',common/f'k{i}.secret','--auth-key',common/f'a{i}.key'))
        start(command('mailbox',d/'mailbox-worker',d/'broadcast-out',5,0,
            '--source',d/'batch3-incoming','--secret',common/'k3.secret','--auth-key',common/'a3.key',
            '--target',delay_path,'--config',fixture/'host.config','--custody-hold-ms',3000))
        for i in range(W):
            start(command('scan',d/f'client{i}-scan-worker',d/f'client{i}-opened',5,i,
                '--source',d/f'client{i}-broadcast','--caps',d/f'client{i}-worker'/'caps'))
        for i in range(W):edge(f'client{i}-registrar',0,i,d/f'client{i}-out',registrar_sources[i])
        for i in range(4):edge(f'stage{i}',i+1,0,d/f'batch{i}-out',d/f'batch{i}-incoming')
        for i in range(W):edge(f'broadcast-client{i}',5,i,d/'broadcast-out',d/f'client{i}-broadcast')
        limit=time.monotonic()+80+N+5*G
        for p,cmd in processes:
            rc=p.wait(timeout=max(.1,limit-time.monotonic()))
            if rc:raise RuntimeError('actor failed '+str(rc)+': '+repr(cmd))
        for t in observers:t.join(timeout=3)
        if errors:raise RuntimeError('; '.join(errors))
        assert len(public)==12*N,(len(public),12*N)
        assert all(abs(v['relative_ms']-(v['epoch']+v['phase']*G+1)*T)<100 for v in public)
        for i in range(W):
            for epoch in range(N):
                record=(d/f'client{i}-broadcast'/f'epoch-{epoch}.record').read_bytes();assert len(record)==5+19+W*P and record[0]==1,'missing valid broadcast'
        if real:
            assert len(forwarded)==2,'second semantic dispatch occurred'
            for i in range(2):
                first=(d/f'client{i}-opened'/'epoch-0.payload').read_bytes()
                n=struct.unpack('<I',first[:4])[0];assert n==len(first)-4 and first[4]==3,'not physical continuation'
                last=(d/f'client{i}-opened'/f'epoch-{N-1}.payload').read_bytes()
                n=struct.unpack('<I',last[:4])[0];assert n==len(last)-4 and last[4:]==expected,'not exact source frame'
        else:assert not forwarded
        public.sort(key=lambda v:(v['phase'],v['slot'],v['epoch']))
        (d/'public-wire-observation.json').write_text(json.dumps(public,indent=2))
        log.write(('PASS '+name+': '+str(len(public))+' authenticated fixed TCP records, valid broadcast every epoch, '+str(len(forwarded))+' exact original source calls.\n').encode())
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
        counts={}
        for label in ['batch0-out','batch1-out','batch2-out','batch3-out','broadcast-out']:
            counts[label]=sum((d/label/f'epoch-{epoch}.payload').exists() for epoch in range(N))
        latencies=[v['relative_ms']-(v['epoch']+v['phase']*G+1)*T for v in public]
        (d/'public-run-summary.json').write_text(json.dumps({
            'tick_ms':T,'processing_slots':G,'epochs':N,'epoch_buffer_lengths':N/G,
            'contribution_to_broadcast_schedule_ms':(5*G+1)*T,
            'records_observed':len(public),'records_expected':12*N,
            'min_wire_lateness_ms':min(latencies) if latencies else None,
            'max_wire_lateness_ms':max(latencies) if latencies else None,
            'durable_useful_epoch_counts':counts,'actual_source_submissions':len(forwarded),
            'errors':errors},indent=2))
baseline=scenario('all-cover',False)
active=scenario('native-delayed',True)
assert baseline==active,'public epoch/slot/phase/record shape changed with hidden work'
log.write(b'PASS matched public shapes at 1s: all-cover and delayed actual native work; no missing broadcast, no catch-up burst; initial physical continuation and authorized fresh-cap repair fetch returned exact source outcome; exactly two source submissions.\n')
log.close()
