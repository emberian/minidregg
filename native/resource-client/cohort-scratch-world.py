#!/usr/bin/env python3
"""A scratch plain-Host Mini world for cohort carrier receiving, and the exact
native fixtures the carrier needs. Never the live mesh or a common world.

  world   --mini M --host H --store S --verifier V --root NEW_DIR
          fresh private one-sponsor Store + `mini serve` on ROOT/public/mini.sock,
          and a declared resource `carried` (fields 2,3) the sponsor controls.
  lookup  --root W --out NEW_DIR
          one ordinary direct write, then the READ-ONLY op3 historical lookup of
          its exact call as request.native + its exact transport outcome (the
          v12-style replayed fixture).
  prepare --root W --out NEW_DIR --value V
          a NEW signed content write (field 3 := V), prepared and signed but NOT
          submitted (`workspace submit --prepare-only true`); request.native is
          its exact op2 envelope. No expected outcome exists until it happens.
  verify  --root W --fixture F --evidence E
          after the carrier run: the Host's captured reply decodes as an
          installed receipt, the client's retained attempt recovers the SAME
          receipt by read-only lookup, a signed read returns the value, and the
          Store advanced by exactly one accepted record.
  stop    --root W        stop this world's own `mini serve`.
"""
import argparse,hashlib,json,os,pathlib,signal,socket,struct,subprocess,sys,time
os.umask(0o077)
ap=argparse.ArgumentParser();ap.add_argument('verb',choices=['world','lookup','prepare','verify','stop'])
for f in ['mini','host','store','verifier','root','out','value','fixture','evidence']:ap.add_argument('--'+f)
a=ap.parse_args()
HERE=pathlib.Path(__file__).resolve().parent
root=pathlib.Path(a.root).resolve() if a.root else None
def sh(*cmd,out=None,ok=(0,)):
    r=subprocess.run([str(c) for c in cmd],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if out:pathlib.Path(out).write_bytes(r.stdout+b'\n--stderr--\n'+r.stderr)
    if r.returncode not in ok:
        raise SystemExit(f'FAILED {cmd[1] if len(cmd)>1 else cmd[0]} rc={r.returncode}: {r.stderr.decode(errors="replace")[-600:]}')
    return r.stdout
def meta():return json.loads((root/'scratch-world.json').read_text())
def exchange(sock,body):
    with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as s:
        s.settimeout(120);s.connect(sock);s.sendall(struct.pack('<I',len(body))+body)
        def readn(n):
            b=b''
            while len(b)<n:
                v=s.recv(n-len(b))
                if not v:raise SystemExit('short native reply')
                b+=v
            return b
        return readn(struct.unpack('<I',readn(4))[0])
def envelope(m,op,call):
    config=pathlib.Path(m['config']).read_bytes()
    pin=bytes.fromhex(m['hostSha256'])
    return bytes([2])+struct.pack('<I',len(config))+config+pin+bytes([op])+call,config
def field(read_json,name):
    v=json.loads(read_json)
    for e in v.get('cell',{}).get('entries',[]):
        if e.get('key',{}).get('field')==name:return e.get('value')
    return None
def receipt_fields(v):
    # A confirmed outcome, possibly nested under a wrapper key.
    if isinstance(v,dict):
        if 'transactionId' in v and 'acceptedCount' in v:return v
        for x in v.values():
            r=receipt_fields(x)
            if r:return r
    return None
def last_count(m):
    counts=[]
    for o in pathlib.Path(m['sponsor']).glob('attempts/*/outcome.json'):
        r=receipt_fields(json.loads(o.read_text()))
        if r:counts.append(int(r['acceptedCount']))
    if not counts:raise SystemExit('no accepted sponsor record to anchor the count')
    return max(counts)
def read_height(m,tag):
    out=sh(m['mini'],'workspace','--action','read','--dir',m['sponsor'],'--name','carried',out=root/f'{tag}.read.log')
    return out
def propose(m,pid,fieldname,value):
    req=root/'requests'/f'{pid}.json';req.parent.mkdir(mode=0o700,exist_ok=True)
    req.write_text(json.dumps({'type':'minidregg-workspace-proposal-v1','action':'invoke','targets':[{'name':'carried',
        'payload':{'type':'scalar','actions':[{'type':'create','key':{'type':'object','field':fieldname},'value':value}]}}]}))
    sh(m['mini'],'workspace','--action','propose','--dir',m['sponsor'],'--request',req,'--proposal-id',pid,out=root/f'{pid}.propose.log')
    return pathlib.Path(m['sponsor'])/'proposals'/pid/'intent.json'

if a.verb=='world':
    for f in ['mini','host','store','verifier']:
        if not pathlib.Path(getattr(a,f)).is_file():raise SystemExit('missing '+f)
    sockp=root/'public'/'mini.sock'
    sh('sh',HERE/'newparticipant-acceptance.sh',a.host,a.mini,a.store,a.verifier,root,sockp,out=pathlib.Path(str(root)+'.bootstrap.log'))
    m={'type':'minidregg-cohort-scratch-world-v1','root':str(root),'mini':str(pathlib.Path(a.mini).resolve()),
       'host':str(pathlib.Path(a.host).resolve()),'config':str(root/'deployment'/'pinned-config.json'),
       'socket':str(sockp),'sponsor':str(root/'sponsor'),'sponsorKey':str(root/'sponsor.key'),'sponsorPub':str(root/'sponsor.pub'),
       'serverPid':int((root/'public'/'server.pid').read_text()),
       'hostSha256':hashlib.sha256(pathlib.Path(a.host).read_bytes()).hexdigest(),
       'miniSha256':hashlib.sha256(pathlib.Path(a.mini).read_bytes()).hexdigest(),
       'storeSha256':hashlib.sha256(pathlib.Path(a.store).read_bytes()).hexdigest(),
       'verifierSha256':hashlib.sha256(pathlib.Path(a.verifier).read_bytes()).hexdigest()}
    (root/'requests').mkdir(mode=0o700,exist_ok=True)
    (root/'requests'/'permit-all.json').write_text('{"type":"all","predicates":[]}\n')
    sh(m['mini'],'workspace','--action','create','--dir',m['sponsor'],'--name','carried','--storage','declared',
       '--predicate',root/'requests'/'permit-all.json','--fields','2,3',out=root/'create-carried.log')
    (root/'scratch-world.json').write_text(json.dumps(m,indent=1))
    print(root/'scratch-world.json')

elif a.verb=='lookup':
    m=meta();out=pathlib.Path(a.out);out.mkdir(mode=0o700)
    intent=propose(m,'lookup-write','2','1')
    attempt=pathlib.Path(m['sponsor'])/'attempts'/'lookup-write'
    sh(m['mini'],'workspace','--action','submit','--dir',m['sponsor'],'--intent',intent,'--attempt',attempt,out=root/'lookup-write.submit.log')
    call=(attempt/'call.bin').read_bytes()
    body,config=envelope(m,3,call)
    reply=exchange(m['socket'],body)
    again=exchange(m['socket'],body)
    if reply!=again:raise SystemExit('historical lookup is not byte-stable; not a replayable read-only fixture')
    (out/'request.native').write_bytes(body);(out/'host.config').write_bytes(config)
    (out/'expected-transport-outcome.bin').write_bytes(b'\x00'+reply)
    (out/'manifest.json').write_text(json.dumps({'type':'minidregg-cohort-lookup-fixture-v1','operation':3,
        'requestSha256':hashlib.sha256(body).hexdigest(),'callSha256':hashlib.sha256(call).hexdigest(),
        'nativeReplySha256':hashlib.sha256(reply).hexdigest(),'world':str(root/'scratch-world.json'),
        'readOnly':'two identical direct lookups'},indent=1))
    print(out)

elif a.verb=='prepare':
    m=meta();out=pathlib.Path(a.out);out.mkdir(mode=0o700)
    before=read_height(m,'effect-before')
    if field(before,'3') is not None:raise SystemExit('field 3 already written; not a NEW effect')
    intent=propose(m,'carried-write','3',a.value)
    attempt=pathlib.Path(m['sponsor'])/'attempts'/'carried-write'
    sh(m['mini'],'workspace','--action','submit','--dir',m['sponsor'],'--intent',intent,'--attempt',attempt,
       '--prepare-only','true',out=root/'carried-write.prepare.log')
    if (attempt/'outcome.bin').exists():raise SystemExit('prepare-only produced an outcome')
    call=(attempt/'call.bin').read_bytes()
    body,config=envelope(m,2,call)
    (out/'request.native').write_bytes(body);(out/'host.config').write_bytes(config)
    (out/'manifest.json').write_text(json.dumps({'type':'minidregg-cohort-new-effect-fixture-v1','operation':2,
        'effect':{'resource':'carried','field':'3','value':a.value},'attempt':str(attempt),
        'requestSha256':hashlib.sha256(body).hexdigest(),'callSha256':hashlib.sha256(call).hexdigest(),
        'fieldBefore':None,'submitted':False,'acceptedCountBefore':last_count(m),
        'world':str(root/'scratch-world.json')},indent=1))
    print(out)

elif a.verb=='verify':
    m=meta();fx=pathlib.Path(a.fixture);ev=pathlib.Path(a.evidence)
    man=json.loads((fx/'manifest.json').read_text());attempt=pathlib.Path(man['attempt'])
    reply=(ev/'native-delayed'/'captured-native-reply.bin').read_bytes()
    v=root/'verify';v.mkdir(mode=0o700,exist_ok=True)
    # The Host answers an op2 envelope with one tag byte (2) then the exact outcome record.
    if reply[:1]!=b'\x02':raise SystemExit('captured reply is not an op2 answer: tag '+reply[:1].hex())
    (v/'carried-outcome.bin').write_bytes(reply[1:])
    sh(m['host'],m['config'],'inspect','outcome',v/'carried-outcome.bin',v/'carried-outcome.json',out=v/'inspect.log')
    receipt=json.loads((v/'carried-outcome.json').read_text())
    if receipt.get('type')!='confirmed' or receipt.get('confirmation')!='installed':
        raise SystemExit('carried reply is not an installed receipt: '+json.dumps(receipt))
    # The member's own retained attempt recovers the receipt by READ-ONLY lookup.
    printed=sh(m['mini'],'retry','--attempt',attempt,'--mode','lookup','--socket',m['socket'],out=v/'retry-lookup.log')
    looked=receipt_fields(json.loads(printed))
    after=read_height(m,'effect-after')
    got=field(after,'3')
    same=looked is not None and all(looked.get(k)==receipt.get(k) for k in ['transactionId','eventId','acceptedCount','worldRoot'])
    # Exactly one accepted record between the last direct write and this one.
    one=int(receipt['acceptedCount'])==int(man['acceptedCountBefore'])+1
    result={'type':'minidregg-cohort-new-effect-verification-v1',
        'carriedReceipt':receipt,'lookupReceipt':looked,'lookupMatchesCarried':same,
        'acceptedCountBefore':man['acceptedCountBefore'],'exactlyOneAcceptedRecord':one,
        'readback':{'field':'3','value':got,'expected':man['effect']['value']},
        'callSha256':man['callSha256'],'nativeReplySha256':hashlib.sha256(reply).hexdigest()}
    (v/'verification.json').write_text(json.dumps(result,indent=1))
    if not same:raise SystemExit('lookup receipt differs from the carried receipt')
    if not one:raise SystemExit('the Store did not advance by exactly one accepted record')
    if got!=man['effect']['value']:raise SystemExit(f'readback {got!r} != {man["effect"]["value"]!r}')
    print(v/'verification.json')

elif a.verb=='stop':
    m=meta();pid=m['serverPid']
    args=open(f'/proc/{pid}/cmdline','rb').read().split(b'\0') if os.path.exists(f'/proc/{pid}') else []
    if b'serve' in args and m['socket'].encode() in args:
        os.kill(pid,signal.SIGTERM)
        for _ in range(300):
            if not os.path.exists(f'/proc/{pid}'):break
            time.sleep(.1)
        print('stopped',pid)
    else:print('not running (or not ours)',pid)
