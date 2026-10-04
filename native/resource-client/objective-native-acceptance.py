#!/usr/bin/env python3
"""The native Objective Accepted receipt on a scratch world, and its refusals.

A fresh private one-sponsor Store (newparticipant-acceptance.sh) whose genesis
pins an Objective invocation policy (tariff, output codecs, the parser/frontend/
elaborator pins of THIS checkout's tools). Never a live or common world.

  world    --bin DIR --root NEW_DIR [--tariff-base N --tariff-tick N] [--disable EVALUATOR-NAMES]
           policy authoring, genesis, `mini serve`, two content documents
           (`source` holds the published method, `notes` is its input and
           its effect/result target).
  publish  --root W [--method FILE.obend --entry NAME]
           pinned frontend capture, pinned elaborator, package input, the
           Host's objective-publication author, and an ordinary content
           proposal of the package and artifact atoms on `source`.
  invoke   --root W --label L [--byte B]
           fresh nonce; signed resource-scope queries of `source` and `notes`
           (that nonce); the retained request; `mini objective-invoke` (local
           quote, prepare intent, plan, endpoint-227 consent, assemble, submit).
  refuse   --root W --label L --mutation M [--argument X|@variant] [--move-source LABEL]
           a DISHONEST signer: the honest quote's command mutated by
           tests/objective-native/Mutate.lean, signed through the ordinary
           plan consent, submitted; the Host must refuse and the judged height
           and notes root must not move.
  publish-variant --root W --label L
           the same method under a package naming another elaborator.
  retry-submit --root W --label L
           submit a retained (prepare-only) call later.
  readback --root W --label L
           a signed read of `notes`; the created atom and the result atom.
  lookup   --root W --label L
           lost reply: the read-only lookup and the exact re-submission of the
           retained call; both must return the SAME receipt (no second record).
  reopen   --root W
           stop this world's own `mini serve` and start it again on the same
           Store: replay re-admits every record, the Objective one included.
  stop     --root W
Every step writes its exact command output under ROOT/transcript/.
"""
import argparse,hashlib,json,os,pathlib,secrets,subprocess,sys,time
os.umask(0o077)
HERE=pathlib.Path(__file__).resolve().parent
REPO=HERE.parent.parent
ap=argparse.ArgumentParser()
ap.add_argument('verb',choices=['all','world','publish','publish-variant','invoke','refuse','retry-submit','readback','lookup','reopen','stop'])
for f in ['bin','root','method','entry','label','byte','tariff-base','tariff-tick','request-edit','mutation','argument','expect','prepare-only','move-source','disable']:
    ap.add_argument('--'+f)
a=ap.parse_args()
root=pathlib.Path(a.root).resolve()
T=root/'transcript'

def sh(tag,*cmd,ok=(0,),env=None,cwd=None):
    T.mkdir(parents=True,exist_ok=True)
    e=dict(os.environ);e.update(env or {})
    r=subprocess.run([str(c) for c in cmd],stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=e,cwd=cwd)
    (T/f'{tag}.cmd').write_text(' '.join(str(c) for c in cmd)+'\n')
    (T/f'{tag}.out').write_bytes(r.stdout);(T/f'{tag}.err').write_bytes(r.stderr)
    (T/f'{tag}.rc').write_text(f'{r.returncode}\n')
    if r.returncode not in ok:
        raise SystemExit(f'FAILED {tag} rc={r.returncode}: {r.stderr.decode(errors="replace")[-1500:]}')
    return r
def state():return json.loads((root/'state.json').read_text())
def save(s):(root/'state.json').write_text(json.dumps(s,indent=1)+'\n')
def enc_nat(v):
    out=[]
    while v>0:out.append(v%255);v//=255
    return bytes(out+[255])
def digest_hex(decimal):return enc_nat(int(decimal)).hex()
def canonical(obj):return json.dumps(obj,sort_keys=True,separators=(',',':'),ensure_ascii=False)
def ref(s,name):return json.loads((pathlib.Path(s['sponsor'])/'refs'/f'{name}.json').read_text())

CAP_KEYS=['typeFuel','sourceTicks','heap','stack','outputNodes','outputBytes','inputBytes','scalarBits',
  'memoryTouches','proofWork','feeDebit','turnBytes','witnessBytes','storageBytes','sideEffectCount',
  'networkBytes','leaseByteBlocks','incidences']
MAXIMUM={'typeFuel':16384,'sourceTicks':200000,'heap':200000,'stack':200000,'outputNodes':20000,
  'outputBytes':200000,'inputBytes':200000,'scalarBits':512,'memoryTouches':2000000,'proofWork':900000,
  'feeDebit':1000000,'turnBytes':4000000,'witnessBytes':4000000,'storageBytes':4000000,'sideEffectCount':16,
  'networkBytes':0,'leaseByteBlocks':0,'incidences':16}
ENVELOPE={'typeFuel':16384,'sourceTicks':100000,'heap':100000,'stack':100000,'outputNodes':10000,
  'outputBytes':100000,'inputBytes':100000,'scalarBits':512,'memoryTouches':1000000,'feeDebit':0,
  'turnBytes':2000000,'witnessBytes':2000000,'storageBytes':2000000,'sideEffectCount':8,
  'networkBytes':0,'leaseByteBlocks':0,'incidences':8}
TARIFF_KEYS=['typeFuel','sourceTicks','heap','stack','outputNodes','outputBytes','inputBytes']
def price(tariff,c):return int(tariff['base'])+sum(int(tariff[k])*int(c[k]) for k in TARIFF_KEYS)

if a.verb=='all':
    # The complete acceptance on one fresh world, one binary set.
    me=[sys.executable,__file__]
    def step(*args):
        r=subprocess.run(me+list(args),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        line=r.stdout.decode(errors='replace').strip().splitlines()[-1:] or ['']
        print(' '.join(args[:5]),'->',line[0][:300],flush=True)
        if r.returncode:raise SystemExit(f'step {args} failed: {r.stderr.decode(errors="replace")[-1500:]}')
    W=['--root',str(root)]
    step('world','--bin',a.bin,*W)
    step('publish',*W)
    step('invoke',*W,'--label','first')
    step('readback',*W,'--label','first')
    step('lookup',*W,'--label','first')
    step('refuse',*W,'--label','r01-source-is-package','--mutation','source-atom','--argument','@package')
    step('invoke',*W,'--label','r02-core-differs-from-replay','--request-edit',str(HERE/'objective-native-edit-core.py'),'--expect','refused')
    step('publish-variant',*W,'--label','pin')
    step('refuse',*W,'--label','r03-elaborator-pin','--mutation','source-atom','--argument','@pin')
    step('refuse',*W,'--label','r04-foreign-capability','--mutation','capability','--argument','@source-operation')
    step('refuse',*W,'--label','r05-query-nonce','--mutation','command-nonce')
    step('invoke',*W,'--label','r06-stale','--prepare-only','true','--expect','prepared')
    step('invoke',*W,'--label','second','--byte','5')
    step('retry-submit',*W,'--label','r06-stale')
    # The source document moves (another publication) after an honest call was
    # signed: only the route's consumed-read guards bind the source cell.
    step('invoke',*W,'--label','r11-source-moved','--prepare-only','true','--expect','prepared')
    step('publish-variant',*W,'--label','moved')
    step('retry-submit',*W,'--label','r11-source-moved')
    step('refuse',*W,'--label','r12-stale-source-query','--mutation','none','--move-source','moved-again')
    step('refuse',*W,'--label','r07-credits-not-quote','--mutation','fee-debit')
    step('refuse',*W,'--label','r08-tariff','--mutation','tariff')
    step('refuse',*W,'--label','r09-altered-argument','--mutation','argument')
    step('refuse',*W,'--label','r10-injected-output','--mutation','output')
    step('lookup',*W,'--label','second')
    step('reopen',*W)
    step('lookup',*W,'--label','first')
    step('lookup',*W,'--label','second')
    step('readback',*W,'--label','after-reopen')
    # A second world whose operator disabled Core4 by name: no Objective
    # invocation is admitted there (the quote refuses before any signature).
    D=['--root',str(root)+'-disabled']
    step('world','--bin',a.bin,*D,'--disable','objective-core4')
    step('publish',*D)
    step('invoke',*D,'--label','r13-core4-disabled','--expect','refused')
    for p in (pathlib.Path(str(root)+'-disabled')/'results').glob('*.json'):
        if not p.name.endswith('.dry.json'):(root/'results'/p.name).write_bytes(p.read_bytes())
    rows=[json.loads(p.read_text()) for p in sorted((root/'results').glob('*.json')) if not p.name.endswith('.dry.json')]
    def ok(row):
        if row['expect']=='confirmed':return row['rc']==0 and not row['unchanged']
        if row['expect']=='prepared':return row['rc']==0 and row['unchanged']
        return row['refused'] and row['unchanged']
    summary={'world':str(root),'rows':[{k:row.get(k) for k in ['label','expect','rc','unchanged','reason','detail']}|{'pass':ok(row)} for row in rows]}
    summary['allPass']=all(r['pass'] for r in summary['rows'])
    (root/'results'/'summary.json').write_text(json.dumps(summary,indent=1)+'\n')
    print(json.dumps({'allPass':summary['allPass'],'rows':len(rows)}))
    if not summary['allPass']:raise SystemExit('acceptance failed: see results/summary.json')

elif a.verb=='world':
    bin_=pathlib.Path(a.bin).resolve()
    host,mini,store,verifier=[bin_/n for n in ['minidregg-host','mini','minidregg-link-sqlite-store',
        'minidregg-credential-signature-verifier']]
    for p in [host,mini,store,verifier,bin_/'minidregg-client-consent']:
        if not p.is_file():raise SystemExit(f'missing {p}')
    if root.exists():raise SystemExit('root exists')
    root.mkdir(mode=0o700);T.mkdir()
    pins=json.loads(sh('pins','bun',REPO/'native/bend-source/objective-source-package.ts','--pins').stdout)
    constants=json.loads(sh('constants',host,'/dev/null','objective-constants').stdout)
    tariff={'version':'1','base':a.tariff_base or '1','typeFuel':'0','sourceTicks':a.tariff_tick or '1','heap':'0',
        'stack':'0','outputNodes':'0','outputBytes':'0','inputBytes':'0'}
    policy={'schema':'dregg.objective-bend.policy.v1','sourceBytes':'4194304',
        'maximum':{k:str(v) for k,v in MAXIMUM.items()},'outputs':[constants['genericCodec']],
        'clearAudience':digest_hex(1),'tooling':pins,'tariff':tariff}
    (root/'policy.json').write_text(json.dumps(policy,indent=1))
    sh('policy',host,'/dev/null','author','objective-policy',root/'policy.json',root/'policy.hex')
    policy_hex=(root/'policy.hex').read_text().strip()
    w=root/'w';sock=w/'public'/'mini.sock'
    genesis_env={'OBJECTIVE_INVOCATION_POLICY':policy_hex}
    if a.disable:genesis_env['NEWPARTICIPANT_DISABLED_EVALUATORS']=a.disable
    sh('genesis','sh',HERE/'newparticipant-acceptance.sh',host,mini,store,verifier,w,sock,env=genesis_env)
    s={'type':'minidregg-objective-native-acceptance-v1','root':str(root),'bin':str(bin_),'host':str(host),
       'mini':str(mini),'config':str(w/'deployment'/'pinned-config.json'),'socket':str(sock),
       'sponsor':str(w/'sponsor'),'key':str(w/'sponsor.key'),'subject':'7',
       'serverPid':int((w/'public'/'server.pid').read_text()),'constants':constants,'pins':pins,
       'tariff':tariff,'policyHex':policy_hex,
       'hostSha256':hashlib.sha256(host.read_bytes()).hexdigest(),
       'miniSha256':hashlib.sha256(mini.read_bytes()).hexdigest()}
    (root/'permit-all.json').write_text('{"type":"all","predicates":[]}\n')
    for name in ['source','notes']:
        sh(f'create-{name}',mini,'workspace','--action','create','--dir',s['sponsor'],'--name',name,
           '--storage','content','--predicate',root/'permit-all.json')
    save(s);print(root/'state.json')

elif a.verb=='publish':
    s=state();host=s['host'];mini=s['mini']
    method=pathlib.Path(a.method or REPO/'world'/'NativeReceipt.obend').resolve()
    entry=a.entry or 'note'
    pub=root/'publication';pub.mkdir(mode=0o700)
    spec={'schema':'dregg.objective-bend.package-input.v1','edition':'objective-bend-1',
        'modules':[{'name':method.stem,'sourcePath':str(method),'imports':[]}],'entryModule':'0','entryDefinition':entry}
    (pub/'spec.json').write_text(json.dumps(spec))
    sh('frontend','bun',REPO/'native/bend-source/objective-frontend.ts',pub/'spec.json',pub/'cap')
    limits=json.dumps({'heap':'100000','stack':'100000','ticks':'100000','typeFuel':'16384'})
    sh('elaborate','bun',REPO/'native/bend-source/objective-elaborate.ts',pub/'cap'/'objective.json',pub/'def',
       '[]','[]',limits,'definition')
    sh('package-input','bun',REPO/'native/bend-source/objective-source-package.ts',pub/'cap'/'objective.json',
       pub/'package-input.json')
    core=pub/'def.typed.json'
    if not core.exists():raise SystemExit('elaborator wrote no def.typed.json: '+' '.join(p.name for p in pub.iterdir()))
    sh('publication',host,s['config'],'objective-publication',pub/'package-input.json',core,'generic',pub/'out')
    out=json.loads((pub/'out'/'publication.json').read_text())
    req={'type':'minidregg-workspace-proposal-v1','action':'invoke','targets':[{'name':'source','payload':out['payload']}]}
    (pub/'proposal.json').write_text(json.dumps(req))
    pid='objective-publish-'+secrets.token_hex(4)
    sh('publish-propose',mini,'workspace','--action','propose','--dir',s['sponsor'],'--request',pub/'proposal.json',
       '--proposal-id',pid)
    sh('publish-submit',mini,'workspace','--action','submit','--dir',s['sponsor'],
       '--intent',pathlib.Path(s['sponsor'])/'proposals'/pid/'intent.json',
       '--attempt',pathlib.Path(s['sponsor'])/'attempts'/pid)
    s['publication']={'artifactId':out['artifactId'],'packageId':out['packageId'],
        'package':str(pub/'out'/'package.bin'),'artifact':str(pub/'out'/'artifact.bin'),'attempt':pid}
    save(s);print(json.dumps(s['publication']))

def height_and_root(tag):
    """The judged height and the notes root from a signed read (reads commit nothing)."""
    s=state()
    sh(tag,s['mini'],'workspace','--action','read','--dir',s['sponsor'],'--name','notes')
    v=json.loads((T/f'{tag}.out').read_text())
    return {'height':v['judgedAt']['height'],'notesRoot':v['cell']['root'],'worldRoot':v['judgedAt']['worldRoot']}

def build_request(s,label,byte=7):
    host=s['host'];mini=s['mini']
    d=root/'invocations'/label;d.mkdir(parents=True,mode=0o700)
    nonce=str(secrets.randbelow(2**62)+1)
    reads={}
    for name in ['source','notes']:
        r=ref(s,name)
        q={'subject':s['subject'],'nonce':nonce,
           'purpose':{'type':'query','kind':r['kind'],'target':r['target'],'view':'resource-scope'},
           'grants':[{'kind':r['kind'],'target':r['target'],'capability':r['observeCapability']}]}
        (d/f'query-{name}.json').write_text(json.dumps(q))
        sh(f'{label}-query-{name}',mini,'query','--socket',s['socket'],'--host',host,'--config',s['config'],
           '--intent',d/f'query-{name}.json','--key',s['key'],'--view','resource-scope','--dir',d/f'q-{name}')
        reads[name]={'ref':r,'view':json.loads((T/f'{label}-query-{name}.out').read_bytes() or b'{}')}
    (d/'reads.json').write_text(json.dumps(reads,indent=1))
    def root_of(name):
        v=reads[name]['view']
        try:return v['resource']['cell']['root']
        except (KeyError,TypeError):raise SystemExit(f'no root in the {name} read: {json.dumps(v)[:400]}')
    def input_ref(name):
        r=reads[name]['ref']
        return {'kind':r['kind'],'resource':r['target'],'root':digest_hex(root_of(name)),'capability':r['observeCapability']}
    pubs=s['publication']
    arguments=canonical({'schema':'dregg.objective-bend.argument-values.v1','values':[{'tag':'record','fields':[
        {'name':'atom','value':{'tag':'label','value':digest_hex(secrets.randbelow(2**60)+2**61)}},
        {'name':'schema','value':{'tag':'label','value':digest_hex(4242)}},
        {'name':'byte','value':{'tag':'natural','value':str(int(byte))}}]}]})
    capacity=dict(ENVELOPE);capacity['proofWork']=price(s['tariff'],capacity)
    notes=reads['notes']['ref']
    request={'schema':'dregg.objective-bend.request.v1','subject':s['subject'],'nonce':nonce,
        'source':{'ref':input_ref('source'),'atom':digest_hex(pubs['artifactId']),
            'expectedArtifact':pathlib.Path(pubs['artifact']).read_bytes().hex(),
            'expectedPackage':pathlib.Path(pubs['package']).read_bytes().hex(),
            'envelope':(d/'q-source'/'signed-observation.bin').read_bytes().hex()},
        'arguments':arguments,'inputRefs':[input_ref('notes')],
        'inputEnvelopes':[(d/'q-notes'/'signed-observation.bin').read_bytes().hex()],
        'capacity':{k:str(capacity[k]) for k in CAP_KEYS},
        'inputCodec':s['constants']['inputCodec'],'outputCodec':s['constants']['genericCodec'],
        'roles':[{'kind':notes['kind'],'resource':notes['target'],'capability':notes['operationCapability'],
            'schemaVersion':'9','root':digest_hex(root_of('notes')),'observeCapability':notes['observeCapability']}],
        'resultResource':notes['target']}
    if a.request_edit:exec(pathlib.Path(a.request_edit).read_text(),{'request':request,'s':s,'digest_hex':digest_hex})
    (d/'request.json').write_text(json.dumps(request,indent=1))
    return d

def diagnose(label,attempt):
    """Operator-local reason for a refused submission: the Host's dry run of the
    retained observation and signatures (DryRun.dryRun_commits_nothing), whose
    outcome names the exact Reject the public reply leaves undisclosed."""
    s=state();attempt=pathlib.Path(attempt)
    obs,sig=attempt/'signed-observation.bin',attempt/'transaction-signatures.bin'
    if not (obs.exists() and sig.exists()):
        # Refused before any transaction signature: the Host's prepare (whose
        # reply names its reason) or the local quote/consent.
        import re
        text=b''.join((T/f'{label}-{x}.err').read_bytes() for x in ['submit','invoke'] if (T/f'{label}-{x}.err').exists()).decode(errors='replace')
        m=re.findall(r'(Minidregg\.[A-Za-z.]*Reject\.[A-Za-z]+)',text)
        stage='host prepare' if 'host refused prepare' in text else 'client (quote/consent, before signing)'
        last=[l for l in text.strip().splitlines() if l.strip()][-1:] or ['']
        return {'reason':stage,'detail':m[-1] if m else last[0][-300:]}
    out=root/'results'/f'{label}.dry.bin';out.parent.mkdir(exist_ok=True)
    sh(f'{label}-dry',s['host'],s['config'],'dry-run',obs,sig,out,ok=(0,3))
    sh(f'{label}-dry-inspect',s['host'],s['config'],'inspect','outcome',out,out.with_suffix('.json'))
    v=json.loads(out.with_suffix('.json').read_text())
    dec=lambda h:bytes.fromhex(h).decode(errors='replace') if isinstance(h,str) else h
    return {'reason':v.get('reason'),'phase':dec(v.get('phase')),'detail':dec(v.get('detail')),'dryType':v.get('type')}

def record(label,expect,before,after,r,extra=None):
    row={'label':label,'expect':expect,'rc':r.returncode,'before':before,'after':after,
        'unchanged':before==after,'refused':r.returncode!=0,
        'diagnostic':(r.stderr.decode(errors='replace').strip().splitlines() or [''])[-1][-600:]}
    if extra:row.update(extra)
    (root/'results').mkdir(exist_ok=True)
    (root/'results'/f'{label}.json').write_text(json.dumps(row,indent=1)+'\n')
    print(json.dumps(row))
    return row

if a.verb=='invoke':
    s=state();host=s['host'];mini=s['mini'];label=a.label
    d=build_request(s,label,int(a.byte or 7))
    intent_nonce=str(secrets.randbelow(2**62)+1)
    attempt=pathlib.Path(s['sponsor'])/'attempts'/f'objective-{label}'
    before=height_and_root(f'{label}-before')
    extra=['--prepare-only','true'] if a.prepare_only else []
    r=sh(f'{label}-invoke',mini,'objective-invoke','--socket',s['socket'],'--host',host,'--config',s['config'],
       '--request',d/'request.json','--intent-nonce',intent_nonce,'--key',s['key'],'--dir',attempt,*extra,ok=(0,1,2,3))
    (d/'attempt.txt').write_text(str(attempt)+'\n')
    after=height_and_root(f'{label}-after')
    record(label,a.expect or 'confirmed',before,after,r,{'attempt':str(attempt),
        'stdout':r.stdout.decode(errors='replace')[-1500:],**(diagnose(label,attempt) if r.returncode!=0 else {})})

elif a.verb=='refuse':
    s=state();host=s['host'];mini=s['mini'];label=a.label
    d=build_request(s,label)
    sh(f'{label}-author',host,s['config'],'author','objective-request',d/'request.json',d/'request.bin')
    sh(f'{label}-quote',host,s['config'],'objective-quote',d/'request.bin',str(secrets.randbelow(2**62)+1),d/'quote.json')
    if a.move_source:
        # The source document moves AFTER the honest quote: the signed queries
        # now name a root the Host no longer holds.
        r=subprocess.run([sys.executable,__file__,'publish-variant','--root',str(root),'--label',a.move_source],
            stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        if r.returncode:raise SystemExit('move-source publication failed: '+r.stderr.decode(errors='replace')[-800:])
        s=state()
    argument=[a.argument] if a.argument else []
    def resolve(x):
        if not x.startswith('@'):return x
        name=x[1:]
        if name=='package':return s['publication']['packageId']
        if name.endswith('-operation'):return ref(s,name[:-len('-operation')])['operationCapability']
        return s['variants'][name]
    argument=[resolve(x) for x in argument]
    sh(f'{label}-mutate','lake','env','lean','--run',REPO/'tests/objective-native/Mutate.lean',a.mutation,
       d/'quote.json',str(secrets.randbelow(2**62)+1),d/'mutated-intent.bin',*argument,cwd=REPO)
    attempt=pathlib.Path(s['sponsor'])/'attempts'/f'dishonest-{label}'
    before=height_and_root(f'{label}-before')
    r=sh(f'{label}-submit',mini,'submit','--socket',s['socket'],'--host',host,'--config',s['config'],
       '--intent',d/'mutated-intent.bin','--intent-kind','binary','--key',s['key'],'--dir',attempt,ok=(0,1,2,3))
    after=height_and_root(f'{label}-after')
    record(label,a.expect or 'refused',before,after,r,{'mutation':a.mutation,'argument':argument,'attempt':str(attempt),
        **(diagnose(label,attempt) if r.returncode!=0 else {})})

elif a.verb=='retry-submit':
    s=state();label=a.label
    attempt=(root/'invocations'/label/'attempt.txt').read_text().strip()
    before=height_and_root(f'{label}-resubmit-before')
    r=sh(f'{label}-resubmit',s['mini'],'retry','--attempt',attempt,'--mode','submit',ok=(0,1,2,3))
    after=height_and_root(f'{label}-resubmit-after')
    record(f'{label}-resubmit',a.expect or 'refused',before,after,r,{'attempt':attempt,
        **(diagnose(f'{label}-resubmit',attempt) if r.returncode!=0 else {})})

elif a.verb=='publish-variant':
    # A second artifact of the SAME method whose package names an elaborator
    # other than the policy's: the receiver must refuse it by the pin alone.
    s=state();host=s['host'];mini=s['mini']
    pub=root/'publication';v=root/f'variant-{a.label}';v.mkdir(mode=0o700)
    pin=json.loads((pub/'package-input.json').read_text())
    # A well-formed pin naming no elaborator the policy admits (one per label,
    # so two variants are two packages).
    pin['elaboratorSha256']=hashlib.sha256(f'not-the-pinned-elaborator:{a.label}'.encode()).hexdigest()
    (v/'package-input.json').write_text(json.dumps(pin))
    sh(f'variant-{a.label}-publication',host,s['config'],'objective-publication',v/'package-input.json',
       pub/'def.typed.json','generic',v/'out')
    out=json.loads((v/'out'/'publication.json').read_text())
    (v/'proposal.json').write_text(json.dumps({'type':'minidregg-workspace-proposal-v1','action':'invoke',
        'targets':[{'name':'source','payload':out['payload']}]}))
    pid=f'variant-{a.label}-'+secrets.token_hex(4)
    sh(f'variant-{a.label}-propose',mini,'workspace','--action','propose','--dir',s['sponsor'],'--request',
       v/'proposal.json','--proposal-id',pid)
    sh(f'variant-{a.label}-submit',mini,'workspace','--action','submit','--dir',s['sponsor'],
       '--intent',pathlib.Path(s['sponsor'])/'proposals'/pid/'intent.json','--attempt',pathlib.Path(s['sponsor'])/'attempts'/pid)
    s.setdefault('variants',{})[a.label]=out['artifactId'];s['variants'][a.label+'-package']=out['packageId']
    save(s);print(json.dumps({'variant':a.label,'artifactId':out['artifactId'],'elaboratorSha256':pin['elaboratorSha256']}))

elif a.verb=='readback':
    # A signed read of `notes`; for every confirmed invocation, the return atom
    # its quote derived (id, exact bytes) must be stored there, and the created
    # atom with the requested byte.
    s=state()
    sh(f'{a.label}-readback',s['mini'],'workspace','--action','read','--dir',s['sponsor'],'--name','notes')
    view=json.loads((T/f'{a.label}-readback.out').read_text())
    atoms={e['id']:e for e in view['cell']['entries'] if e.get('type')=='atom'}
    checks=[]
    for d in sorted((root/'invocations').iterdir()):
        att=d/'attempt.txt'
        if not att.exists():continue
        attempt=pathlib.Path(att.read_text().strip())
        outcome=attempt/'outcome.json'
        if not outcome.exists() or json.loads(outcome.read_text()).get('type')!='confirmed':continue
        quote=json.loads((attempt/'quote.json').read_text())
        for ret in quote['returns']:
            stored=atoms.get(ret['atom'])
            checks.append({'invocation':d.name,'returnAtom':ret['atom'],'stored':stored is not None,
                'bytesExact':stored is not None and stored['payload']==ret['payload'],'value':ret['value']})
    out={'height':view['judgedAt']['height'],'notesRoot':view['cell']['root'],'atoms':len(atoms),'returns':checks}
    (root/'results').mkdir(exist_ok=True)
    (root/'results'/f'readback-{a.label}.json').write_text(json.dumps(out,indent=1)+'\n')
    print(json.dumps(out))
    if not checks or not all(c['stored'] and c['bytesExact'] for c in checks):
        raise SystemExit('a return atom of a confirmed invocation is not stored exactly')

elif a.verb=='lookup':
    s=state();attempt=(root/'invocations'/a.label/'attempt.txt').read_text().strip()
    out={}
    for mode in ['lookup','submit']:
        r=sh(f'{a.label}-retry-{mode}',s['mini'],'retry','--attempt',attempt,'--mode',mode)
        out[mode]=json.loads(r.stdout)
    original=json.loads((pathlib.Path(attempt)/'outcome.json').read_text())
    same=all(out[m][k]==original[k] for m in out for k in ['transactionId','eventId','acceptedCount','worldRoot'])
    print(json.dumps({'original':original,'retries':out,'sameReceipt':same}))
    if not same:raise SystemExit('lost-reply recovery returned a different receipt')

elif a.verb=='reopen':
    s=state()
    try:os.kill(s['serverPid'],15)
    except ProcessLookupError:pass
    sock=pathlib.Path(s['socket'])
    for _ in range(600):
        try:os.kill(s['serverPid'],0);time.sleep(0.1)
        except ProcessLookupError:break
    if sock.exists():sock.unlink()
    log=open(root/'w'/'public'/'serve-reopen.log','ab')
    p=subprocess.Popen([s['mini'],'serve','--host',s['host'],'--config',s['config'],'--socket',str(sock)],
        stdout=log,stderr=log,stdin=subprocess.DEVNULL,start_new_session=True)
    t0=time.time()
    while not sock.exists():
        if p.poll() is not None:raise SystemExit('reopened server exited: see serve-reopen.log')
        if time.time()-t0>600:raise SystemExit('reopened server socket did not appear')
        time.sleep(0.2)
    s['serverPid']=p.pid;s.setdefault('reopens',[]).append({'pid':p.pid,'seconds':round(time.time()-t0,1)})
    save(s);print(json.dumps(s['reopens'][-1]))

elif a.verb=='stop':
    s=state()
    try:os.kill(s['serverPid'],15)
    except ProcessLookupError:pass
    print('stopped',s['serverPid'])
