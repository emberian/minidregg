#!/usr/bin/env python3
"""Two funded Mini members and controllers share one inference capacity group.

Requires Linux user systemd, bwrap, jq, PyNaCl and sudo -n install for the two
operator-owned fixture inventories. Scripted ACP/HTTP uses no paid API. Retains
all artifacts; --continue-funded preserves a failed pre-HTTP Store and journals.
"""
import argparse, ast, hashlib, http.server, json, os, pathlib, shutil, signal, socket, urllib.parse
import struct, subprocess, sys, threading, time

p = argparse.ArgumentParser()
for name in ('repo', 'manifest', 'mini', 'grain', 'scheduler', 'launch-gate', 'run'):
    p.add_argument('--' + name, required=True)
p.add_argument('--task', type=int, default=8911)
p.add_argument('--task2', type=int, default=8921)
p.add_argument('--continue-funded', action='store_true', help='resume exact funded fixture only before its first provider receive')
p.add_argument('--repair-fixture-endpoints', action='store_true')
p.add_argument('--exhaustion-only', action='store_true', help='require automatic refusal cleanup, refill and successful reuse; never issue admin abort')
p.add_argument('--typed-acp-refusal', action='store_true', help='copied ACP fixture returns typed provider_refused errors on HTTP failures')
a = p.parse_args()
if a.typed_acp_refusal and not a.exhaustion_only:
    raise SystemExit('--typed-acp-refusal requires --exhaustion-only')
run_label='continued-'+str(time.time_ns()) if a.continue_funded else 'initial'
root = pathlib.Path(a.run)
if not root.is_absolute() or len(str(root)) > 55 or (root.exists() and not a.continue_funded):
    raise SystemExit('fresh absolute run directory <=55 bytes required')
os.umask(0o077)
root.mkdir(mode=0o700,exist_ok=a.continue_funded)
os.nice(10)
manifest = json.loads(pathlib.Path(a.manifest).read_text())
for role in ('host', 'store', 'verifier'):
    actual = hashlib.sha256(pathlib.Path(manifest[role]).read_bytes()).hexdigest()
    if actual != manifest['sha256'][role]: raise SystemExit('manifest pin differs: ' + role)
for binary in (a.mini, a.grain, a.scheduler, a.launch_gate):
    if not os.access(binary, os.X_OK): raise SystemExit('missing executable ' + binary)
units = [f'mini-grain-controller@{task}.service' for task in (a.task,a.task2)]
def ctl(*args):
    return subprocess.run(['systemctl', '--user', *args], capture_output=True, text=True, check=True).stdout.strip()
for unit in units:
    if ctl('show', unit, '-p', 'LoadState', '--value') != 'not-found':
        raise SystemExit('refusing existing controller unit '+unit)
def save(name, value):
    (root / name).write_text(json.dumps(value, indent=2))
def wait(label, predicate, timeout=300):
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        try:
            value = predicate()
            if value: return value
        except (OSError, ValueError, KeyError): pass
        time.sleep(.2)
    raise RuntimeError('timeout: ' + label)
rows = json.loads((root/'checks.json').read_text()) if a.continue_funded else []
if a.continue_funded:
    if (root/'received.json').exists() and json.loads((root/'received.json').read_text()):
        raise SystemExit('funded continuation refuses any prior provider receive; inspect exact later-stage recovery')
    if not any(r['check']=='member 21 native debit equals own purse gain' and r['passed'] for r in rows):
        raise SystemExit('funded continuation requires completed native two-member funding')
    prior=json.loads((root/'inputs.json').read_text())
    if prior['manifest'] != manifest: raise SystemExit('continuation Host/Store manifest differs')
    save(run_label+'-boundary.json',{'priorChecks':len(rows),'priorControllerBJournal':json.loads((root/'controller-b/journal.json').read_text()),'priorReceived':[]})
def check(label, condition, evidence):
    rows.append({'run':run_label,'check': label, 'passed': bool(condition), 'evidence': evidence})
    save('checks.json', rows)
    print(('PASS ' if condition else 'FAIL ') + label, flush=True)
    if not condition: raise RuntimeError(label)

# Reuse source-owned genesis/birth and native Book authoring helpers, stopping
# before the original journey. This script signs its own two-member funding;
# no live Store, external credentials or private user data are copied.
source = pathlib.Path(a.repo) / 'native/resource-client/journey.d/jpay6.sh'
raw = source.read_text()
code = raw.split('python3 - "$DIR" <<\'PY\'\n', 1)[1].split('# ---------------------------------------------------------------- the journey', 1)[0]
def insert(anchor, extra):
    global code
    if code.count(anchor) != 1: raise RuntimeError('bootstrap seam changed: ' + anchor)
    code = code.replace(anchor, extra + '\n' + anchor, 1)
insert('# ---------------------------------------------------------------- keys and genesis',
       'SUBJECTS.append(19)\nCAPS[19]=(44,58,59)\nBALANCE[19]=100\nBALANCE[20]=1000000\nBALANCE[21]=1000000')
insert('json.dump(operator, open(path("operator.json"), "w"), indent=1)',
       'service_tariff=operator.pop("providerMetering")["tariff"]\noperator.pop("continuityProviderResourceId")\noperator["providerServices"]=[{"providerResourceId":PURSE,"tariff":service_tariff},{"providerResourceId":'+str(a.task2+3)+',"tariff":service_tariff}]')
code=code.replace('for key in ("continuityProviderResourceId", "providerMetering"):', 'for key in ("providerServices",):')
insert('json.dump(genesis, open(path("genesis.json"), "w"), indent=1)',
       'genesis["clockTickers"]=[]\ngenesis["tailBound"]="256"')
insert('json.dump(birth, open(path("birth-intent.json"), "w"))',
       'import copy\nresources=birth["birth"]["resources"]\nresources[0]["budget"]="1000"\nresources[3]["owner"]="20"\nresources[3]["budget"]="0"\nsecond=copy.deepcopy(resources)\n'+
       'second[0].update(target="'+str(a.task2)+'",ownerCapability="171",controlCapability="172",workerSubjects=["8","19"])\n'+
       'second[1].update(target="'+str(a.task2+1)+'",ownerCapability="181",controlCapability="182")\n'+
       'second[2].update(target="'+str(a.task2+2)+'",ownerCapability="191",controlCapability="192")\n'+
       'second[3].update(target="'+str(a.task2+3)+'",owner="21",ownerCapability="111",controlCapability="112")\n'+
       'birth["birth"]["resources"]+=second')
os.environ.update(HOST=manifest['host'], MINI=a.mini, STORE=manifest['store'],
                  VERIFIER=manifest['verifier'], GRAIN=a.grain, TEST_PROVIDER='UNUSED',
                  REPO=a.repo, HERMES_STANDIN='UNUSED', LAUNCH_GATE=a.launch_gate,
                  JPAY6_BASE=str(a.task))
save(run_label+'-inputs.json' if a.continue_funded else 'inputs.json', {'arguments': vars(a), 'manifest': manifest,
     'binarySha256': {b: hashlib.sha256(pathlib.Path(b).read_bytes()).hexdigest()
                     for b in (a.mini, a.grain, a.scheduler, a.launch_gate)},
     'bootstrapSha256': hashlib.sha256(raw.encode()).hexdigest(),
     'journeySha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()})
shutil.copyfile(__file__,root/(run_label+'-journey.py' if a.continue_funded else 'journey.py'))
if a.continue_funded:
    head=code.split('# ---------------------------------------------------------------- keys and genesis',1)[0]
    definitions='\n'.join(ast.get_source_segment(code,node) for node in ast.parse(code).body if isinstance(node,(ast.FunctionDef,ast.ClassDef)))
    code=head+'''
keys={s:nacl.signing.SigningKey(open(path(f"keys/{s}.key"),"rb").read()) for s in SUBJECTS}
operator=json.load(open(path("operator.json")))
genesis=json.load(open(path("genesis.json")))
CONFIG=path("deployment/continuity-config.json")
SOCKET=path("session/host.sock")
ACTIVE=[CONFIG]
profile=json.loads(subprocess.run([HOST,CONFIG,"profile"],check=True,capture_output=True).stdout)
SEMANTICS=profile["semantics"]
query_nonce=[41000]
counter=[10000]
nonce=[10000]
PAY_OPS,REFILL_OPS=(103,104,105),(113,114,115)
born=json.load(open(path("birth-attempt/outcome.json")))
delegations=[json.load(open(path(name+"-attempt/outcome.json"))) for name in ("parent-witness-tool","parent-witness-provider","publication-tool","publication-read")]
'''+definitions
else:
    (root / 'bootstrap-extracted.py').write_text(code)
oldargv = sys.argv
sys.argv = [str(root / 'bootstrap-extracted.py'), str(root)]
ns = {'__name__': '__native_inference_bootstrap__'}
print('Native bootstrap', flush=True)
exec(compile(code, str(root / 'bootstrap-extracted.py'), 'exec'), ns)
sys.argv = oldargv
original_query=ns['mini_query']
def unique_query(label,*args): return original_query(run_label+'-'+label,*args)
ns['mini_query']=unique_query
check('native eight-resource first birth and initial delegated witnesses',
      ns['born'].get('type') == 'confirmed' and all(v.get('type') == 'confirmed' for v in ns['delegations']),
      {'birth': ns['born'], 'delegations': ns['delegations']})


# Complete native delegation and Book funding before any controller owns Store.
# Bootstrap leaves its temporary mini serve stopped. Reuse its sole Host stdio
# owner for Book setup; never open this beside the eventual persistent Host.
def delegate(label, owner, target, parent, child, holder, nonce, verbs=None):
    cell, authority=ns['mini_query'](label+'-pre',owner,target,parent)
    intent={'subject':str(owner),'nonce':str(nonce),'purpose':{'type':'prepare','draft':{
        'type':'delegate-source','command':{'kind':'object','domain':'8501','semantics':ns['SEMANTICS'],
        'subject':str(owner),'nonce':str(nonce+1),'expectedTargetRoot':cell['root'],
        'parentId':str(parent),'target':str(target),
        'child':{'id':str(child),'root':str(parent),'parent':str(parent),'issuer':'5',
        'holder':{'type':'subject','subject':str(holder)},'targets':[str(target)],'verbs':verbs or ['observe','mutate'],
        'maxCost':'50000','notBefore':'10','notAfter':'1000','issuerEpoch':'2','policyId':str(target),
        'policyEpoch':'0','ancestors':[str(parent)],'channels':[]}}}},
        'grants':[{'kind':'object','target':str(target),'capability':str(parent)}]}
    result=ns['mini_submit'](label,intent,owner)
    check(label,result.get('type')=='confirmed',result)
    return result
if not a.continue_funded:
    host=ns['Serve']()
    for args in [('member-a-provider-grant',20,a.task+3,101,103,9,32000),
                 ('member-b-provider-grant',21,a.task2+3,111,113,19,32010),
                 ('second-tool-witness',7,a.task2,171,173,8,32020),
                 ('second-provider-witness',7,a.task2,171,175,19,32030),
                 ('second-publication',7,a.task2+2,191,193,8,32040),
                 ('second-publication-read',7,a.task2+2,191,194,8,32050,['observe'])]: delegate(*args)
    host.stop()
    bookhost=ns['Host'](); v=ns['view'](bookhost)
    tariff={'version':'1','asset':'0','mint':'85'*32,'tokenProgram':'06'*32,'decimals':'6',
        'creditPerAtomic':'1','maxPerObservation':'2000000000','minTickSlots':'1500',
        'nodeWeekRate':'999999840','enrolIndex':None,'journalFloor':'1000000','slashCallerPermille':'500'}
    book={'sponsor':'7','control':'53','nonce':ns['fresh'](),'expectedFactoryRoot':v['factoryRoot'],
        'expectedAuthorityRoot':v['authorityRoot'],'expectedPayRoot':v['payRoot'],
        'bookStart':'0','book':['16'*32,'17'*32],'tariff':tariff}
    result,_=ns['sign_and_submit'](bookhost,'pay-book',book,7,ns['PAY_OPS'])
    check('native two-member Book tariff installed',result.get('type')=='confirmed',result)
    for owner,index in ((20,0),(21,1)):
        v=ns['view'](bookhost)
        assign={'subject':str(owner),'capability':str(ns['CAPS'][owner][0]),'account':str(owner),
            'index':str(index),'nonce':ns['fresh'](),'expectedAuthorityRoot':v['authorityRoot'],'expectedPayRoot':v['payRoot']}
        result,_=ns['sign_and_submit'](bookhost,'pay-assign',assign,owner,ns['PAY_OPS'])
        check('native member '+str(owner)+' assigns own Book account',result.get('type')=='confirmed',result)
    bookhost.stop()
    ledger_before=ns['ledger']()
    bookhost=ns['Host']()
    for owner,task,amount in ((20,a.task+3,12),(21,a.task2+3,6)):
        result,_=ns['refill'](bookhost,owner,ns['CAPS'][owner][0],owner,amount,amount,task)
        check('member '+str(owner)+' signs own account-to-purse refill',result.get('type')=='confirmed',result)
    bookhost.stop()
    ledger_after=ns['ledger']()
    for owner,task,amount in ((20,a.task+3,12),(21,a.task2+3,6)):
        purse=ns['purse'](task)
        check('member '+str(owner)+' native debit equals own purse gain',
            ns['balance'](ledger_before,owner)-ns['balance'](ledger_after,owner)==amount and purse['remaining']==str(amount) and purse['reserved']=='0',
            {'ledgerBefore':ledger_before,'ledgerAfter':ledger_after,'purse':purse})

received=[]; barriers={n:threading.Event() for n in ('a','b')}; completed=[]
for event in barriers.values(): event.set()
class Endpoint(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        member=self.server.member
        if self.path!='/v1/chat/completions': self.send_error(404); return
        body=self.rfile.read(int(self.headers['Content-Length']))
        number=len(received); received.append({'member':member,'digest':hashlib.sha256(body).hexdigest(),'authorization':self.headers.get('Authorization') is not None})
        save('received.json',received)
        if not barriers[member].wait(900): return
        chunks=[{'id':'members-fixture','object':'chat.completion.chunk','created':1,'model':ns['MODEL'],
            'choices':[{'index':0,'delta':{'role':'assistant','content':'fixture complete'},'finish_reason':'stop'}]},
            {'id':'members-fixture','object':'chat.completion.chunk','created':1,'model':ns['MODEL'],'choices':[],
             'usage':{'prompt_tokens':1,'completion_tokens':2,'total_tokens':3}}]
        body=(''.join('data: '+json.dumps(chunk)+'\n\n' for chunk in chunks)+'data: [DONE]\n\n').encode()
        try:
            self.send_response(200); self.send_header('Content-Type','text/event-stream'); self.send_header('Content-Length',str(len(body)))
            self.end_headers(); self.wfile.write(body); self.wfile.flush()
        except (BrokenPipeError,ConnectionResetError): pass
        finally: completed.append(number); save('physically-completed.json',completed)
    def log_message(self,*_): pass
existing_providers=json.loads((root/'providers.json-source.json').read_text()) if a.continue_funded else None
servers={}; endpoints={}
for index,name in enumerate(('a','b')):
    previous=existing_providers['providers'][index]['endpoint'] if existing_providers else None
    port=urllib.parse.urlsplit(previous).port if previous else 0
    if a.repair_fixture_endpoints and name=='b': port=0
    server=http.server.ThreadingHTTPServer(('127.0.0.1',port),Endpoint); server.member=name
    servers[name]=server; threading.Thread(target=server.serve_forever,daemon=True).start()
    endpoints[name]=f'http://127.0.0.1:{server.server_port}/v1/chat/completions'
for name in ('etc','credentials','launcher','broker','runtime-root'): (root/name).mkdir(mode=0o700,exist_ok=a.continue_funded)
runtime=root/'runtime-root'; runtime.chmod(0o755)
for source,name in ((a.grain,'grain-runtime'),(str(pathlib.Path(a.grain).parent/'grain-provider-bridge'),'grain-provider-bridge'),
    (str(pathlib.Path(a.repo)/'native/resource-client/journey.d/jpay6-hermes-acp'),'hermes-acp')):
    shutil.copyfile(source,runtime/name); (runtime/name).chmod(0o755)
fixture_path=runtime/'hermes-acp'
fixture_original=fixture_path.read_bytes()
if a.typed_acp_refusal:
    seam='        send({"jsonrpc": "2.0", "id": ident, "result": {"stopReason": "end_turn", "status": status}})'
    replacement='        if status >= 400:\n            failure={"jsonrpc":"2.0","id":ident,"error":{"code":-32003,\n                "message":"provider refused","data":{"type":"mini-hermes-turn-failure-v1",\n                "reason":"provider_refused","retryable":False,"detail":"bounded fixture refusal"}}}\n            with open("/workspace/typed-failures.jsonl","a") as log:\n                log.write(json.dumps(failure)+"\\n")\n            send(failure)\n        else:\n            send({"jsonrpc": "2.0", "id": ident, "result": {"stopReason": "end_turn", "status": status}})'
    copied=fixture_original.decode()
    if copied.count(seam)!=1: raise RuntimeError('typed ACP fixture seam changed')
    copied=copied.replace(seam,replacement)
    compile(copied,str(fixture_path),'exec')
    fixture_path.write_text(copied)
save('acp-fixture.json',{'source':str(pathlib.Path(a.repo)/'native/resource-client/journey.d/jpay6-hermes-acp'),
    'sourceSha256':hashlib.sha256(fixture_original).hexdigest(),
    'copiedSha256':hashlib.sha256(fixture_path.read_bytes()).hexdigest(),
    'typedRefusal':a.typed_acp_refusal,'scope':'scripted ACP process with real typed failure protocol; no upstream model'})
for source,name in ((str(pathlib.Path(a.repo)/'deploy/grain-host/bwrap'),'bwrap'),(a.launch_gate,'launch-gate')):
    shutil.copyfile(source,root/'launcher'/name); (root/'launcher'/name).chmod(0o700)
def inventory(name,value):
    if a.continue_funded:
        old=json.loads((root/(name+'-source.json')).read_text())
        if not a.repair_fixture_endpoints:
            if old != value: raise RuntimeError('continuation inventory differs: '+name)
            return
        if json.loads((root/'broker/state.json').read_text())['jobs']: raise RuntimeError('endpoint repair requires empty prior broker history')
        save(run_label+'-'+name+'-prior.json',old)
    save(name+'-source.json',value)
    subprocess.run(['sudo','-n','install','-o','root','-g','root','-m','0644',str(root/(name+'-source.json')),str(root/'etc'/name)],check=True)
inventory('providers.json',{'type':'mini-provider-table-v2','providers':[
    {'name':'member-'+name,'endpoint':endpoints[name],'kind':'openai-compatible','models':[ns['MODEL']],'credential':'homelab'} for name in ('a','b')]})
inventory('inference.json',{'version':1,'max_jobs':100,'max_queued_per_principal':8,'max_active_per_principal':1,
    'lease_ms':300000,'groups':{'shared-hardware':1},
    'controllers':{name:{'uid':os.getuid(),'principal':str(owner),'pool':'members'} for name,owner in (('a',20),('b',21))},
    'backends':{name:{'pool':'members','group':'shared-hardware','endpoint':endpoints[name],
        'models':{ns['MODEL']:{'context':32768,'max_output':100,'tools':True,'input_us':1,'output_us':1}}} for name in ('a','b')}})
broker_socket=root/'broker/control.sock'
state_pointer=root/'broker-state-directory.json'
if a.repair_fixture_endpoints:
    if not a.continue_funded: raise RuntimeError('endpoint repair requires preserved funded fixture')
    broker_directory=root/'broker-canonical'; broker_directory.mkdir(mode=0o700)
    save('broker-state-directory.json',{'path':str(broker_directory),'prior':str(root/'broker'),'reason':'zero-job invalid endpoint fixture inventory repaired'})
else: broker_directory=pathlib.Path(json.loads(state_pointer.read_text())['path']) if state_pointer.exists() else root/'broker'
def broker_status():
    result=subprocess.run([a.scheduler,'status',str(broker_socket)],capture_output=True)
    return json.loads(result.stdout) if result.returncode==0 else None
def start_broker():
    process=subprocess.Popen([a.scheduler,str(root/'etc/inference.json'),str(broker_directory),str(broker_socket)],stdout=open(root/'broker.log','ab'),stderr=subprocess.STDOUT)
    ns['LIVE'].append(process); wait('broker ready',broker_status); return process
def broker(command):
    frame=json.dumps(command).encode()
    with socket.socket(socket.AF_UNIX) as channel:
        channel.settimeout(10); channel.connect(str(broker_socket)); channel.sendall(struct.pack('>I',len(frame))+frame)
        def exact(length):
            data=b''
            while len(data)<length:
                chunk=channel.recv(length-len(data))
                if not chunk: raise RuntimeError('broker closed frame')
                data+=chunk
            return data
        value=json.loads(exact(struct.unpack('>I',exact(4))[0]))
    if value.get('type')=='refused': raise RuntimeError(value)
    return value
broker_process=start_broker()
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]/'mini-keys'))
import atexit, journey_broker
# The provider tasks' key broker: same account, production binary (native/mini-keys).
keys_proc,keys_client=journey_broker.start(root,a.mini,providers=root/'etc/providers.json',
    host=manifest['host'],host_config=ns['CONFIG'],public_socket=ns['SOCKET'])
atexit.register(keys_proc.kill)
members={}
for index,(name,task,owner,actor,pc,tc,pubc,cap,owner_cap,control_cap) in enumerate([
    ('a',a.task,20,9,71,81,91,103,101,102),('b',a.task2,21,19,171,181,191,113,111,112)]):
    state=root/('controller-'+name); work=root/('worker-'+name); state.mkdir(mode=0o700,exist_ok=a.continue_funded); work.mkdir(mode=0o700,exist_ok=a.continue_funded)
    with socket.socket() as probe: probe.bind(('127.0.0.1',0)); port=probe.getsockname()[1]
    config={'mini':a.mini,'host':manifest['host'],'hostConfig':ns['CONFIG'],'hostSocket':ns['SOCKET'],
        'controlSocket':str(state/'control.sock'),'custodyKey':str(root/'keys/7.key'),'stateDir':str(state),
        'cwd':str(root),'task':str(task),'subject':'7','capability':str(pc),'queryCapability':str(pc),'policyControlCapability':str(pc+1),
        'toolTask':{'task':str(task+1),'subject':'8','capability':str(tc),'queryCapability':str(tc),'custodyKey':str(root/'keys/8.key'),
            'parentCapability':str(pc+2),'parentObserveCapability':str(pc+2),'reserve':'2','charge':'1',
            'allowedPublications':[{'kind':'object','target':str(task+2),'capability':str(pubc+2),'observeCapability':str(pubc+2)}],
            'allowedReads':[{'name':'publication','kind':'object','target':str(task+2),'observeCapability':str(pubc+3),'maxResultBytes':65536}]},
        'providerTask':{'task':str(task+3),'subject':str(actor),'capability':str(cap),'queryCapability':str(cap),'custodyKey':str(root/f'keys/{actor}.key'),
            'parentCapability':str(pc+4),'parentObserveCapability':str(pc+4),'reserve':'3','maxInputTokens':1000,'maxOutputTokens':100,'maxIterations':1,
            'onBehalfOf':{'subject':str(owner),'publicKey':ns['keys'][owner].verify_key.encode().hex()},
            'model':ns['MODEL'],'provider':'member-'+name,'providers':str(root/'etc/providers.json'),
            'credentialBroker':str(keys_client),'gatewayBind':f'127.0.0.1:{port}',
            'maxRequestBytes':12000,'maxResponseBytes':1048576,'timeoutSeconds':600,'localFixtureHostNetwork':True,
            'homelab':{'socket':str(broker_socket),'controller':name,'domain':'8501:'+str(json.loads(pathlib.Path(ns['CONFIG']).read_text())['expectedSeed']),
                'principal':str(owner),'pool':'members','backends':['member-'+name],'queueTimeoutMs':300000}},
        'commands':[{'name':'hermes-acp','program':str(root/'launcher/bwrap'),
            'args':['--workspace',str(work),'--runtime-root',str(runtime),'--network','host','--','/agent/hermes-acp'],
            'systemdScope':True,'wallTimeSeconds':1500,'reserve':'3','charge':'1'}]}
    if a.continue_funded:
        previous=json.loads((root/('controller-'+name+'.json')).read_text())
        config['providerTask']['gatewayBind']=previous['providerTask']['gatewayBind']
        if config != previous: raise RuntimeError('continuation controller configuration differs: '+name)
    else: save('controller-'+name+'.json',config)
    members[name]={'task':task,'owner':owner,'actor':actor,'ownerCap':owner_cap,'controlCap':control_cap,
        'cap':cap,'state':state,'work':work,'unit':units[index],'config':config,'connector':None}
host=ns['Serve']()
def start_controller(name):
    m=members[name]; ns['UNITS'].append(m['unit']); launch_time=time.time_ns()
    subprocess.run(['systemd-run','--user','--collect','--unit='+m['unit'],'--property=Nice=10',
        '--property=KillMode=control-group','--property=Restart=on-failure','--property=RestartSec=2','--property=RuntimeMaxSec=5400s',
        '--property=StandardOutput=append:'+str(root/('controller-'+name+'.stdout')),
        '--property=StandardError=append:'+str(root/('controller-'+name+'.stderr')),a.grain,'serve',str(root/('controller-'+name+'.json'))],check=True,capture_output=True)
    wait('controller '+name+' fresh socket',lambda:(m['state']/'control.sock').exists() and (m['state']/'control.sock').stat().st_ctime_ns > launch_time)
def journal(name): return json.loads((members[name]['state']/'journal.json').read_text())
def connect(name):
    m=members[name]; output=root/('connector-'+name+'.stdout'); m['outputOffset']=output.stat().st_size if output.exists() else 0
    process=subprocess.Popen([a.grain,'connect',str(m['state']/'control.sock')],stdin=subprocess.PIPE,
        stdout=open(root/('connector-'+name+'.stdout'),'ab'),stderr=open(root/('connector-'+name+'.stderr'),'ab'))
    ns['LIVE'].append(process); m['connector']=process; return process
def send(name,text):
    stream=members[name]['connector'].stdin; stream.write((text+'\n').encode()); stream.flush()
def done(name):
    j=journal(name)
    return all(j.get(k) is None for k in ('providerAttempt','providerHold','pending','child','parentHold','toolHold')) and not j.get('settlementDue') and j.get('connection')=='soft'
def statuses(name):
    try: return [part for part in (members[name]['work']/'standin.log').read_text().split() if part.startswith('status=')]
    except FileNotFoundError: return []
def prompt(name,text):
    send(name,'conversation new'); wait(name+' new conversation',lambda:journal(name).get('hermesSession') is None)
    send(name,'hermes '+text)
def purse(name,label):
    m=members[name]; return ns['mini_query'](label,m['owner'],m['task']+3,m['ownerCap'])[0]['grain']
def finish_prompt(name,count):
    wait(name+' worker reply',lambda:len(statuses(name))>=count,600)
    wait(name+' native settlement',lambda:done(name),600)
for name in members:
    start_controller(name); connect(name); send(name,'attach soft')
    attempts=[0]; last_retry=[time.monotonic()]
    def attached(name=name):
        output=(root/('connector-'+name+'.stdout')).read_text()[members[name]['outputOffset']:]
        if 'attached soft to Mini grain '+str(members[name]['task']) in output and done(name): return True
        j=journal(name)
        if time.monotonic()-last_retry[0]>20 and attempts[0]<3 and j.get('pending') is None and j.get('child') is None and all(j.get(k) is None for k in ('parentHold','providerHold','toolHold')):
            if 'stale-root' in (root/('controller-'+name+'.stderr')).read_text()[-2500:]:
                send(name,'attach soft'); attempts[0]+=1; last_retry[0]=time.monotonic()
        return False
    wait(name+' native attach',attached,600)
check('two real same-owner controllers attach under distinct native namespaces',all(done(name) for name in members),{name:journal(name)['nextOperationId'] for name in members})
initial={name:purse(name,'initial-'+name) for name in members}
if a.exhaustion_only:
    # Keep this focused refusal qualification sequential. The full journey
    # separately exercises shared-machine queuing and concurrent settlement.
    prompt('a','member A baseline purse remains independent of B exhaustion')
    finish_prompt('a',1)
    prompt('b','member B first successful charge before exhaustion')
    finish_prompt('b',1)
else:
    barriers['a'].clear(); prompt('a','member A first request held until B queues')
    wait('A physical receive',lambda:len(received)==1,600)
    prompt('b','member B separate native purse waits for the same machine')
    wait('B queued behind A',lambda:broker_status()['counts']['queued']==1,600)
    check('two real controllers share one alias capacity group',len(received)==1 and broker_status()['counts']['running']==1,broker_status())
    barriers['a'].set(); finish_prompt('a',1); finish_prompt('b',1)
first={name:purse(name,'after-first-'+name) for name in members}
check('both native member purses settle separately at fee three',all(int(initial[name]['remaining'])-int(first[name]['remaining'])==3 and first[name]['reserved']=='0' for name in members),{'initial':initial,'after':first})
check('both member endpoints saw exactly one bearerless call',len(received)==2 and [r['member'] for r in received]==['a','b'] and not any(r['authorization'] for r in received),received)
cell,authority=ns['mini_query']('cross-purse-before',20,a.task+3,101)
intent={'grain':{'task':str(a.task+3),'subject':'19','capability':'103','observeCapability':'103','schemaVersion':'1',
    'expectedTargetRoot':cell['root'],'context':{'operationId':'64001','payload':'foreign provider actor attempts A purse'},
    'before':{field:cell['grain'][field] for field in ('generation','status','remaining','reserved','route')},
    'operation':{'type':'attach','soft':False},'publications':[]},
    'grants':[{'kind':'object','target':str(a.task+3),'capability':'103'}],'intentNonce':'64002'}
cross=ns['mini_submit']('cross-member-purse',intent,19,kind='grain-intent')
after_cross=purse('a','after-cross-purse')
cross_refusal=(root/'cross-member-purse.stderr').read_text()
cross_receipt=root/'cross-member-purse-attempt/pre-submit-refusal.json'
check('provider actor19 cannot use member20 purse grant held by actor9',
    cross.get('type')!='confirmed' and 'refused: no-grant:' in cross_refusal and cross_receipt.exists()
    and (root/'cross-member-purse-attempt/signed-observation.bin').exists()
    and after_cross['remaining']==first['a']['remaining'] and after_cross['reserved']=='0',
    {'outcome':cross,'nativeRefusal':cross_refusal,'retainedRefusal':str(cross_receipt),'before':cell['grain'],'after':after_cross})
prompt('b','member B consumes its remaining three credits'); finish_prompt('b',2)
empty=purse('b','member-b-empty'); a_untouched=purse('a','a-after-b-spend')
check('member B exhaustion leaves A purse untouched',empty['remaining']=='0' and empty['reserved']=='0' and a_untouched['remaining']==first['a']['remaining'],{'b':empty,'a':a_untouched})
count=len(received); prompt('b','member B must not spend after exhaustion')
wait('B exhausted reply',lambda:len(statuses('b'))>=3,600)
wait('B exhausted worker stopped',lambda:journal('b').get('child') is None and journal('b').get('pending') is None and journal('b').get('parentHold') is None,600)
if a.exhaustion_only:
    # This mode must never issue a reconciliation command. The caller's normal
    # completion path must retire a proven-unsent native refusal itself.
    wait('B exhausted automatic cleanup',lambda:done('b'),600)
    retired=journal('b')
    audit=[row for row in retired.get('reconciliationLog',[])
        if row.get('action')=='abort-definitively-unreserved-provider-request'
        and row.get('stage')=='signed-origin-confirmed' and row.get('automatic') is True
        and (row.get('refusal') or {}).get('type')=='native-refusal'
        and (row.get('refusal') or {}).get('reason')=='law-denied']
    check('native refusal automatically retires its exact unsent attempt',
        bool(audit) and len(received)==count and statuses('b')[-1]!='status=200',
        {'journal':retired,'automaticRetirement':audit,'worker':statuses('b'),'received':len(received)})
    save('exhaustion-after-automatic-retirement.json',retired)
    if a.typed_acp_refusal:
        def typed_closed():
            j=journal('b'); session=j.get('hermesSession') or {}
            return (session.get('pendingPrompt') is False
                and len(list(members['b']['state'].glob('hermes-failed-*.closed.json')))==1
                and 'Hermes turn failed at a settled boundary' in (root/'controller-b.stderr').read_text())
        wait('typed failed prompt durable closure',typed_closed,600)
        failed_paths=[path for path in members['b']['state'].glob('hermes-failed-*.json') if not path.name.endswith('.closed.json')]
        closed_paths=list(members['b']['state'].glob('hermes-failed-*.closed.json'))
        assert len(failed_paths)==1 and len(closed_paths)==1
        failed=json.loads(failed_paths[0].read_text()); closed=json.loads(closed_paths[0].read_text())
        emitted=[json.loads(line) for line in (members['b']['work']/'typed-failures.jsonl').read_text().splitlines()]
        error=failed.get('error') or {}; data=error.get('data') or {}
        check('typed ACP refusal remains a durable failed turn with closed pending prompt',
            failed.get('type')=='mini-hermes-failed-turn-v1'
            and closed.get('type')=='mini-hermes-failed-turn-closed-v1'
            and failed.get('promptOperationId')==closed.get('promptOperationId')
            and error.get('code')==-32003 and data.get('type')=='mini-hermes-turn-failure-v1'
            and data.get('reason')=='provider_refused' and data.get('retryable') is False
            and len(emitted)==1 and emitted[0].get('error')==error and 'result' not in emitted[0]
            and failed.get('promptReplayed') is False and closed.get('promptReplayed') is False
            and (closed.get('session') or {}).get('pendingPrompt') is False
            and (journal('b').get('hermesSession') or {}).get('pendingPrompt') is False
            and 'Hermes turn failed at a settled boundary' in (root/'controller-b.stderr').read_text()
            and len(received)==count,
            {'failedPath':str(failed_paths[0]),'failed':failed,'closedPath':str(closed_paths[0]),'closed':closed,
             'emitted':emitted,'journal':journal('b'),'received':len(received)})

else:
    # Definite native refusal intentionally retains its unsent attempt for explicit
    # owner reconciliation. Use the supported signed-origin abort, never edit it.
    refused=journal('b')
    check('empty purse retains a definitively refused unsent attempt',
        (refused.get('providerHold') or {}).get('reserveRefused') is True
        and not (refused.get('providerHold') or {}).get('reserveConfirmed',False)
        and not (refused.get('providerAttempt') or {}).get('sendStarted',False)
        and len(received)==count,refused)
    save('exhaustion-before-supported-abort.json',refused)
    abort=subprocess.run([a.grain,'admin',str(members['b']['state']/'admin.sock'),'reconcile provider abort'],capture_output=True,text=True)
    save('exhaustion-supported-abort.json',{'command':'reconcile provider abort','exit':abort.returncode,'stdout':abort.stdout,'stderr':abort.stderr})
    check('owner abort verifies exact signed unreserved origin',abort.returncode==0 and 'error:' not in abort.stdout,{'stdout':abort.stdout,'stderr':abort.stderr})
    wait('B exhausted cleanup',lambda:done('b'),600)
    save('exhaustion-after-supported-abort.json',journal('b'))
check('native exhausted purse prevents another physical request',len(received)==count and statuses('b')[-1]!='status=200',{'worker':statuses('b'),'journal':journal('b'),'received':len(received)})
m=members['b']
refill=subprocess.run([a.mini,'pay','--action','refill','--mode','submit','--host',manifest['host'],'--config',ns['CONFIG'],'--socket',ns['SOCKET'],
    '--subject','21','--capability','1021','--account','21','--task',str(a.task2+3),'--amount','6','--gain','6','--key',str(root/'keys/21.key'),'--dir',str(root/'refill-b-after-exhaustion')],capture_output=True)
(root/'refill-b.stdout').write_bytes(refill.stdout); (root/'refill-b.stderr').write_bytes(refill.stderr)
check('member B replenishes exhausted purse with new signed account debit',refill.returncode==0,{'exit':refill.returncode,'stdout':refill.stdout.decode(errors='replace')[-1500:]})


if a.exhaustion_only:
    replenished=purse('b','b-after-refill-before-new-request')
    check('automatic retirement permits member refill into an idle native purse',
        replenished['remaining']=='6' and replenished['reserved']=='0' and done('b'),replenished)
    before_new=len(received)
    prompt('b','member B sends fresh work after automatic refusal retirement and refill')
    finish_prompt('b',4)
    reused=purse('b','b-after-refilled-success'); stable_a=purse('a','a-after-refilled-b-success')
    check('refilled member succeeds without a refusal-recovery admin command',
        len(received)==before_new+1 and received[-1]['member']=='b' and statuses('b')[-1]=='status=200'
        and reused['remaining']=='3' and reused['reserved']=='0' and done('b')
        and stable_a['remaining']==first['a']['remaining'] and stable_a['reserved']=='0'
        and not (root/'exhaustion-supported-abort.json').exists(),
        {'before':replenished,'after':reused,'aPurse':stable_a,'journal':journal('b'),'worker':statuses('b'),'received':received})
    current_rows=[row for row in rows if row.get('run')==run_label]
    save('result.json',{'passed':all(row['passed'] for row in current_rows),'run':run_label,
        'currentChecks':len(current_rows),'paidCalls':0,'scope':'native funded exhaustion, automatic definite-unsent retirement, signed refill and fresh success',
        'refusalRetirementAdminCommands':0,'typedAcpRefusal':a.typed_acp_refusal,
        'initialSettlementRecoveryArtifacts':[str(path) for path in root.glob('first-round-*-settlement.json')],
        'controllersIdle':all(done(name) for name in members)})
    print('Native automatic refusal retirement passed '+str(len(current_rows))+' checks without refusal-retirement admin reconciliation',flush=True)
    raise SystemExit(0)

# A's unresolved physical effect and native held budget survive independent
# broker and controller restart; B remains a valid funded waiting member.
barriers['a'].clear(); before_uncertain=len(received); prompt('a','A outcome becomes uncertain across restart')
wait('A request physically received',lambda:len(received)==before_uncertain+1,600)
wait('A durable native send fence',lambda:(journal('a').get('providerAttempt') or {}).get('sendStarted') is True,600)
save('journal-a-before-crash.json',journal('a'))
broker_process.kill(); broker_process.wait(); broker_process=start_broker()
check('broker restart quarantines actually dispatched A capacity',broker_status()['counts']['uncertain']==1,broker_status())
pid=ctl('show',members['a']['unit'],'-p','MainPID','--value')
def process_identity(pid):
    try:
        stat=pathlib.Path('/proc/'+str(pid)+'/stat').read_text()
        return stat.rsplit(')',1)[1].split()[19]
    except FileNotFoundError: return None
old_processes={}
def retain_tree(pid):
    identity=process_identity(pid)
    if identity is None: return
    old_processes[str(pid)]=identity
    try: children=pathlib.Path('/proc/'+str(pid)+'/task/'+str(pid)+'/children').read_text().split()
    except FileNotFoundError: children=[]
    for child in children: retain_tree(child)
retain_tree(pid)
old_worker=(journal('a').get('child') or {}).get('unit')
save('pre-crash-processes.json',{'identities':old_processes,'workerUnit':old_worker})
os.kill(int(pid),signal.SIGKILL)
wait('A controller restarted',lambda:ctl('show',members['a']['unit'],'-p','MainPID','--value') not in ('0',pid))
wait('A native hold fenced after uncertain send',lambda:journal('a').get('connection')=='fenced' and (journal('a').get('providerHold') or {}).get('reserveConfirmed') is True,600)
prompt('b','valid B cannot bypass uncertain A physical occupancy')
wait('valid B queues behind uncertain A',lambda:broker_status()['counts']['queued']==1,600)
a_hold=purse('a','a-uncertain-hold'); b_wait=purse('b','b-blocked-by-uncertainty')
check('uncertain A retains native hold and valid B cannot spend or bypass',
    a_hold['reserved']=='3' and b_wait['remaining']=='6' and b_wait['reserved']=='0' and broker_status()['counts']['uncertain']==1 and len(received)==before_uncertain+1,
    {'aPurse':a_hold,'bPurse':b_wait,'aJournal':journal('a'),'bJournal':journal('b'),'broker':broker_status(),'received':len(received)})
subprocess.run([a.scheduler,'drain',str(broker_socket)],check=True,stdout=open(root/'uncertain-drain.json','wb'))
broker_process.kill(); broker_process.wait(); broker_process=start_broker()
check('drain and repeated broker restart retain native uncertainty',broker_status()['draining'] and broker_status()['counts']['uncertain']==1 and len(received)==before_uncertain+1,broker_status())
finish_prompt('b',4)
subprocess.run([a.scheduler,'resume',str(broker_socket)],check=True,stdout=open(root/'uncertain-resume.json','wb'))
prompt('b','B native authority revoked during a fresh shared-capacity wait')
wait('B queued before member revocation',lambda:broker_status()['counts']['queued']==1,600)
b_before=purse('b','b-before-revoke')
cell,authority=ns['mini_query']('member-b-revoke-pre',21,a.task2+3,111)
revoke=ns['mini_submit']('member-b-revoke',{'subject':'21','nonce':'65000','purpose':{'type':'prepare','draft':{'type':'revoke-source','command':{
    'kind':'object','subject':'21','nonce':'65001','target':str(a.task2+3),'victimKind':'object','capability':'113','controlCapability':'112',
    'expectedTargetRoot':cell['root'],'expectedAuthorityRoot':authority}}},'grants':[{'kind':'object','target':str(a.task2+3),'capability':'111'}]},21)
check('member B externally revokes only its provider grant while queued',revoke.get('type')=='confirmed',revoke)
# The test owns this endpoint, so its completion barrier is an exact physical
# completion witness. Release only that broker lease; Mini settlement remains
# unresolved because the killed controller never retained the response usage.
barriers['a'].set(); wait('own A endpoint finishes exact request',lambda:before_uncertain in completed)
job=next(job for job in broker_status()['jobs'] if job['controller']=='a' and job['state']=='uncertain')
exact=broker({'command':'inspect','controller':'a','id':job['id']})['job']
check('exact physical completion matches retained dispatch request',
    exact['request']['request_digest']==received[before_uncertain]['digest']
    and exact['state']['lease']==json.loads((root/'journal-a-before-crash.json').read_text())['providerAttempt']['placement']['lease'],
    {'requestDigest':exact['request']['request_digest'],'lease':exact['state']['lease'],'received':received[before_uncertain]})
wait('old controller and curl descendants stopped',lambda:all(process_identity(pid)!=identity for pid,identity in old_processes.items()))
worker_state=ctl('show',old_worker,'-p','ActiveState','--value') if old_worker else 'absent'
check('old worker scope stopped before physical slot reconciliation',worker_state in ('inactive','failed','absent'),{'unit':old_worker,'state':worker_state,'oldProcessIdentities':old_processes})
save('physical-completion-proof.json',{'completedRequest':received[before_uncertain],'completedIndex':before_uncertain,
    'oldControllerPid':pid,'currentControllerPid':ctl('show',members['a']['unit'],'-p','MainPID','--value'),'brokerJob':exact})
broker({'command':'finish','controller':'a','id':job['id'],'lease':exact['state']['lease'],'outcome':'ended'})
wait('B revoked worker reply',lambda:len(statuses('b'))>=5,600)
wait('B revoked parent settlement',lambda:all(journal('b').get(k) is None for k in ('child','pending','parentHold','settlementDue')),600)
b_after=purse('b','b-after-revoke'); still_held=purse('a','a-still-native-uncertain')
check('queued B fresh native authority refuses despite physical placement',
    len(received)==before_uncertain+1 and b_before['remaining']==b_after['remaining'] and b_after['reserved']=='0'
    and not (journal('b').get('providerHold') or {}).get('reserveConfirmed',False)
    and not (journal('b').get('providerAttempt') or {}).get('sendStarted',False),
    {'bBefore':b_before,'bAfter':b_after,'bJournal':journal('b'),'broker':broker_status(),'received':len(received)})
check('physical completion does not counterfeit native settlement',still_held['reserved']=='3' and (journal('a').get('providerHold') or {}).get('reserveConfirmed') is True,{'purse':still_held,'journal':journal('a')})
broker_process.kill(); broker_process.wait(); broker_process=start_broker()
terminal=broker({'command':'inspect','controller':'a','id':job['id']})['job']
replayed=broker({'command':'finish','controller':'a','id':job['id'],'lease':exact['state']['lease'],'outcome':'ended'})['job']
check('exact physical completion replay survives broker restart',terminal['state']==replayed['state'] and terminal['state']['outcome']=='ended',{'terminal':terminal['state'],'replay':replayed['state']})
current_rows=[row for row in rows if row.get('run')==run_label]
save('result.json',{'passed':all(row['passed'] for row in current_rows),'run':run_label,
    'currentChecks':len(current_rows),'retainedHistoricalChecks':len(rows)-len(current_rows),
    'retainedHistoricalFailures':sum(not row['passed'] for row in rows if row.get('run')!=run_label),
    'paidCalls':0,'scope':'two funded member-owned purses, distinct actors, same Store, real controllers, exhaustion, grant isolation, uncertainty',
    'retainedNativeUncertain':True,'physicalCompletionIndependentlyWitnessed':True})
print('Two-member native inference passed '+str(len(current_rows))+' current-run checks; native uncertainty and historical checks retained',flush=True)
