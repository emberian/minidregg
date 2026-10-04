#!/usr/bin/env python3
"""Real Mini admission + shared inference broker; scripted ACP/HTTP, no paid API.

Requires Linux user systemd, bwrap, jq, PyNaCl and sudo -n install for the two
operator-owned fixture inventories. Retains every artifact in a fresh short root.
"""
import argparse, hashlib, http.server, json, os, pathlib, shutil, signal, socket
import struct, subprocess, sys, threading, time

p = argparse.ArgumentParser()
for name in ('repo', 'manifest', 'mini', 'grain', 'scheduler', 'launch-gate', 'run'):
    p.add_argument('--' + name, required=True)
p.add_argument('--task', type=int, default=8891)
p.add_argument('--authority-only', action='store_true')
p.add_argument('--continue-after-success', action='store_true')
p.add_argument('--verify-uncertain-restart', action='store_true')
p.add_argument('--verify-refused-retirement', action='store_true')
p.add_argument('--runtime-sha256', help='explicit replacement runtime pin for a preserved-fixture recovery repair')
a = p.parse_args()
restart_nonce=str(time.time_ns())
if a.verify_uncertain_restart or a.verify_refused_retirement: a.continue_after_success = True
root = pathlib.Path(a.run)
if not root.is_absolute() or len(str(root)) > 55 or (root.exists() and not a.continue_after_success):
    raise SystemExit('fresh absolute run directory <=55 bytes required')
os.umask(0o077)
root.mkdir(mode=0o700,exist_ok=a.continue_after_success)
os.nice(10)
manifest = json.loads(pathlib.Path(a.manifest).read_text())
for role in ('host', 'store', 'verifier'):
    actual = hashlib.sha256(pathlib.Path(manifest[role]).read_bytes()).hexdigest()
    if actual != manifest['sha256'][role]: raise SystemExit('manifest pin differs: ' + role)
for binary in (a.mini, a.grain, a.scheduler, a.launch_gate):
    if not os.access(binary, os.X_OK): raise SystemExit('missing executable ' + binary)
unit = f'mini-grain-controller@{a.task}.service'
def ctl(*args):
    return subprocess.run(['systemctl', '--user', *args], capture_output=True, text=True, check=True).stdout.strip()
if ctl('show', unit, '-p', 'LoadState', '--value') != 'not-found':
    raise SystemExit('refusing existing controller unit')
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
rows = json.loads((root/'checks.json').read_text()) if a.continue_after_success else []
def check(label, condition, evidence):
    rows.append({'check': label, 'passed': bool(condition), 'evidence': evidence})
    save('checks.json', rows)
    print(('PASS ' if condition else 'FAIL ') + label, flush=True)
    if not condition: raise RuntimeError(label)

# Reuse the established source-owned genesis/birth helper, without payments,
# credential setup or its later controller fixture. No live Store is copied.
source = pathlib.Path(a.repo) / 'native/resource-client/journey.d/jpay6.sh'
raw = source.read_text()
code = raw.split('python3 - "$DIR" <<\'PY\'\n', 1)[1].split('# ---------------------------------------------------------------- Host plumbing', 1)[0]
def insert(anchor, extra):
    global code
    if code.count(anchor) != 1: raise RuntimeError('bootstrap seam changed: ' + anchor)
    code = code.replace(anchor, extra + '\n' + anchor, 1)
insert('json.dump(genesis, open(path("genesis.json"), "w"), indent=1)',
       'genesis["clockTickers"]=[]\ngenesis["tailBound"]="256"')
insert('json.dump(birth, open(path("birth-intent.json"), "w"))',
       'birth["birth"]["resources"][0]["budget"]="1000"\nbirth["birth"]["resources"][3]["budget"]="300000"')
os.environ.update(HOST=manifest['host'], MINI=a.mini, STORE=manifest['store'],
                  VERIFIER=manifest['verifier'], GRAIN=a.grain, TEST_PROVIDER='UNUSED',
                  REPO=a.repo, HERMES_STANDIN='UNUSED', LAUNCH_GATE=a.launch_gate,
                  JPAY6_BASE=str(a.task))
save('restart-inputs.json' if a.verify_uncertain_restart else ('continued-inputs.json' if a.continue_after_success else 'inputs.json'), {'arguments': vars(a), 'manifest': manifest,
     'binarySha256': {b: hashlib.sha256(pathlib.Path(b).read_bytes()).hexdigest()
                     for b in (a.mini, a.grain, a.scheduler, a.launch_gate)},
     'bootstrapSha256': hashlib.sha256(raw.encode()).hexdigest(),
     'journeySha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()})
shutil.copyfile(__file__,root/('restart-journey.py' if a.verify_uncertain_restart else ('continued-journey.py' if a.continue_after_success else 'journey.py')))
if a.continue_after_success:
    prior=json.loads((root/'inputs.json').read_text())
    for binary, expected in prior['binarySha256'].items():
        actual=hashlib.sha256(pathlib.Path(binary).read_bytes()).hexdigest()
        if actual!=expected and not (binary==a.grain and actual==a.runtime_sha256):
            raise RuntimeError('continuation binary changed: '+binary)
    head=code.split('# ---------------------------------------------------------------- keys and genesis',1)[0]
    tail=code.split('# ---------------------------------------------------------------- the purse: the grain birth (first event)',1)[1]
    tail=tail.split('serve = Serve()\nborn =',1)[0]
    tail=tail.replace('os.makedirs(path("session"), mode=0o700)','os.makedirs(path("session"), mode=0o700, exist_ok=True)')
    code=head+'''
keys={s:nacl.signing.SigningKey(open(path(f"keys/{s}.key"),"rb").read()) for s in SUBJECTS}
operator=json.load(open(path("operator.json")))
genesis=json.load(open(path("genesis.json")))
CONFIG=path("deployment/continuity-config.json")
profile=json.loads(subprocess.run([HOST, CONFIG, "profile"],check=True,capture_output=True).stdout)
born=json.load(open(path("birth-attempt/outcome.json")))
delegations=[json.load(open(path(name+"-attempt/outcome.json"))) for name in
 ("parent-witness-tool","parent-witness-provider","publication-tool","publication-read")]
'''+tail
else:
    (root / 'bootstrap-extracted.py').write_text(code)
oldargv = sys.argv
sys.argv = [str(root / 'bootstrap-extracted.py'), str(root)]
ns = {'__name__': '__native_inference_bootstrap__'}
print('Native bootstrap', flush=True)
exec(compile(code, str(root / 'bootstrap-extracted.py'), 'exec'), ns)
sys.argv = oldargv
check('native four-resource birth and delegated provider witness',
      ns['born'].get('type') == 'confirmed' and all(v.get('type') == 'confirmed' for v in ns['delegations']),
      {'birth': ns['born'], 'delegations': ns['delegations']})

# Local endpoint receives complete requests and can hold completion at a durable
# test barrier. Every actual send is recorded independently of controller logs.
received = json.loads((root/'received.json').read_text()) if a.continue_after_success else []
released = threading.Event()
released.set()
class Endpoint(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        body = self.rfile.read(int(self.headers['Content-Length']))
        received.append({'digest': hashlib.sha256(body).hexdigest(), 'authorization': self.headers.get('Authorization') is not None})
        save('received.json', received)
        released.wait(600)
        reply = ('data: ' + json.dumps({'id':'native-fixture','object':'chat.completion.chunk',
            'model':ns['MODEL'],'choices':[{'index':0,'delta':{'role':'assistant','content':'fixture complete'},'finish_reason':'stop'}]}) + '\n\n' +
            'data: ' + json.dumps({'id':'native-fixture','object':'chat.completion.chunk','created':1,
            'model':ns['MODEL'],'choices':[],
            'usage':{'prompt_tokens':1,'completion_tokens':2,'total_tokens':3}}) + '\n\ndata: [DONE]\n\n').encode()
        try:
            self.send_response(200); self.send_header('Content-Type','text/event-stream')
            self.send_header('Content-Length',str(len(reply))); self.end_headers()
            self.wfile.write(reply); self.wfile.flush()
        except (BrokenPipeError, ConnectionResetError): pass
    def log_message(self, *_): pass
port = int(json.loads((root/'providers.json-source.json').read_text())['providers'][0]['endpoint'].split(':')[2].split('/')[0]) if a.continue_after_success else 0
server = http.server.ThreadingHTTPServer(('127.0.0.1', port), Endpoint)
threading.Thread(target=server.serve_forever, daemon=True).start()
endpoint = f'http://127.0.0.1:{server.server_port}/v1/chat/completions'
state, runtime, work = (root / v for v in ('controller', 'runtime-root', 'worker-work'))
for path in (state, runtime, work, root/'etc', root/'credentials', root/'launcher', root/'broker'):
    path.mkdir(mode=0o700,exist_ok=a.continue_after_success)
runtime.chmod(0o755)
for src, name in ((a.grain,'grain-runtime'),
                  (str(pathlib.Path(a.grain).parent/'grain-provider-bridge'),'grain-provider-bridge'),
                  (str(pathlib.Path(a.repo)/'native/resource-client/journey.d/jpay6-hermes-acp'),'hermes-acp')):
    shutil.copyfile(src, runtime/name); (runtime/name).chmod(0o755)
shutil.copyfile(pathlib.Path(a.repo)/'deploy/grain-host/bwrap', root/'launcher/bwrap')
shutil.copyfile(a.launch_gate, root/'launcher/launch-gate')
for path in (root/'launcher/bwrap',root/'launcher/launch-gate'): path.chmod(0o700)
def install_inventory(name, value):
    save(name + '-source.json', value)
    subprocess.run(['sudo','-n','install','-o','root','-g','root','-m','0644',
                    str(root/(name+'-source.json')),str(root/'etc'/name)],check=True)
install_inventory('providers.json', {'type':'mini-provider-table-v2','providers':[
    {'name':'native-homelab','endpoint':endpoint,'kind':'openai-compatible','models':[ns['MODEL']],'credential':'homelab'}]})
inventory = {'version':1,'max_jobs':100,'max_queued_per_principal':8,'max_active_per_principal':1,
    'lease_ms':300000,'groups':{'shared':1},'controllers':{
        'native':{'uid':os.getuid(),'principal':'20','pool':'members'},
        'barrier':{'uid':os.getuid(),'principal':'barrier','pool':'members'}},
    'backends':{'local':{'pool':'members','group':'shared','endpoint':endpoint,'models':{
        ns['MODEL']:{'context':32768,'max_output':100,'tools':True,'input_us':1,'output_us':1}}}}}
install_inventory('inference.json', inventory)
broker_socket = root/'broker/control.sock'
broker_directory = root/('restored-broker' if a.verify_uncertain_restart else 'broker')
def start_broker():
    proc = subprocess.Popen([a.scheduler,str(root/'etc/inference.json'),str(broker_directory),str(broker_socket)],
        stdout=open(root/'broker.log','ab'),stderr=subprocess.STDOUT)
    ns['LIVE'].append(proc)
    wait('broker ready', lambda: broker_status())
    return proc
def broker_status():
    result = subprocess.run([a.scheduler,'status',str(broker_socket)],capture_output=True)
    return json.loads(result.stdout) if result.returncode == 0 else None
def broker(command):
    frame = json.dumps(command).encode()
    with socket.socket(socket.AF_UNIX) as channel:
        channel.settimeout(5); channel.connect(str(broker_socket))
        channel.sendall(struct.pack('>I',len(frame))+frame)
        size = struct.unpack('>I',channel.recv(4))[0]; data=b''
        while len(data)<size:
            part=channel.recv(size-len(data))
            if not part: raise RuntimeError('broker closed truncated reply')
            data += part
    value = json.loads(data)
    if value.get('type') == 'refused': raise RuntimeError(value)
    return value
broker_proc = start_broker()
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]/'mini-keys'))
import atexit, journey_broker
# The provider task's key broker: same account, production binary (native/mini-keys).
keys_proc, keys_client = journey_broker.start(root, a.mini, providers=root/'etc/providers.json',
    host=manifest['host'], host_config=ns['CONFIG'], public_socket=ns['SOCKET'])
atexit.register(keys_proc.kill)
with socket.socket() as probe:
    probe.bind(('127.0.0.1',0)); gateway_port=probe.getsockname()[1]
config = {'mini':a.mini,'host':manifest['host'],'hostConfig':ns['CONFIG'],'hostSocket':ns['SOCKET'],
    'controlSocket':str(state/'control.sock'),'custodyKey':str(root/'keys/7.key'),
    'stateDir':str(state),'cwd':str(root),'task':str(a.task),'subject':'7','capability':'71',
    'queryCapability':'71','policyControlCapability':'72',
    'toolTask':{'task':str(a.task+1),'subject':'8','capability':'81','queryCapability':'81',
        'custodyKey':str(root/'keys/8.key'),'parentCapability':'73','parentObserveCapability':'73',
        'reserve':'2','charge':'1','allowedPublications':[{'kind':'object','target':str(a.task+2),
            'capability':'93','observeCapability':'93'}],
        'allowedReads':[{'name':'publication','kind':'object','target':str(a.task+2),
            'observeCapability':'94','maxResultBytes':65536}]},
    'providerTask':{'task':str(a.task+3),'subject':'9','capability':'101','queryCapability':'101',
        'custodyKey':str(root/'keys/9.key'),'parentCapability':'75','parentObserveCapability':'75',
        'reserve':'30000','maxInputTokens':1000,'maxOutputTokens':100,'maxIterations':1,
        'onBehalfOf':{'subject':'20','publicKey':ns['keys'][20].verify_key.encode().hex()},
        'model':ns['MODEL'],'provider':'native-homelab','providers':str(root/'etc/providers.json'),
        'credentialBroker':str(keys_client),
        'gatewayBind':f'127.0.0.1:{gateway_port}','maxRequestBytes':12000,
        'maxResponseBytes':1048576,'timeoutSeconds':600,'localFixtureHostNetwork':True,
        'homelab':{'socket':str(broker_socket),'controller':'native',
            'domain':'8501:'+str(json.loads(pathlib.Path(ns['CONFIG']).read_text())['expectedSeed']),
            'principal':'20','pool':'members','backends':['native-homelab'],'queueTimeoutMs':300000}},
    'commands':[{'name':'hermes-acp','program':str(root/'launcher/bwrap'),
        'args':['--workspace',str(work),'--runtime-root',str(runtime),'--network','host','--','/agent/hermes-acp'],
        'systemdScope':True,'wallTimeSeconds':1500,'reserve':'3','charge':'1'}]}
if a.continue_after_success:
    # Reuse the exact admitted controller binding, including its gateway port;
    # changing configuration is a separate audited migration, never a restart.
    config=json.loads((state/'journal.json').read_text())['binding']['config']
save('controller.json',config)
host_started_ns=time.time_ns()
host = ns['Serve']()
wait('new Host socket',lambda:pathlib.Path(ns['SOCKET']).stat().st_ctime_ns>host_started_ns)
if a.verify_uncertain_restart or a.verify_refused_retirement:
    before_restart_parent=ns['mini_query']('restart-before-parent-'+restart_nonce,7,a.task,71)[0]['grain']
    before_restart_purse=ns['mini_query']('restart-before-purse-'+restart_nonce,9,a.task+3,101)[0]['grain']
    before_restart_receives=len(received)
    before_restart_log=json.loads((state/'journal.json').read_text())['reconciliationLog']
    if a.verify_uncertain_restart and (not before_restart_purse['reserved'] or int(before_restart_purse['reserved'])==0):
        raise RuntimeError('restart qualification requires retained native uncertainty')
ns['UNITS'].append(unit)
controller_started_ns=time.time_ns()
subprocess.run(['systemd-run','--user','--collect','--unit='+unit,
    '--property=KillMode=control-group','--property=Restart=on-failure','--property=RestartSec=2',
    '--property=RuntimeMaxSec=3600s','--property=StandardOutput=append:'+str(root/'controller.stdout'),
    '--property=StandardError=append:'+str(root/'controller.stderr'),
    a.grain,'serve',str(root/'controller.json')],check=True,capture_output=True)
def journal(): return json.loads((state/'journal.json').read_text())
def exact_uncertain_job():
    current=journal(); attempt=current['providerAttempt']; placement=attempt['placement']
    job=broker({'command':'inspect','controller':placement['config']['controller'],'id':placement['request']['id']})['job']
    assert job['request']==placement['request']
    assert job['request']['request_digest']==attempt['requestSha256']==received[-1]['digest']
    assert job['state']['state']=='uncertain' and job['state']['lease']==placement['lease']
    assert job['state']['attempt']==placement['request']['id']+':'+str(attempt['id'])
    assert job['principal']==placement['config']['principal'] and job['pool']==placement['config']['pool']
    assert attempt['sendStarted'] and current['providerHold']['reserveConfirmed']
    return job

def connect():
    proc = subprocess.Popen([a.grain,'connect',str(state/'control.sock')],stdin=subprocess.PIPE,
        stdout=open(root/'connector.stdout','ab'),stderr=open(root/'connector.stderr','ab'))
    ns['LIVE'].append(proc); return proc
def send(text):
    connector.stdin.write((text+'\n').encode()); connector.stdin.flush()
def done():
    j=journal()
    return all(j.get(name) is None for name in ('providerAttempt','providerHold','pending','child',
        'parentHold','toolHold','settlementDue')) and j.get('connection')=='soft'
def statuses():
    return [part for part in (work/'standin.log').read_text().split() if part.startswith('status=')]
def new_prompt(text):
    send('conversation new'); wait('new conversation',lambda: journal().get('hermesSession') is None)
    send('hermes '+text)
def purse(label): return ns['mini_query'](label,9,a.task+3,101)[0]['grain']
wait('controller socket',lambda:(state/'control.sock').stat().st_ctime_ns>controller_started_ns)
if a.verify_refused_retirement:
    wait('automatic refused-request retirement',lambda:done())
    after_parent=ns['mini_query']('retirement-parent-'+restart_nonce,7,a.task,71)[0]['grain']
    after_purse=ns['mini_query']('retirement-purse-'+restart_nonce,9,a.task+3,101)[0]['grain']
    decisions=[v for v in journal()['reconciliationLog'] if v.get('action')=='abort-definitively-unreserved-provider-request' and v.get('automatic')]
    check('native refused request retires automatically without changing idle purse or sending',
        before_restart_purse==after_purse and after_purse['reserved']=='0' and len(received)==before_restart_receives
        and len(decisions)==1 and decisions[0]['stage']=='signed-origin-confirmed'
        and decisions[0]['refusal']['reason']=='revoked',
        {'beforePurse':before_restart_purse,'afterPurse':after_purse,'beforeParent':before_restart_parent,
         'afterParent':after_parent,'decisions':decisions,'scheduler':broker_status(),'received':len(received)})
    save('retirement-result.json',{'passed':True,'paidCalls':0,'newProviderCalls':0,'adminActions':0})
    sys.exit(0)
if a.verify_uncertain_restart:
    def retained_fence():
        j=journal()
        return j.get('connection')=='fenced' and (j.get('providerAttempt') or {}).get('sendStarted') is True
    wait('retained uncertainty after restart',retained_fence)
    first_parent=ns['mini_query']('restart-first-parent-'+restart_nonce,7,a.task,71)[0]['grain']
    first_purse=ns['mini_query']('restart-first-purse-'+restart_nonce,9,a.task+3,101)[0]['grain']
    restart_ns=time.time_ns();ctl('restart',unit)
    wait('second fresh controller socket',lambda:(state/'control.sock').stat().st_ctime_ns>restart_ns)
    wait('retained uncertainty after second restart',retained_fence)
    second_parent=ns['mini_query']('restart-second-parent-'+restart_nonce,7,a.task,71)[0]['grain']
    second_purse=ns['mini_query']('restart-second-purse-'+restart_nonce,9,a.task+3,101)[0]['grain']
    prior_reprepare=[x for x in before_restart_log if x.get('action')=='reprepare-interrupted-parent-settlement']
    current_reprepare=[x for x in journal()['reconciliationLog'] if x.get('action')=='reprepare-interrupted-parent-settlement']
    check('two further controller restarts never repeat settled parent charge or release provider uncertainty',
        before_restart_parent==first_parent==second_parent and before_restart_purse==first_purse==second_purse
        and prior_reprepare==current_reprepare and len(prior_reprepare)==1 and len(received)==before_restart_receives
        and broker_status()['counts']['uncertain']==1 and broker_status()['draining'],
        {'parentBefore':before_restart_parent,'parentFirst':first_parent,'parentSecond':second_parent,
         'purseBefore':before_restart_purse,'purseFirst':first_purse,'purseSecond':second_purse,
         'settlementReprepares':current_reprepare,'scheduler':broker_status(),'exactJob':exact_uncertain_job(),'received':len(received)})
    save('restart-result.json',{'passed':True,'paidCalls':0,'newProviderCalls':0})
    sys.exit(0)
connector=connect(); send('attach soft'); wait('native attach',lambda:done())
if a.continue_after_success:
    after=purse('continued-purse')
    prior=next(r['evidence']['after'] for r in rows if r['check']=='real native reserve/send/settle charges homelab tariff exactly')
    check('continuation preserves successful native purse state',after==prior and len(received)==1,after)
else:
    before=purse('before-success')
    send('hermes complete native inference fixture')
    wait('actual provider receive',lambda:len(received)==1)
    wait('native provider settle',done)
    after=purse('after-success')
    check('real native reserve/send/settle charges homelab tariff exactly',
        int(before['remaining'])-int(after['remaining'])==3 and after['reserved']=='0' and statuses()[-1]=='status=200',
        {'before':before,'after':after,'worker':statuses(),'scheduler':broker_status()})
    check('homelab physical endpoint receives no bearer',received[0]['authorization'] is False,received)

request={'id':'a'*64,'request_digest':'b'*64,'model':ns['MODEL'],'max_input':1,'max_output':1,
    'tools':True,'queue_deadline_ms':int(time.time()*1000)+300000,'allowed_endpoints':[endpoint]}
held=broker({'command':'enqueue','controller':'barrier','job':request})
save('barrier.json',held)
new_prompt('drain this waiting native request')
wait('native queued',lambda:broker_status()['counts']['queued']==1)
subprocess.run([a.scheduler,'drain',str(broker_socket)],check=True,stdout=open(root/'drain.json','wb'))
wait('drained worker reply',lambda:len(statuses())==2)
wait('drained prompt done',done)
drained=purse('after-drain')
check('drained native queue performs no provider reserve or physical send',
    len(received)==1 and drained['remaining']==after['remaining'] and drained['reserved']=='0' and statuses()[-1]=='status=403',
    {'purse':drained,'worker':statuses(),'scheduler':broker_status()})
broker_proc.kill(); broker_proc.wait(); broker_proc=start_broker()
check('broker restart retains native drained jobs',broker_status()['draining'],broker_status())
subprocess.run([a.scheduler,'resume',str(broker_socket)],check=True,stdout=open(root/'resume.json','wb'))

if a.authority_only:
    # The queue is outside the controller loop. Source authority may change
    # during the wait; placement must never substitute for current admission.
    request['id']='c'*64
    request['queue_deadline_ms']=int(time.time()*1000)+300000
    broker({'command':'enqueue','controller':'barrier','job':request})
    new_prompt('revoke native parent authority while this waits')
    wait('native queued before revoke',lambda:broker_status()['counts']['queued']==1)
    cell, authority=ns['mini_query']('revoke-parent-provider-pre',7,a.task,71)
    revoke=ns['mini_submit']('revoke-parent-provider',{'subject':'7','nonce':'63000',
        'purpose':{'type':'prepare','draft':{'type':'revoke-source','command':{
            'kind':'object','subject':'7','nonce':'63001','target':str(a.task),
            'victimKind':'object','capability':'75','controlCapability':'72',
            'expectedTargetRoot':cell['root'],'expectedAuthorityRoot':authority}}},
        'grants':[{'kind':'object','target':str(a.task),'capability':'71'}]},7)
    check('external signed revocation commits while provider waits',revoke.get('type')=='confirmed',revoke)
    broker({'command':'cancel','controller':'barrier','id':request['id']})
    wait('revoked native worker reply',lambda:len(statuses())==3)
    revoked_purse=purse('after-revoked-reserve')
    current=journal()
    check('native queued authority recheck refuses reserve and physical send',
        len(received)==1 and statuses()[-1]=='status=403' and revoked_purse['remaining']==drained['remaining']
        and revoked_purse['reserved']=='0' and not (current.get('providerHold') or {}).get('reserveConfirmed',False)
        and not (current.get('providerAttempt') or {}).get('sendStarted',False),
        {'purse':revoked_purse,'journal':current,'worker':statuses(),'scheduler':broker_status(),'received':len(received)})
    save('result.json',{'passed':True,'checks':len(rows),'paidCalls':0,'pole':'native queued authority revocation'})
    print('Native queued authority revocation passed',flush=True)
    sys.exit(0)

# Start a real request, then kill both broker and controller after the signed
# provider hold and durable send fence. No test-supplied ACK bypasses Mini.
released.clear(); new_prompt('hold this native inference across restart')
wait('held request physically received',lambda:len(received)==2)
wait('native durable send fence',lambda:(journal().get('providerAttempt') or {}).get('sendStarted') is True)
save('journal-before-crash.json',journal())
broker_proc.kill(); broker_proc.wait(); broker_proc=start_broker()
check('broker crash retains actual dispatched physical occupancy',broker_status()['counts']['uncertain']==1,broker_status())
pid=ctl('show',unit,'-p','MainPID','--value'); os.kill(int(pid),signal.SIGKILL)
released.set()
wait('controller restarted',lambda:ctl('show',unit,'-p','MainPID','--value') not in ('0',pid))
def fenced():
    j=journal()
    return j.get('connection')=='fenced' and j.get('providerAttempt') is not None and (j.get('providerHold') or {}).get('reserveConfirmed') is True
wait('native uncertain recovery',fenced,600)
held_purse=purse('after-crash')
check('native recovery retains matching purse hold and broker uncertainty',
    held_purse['reserved']==journal()['providerHold']['reserve']==config['providerTask']['reserve'] and broker_status()['counts']['uncertain']==1 and len(received)==2,
    {'purse':held_purse,'journal':journal(),'scheduler':broker_status(),'exactJob':exact_uncertain_job(),'received':len(received)})
subprocess.run([a.scheduler,'drain',str(broker_socket)],check=True,stdout=open(root/'uncertain-drain.json','wb'))
broker_proc.kill(); broker_proc.wait(); broker_proc=start_broker()
check('drain plus repeated restart cannot erase native uncertainty',
    broker_status()['draining'] and broker_status()['counts']['uncertain']==1 and len(received)==2,broker_status())
broker_proc.kill(); broker_proc.wait()
# Restore the current stopped snapshot into a fresh private state directory.
# This does not claim that an older snapshot can replace newer live evidence.
broker_directory=root/'restored-broker'; broker_directory.mkdir(mode=0o700)
shutil.copyfile(root/'broker/state.json',broker_directory/'state.json')
broker_proc=start_broker()
restored=broker_status()
check('restored broker snapshot retains native uncertain occupancy and drain',
    restored['draining'] and restored['counts']['uncertain']==1 and not restored['quiescent']
    and len(received)==2,{'status':restored,'exactJob':exact_uncertain_job()})
save('result.json',{'passed':True,'checks':len(rows),'paidCalls':0,'pole':'native uncertainty restart/restore'})
print('Native inference journey passed; uncertainty intentionally retained (check log includes preserved continuation history)',flush=True)
