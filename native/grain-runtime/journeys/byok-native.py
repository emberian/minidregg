#!/usr/bin/env python3
"""Real Mini BYOK choice/provisioning + scripted ACP/HTTP, no paid API.

Requires Linux user systemd, bwrap, jq, PyNaCl and sudo -n install for the two
operator-owned fixture inventories. Retains every artifact in a fresh short root.
"""
import argparse, hashlib, http.server, json, os, pathlib, shutil, signal, socket
import struct, subprocess, sys, threading, time, textwrap

p = argparse.ArgumentParser()
for name in ('repo', 'manifest', 'mini', 'grain', 'launch-gate', 'run'):
    p.add_argument('--' + name, required=True)
p.add_argument('--task', type=int, default=8961)
p.add_argument('--ssh',action='store_true',help='qualify the real forced SSH credential service and native key rotation')
a = p.parse_args()
root = pathlib.Path(a.run)
if not root.is_absolute() or len(str(root)) > 55 or root.exists():
    raise SystemExit('fresh absolute run directory <=55 bytes required')
os.umask(0o077)
root.mkdir(mode=0o700,exist_ok=False)
os.nice(10)
manifest = json.loads(pathlib.Path(a.manifest).read_text())
for role in ('host', 'store', 'verifier'):
    actual = hashlib.sha256(pathlib.Path(manifest[role]).read_bytes()).hexdigest()
    if actual != manifest['sha256'][role]: raise SystemExit('manifest pin differs: ' + role)
for binary in (a.mini, a.grain, a.launch_gate):
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
rows = []
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
    code = code.replace(anchor, textwrap.dedent(extra) + '\n' + anchor, 1)
if a.ssh:
    insert('genesis = {"domain": "8501"',"""
    next_member=nacl.signing.SigningKey.generate()
    open(path('keys/20.key.next'),'wb').write(bytes(next_member))
    os.chmod(path('keys/20.key.next'),0o600)
    open(path('member-next.json'),'w').write(json.dumps({'publicKey':next_member.verify_key.encode().hex()}))
    subprocess.run([HOST,path('operator.json'),'author','signing-key-next-digest',path('member-next.json'),path('member-next.digest')],check=True,capture_output=True)
    next_digest=open(path('member-next.digest')).read().strip()
    """)
    code=code.replace('"nextKeyDigest": None','"nextKeyDigest": next_digest if s==20 else None')
insert('json.dump(genesis, open(path("genesis.json"), "w"), indent=1)',
       'genesis["clockTickers"]=[]\ngenesis["tailBound"]="256"')
insert('json.dump(birth, open(path("birth-intent.json"), "w"))',
       'birth["birth"]["resources"][0]["budget"]="1000"\nbirth["birth"]["resources"][3]["budget"]="300000"')
os.environ.update(HOST=manifest['host'], MINI=a.mini, STORE=manifest['store'],
                  VERIFIER=manifest['verifier'], GRAIN=a.grain, TEST_PROVIDER='UNUSED',
                  REPO=a.repo, HERMES_STANDIN='UNUSED', LAUNCH_GATE=a.launch_gate,
                  JPAY6_BASE=str(a.task))
save('inputs.json', {'arguments': vars(a), 'manifest': manifest,
     'binarySha256': {b: hashlib.sha256(pathlib.Path(b).read_bytes()).hexdigest()
                     for b in (a.mini, a.grain, a.launch_gate)},
     'bootstrapSha256': hashlib.sha256(raw.encode()).hexdigest(),
     'journeySha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()})
shutil.copyfile(__file__,root/'journey.py')
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
received = []
released = threading.Event()
released.set()
class Endpoint(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        body = self.rfile.read(int(self.headers['Content-Length']))
        received.append({'digest': hashlib.sha256(body).hexdigest(), 'authorizationSha256':hashlib.sha256((self.headers.get('Authorization') or '').encode()).hexdigest(), 'model':json.loads(body).get('model')})
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
port = 0
server = http.server.ThreadingHTTPServer(('127.0.0.1', port), Endpoint)
threading.Thread(target=server.serve_forever, daemon=True).start()
endpoint = f'http://127.0.0.1:{server.server_port}/v1/chat/completions'
state, runtime, work = (root / v for v in ('controller', 'runtime-root', 'worker-work'))
for path in (runtime, work, root/'etc', root/'credentials', root/'launcher'):
    path.mkdir(mode=0o700,exist_ok=False)
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
    {'name':name,'endpoint':endpoint,'kind':'openai-compatible','models':[ns['MODEL'],'not-selected'],'credential':'user'} for name in ['openrouter','chutes']]})
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]/'mini-keys'))
import atexit, journey_broker
# Credential custody is the key broker's (native/mini-keys): same account here,
# production binary and checks; neither the member client nor the controller opens a seal key.
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
        'model':'not-selected','provider':'openrouter','providers':str(root/'etc/providers.json'),
        'credentialBroker':str(keys_client),
        'gatewayBind':f'127.0.0.1:{gateway_port}','maxRequestBytes':12000,
        'maxResponseBytes':1048576,'timeoutSeconds':600,'localFixtureHostNetwork':True,
        },
    'commands':[{'name':'hermes-acp','program':str(root/'launcher/bwrap'),
        'args':['--workspace',str(work),'--runtime-root',str(runtime),'--network','host','--','/agent/hermes-acp'],
        'systemdScope':True,'wallTimeSeconds':1500,'reserve':'3','charge':'1'}]}
host = ns['Serve']()
# The member uses real Mini commands and the native identity check on its own key.
member=root/'member'
subprocess.run([a.mini,'workspace','--action','init','--host',manifest['host'],'--config',ns['CONFIG'],
    '--socket',ns['SOCKET'],'--key',str(root/'keys/20.key'),'--subject','20','--dir',str(member)],check=True,capture_output=True)
if a.ssh:
    # A genuine SSH forced proxy. The SSH login key and Mini member key differ.
    import atexit
    sshroot=root/'ssh';sshroot.mkdir(mode=0o700)
    subprocess.run(['ssh-keygen','-q','-t','ed25519','-N','','-f',str(sshroot/'host')],check=True)
    subprocess.run(['ssh-keygen','-q','-t','ed25519','-N','','-f',str(sshroot/'login')],check=True)
    # The forced command relays to the broker this root-owned client config names.
    service_path=pathlib.Path("/etc/mini-byok-fixtures")/(root.name+".json")
    subprocess.run(["sudo","-n","install","-d","-o","root","-g","root","-m","0755",str(service_path.parent)],check=True)
    subprocess.run(["sudo","-n","install","-o","root","-g","root","-m","0644",str(keys_client),str(service_path)],check=True)
    wrapper=pathlib.Path(__file__).parents[3]/'deploy/shell/mini-socket-proxy'
    command=' '.join([str(wrapper),a.mini,ns['SOCKET'],str(service_path)])
    (sshroot/'authorized_keys').write_text('restrict,command="'+command+'" '+(sshroot/'login.pub').read_text())
    with socket.socket() as probe: probe.bind(('127.0.0.1',0));sshport=probe.getsockname()[1]
    user=subprocess.run(['id','-un'],check=True,capture_output=True,text=True).stdout.strip()
    (sshroot/'sshd_config').write_text('\n'.join(['Port '+str(sshport),'ListenAddress 127.0.0.1','HostKey '+str(sshroot/'host'),
        'PidFile '+str(sshroot/'sshd.pid'),'AuthorizedKeysFile '+str(sshroot/'authorized_keys'),'PasswordAuthentication no',
        'KbdInteractiveAuthentication no','UsePAM no','StrictModes no','AllowUsers '+user,'LogLevel ERROR'])+'\n')
    sshd=subprocess.Popen(['sudo','-n','/usr/sbin/sshd','-D','-e','-f',str(sshroot/'sshd_config')],stdout=open(sshroot/'sshd.log','ab'),stderr=subprocess.STDOUT)
    def stop_sshd():
        if sshd.poll() is None:
            subprocess.run(['sudo','-n','kill','-TERM',str(sshd.pid)],capture_output=True)
            try:sshd.wait(timeout=10)
            except subprocess.TimeoutExpired:pass
    atexit.register(stop_sshd)
    (sshroot/'known_hosts').write_text('[127.0.0.1]:'+str(sshport)+' '+(sshroot/'host.pub').read_text())
    (sshroot/'ssh_config').write_text('Host byok-fixture\n HostName 127.0.0.1\n Port '+str(sshport)+'\n User '+user+'\n IdentityFile '+str(sshroot/'login')+'\n IdentitiesOnly yes\n StrictHostKeyChecking yes\n UserKnownHostsFile '+str(sshroot/'known_hosts')+'\n')
    sshcmd=sshroot/'ssh-client';sshcmd.write_text('#!/bin/sh\nexec /usr/bin/ssh -F '+str(sshroot/'ssh_config')+' "$@"\n');sshcmd.chmod(0o700)
    os.environ['MINI_SSH']=str(sshcmd)
    wait('real SSH listener',lambda:sshd.poll() is None and subprocess.run([str(sshcmd),'-T','-o','BatchMode=yes','--','byok-fixture'],input=b'',capture_output=True).returncode==0)
    # Preserve the source config pin but let this workspace use only the SSH pipe.
    ws=json.loads((member/'workspace.json').read_text());ws['socket']='ssh:byok-fixture';ws['host']=None;ws['hostSha256']=hashlib.sha256(pathlib.Path(manifest['host']).read_bytes()).hexdigest();save('member/workspace.json',ws)
    rogue=subprocess.run([str(sshcmd),'-T','--','byok-fixture','touch /tmp/not-authorized'],capture_output=True)
    check('forced SSH proxy rejects arbitrary Unix commands',rogue.returncode!=0,{})
def key_action(action,*flags,secret=None,ok=True):
    cmd=[a.mini,'key','--action',action,'--dir',str(member),*flags]
    if not a.ssh:cmd.extend(['--broker',str(keys_client)])
    result=subprocess.run(cmd,input=secret,capture_output=True)
    if (result.returncode==0)!=ok: raise RuntimeError('key action '+action+': '+result.stderr.decode())
    if secret and secret.strip() in result.stdout+result.stderr: raise RuntimeError('secret leaked in client output')
    return json.loads(result.stdout) if ok else result.stderr.decode()
def challenge_exchange():
    child=subprocess.Popen([str(sshcmd),'-T','--','byok-fixture','mini-provider-credentials-v1'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    def receive():
        head=child.stdout.read(4)
        if len(head)!=4:raise RuntimeError('missing credential challenge: '+child.stderr.read().decode())
        size=int.from_bytes(head,'little')
        if size>32768:raise RuntimeError('unbounded credential challenge')
        return json.loads(child.stdout.read(size))
    challenge=receive()
    def complete(action,signer=ns['keys'][20]):
        request={'challenge':challenge,'owner':{'subject':'20','publicKey':signer.verify_key.encode().hex()},'action':action}
        unsigned=json.dumps(request,sort_keys=True,separators=(',',':')).encode()
        request['signature']=signer.sign(b'mini/member-provider-action/v1\x00'+unsigned).signature.hex()
        body=json.dumps(request,separators=(',',':')).encode()
        child.stdin.write(len(body).to_bytes(4,'little')+body);child.stdin.flush()
        reply=receive();child.stdin.close();child.wait(timeout=10)
        return reply
    return complete
if a.ssh:
    for name in ['table','service']:
        finish=challenge_exchange()
        target=root/'etc/providers.json' if name=='table' else service_path
        original=target.read_bytes();changed=root/(name+'-changed.json');changed.write_bytes(original+b'\n')
        subprocess.run(['sudo','-n','install','-o','root','-g','root','-m','0644',str(changed),str(target)],check=True)
        result=finish({'action':'set','provider':'chutes','secret':'synthetic-drift-refused'})
        check('in-flight '+name+' binding drift refuses before custody mutation',result.get('type')=='mini-member-provider-refused-v1' and 'binding changed' in result.get('error',''),result)
        changed.write_bytes(original)
        subprocess.run(['sudo','-n','install','-o','root','-g','root','-m','0644',str(changed),str(target)],check=True)
key_action('providers')
key_action('set','--provider','chutes','--secret','-',secret=b'synthetic-byok-first\n')
key_action('grant','--provider','chutes','--runner','9','--per-call','100','--per-day','20','--until','1000000','--model',ns['MODEL'])
key_action('choose','--provider','chutes','--runner','9','--task',str(a.task+3),'--model',ns['MODEL'])
save('template.json',config)
install_inventory('provision-policy.json',{'type':'mini-member-provider-provision-v1',
    'templateSha256':hashlib.sha256((root/'template.json').read_bytes()).hexdigest(),
    'routes':[{'provider':'chutes','models':[ns['MODEL']]}]})
provision_cmd=[a.grain,'provider-provision',str(root/'template.json'),str(root/'etc/provision-policy.json'),str(root/'controller.json')]
provision=subprocess.run(provision_cmd,check=True,capture_output=True)
save('provision-result.json',json.loads(provision.stdout))
selected=json.loads((root/'controller.json').read_text())
check('signed member choice consumed by immutable fresh controller',
    selected['providerTask']['provider']=='chutes' and selected['providerTask']['model']==ns['MODEL']
    and selected['providerTask']['onBehalfOf']==config['providerTask']['onBehalfOf'],selected['providerTask'])
check('exact repeated provisioning is idempotent',json.loads(subprocess.run(provision_cmd,check=True,capture_output=True).stdout)['existing'] is True,{})
config=selected
ns['UNITS'].append(unit)
controller_started_ns=time.time_ns()
subprocess.run(['systemd-run','--user','--collect','--unit='+unit,
    '--property=KillMode=control-group','--property=Restart=on-failure','--property=RestartSec=2',
    '--property=RuntimeMaxSec=3600s','--property=StandardOutput=append:'+str(root/'controller.stdout'),
    '--property=StandardError=append:'+str(root/'controller.stderr'),
    a.grain,'serve',str(root/'controller.json')],check=True,capture_output=True)
def journal(): return json.loads((state/'journal.json').read_text())
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
connector=connect(); send('attach soft'); wait('native attach',lambda:done())
before=purse('before-success')
send('hermes complete native BYOK fixture')
wait('actual provider receive',lambda:len(received)==1)
wait('native provider settle',done)
after=purse('after-success')
check('real native reserve/send/settle charges user fee exactly',
    int(before['remaining'])-int(after['remaining'])==5 and after['reserved']=='0' and statuses()[-1]=='status=200',
    {'before':before,'after':after,'worker':statuses()})
check('endpoint receives selected model and member bearer',
    received[0]['authorizationSha256']==hashlib.sha256(b'Bearer synthetic-byok-first').hexdigest() and received[0]['model']==ns['MODEL'],received)
key_action('set','--provider','chutes','--secret','-',secret=b'synthetic-byok-replaced\n')
new_prompt('use the replaced member key')
wait('replaced provider receive',lambda:len(received)==2);wait('replaced provider settlement',done)
check('key replacement reaches next request without rebinding controller',
    received[-1]['authorizationSha256']==hashlib.sha256(b'Bearer synthetic-byok-replaced').hexdigest(),received[-1])
key_action('revoke','--provider','chutes','--runner','9')
new_prompt('must refuse revoked member key')
wait('revoked worker response',lambda:len(statuses())==3)
check('revoked grant prevents upstream send',len(received)==2 and statuses()[-1]=='status=403',{'statuses':statuses(),'received':len(received)})
# Source generation, not just pathname existence, refuses cloning a used controller.
clone=dict(config);clone['stateDir']=str(root/'clone-state');clone['controlSocket']=str(root/'clone-state/control.sock')
save('clone-template.json',clone)
key_action('grant','--provider','chutes','--runner','9','--per-call','100','--per-day','20','--until','1000000','--model',ns['MODEL'])
install_inventory('clone-policy.json',{'type':'mini-member-provider-provision-v1','templateSha256':hashlib.sha256((root/'clone-template.json').read_bytes()).hexdigest(),'routes':[{'provider':'chutes','models':[ns['MODEL']]}]})
cloned=subprocess.run([a.grain,'provider-provision',str(root/'clone-template.json'),str(root/'etc/clone-policy.json'),str(root/'clone-controller.json')],capture_output=True)
check('live source task cannot be cloned under an unused path',cloned.returncode!=0 and b'never-attached source tasks' in cloned.stderr and not (root/'clone-controller.json').exists(),cloned.stderr.decode())
if a.ssh:
    # Real native key rotation invalidates the old action signer at the service.
    pending_old=challenge_exchange()
    old_seed=(root/'keys/20.key').read_bytes()
    rotation=root/"rotation-member";rotation.mkdir(mode=0o700)
    rotation_ws=dict(ws);rotation_ws["socket"]=ns["SOCKET"];rotation_ws["host"]=manifest["host"]
    save("rotation-member/workspace.json",rotation_ws)
    rotated=subprocess.run([a.mini,'rotate-key','--workspace',str(rotation),'--next-key',str(root/'keys/20.key.next')],capture_output=True)
    check('member key rotation is admitted by native source',rotated.returncode==0,{'stdout':rotated.stdout.decode(),'stderr':rotated.stderr.decode()})
    stale=pending_old({'action':'set','provider':'chutes','secret':'synthetic-stale-owner'})
    check('native rotation after challenge refuses old action before custody mutation',stale.get('type')=='mini-member-provider-refused-v1' and 'native current-key authority refused' in stale.get('error',''),stale)
    new_seed=(root/'keys/20.key').read_bytes()
    (root/'keys/20.key').write_bytes(old_seed)
    old=key_action('ls',ok=False)
    check('rotated-out signer cannot access service custody', 'native current-key authority refused' in old,old)
    (root/'keys/20.key').write_bytes(new_seed)
    current=key_action('ls')
    check('new current signer enters its own custody namespace',current['result']['credentials']==[],current)
for folder in [root/'credentials',state]:
    for f in folder.rglob('*'):
        if f.is_file():
            data=f.read_bytes()
            if b'synthetic-byok-first' in data or b'synthetic-byok-replaced' in data: raise RuntimeError('plaintext secret in durable controller/custody')
check('controller journals and sealed custody contain no plaintext bearer',True,{})
save('result.json',{'passed':True,'checks':len(rows),'paidCalls':0,'nativeProfile':'c29 matched compatibility baseline','transport':'real sshd forced proxy' if a.ssh else 'hosted local custody'})
print('Native BYOK provisioning passed',flush=True)
