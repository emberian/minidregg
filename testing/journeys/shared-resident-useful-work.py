#!/usr/bin/env python3
"""Native two-author resident completion/recovery on a supplied existing Store.

Consumes platform-inputs.json and exact archived roles; never bootstraps a world,
starts/stops its Store, invents members, or seeds runtime journals. Source birth,
signed delegations, ordinary room/summon/dispatch, actual MCP/SQLite/SSE work,
SIGKILL driver cut, late exact reply and source delivery replay are retained.
Provider is a scripted local fixture with explicit600s deadline, no paid calls.
"""
import argparse,atexit,hashlib,http.server,json,os,pathlib,pwd,re,signal,socket,sqlite3,subprocess,sys,threading,time
import socket as net_socket
import nacl.signing
p=argparse.ArgumentParser()
p.add_argument('--platform-inputs',required=True)
p.add_argument('--base',required=True)
p.add_argument('--repo',required=True)
p.add_argument('--fixture-runtime',required=True)
p.add_argument('--fixture-provider',required=True)
p.add_argument('--registration',required=True)
p.add_argument('--task',type=int,default=8997)
p.add_argument('--capture-reference',required=True)
p.add_argument('--shared-document-reference',required=True)
p.add_argument('--shared-room-alias',required=True)
p.add_argument('--provider-subject')
p.add_argument('--preserve-on-success',action='store_true')
a=p.parse_args()
os.umask(0o077);os.nice(10)
context_path=pathlib.Path(a.platform_inputs);ctx=json.loads(context_path.read_text())
def digest(path):return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()
manifest_path=pathlib.Path(ctx['manifest']);manifest=json.loads(manifest_path.read_text())
if digest(manifest_path)!=ctx['identity']['manifestSha256']:raise RuntimeError('supplied manifest pin differs')
for role in ('mini','host','store','verifier','grainRuntime','launchGate'):
    path=manifest[role]
    if digest(path)!=manifest['sha256'][role]:raise RuntimeError('source role bytes differ '+role)
a.mini=manifest['mini'];a.host=manifest['host'];a.grain=manifest['grainRuntime'];a.launch_gate=manifest['launchGate']
base=pathlib.Path(a.base);node=base/'var/lib/mini/store/node'
config=ctx['config'];socket=ctx['privateSocket'];genesis=json.loads(pathlib.Path(ctx['genesis']).read_text())
if pathlib.Path(config)!=node/'deployment/pinned-config.json':raise RuntimeError('canonical shared Node/config required')
if digest(config)!=ctx['identity']['configSha256']:raise RuntimeError('supplied source configuration differs')
configured=json.loads(pathlib.Path(config).read_text())
owner=ctx['custody']['owner'];manager=ctx['custody']['management']
owner_subject=owner['subject'];tool_subject=manager['subject'];owner_key=pathlib.Path(owner['seed']);tool_key=pathlib.Path(manager['seed'])
members=list(ctx['memberInventory'].values())
if len(members)<5 and not a.provider_subject:raise RuntimeError('fixture provider witness needs explicit source subject or declared member4')
first_member,second_member=members[:2]
provider_member=ctx['memberInventory'][a.provider_subject] if a.provider_subject else members[4]
first_subject=first_member['subject'];second_subject=second_member['subject'];provider_subject=provider_member['subject']
if len({owner_subject,tool_subject,provider_subject})!=3:raise RuntimeError('provider/tool/parent source principals must differ')
founder_ws=pathlib.Path(first_member['workspace']);founder_home=pathlib.Path(first_member['home'])
second_ws=pathlib.Path(second_member['workspace']);second_home=pathlib.Path(second_member['home'])
first_key=pathlib.Path(json.loads((founder_ws/'workspace.json').read_text())['key'])
provider_key=pathlib.Path(json.loads((pathlib.Path(provider_member['workspace'])/'workspace.json').read_text())['key'])
controller_root=base/'var/lib/mini/controllers'/str(a.task);controller_root.mkdir(mode=0o700,exist_ok=True)
root=controller_root/'receiving';root.mkdir(mode=0o700)
state=controller_root/'state';state.mkdir(mode=0o700,exist_ok=True)
(state/'resident').mkdir(mode=0o700,exist_ok=True)
home=state/'room-home';home.mkdir(mode=0o700)
ws=state/'resource-workspace'
for folder in ('etc','credentials','keys'): (root/folder).mkdir(mode=0o700)
worker=controller_root/'worker-work';worker.mkdir(mode=0o700,exist_ok=True)
fixture_runtime=pathlib.Path(a.fixture_runtime)
controller_config=controller_root/'controller.json';resident_config=controller_root/'resident.json'
controller_unit=f'mini-grain-controller@{a.task}.service'
owned_units=[];owned_system_units=[];owned_processes=[];successful=False
def cleanup():
    for proc in owned_processes:
        if proc.poll() is None:proc.terminate()
    if not (successful and a.preserve_on_success):
        for name in reversed(owned_units):subprocess.run(['systemctl','--user','stop',name],capture_output=True)
        for name in reversed(owned_system_units):subprocess.run(['sudo','-n','systemctl','stop',name],capture_output=True)
atexit.register(cleanup)
FINAL='I read lab-index. Its document alias is lab-index.'
def save(name,value):(root/name).write_text(json.dumps(value,indent=2)+'\n')
def wait(label,predicate,timeout=600):
    end=time.monotonic()+timeout
    while time.monotonic()<end:
        try:
            value=predicate()
            if value:return value
        except (OSError,ValueError,KeyError):pass
        time.sleep(.2)
    raise RuntimeError('timeout: '+label)
checks=[]
def check(label,ok,evidence):
    checks.append({'check':label,'passed':bool(ok),'evidence':evidence});save('checks.json',checks)
    print(('PASS ' if ok else 'FAIL ')+label,flush=True)
    if not ok:raise RuntimeError(label)
save('source-inputs.json',{'platformInputs':str(context_path),'platformInputsSha256':digest(context_path),'manifest':str(manifest_path),'manifestSha256':digest(manifest_path),'journeySha256':digest(__file__),'sharedRoomAlias':a.shared_room_alias,'sharedDocumentReference':a.shared_document_reference,'subjects':{'owner':owner_subject,'tool':tool_subject,'first':first_subject,'second':second_subject,'provider':provider_subject},'fixtureDeadlineSeconds':600})
# The endpoint is a separately managed fixture dependency, kept on success.
provider_unit=f'mini-resident-fixture-provider@{a.task}.service'
provider_source=pathlib.Path(a.fixture_provider)
provider_sha=digest(provider_source)
owned_units.append(provider_unit)
provider_start=subprocess.run(['systemd-run','--user','--collect','--unit='+provider_unit,'--property=Type=exec','--property=Nice=10','--property=KillMode=control-group','--property=StandardOutput=append:'+str(root/'provider.stdout'),'--property=StandardError=append:'+str(root/'provider.stderr'),'/usr/bin/python3',str(provider_source),'--state',str(root)],capture_output=True,text=True)
save('provider-start.json',{'commandSource':str(provider_source),'sourceSha256':provider_sha,'returncode':provider_start.returncode,'stdout':provider_start.stdout,'stderr':provider_start.stderr})
if provider_start.returncode:raise RuntimeError('managed fixture provider failed to start')
provider_ready=wait('managed fixture provider',lambda:json.loads((root/'provider-ready.json').read_text()))
if provider_ready.get('protocol')!='mini-resident-fixture-provider-ready-v1' or provider_ready.get('sourceSha256')!=provider_sha or provider_ready.get('pid',0)<=0:raise RuntimeError('fixture provider readiness differs')
endpoint=provider_ready['endpoint']
with net_socket.socket() as probe:
    probe.bind(('127.0.0.1',0));gateway=f'127.0.0.1:{probe.getsockname()[1]}'
def run(label,words):
    command=[str(x) for x in words];save(label+'.command.json',command)
    start=time.monotonic()
    result=subprocess.run(command,capture_output=True,text=True,timeout=600)
    (root/(label+'.stdout')).write_text(result.stdout)
    (root/(label+'.stderr')).write_text(result.stderr)
    save(label+'.timing.json',{'seconds':time.monotonic()-start,'returncode':result.returncode})
    if result.returncode:raise RuntimeError(label+' refused; retained stderr')
    return result.stdout
# Every mutation below enters the existing native client against supplied Store.
# All caller-selected numeric values are explicit allocation, never evidence.
caps={k:str(a.task*100+i) for k,i in {'parent':71,'parentControl':72,'toolWitness':73,'providerWitness':75,'tool':81,'toolControl':82,'publication':91,'publicationControl':92,'publicationTool':93,'publicationRead':94,'provider':101,'providerControl':102}.items()}
owner_enrollment=next(row for row in genesis['enrollments'] if row['key']['subject']==owner_subject)
account={'target':owner_enrollment['accountId'],'operationCapability':owner_enrollment['spendCapabilityId'],'controlCapability':owner_enrollment['controlCapabilityId']}
save('source-owner-account-hint.json',{'genesisSha256':digest(ctx['genesis']),'subject':owner_subject,'account':account})
nonce=int(time.time_ns()%8_000_000_000)+1_000_000_000
def next_nonce():
    global nonce
    nonce+=2
    return nonce
keys={owner_subject:owner_key,tool_subject:tool_key,provider_subject:provider_key,first_subject:first_key}
def mini_submit(label,intent,signer,kind=None):
    intent_file=root/(label+'-intent.json');intent_file.write_text(json.dumps(intent,indent=2))
    attempt=root/(label+'-attempt')
    words=[a.mini,'submit','--host',a.host,'--config',config,'--socket',socket,'--intent',intent_file,'--key',keys[signer],'--dir',attempt]
    if kind:words.extend(['--intent-kind',kind])
    run(label,words)
    outcome=json.loads((attempt/'outcome.json').read_text())
    if outcome.get('type')!='confirmed':raise RuntimeError('native effect not confirmed; retained exact attempt '+label)
    return outcome

def mini_query(label,subject,target,capability):
    intent={'subject':subject,'nonce':str(next_nonce()),'purpose':{'type':'query','kind':'object','target':str(target),'view':'resource'},'grants':[{'kind':'object','target':str(target),'capability':str(capability)}]}
    intent_file=root/(label+'-query-intent.json');intent_file.write_text(json.dumps(intent))
    attempt=root/(label+'-query')
    run(label,[a.mini,'query','--host',a.host,'--config',config,'--socket',socket,'--intent',intent_file,'--key',keys[subject],'--view','resource','--dir',attempt])
    view=json.loads((attempt/'view.json').read_text());challenge=json.loads((attempt/'challenge.json').read_text())
    return view.get('cell') or view.get('page'),challenge['authorityRoot']

def delegate(label,target,parent,child,holder,verbs):
    cell,authority=mini_query(label+'-pre',owner_subject,target,parent)
    n=next_nonce()
    intent={'subject':owner_subject,'nonce':str(n),'purpose':{'type':'prepare','draft':{'type':'delegate-source','command':{'kind':'object','domain':str(genesis['domain']),'semantics':genesis['expectedSemantics'],'subject':owner_subject,'nonce':str(n+1),'expectedTargetRoot':cell['root'],'parentId':parent,'target':str(target),'expectedPreRoot':authority,'child':{'id':child,'root':parent,'parent':parent,'issuer':str(configured['issuer']),'holder':{'type':'subject','subject':holder},'targets':[str(target)],'verbs':verbs,'maxCost':'50000','notBefore':str(configured['genesisHeight']),'notAfter':str(int(configured['genesisHeight'])+int(configured['lifetime'])-1),'issuerEpoch':genesis['issuerEpoch'],'policyId':str(target),'policyEpoch':'0','ancestors':[parent],'channels':[]}}}},'grants':[{'kind':'object','target':str(target),'capability':parent}]}
    return mini_submit(label,intent,owner_subject)

operator_status=json.loads(run('native-private-operator-preflight',[a.mini,'operator-status','--socket',socket,'--host',a.host,'--config',config]))
if operator_status.get('format')!='mini-operator-drain-v1' or operator_status.get('phase')!='serving' or operator_status.get('admissionClosed') is not False or operator_status.get('hostProcessId',0)<=0 or operator_status.get('hostSha256')!=digest(a.host) or operator_status.get('configSha256')!=digest(config):raise RuntimeError('shared source private operator role/pins not ready')
birth_nonce=next_nonce()
birth={'subject':owner_subject,'nonce':str(birth_nonce),'birth':{'genesis':genesis,'template':{'issuer':str(configured['issuer']),'ownerBudget':str(configured['ownerBudget']),'lifetime':str(configured['lifetime'])},'creator':owner_subject,'nonce':str(birth_nonce),'resources':[
    {'kind':'object','storage':'grain','target':str(a.task),'owner':owner_subject,'ownerCapability':caps['parent'],'controlCapability':caps['parentControl'],'budget':'1000','workerSubjects':[tool_subject,provider_subject],'workerGeneration':'1'},
    {'kind':'object','storage':'grain','target':str(a.task+1),'owner':tool_subject,'ownerCapability':caps['tool'],'controlCapability':caps['toolControl'],'budget':'1000'},
    {'kind':'object','storage':'declared','target':str(a.task+2),'owner':owner_subject,'ownerCapability':caps['publication'],'controlCapability':caps['publicationControl'],'predicate':{'type':'all','predicates':[]}},
    {'kind':'object','storage':'grain','target':str(a.task+3),'owner':provider_subject,'ownerCapability':caps['provider'],'controlCapability':caps['providerControl'],'budget':'300000'}],
    'sourceCapabilities':[account['operationCapability']],'funding':[],'feePayer':owner_subject},'grants':[{'kind':'object','target':ctx['authority']['factory']['target'],'capability':ctx['authority']['factory']['ownerCapability']},{'kind':'account','target':account['target'],'capability':account['operationCapability']}]}
if 'grainBirthTariff' in configured:birth['birth']['grainBirthTariff']={k:str(v) for k,v in configured['grainBirthTariff'].items()}
born=mini_submit('resident-native-birth',birth,owner_subject,'birth-intent')
delegations=[delegate('resident-parent-tool',a.task,caps['parent'],caps['toolWitness'],tool_subject,['observe','mutate']),delegate('resident-parent-provider',a.task,caps['parent'],caps['providerWitness'],provider_subject,['observe','mutate']),delegate('resident-publication-tool',a.task+2,caps['publication'],caps['publicationTool'],tool_subject,['observe','mutate']),delegate('resident-publication-read',a.task+2,caps['publication'],caps['publicationRead'],tool_subject,['observe'])]
check('resident tasks born and delegated on supplied Store',born['type']=='confirmed' and all(d['type']=='confirmed' for d in delegations),{'birth':born,'delegations':delegations,'caps':caps})
# Reuse the existing source-enrolled management key; init does not rotate it.
tool_enrollment=next(row for row in genesis['enrollments'] if row['key']['subject']==tool_subject)
tool_context={'type':'minidregg-participant-birth-context-v1','genesis':genesis,'template':{'issuer':str(configured['issuer']),'ownerBudget':str(configured['ownerBudget']),'lifetime':str(configured['lifetime'])},'sourceCapabilities':[tool_enrollment['spendCapabilityId']],'funding':[],'feePayer':tool_subject,'grants':[{'kind':'object','target':str(configured['factoryId']),'capability':ctx['authority']['factory']['managementCapability']},{'kind':'account','target':tool_enrollment['accountId'],'capability':tool_enrollment['spendCapabilityId']}]}
save('tool-birth-context.json',tool_context)
run('resident-tool-workspace',[a.mini,'workspace','--action','init','--no-prerotation','--host',a.host,'--config',config,'--socket',socket,'--key',tool_key,'--subject',tool_subject,'--birth-context',root/'tool-birth-context.json','--dir',ws])
run('resident-tool-factory-ref',[a.mini,'workspace','--action','import','--dir',ws,'--name','factory','--kind','object','--target',configured['factoryId'],'--observe-capability',ctx['authority']['factory']['managementCapability']])
run('resident-tool-account-ref',[a.mini,'workspace','--action','import','--dir',ws,'--name','account','--kind','account','--target',tool_enrollment['accountId'],'--observe-capability',tool_enrollment['spendCapabilityId'],'--operation-capability',tool_enrollment['spendCapabilityId'],'--control-capability',tool_enrollment['controlCapabilityId']])
member_socket=ctx['publicSocket']
def shell(label,line):
    return run(label,[a.mini,'shell','--socket',member_socket,'--host',a.host,'--config',config,
        '--workspace',founder_ws,'--home',founder_home,'--line',line])
room_alias=a.shared_room_alias
if not re.fullmatch(r'[A-Za-z0-9-]{1,48}',room_alias):raise RuntimeError('supplied source room alias malformed')
room_cell=json.loads((founder_ws/'refs'/(room_alias+'.json')).read_text())['target']
shell('shared-room-native-read','tail --in '+room_alias+' --json -n 1')
shared_document_ref=pathlib.Path(a.shared_document_reference)
existing_document_ref=json.loads(shared_document_ref.read_text())
capture_alias=existing_document_ref['name']
if not re.fullmatch(r'[A-Za-z0-9-]{1,64}',capture_alias) or shared_document_ref.resolve()!=(founder_ws/'refs'/(capture_alias+'.json')).resolve():raise RuntimeError('supplied shared document reference is not the founder bound alias')
existing_document_target=existing_document_ref['target']
shell('capture-destination-native-read','doc show '+capture_alias)
room_context={'protocol':'mini-resident-room-capture-request-v1','worldConfig':config,'socket':member_socket,'founderSubject':first_subject,'founderWorkspace':str(founder_ws),'founderHome':str(founder_home),'roomAlias':room_alias,'roomTarget':room_cell,'documentAlias':capture_alias,'documentTarget':existing_document_target}
save('room-context.json',room_context)
print('CAPTURE ROOM READY '+str(root/'room-context.json'),flush=True)
capture_path=pathlib.Path(a.capture_reference)
capture=wait('source app capture/document publication',lambda:json.loads(capture_path.read_text()),1800)
expected={'protocol':'mini-captured-document-room-context-v1','worldConfig':config,'socket':member_socket,'founderSubject':first_subject,'founderWorkspace':str(founder_ws),'roomAlias':room_alias,'roomTarget':room_cell,'documentAlias':capture_alias,'documentTarget':existing_document_target}
if any(capture.get(k)!=v for k,v in expected.items()):raise RuntimeError('captured document coordinates differ from supplied source room')
captured_alias=capture['documentAlias'];captured_target=capture['documentTarget']
if not isinstance(captured_alias,str) or not re.fullmatch(r'[A-Za-z0-9-]{1,64}',captured_alias) or not isinstance(captured_target,str) or not re.fullmatch(r'[1-9][0-9]*',captured_target):raise RuntimeError('captured alias/target malformed')
ref=json.loads((founder_ws/'refs'/(captured_alias+'.json')).read_text())
if ref['target']!=captured_target:raise RuntimeError('captured target differs from native workspace reference')
run('captured-document-current-read',[a.mini,'shell','--socket',member_socket,'--host',a.host,'--config',config,'--workspace',founder_ws,'--home',founder_home,'--line','doc show '+captured_alias])
save('captured-source-context.json',{'reference':capture,'referenceSha256':digest(capture_path),'nativeRef':ref})
FINAL='I read '+captured_alias+'. Its document alias is '+captured_alias+'.'
summary_alias=f'resident-summary-{a.task}'
shell('room-summary',f"doc new {summary_alias} 'any [ not (verb == write), subject == {first_subject}, subject == {tool_subject} ]' --in {room_alias}")
program_dir=founder_home/'requests';program_dir.mkdir(mode=0o700,exist_ok=True)
program_name=f'resident-{a.task}-captured-job.txt'
(program_dir/program_name).write_text('- **Inputs** (read, never write): '+captured_alias+'\n- **Outputs** (write): '+summary_alias+'\nRead the signed current input, append a concise verified summary to '+summary_alias+', read it back, then reply to the addressed source request.\n')

shell('room-tariff',f'tariff {room_alias} set hermes/turn 1')
room_cell=json.loads((founder_ws/'refs'/(room_alias+'.json')).read_text())['target']
(home/'inbox').mkdir(mode=0o700,exist_ok=True)
registrations=root/'dispatch-registrations';registrations.mkdir(mode=0o700)
registration=json.loads(run('native-resident-registration',[a.mini,'hermes-handoff','--action','registration','--dir',ws,'--task',a.task,'--room-cell',room_cell,'--inbox',home/'inbox']))
dispatch_registration=registrations/(str(a.task)+'.json');dispatch_registration.write_text(json.dumps(registration))
public_registry=json.loads(run('native-public-resident-registry',[a.mini,'hermes-handoff','--action','registry','--registrations',registrations]))
registry=founder_home/'hermes';registry.mkdir(mode=0o700,exist_ok=True)
public_registry_path=registry/'registry.json'
if public_registry_path.exists():raise RuntimeError('retained founder public registry already exists; no overwrite')
public_registry_path.write_text(json.dumps(public_registry))
shell('room-invite-second',f'chat invite {room_alias} {second_subject} second')
invitation=json.loads((founder_home/f'chat/invites/{room_alias}-{second_subject}.json').read_text())
# Join uses a source-produced invitation, not an invented room reference.
second_requests=second_home/'requests';second_requests.mkdir(mode=0o700,exist_ok=True)
(second_requests/f'resident-{a.task}-lab-invite.json').write_text(json.dumps(invitation))
def second_shell(label,line):
    return run(label,[a.mini,'shell','--socket',member_socket,'--host',a.host,'--config',config,'--workspace',second_ws,'--home',second_home,'--line',line])
second_shell('second-join',f'chat join {room_alias} @resident-{a.task}-lab-invite.json')
shell('room-summon',f'summon {room_alias} as runner --program @{program_name} --budget 1000')
bundles=list((founder_home/'outbox'/tool_subject).glob('room-'+room_cell+'/assignment-*/handoff.json'))
if len(bundles)!=1: raise RuntimeError('expected one source-bound handoff')
dispatched=json.loads(run('native-dispatch',[a.mini,'hermes-handoff','--socket',socket,'--action','dispatch','--registration',dispatch_registration,'--bundle',bundles[0]]))
inbox=pathlib.Path(dispatched['inbox'])
checked=json.loads(run('native-delivery-check',[a.mini,'hermes-handoff','--socket',socket,'--action','check-delivery','--dir',ws,'--task',a.task,'--inbox',inbox]))
activation=json.loads(run('native-current-assignment-activation',[a.mini,'hermes-handoff','--action','activation','--registration',dispatch_registration]))
if activation.get('type')!='mini-hermes-assignment-activation-v1' or any(activation.get(k)!=checked.get(k) for k in ('task','world','roomCell','assignment','account')) or activation['inbox']!=str(inbox):raise RuntimeError('native activation/check-delivery binding differs')
account=activation['account']['name']
shell('member-request',f'ask {room_alias} Request A: read {captured_alias}, write {summary_alias}, verify it, and reply to this source message.')
second_shell('second-request',f'ask {room_alias} Request B: read {captured_alias}, write {summary_alias}, verify it, and reply to this source message.')
for i in range(129):
    shell(f'prepoll-filler-{i:03d}',f'say --in {room_alias} Before-poll ordinary message {i:03d}')
    if i%32==31: print(f'Native pre-poll history {i+1}/129',flush=True)
save('assignment.json',{'checked':checked,'activation':activation,'dispatch':dispatched,'inbox':str(inbox),'account':account,'roomCell':room_cell})
key=root/'etc/credentials.key'
fd=os.open(key,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
os.write(fd,os.urandom(32)); os.close(fd)
table={'type':'mini-provider-table-v2','providers':[{'name':'resident-fixture-pool','endpoint':endpoint,
    'kind':'openai-compatible','models':['mini-hermes-completion-cut'],'credential':'pool','caps':{'perCall':'2048','perDay':'40'}}]}
(root/'providers-source.json').write_text(json.dumps(table,indent=2))
canonical_table=base/'etc/mini/providers.json';canonical_key=base/'etc/mini/credentials.key'
copy_request={'protocol':'mini-resident-provider-custody-copy-v1','task':str(a.task),'table':{'source':str(root/'providers-source.json'),'sha256':digest(root/'providers-source.json'),'target':str(canonical_table)},'key':{'source':str(key),'sha256':digest(key),'target':str(canonical_key)},'provider':'resident-fixture-pool'}
save('provider-copy-request.json',copy_request)
print('PROVIDER CUSTODY COPY READY '+str(root/'provider-copy-request.json'),flush=True)
ack_path=root/'provider-copy-ready.json'
ack=wait('root canonical provider custody publication',lambda:json.loads(ack_path.read_text()),1800)
if ack.get('protocol')!='mini-resident-provider-custody-ready-v1' or ack.get('task')!=str(a.task) or ack.get('requestSha256')!=digest(root/'provider-copy-request.json'):raise RuntimeError('root provider copy acknowledgment differs')
if digest(canonical_table)!=copy_request['table']['sha256'] or digest(canonical_key)!=copy_request['key']['sha256']:raise RuntimeError('canonical provider custody bytes differ')
if canonical_table.stat().st_uid!=0 or canonical_table.stat().st_mode&0o022 or canonical_key.stat().st_uid!=os.getuid() or canonical_key.stat().st_mode&0o077:raise RuntimeError('canonical provider custody owner/mode refused')
key=canonical_key

runtime={'mini':a.mini,'host':a.host,'hostConfig':config,'hostSocket':socket,
    'controlSocket':str(state/'control.sock'),'custodyKey':str(owner_key),
    'stateDir':str(state),'cwd':str(controller_root),'task':str(a.task),'subject':owner_subject,'capability':caps['parent'],'queryCapability':caps['parent'],'policyControlCapability':caps['parentControl'],
    'toolTask':{'task':str(a.task+1),'subject':tool_subject,'capability':caps['tool'],'queryCapability':caps['tool'],'custodyKey':str(tool_key),
        'parentCapability':caps['toolWitness'],'parentObserveCapability':caps['toolWitness'],'reserve':'2','charge':'1',
        'resourceWorkspace':str(ws),'room':{'mini':a.mini,'host':a.host,'hostConfig':config,'socket':socket,
            'workspace':str(ws),'home':str(home),'room':room_alias,'account':account,'restrictTools':True},
        'allowedPublications':[{'kind':'object','target':str(a.task+2),'capability':caps['publicationTool'],'observeCapability':caps['publicationTool']}],
        'allowedReads':[{'name':'publication','kind':'object','target':str(a.task+2),'observeCapability':caps['publicationRead'],'maxResultBytes':65536}]},
    'providerTask':{'task':str(a.task+3),'subject':provider_subject,'capability':caps['provider'],'queryCapability':caps['provider'],'custodyKey':str(provider_key),
        'parentCapability':caps['providerWitness'],'parentObserveCapability':caps['providerWitness'],'reserve':'7000','provider':'resident-fixture-pool','contextWindowTokens':262144,'maxInputTokens':16384,'maxOutputTokens':2048,
        'onBehalfOf':{'subject':first_subject,'publicKey':nacl.signing.SigningKey(first_key.read_bytes()).verify_key.encode().hex()},
        'model':'mini-hermes-completion-cut','providers':str(canonical_table),'credentialsRoot':str(base/'var/lib/mini/credentials'),
        'credentialsKey':str(key),'gatewayBind':gateway,'maxRequestBytes':32768,'maxResponseBytes':524288,'maxIterations':1,
        'timeoutSeconds':600,'localFixtureHostNetwork':True},
    'commands':[{'name':'hermes-acp','program':str(pathlib.Path(a.launch_gate).parent/'bwrap'),
        'args':['--workspace',str(controller_root/'worker-work'),'--runtime-root',str(fixture_runtime),'--network','host','--','/agent/hermes-acp'],
        'systemdScope':True,'wallTimeSeconds':900,'reserve':'3','charge':'1'}]}
(root/'fixture-pool-key').write_text('completion-cut-local-fixture-key\n')
run('install-fixture-key',[a.mini,'key','--action','set','--pool','true','--provider','resident-fixture-pool','--secret',root/'fixture-pool-key','--providers',canonical_table,'--credentials',root/'credentials','--credentials-key',key])
# Preserve source-created encrypted custody and key; canonical root was provisioned by the root service.
canonical_pool=base/'var/lib/mini/credentials/_pool'
pool_stat=canonical_pool.stat()
if canonical_pool.is_symlink() or pool_stat.st_uid!=os.getuid() or pool_stat.st_mode&0o077: raise RuntimeError('fresh owner-private canonical pool required')
copied=[]
for original in sorted((root/'credentials/_pool').iterdir()):
    if not original.is_file() or original.is_symlink(): raise RuntimeError('unexpected fixture credential entry')
    destination=canonical_pool/original.name
    with open(destination,'xb') as stream:
        stream.write(original.read_bytes());stream.flush();os.fsync(stream.fileno())
    os.chmod(destination,0o600)
    if digest(original)!=digest(destination): raise RuntimeError('encrypted custody copy differs')
    copied.append({'original':str(original),'canonical':str(destination),'sha256':digest(destination)})
directory_fd=os.open(canonical_pool,os.O_RDONLY|os.O_DIRECTORY)
os.fsync(directory_fd);os.close(directory_fd)
save('canonical-credential-copy.json',copied)
controller_config.write_text(json.dumps(runtime,indent=2))
resident_config.write_text(json.dumps({'type':'mini-hermes-room-resident-v1','controller':str(controller_config),
    'inbox':str(inbox),'state':str(state/'resident'),'maxPrompts':2,'intervalSeconds':5},indent=2))
save('ready.json',{'config':config,'socket':socket,'controller':str(controller_config),'resident':str(resident_config),'sharedWorld':str(context_path)})
print('RESIDENT SOURCE READY '+str(root/'ready.json'),flush=True)
if not a.registration: raise SystemExit('controller start requires explicit operator-installed --registration')
print('AWAIT ROOT REGISTRATION '+str(a.registration),flush=True)
wait('root-installed controller registration',lambda:pathlib.Path(a.registration).is_file(),900)
# Registrar --json reports its canonical registry in a receipt. Native runtime
# must receive that actual root registration, never the output receipt itself.
registration_receipt=json.loads(pathlib.Path(a.registration).read_text())
launch=registration_receipt.get('launch')
if not isinstance(launch,dict) or launch.get('protocol')!='mini-controller-launch-v1': raise RuntimeError('typed root launch descriptor required')
if launch.get('runtime')!=a.grain or launch.get('config')!=str(controller_config) or launch.get('unit')!=controller_unit: raise RuntimeError('typed root launch identity differs')
launch_environment=launch['environment']
a.registration=launch['runtimeRegistry']
controller_manager=launch['manager'];worker_manager=launch['workerManager']
if controller_manager=='system':
    owned_system_units.append(controller_unit)
    starter=['sudo','-n','systemd-run','--uid='+str(launch['serviceUid']),'--gid='+str(pwd.getpwuid(launch['serviceUid']).pw_gid),'--property=Type=exec']
else:
    owned_units.append(controller_unit);starter=['systemd-run','--user']
run('start-controller',[*starter,'--collect','--unit='+controller_unit,
    '--property=Nice=10','--property=KillMode=control-group',*['--setenv='+k+'='+v for k,v in launch_environment.items()],*([] if a.preserve_on_success else ['--property=RuntimeMaxSec=1800s']),
    '--property=StandardOutput=append:'+str(root/'controller.stdout'),'--property=StandardError=append:'+str(root/'controller.stderr'),
    a.grain,'serve',controller_config])
wait('controller admin socket',lambda:(state/'admin.sock').exists())
def journal(): return json.loads((state/'journal.json').read_text())
def resident(): return json.loads((state/'resident/resident.json').read_text())
def driver(label):
    env=os.environ.copy();env.update(launch_environment)
    proc=subprocess.Popen([a.grain,'hermes-room','resident',str(resident_config)],stdout=open(root/(label+'.stdout'),'wb'),stderr=open(root/(label+'.stderr'),'wb'),env=env)
    owned_processes.append(proc);return proc
def exact_one(pattern):
    paths=list(state.glob(pattern))
    if len(paths)!=1: raise RuntimeError('expected one '+pattern+', got '+str(paths))
    return paths[0]
def source_query(label,target,capability,subject=owner_subject):
    cell,_=mini_query(label,subject,target,capability)
    return cell['grain']
def room_entries(label):
    output=run(label,[a.mini,'shell','--socket',socket,'--host',a.host,'--config',config,'--workspace',ws,'--home',home,'--line',f'tail --in {room_alias} --json -n 500'])
    return [json.loads(line) for line in output.splitlines() if line.startswith('{')]
def requests(): return json.loads((state/'resident/requests.json').read_text())
def provider_records(): return json.loads((root/'provider-received.json').read_text()) if (root/'provider-received.json').exists() else []
def calls(): return len(provider_records())
till_before=run('before-receive-till',[a.mini,'credit','--action','balance','--dir',founder_ws,'--account',room_alias+'-till'])
book_before=run('before-receive-account',[a.mini,'credit','--action','balance','--dir',ws,'--account',account])
first=driver('driver-before-cut')
gate=wait('real ACP end_turn gate',lambda:json.loads((controller_root/'worker-work/end-turn-gate.json').read_text()) if first.poll() is None else (_ for _ in ()).throw(RuntimeError('driver failed before cut; see stderr')),600)
FINAL=provider_records()[0]['reply']
before=resident(); selected=requests()['selected'];save('resident-before-kill.json',before);save('selected-before-kill.json',selected)
check('signed handoff and old initial request selected before provider',selected['identity']['author']==first_subject and selected['entry']['text'].startswith('Request A') and selected['identity']['binding']['assignment']==checked['assignment'] and before['completed']==0 and calls()==1,{'selected':selected,'ready':checked,'providerCalls':calls()})
for i in range(110):
    second_shell(f'held-filler-{i:03d}',f'say --in {room_alias} During-held-reply ordinary message {i:03d}')
    if i%32==31: print(f'Native held-reply history {i+1}/110',flush=True)
first.kill();first.wait(timeout=10)
check('only driver killed after source advanced beyond tail100',first.returncode==-signal.SIGKILL and (state/'admin.sock').exists(),{'gate':gate,'heldMessages':110})
(controller_root/'worker-work/release-end-turn').write_text('release genuine source end_turn after driver death\n')
turn=wait('source completion without driver',lambda:journal().get('residentCompletion') if journal().get('child') is None and journal().get('parentHold') is None and journal().get('providerHold') is None else None,600)
check('native completion staged without driver counter edit',resident()==before and journal().get('residentDelivery') is not None,{'source':turn,'resident':resident()})
second=driver('driver-receive');second.wait(timeout=600)
check('restart drains old exact reply then other author',second.returncode==0 and resident()['completed']==2 and resident()['pending'] is None and calls()==2,{'resident':resident(),'providerCalls':calls(),'stderr':(root/'driver-receive.stderr').read_text()})
outcomes=[json.loads(p.read_text()) for p in (state/'resident').glob('request-*-completed.json')]
deliveries=[json.loads(p.read_text()) for p in state.glob('resident-delivered-*.json')]
check('both model frames consumed the actual native captured input',calls()==2 and all(row['reply']==FINAL and row['nativeInputTextSha256']==provider_records()[0]['nativeInputTextSha256'] for row in provider_records()),{'providerInputHashes':[row['nativeInputTextSha256'] for row in provider_records()],'sourceReference':capture})
check('two source request identities completed once',len(outcomes)==2 and {x['identity']['author'] for x in outcomes}=={first_subject,second_subject} and all('modelRequests' not in x for x in outcomes),outcomes)
check('native finals match two addressed source refs',len(deliveries)==2 and {d['result']['arguments']['to'] for d in deliveries}=={first_subject,second_subject} and all(d['result']['expectedReply'] and d['result']['payment']['paid'] for d in deliveries),deliveries)
summary_ref=json.loads((founder_ws/'refs'/(summary_alias+'.json')).read_text())
summary_cell,_=mini_query('summary-native-atom-classification',first_subject,summary_ref['target'],summary_ref['observeCapability'])
summary_atoms=[row for row in summary_cell['entries'] if row.get('type')=='atom' and row.get('tombstonedAt') is None]
summary_kinds={row['kind']['type'] for row in summary_atoms}
summary_privacy='sealed-object' if summary_kinds=={'sealedObject'} else 'public-text' if summary_kinds=={'text'} else 'mixed-or-other'
check('summary confidentiality classified from signed native atom kinds',bool(summary_atoms) and summary_kinds<={'text','sealedObject'} and all(row['kind']['fragment']['ciphertext'] for row in summary_atoms if row['kind']['type']=='sealedObject'),{'classification':summary_privacy,'target':summary_ref['target'],'kinds':sorted(summary_kinds),'nativeView':str(root/'summary-native-atom-classification-query/view.json')})
entries=room_entries('signed-delivered-history')
check('one signed final per author despite late delivery',all(len([e for e in entries if e.get('author')==tool_subject and e.get('to')==author and e.get('text')==FINAL])==1 for author in (first_subject,second_subject)),entries)
after=resident();before_journal=journal()
def native_balances(tag):
    return {'provider':source_query(tag+'-provider',a.task+3,caps['provider'],provider_subject),'tool':source_query(tag+'-tool',a.task+1,caps['tool'],tool_subject),'parent':source_query(tag+'-parent',a.task,caps['parent'])}
replay_before=native_balances('before-replay')
book_after=run('after-receive-account',[a.mini,'credit','--action','balance','--dir',ws,'--account',account])
till_after=run('after-receive-till',[a.mini,'credit','--action','balance','--dir',founder_ws,'--account',room_alias+'-till'])
def credit_value(text):
    if not text.startswith('credit '): raise RuntimeError('unexpected native signed balance')
    return int(text.split()[1])
payments=[r['payment'] for r in journal()['roomResolutions'] if r['tool'] in ('mini_say','mini_doc_append')]
prices=sum(int(p['price']) for p in payments)
fees=sum(int(p['fee']) for p in payments)
check('four native Book payments cover two policy-controlled summaries and two addressed replies exactly once',prices==4 and len(payments)==4 and credit_value(till_after)-credit_value(till_before)==prices and credit_value(book_before)-credit_value(book_after)==prices+fees,{'allowanceBefore':book_before,'allowanceAfter':book_after,'tillBefore':till_before,'tillAfter':till_after,'prices':prices,'fees':fees})
for request_path in (state/'resident').glob('completion-request-*.json'):
    run('replay-'+request_path.stem,[a.grain,'resident-completion','receive',state/'admin.sock',request_path])
for request_path in (state/'resident').glob('delivery-request-*.json'):
    run('replay-'+request_path.stem,[a.grain,'resident-delivery','deliver',state/'admin.sock',request_path])
third=driver('driver-repeat');third.wait(timeout=120)
check('exact receiver replay does not call or charge provider',third.returncode==0 and resident()==after and calls()==2 and native_balances('after-replay')==replay_before and run('after-replay-account',[a.mini,'credit','--action','balance','--dir',ws,'--account',account])==book_after,{'providerCalls':calls(),'nativeBalances':replay_before})
check('native finals leave no uncertain holds',len([r for r in journal().get('roomResolutions',[]) if r.get('tool')=='mini_say'])==2 and all(journal().get(k) is None for k in ('residentCompletion','residentDelivery','roomAttempt','parentHold','toolHold','providerHold','child','pending')),journal())
# Continuous provisioning: removing fixture-only maxPrompts must not dispatch
# unchanged maintenance immediately after selected request completion.
continuous=json.loads(resident_config.read_text());continuous.pop('maxPrompts');resident_config.write_text(json.dumps(continuous,indent=2))
# Config is outside the controller's signed pin and controls only the driver.
fourth=driver('driver-continuous');time.sleep(12)
check('continuous unchanged maintenance makes zero extra provider calls',fourth.poll() is None and calls()==2 and resident()==after,{'providerCalls':calls(),'maintenance':requests().get('maintenanceRevision')})
fourth.terminate();fourth.wait(timeout=10)
resident_unit=None
if a.preserve_on_success:
    resident_unit=registration_receipt['residentUnit']
    if registration_receipt.get('residentConfig')!=str(resident_config) or registration_receipt.get('residentState')!=str(state/'resident') or registration_receipt.get('residentInbox')!=str(inbox):raise RuntimeError('root resident launch coordinates differ')
    (owned_system_units if controller_manager=='system' else owned_units).append(resident_unit)
    resident_entry=base/'usr/local/lib/mini/controller-entry.py'
    run('retain-continuous-resident',[*starter,'--collect','--unit='+resident_unit,'--property=Nice=10','--property=KillMode=control-group','--setenv=MINI_ROOT='+str(base),'--property=StandardOutput=append:'+str(root/'resident-live.stdout'),'--property=StandardError=append:'+str(root/'resident-live.stderr'),resident_entry,'resident',str(a.task)])
    resident_manager_command=['sudo','-n','systemctl'] if controller_manager=='system' else ['systemctl','--user']
    wait('retained resident unit active',lambda:subprocess.run([*resident_manager_command,'is-active',resident_unit],capture_output=True,text=True).stdout.strip()=='active',10)
save('result.json',{'type':'mini-resident-multi-author-cut-result-v1','passed':all(r['passed'] for r in checks),'checks':len(checks),'providerCalls':calls(),'assignment':checked,'cut':'SIGKILL driver after >100 source rows; native source completion then unchanged restart','provider':'scripted local SSE; no paid provider qualification','summaryConfidentiality':summary_privacy})
save('controller-inventory.json',{'protocol':'mini-resident-controller-inventory-v1','task':str(a.task),'controller':str(controller_config),'residentConfig':str(resident_config),'stateDir':str(state),'runtimeRegistry':a.registration,'unit':controller_unit,'manager':controller_manager,'workerManager':worker_manager,'environment':launch_environment,'sourceManifest':str(manifest_path),'sourceManifestSha256':digest(manifest_path),'retainedOnSuccess':a.preserve_on_success,'providerUnit':provider_unit,'providerManager':'user','providerServiceUid':os.getuid(),'providerStateDir':str(root),'providerEndpoint':endpoint,'providerSource':str(provider_source),'providerSourceSha256':provider_sha,'residentUnit':resident_unit,'residentManager':controller_manager,'residentEntry':str(base/'usr/local/lib/mini/controller-entry.py')})
successful=True
print(root/'result.json',flush=True)
if a.preserve_on_success:print('RESIDENT LIVE '+str(root/'controller-inventory.json'),flush=True)
