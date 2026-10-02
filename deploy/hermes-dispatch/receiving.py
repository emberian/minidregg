#!/usr/bin/env python3
"""Fresh native room receiving; no provider or external paid calls."""
import argparse, hashlib, json, os, subprocess, threading, time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--manifest',required=True);p.add_argument('--mini',required=True);p.add_argument('--root',required=True);p.add_argument('--pump',required=True);p.add_argument('--resume-through',type=int,default=0);a=p.parse_args()
os.umask(0o077);R=Path(a.root);R.mkdir(mode=0o700,exist_ok=bool(a.resume_through));(R/'logs').mkdir(mode=0o700,exist_ok=bool(a.resume_through))
M=json.loads(Path(a.manifest).read_text());W=R/'world';SOCK=str(W/'public/mini.sock');HOST=M['host'];CONFIG=str(W/'deployment/pinned-config.json');N=0

def run(argv,ok=True,label=None,env=None):
 global N
 N+=1;n=N
 if n<=a.resume_through:
  prior=json.loads((R/'logs'/f'{n}.args.json').read_text());assert prior==list(map(str,argv)),(n,prior,argv)
  print(n,'retained',label or argv[1],flush=True);return (R/'logs'/f'{n}.out').read_text()
 result=subprocess.run(list(map(str,argv)),capture_output=True,text=True,env=env)
 (R/'logs'/f'{n}.out').write_text(result.stdout);(R/'logs'/f'{n}.err').write_text(result.stderr);(R/'logs'/f'{n}.args.json').write_text(json.dumps(list(map(str,argv))))
 print(n,result.returncode,label or argv[1],flush=True)
 if (result.returncode==0)!=ok:raise RuntimeError(f'{n}: unexpected status {result.returncode}: {result.stderr[-2000:]}')
 return result.stdout

def mini(*args,**kw):return run([a.mini,*args],**kw)
def shell(line):return mini('shell','--socket',SOCK,'--host',HOST,'--config',CONFIG,'--workspace',W/'sponsor','--home',R/'member','--line',line)
def hh(action,*args,**kw):return mini('hermes-handoff','--socket',SOCK,'--action',action,*args,**kw)
def write(path,obj):path.parent.mkdir(mode=0o700,parents=True,exist_ok=True);path.write_text(json.dumps(obj));path.chmod(0o600)

mini('keygen','--secret',R/'resident.key','--public',R/'resident.pub')
public=(R/'resident.pub').read_bytes().hex()
write(R/'enroll.json',[{'key':{'keyId':'8008','keyEpoch':'2','algorithm':'1','subject':'8','publicKey':public,'activeFrom':'0','activeUntil':'1000000','nextKeyDigest':None},'accountId':'8','spendCapabilityId':'8042','controlCapabilityId':'8052','factoryObserveCapabilityId':'8055','initialBalance':'100','accountPredicate':{'type':'all','predicates':[]}}])
env=dict(os.environ,EXTRA_GENESIS_ENROLLMENTS=str(R/'enroll.json'))
run(['sh',str(Path(M['fixtureSource'])/'native/resource-client/newparticipant-acceptance.sh'),HOST,a.mini,M['store'],M['verifier'],W],env=env,label='fresh-bootstrap')
mini('workspace','--action','init','--host',HOST,'--config',CONFIG,'--socket',SOCK,'--key',R/'resident.key','--subject','8','--no-prerotation','--namespace-root',W/'namespace','--dir',R/'resident-ws')
(R/'resident-home').mkdir(mode=0o700,exist_ok=True)
identity=json.loads(mini('shell','--socket',SOCK,'--host',HOST,'--config',CONFIG,'--workspace',R/'resident-ws','--home',R/'resident-home','--line','whoami'))
shell('chat new lab');cell=json.loads((W/'sponsor/refs/lab.json').read_text())['target']
reg={'type':'mini-hermes-dispatch-registration-v1','subject':'8','task':'71','roomCell':cell,'encryptionKey':identity['encryptionKey'],'workspace':str(R/'resident-ws'),'inbox':str(R/'inbox')}
(R/'inbox').mkdir(mode=0o700,exist_ok=True);write(R/'registrations/resident.json',reg)
publicreg=json.loads(hh('registry','--registrations',R/'registrations'));write(R/'member/hermes/registry.json',publicreg)
shell('tariff lab set open 1');tariff=shell('tariff lab');assert any(line.split()==['open','1'] for line in tariff.splitlines()),tariff
shell('summon lab as librarian --hermes 8 --budget 20')
bundle=next((R/'member/outbox/8'/f'room-{cell}').glob('assignment-*/handoff.json'));inbox=R/'inbox'/bundle.parent.parent.name/bundle.parent.name
write(R/'pump.json',{'type':'mini-hermes-dispatch-service-v1','mini':a.mini,'socket':SOCK,'registrationsDir':str(R/'registrations'),'memberHomes':[str(R/'member')]})
run(['python3',a.pump,'--config',R/'pump.json','--once'],label='real-pump-once')
assert (inbox/'ready.json').is_file(),'pump did not publish ready'
ready=json.loads(hh('check-delivery','--dir',R/'resident-ws','--task','71','--inbox',inbox));assert ready['roomCell']==cell
hh('dispatch','--registration',R/'registrations/resident.json','--bundle',bundle)
for key,value in [('subject','9'),('task','72'),('roomCell','999'),('encryptionKey','00'*32)]:
 bad=dict(reg);bad[key]=value;write(R/f'bad-{key}.json',bad)
 hh('dispatch','--registration',R/f'bad-{key}.json','--bundle',bundle,ok=False,label='refuse-registration-'+key)
hh('check-delivery','--dir',R/'resident-ws','--task','72','--inbox',inbox,ok=False,label='refuse-wrong-task')
wsfile=R/'resident-ws/workspace.json';original=wsfile.read_bytes();ws=json.loads(original);wrong=json.loads(Path(CONFIG).read_text());wrong['expectedSeed']=int(wrong['expectedSeed'])+1;write(R/'wrong-world.json',wrong);ws['config']=str(R/'wrong-world.json');write(wsfile,ws)
try:hh('check-delivery','--dir',R/'resident-ws','--task','71','--inbox',inbox,ok=False,label='refuse-wrong-world')
finally:wsfile.write_bytes(original)
# Current source writes by another actor while receiving must not starve admission.
errors=[]
def writer():
 for i in range(3):
  result=subprocess.run([a.mini,'clock','--socket',SOCK,'--action','tick','--workspace',W/'clock'],capture_output=True,text=True)
  (R/'logs'/f'writer-{i}.json').write_text(json.dumps({'status':result.returncode,'out':result.stdout,'err':result.stderr}))
  if result.returncode:errors.append(result.stderr)
t=threading.Thread(target=writer);t.start();hh('check-delivery','--dir',R/'resident-ws','--task','71','--inbox',inbox,label='ready-during-writes');t.join();assert not errors,errors
mini('workspace','--socket',SOCK,'--action','continuity-init','--dir',W/'sponsor','--name','factory')
mini('adopt-next-key','--socket',SOCK,'--workspace',W/'sponsor','--next-key',W/'sponsor.key.next')
mini('rotate-key','--socket',SOCK,'--workspace',W/'sponsor','--next-key',W/'sponsor.key.next')
hh('check-delivery','--dir',R/'resident-ws','--task','71','--inbox',inbox,label='ready-after-founder-rotation')
hh('dispatch','--registration',R/'registrations/resident.json','--bundle',bundle,label='exact-retry-after-rotation')
shell('dismiss lab');dismiss=bundle.parent/'dismissal.json'
run(['python3',a.pump,'--config',R/'pump.json','--once'],label='dismiss-pump-once')
hh('check-dismissal','--dir',R/'resident-ws','--task','71','--inbox',inbox)
hh('check-delivery','--dir',R/'resident-ws','--task','71','--inbox',inbox,ok=False,label='refuse-dismissed-assignment')
shell('summon lab as librarian --hermes 8 --budget 20')
second=[x for x in bundle.parent.parent.glob('assignment-*/handoff.json') if x!=bundle][0]
run(['python3',a.pump,'--config',R/'pump.json','--once'],label='replacement-pump-once')
newinbox=R/'inbox'/second.parent.parent.name/second.parent.name
hh('check-delivery','--dir',R/'resident-ws','--task','71','--inbox',newinbox)
hh('check-delivery','--dir',R/'resident-ws','--task','71','--inbox',inbox,ok=False,label='refuse-replaced-assignment')
report={'type':'mini-hermes-native-receiving-evidence-v1','nativeManifest':a.manifest,'mini':a.mini,'miniSha256':hashlib.sha256(Path(a.mini).read_bytes()).hexdigest(),'roomCell':cell,'firstReady':ready,'currentInbox':str(newinbox),'currentBundle':str(second),'registration':reg,'commands':N,'providerCalls':0,'limitations':['Component Host routes, not joined current source family or installed system unit; no actual controller/provider prompt.']}
write(R/'evidence.json',report);print('PASS fresh native source summon, pump receiving, refusal, concurrent writes, rotation, dismissal, replacement',flush=True)
