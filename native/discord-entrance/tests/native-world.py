#!/usr/bin/env python3
"""Local fake Discord + fresh real Mini Host/Store scenario; no deployment.
Usage: native-world.py SOURCE_ROOT BOOTSTRAP_HELPER MANIFEST DISCORD_TARGET NEW_RUN
BOOTSTRAP_HELPER uses a reviewed zero-tariff params file beside genesis.sh.
All native binaries are pinned by MANIFEST sha256. The run directory must not exist.
DISCORD_SCENARIO_RESUME=1 resumes only the same script-owned fixture and pins after setup;
it must not be pointed at an original/deployed world. The result preserves earlier rows.
"""
import hashlib,json,os,pathlib,socket,subprocess,sys,time,urllib.request,urllib.parse
os.umask(0o077)
SOURCE,BOOT,MANIFEST,TARGET,ROOT=map(pathlib.Path,sys.argv[1:])
resume=os.environ.get('DISCORD_SCENARIO_RESUME')=='1'
if ROOT.exists() and not resume: raise RuntimeError('new run directory required')
ROOT.mkdir(exist_ok=resume);manifest=json.loads(MANIFEST.read_text())
if resume:
 prior=json.loads((ROOT/'result.json').read_text())
 if prior['scope']!='fresh ordinary Host/Store; fake Discord only' or prior['artifacts']!=manifest:raise RuntimeError('resume requires this scenario and exact original artifacts')
for name,digest in manifest['sha256'].items():
 if name in ('host','mini','store','verifier') and hashlib.sha256(pathlib.Path(manifest[name]).read_bytes()).hexdigest()!=digest:raise RuntimeError('artifact pin differs: '+name)
MINI=manifest['mini'];HOST=manifest['host'];WORLD=ROOT/'world';HOME=ROOT/'sessions';FAKE=TARGET/'examples/fake-discord'
children=[];rows=prior["rows"] if resume else []
discord_artifacts={name:hashlib.sha256((TARGET/name).read_bytes()).hexdigest() for name in ['mini-discord','mini-discord-mirror','examples/fake-discord']}
rows.append({'label':'run-start','resumed':resume,'discordArtifacts':discord_artifacts,'scenarioSourceSha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()})
def save(): (ROOT/'result.json').write_text(json.dumps({'scope':'fresh ordinary Host/Store; fake Discord only','artifacts':manifest,'discordArtifacts':discord_artifacts,'rows':rows},indent=2))
def run(label,args,env=None,check=True):
 p=subprocess.run(list(map(str,args)),capture_output=True,env=env,timeout=90)
 (ROOT/(label+'.out')).write_bytes(p.stdout);(ROOT/(label+'.err')).write_bytes(p.stderr)
 rows.append({'label':label,'exit':p.returncode});save()
 if check and p.returncode:raise RuntimeError(label+': '+p.stderr.decode(errors='replace')[-1600:])
 return p.stdout.decode()
def test(label,value):
 rows.append({'label':label,'pass':bool(value)});save()
 if not value:raise AssertionError(label)
def start(label,args,env=None):
 p=subprocess.Popen(list(map(str,args)),stdout=open(ROOT/(label+'.log'),'ab'),stderr=subprocess.STDOUT,env=env);children.append(p);return p
def port():
 with socket.socket() as s:s.bind(('127.0.0.1',0));return s.getsockname()[1]
def wait_port(p):
 for _ in range(100):
  try:
   with socket.create_connection(('127.0.0.1',p),.1):return
  except OSError:time.sleep(.05)
 raise RuntimeError('listener not ready')
SOCKET='/run/user/'+str(os.getuid())+'/discord-world-'+str(os.getpid())+'.sock'
CONFIG=WORLD/'deployment/pinned-config.json'
if resume:SOCKET=json.loads((WORLD/'sponsor/workspace.json').read_text())['socket']
def shell(label,who,line,check=True):
 ws=WORLD/'sponsor' if who=='sponsor' else HOME/who/'workspace'
 return run(label,[MINI,'shell','--host',HOST,'--config',CONFIG,'--socket',SOCKET,'--workspace',ws,'--home',HOME/who,'--line',line],check=check)
try:
 if not resume:
  env=dict(os.environ,NEWPARTICIPANT_DOMAIN='90603')
  run('bootstrap',['sh',BOOT,HOST,MINI,manifest['store'],manifest['verifier'],WORLD,SOCKET],env)
  for who in ['sponsor','bridge']:(HOME/who/'requests').mkdir(parents=True)
  shell('bridge-key','bridge','keygen mini.key')
  # Fresh hosted bridge custody; no original world or existing grant is imported.
  (HOME/'sponsor/keys').mkdir()
  (HOME/'sponsor/keys/bridge.key').write_bytes((HOME/'bridge/keys/mini.key').read_bytes())
  pub=(HOME/'bridge/keys/mini.key.next.pub').read_bytes().hex();cosign=(HOME/'bridge/keys/mini.key.next.cosign').read_bytes().hex()
  shell('enroll-plan','sponsor',f'enroll plan bridge bridge.key {pub} {cosign}')
  shell('enroll-seal','sponsor','enroll seal bridge')
  enrollment=json.loads(shell('enroll-submit','sponsor','enroll submit bridge'));subject=enrollment['subject']
  (HOME/'sponsor/requests/open.json').write_text('{"type":"all","predicates":[]}')
  shell('provision','sponsor',f'provision bridge {subject} 1000 @open.json')
  (HOME/'bridge/provision').mkdir();(HOME/'bridge/provision/birth-context.json').write_bytes((WORLD/'sponsor/provisions/bridge/birth-context.json').read_bytes())
  shell('bridge-init','bridge',f'init mini.key {subject}')
  shell('room-new','sponsor','chat new commons')
  invitation=shell('room-invite','sponsor',f'chat invite commons {subject} bridge')
  join=next(x for x in invitation.splitlines() if x.startswith('chat join commons '))
  shell('room-join','bridge',join)
  shell('doc-new','sponsor','doc new notes --in commons')
  shell('doc-append','sponsor',"doc append write-note notes 'One shared source across entrances'")
  shell('doc-submit','sponsor','submit write-note')
  for n in range(23):shell('say-'+str(n),'sponsor',f'say --in commons message-{n}')
 else:
  subject=json.loads((HOME/'bridge/workspace/workspace.json').read_text())['subject']
  server=start('native-resume',[MINI,'serve','--host',HOST,'--config',CONFIG,'--socket',SOCKET])
  (WORLD/'public/server.pid').write_text(str(server.pid))
  for _ in range(100):
   try:
    with socket.socket(socket.AF_UNIX) as probe:probe.connect(SOCKET)
    break
   except OSError:time.sleep(.05)
  else:raise RuntimeError('resumed native socket absent')
 api_port=urllib.parse.urlparse(json.loads((HOME/'bridge/mirror/commons-bridge.json').read_text())['channel']).port if resume else port();api=f'127.0.0.1:{api_port}';api_dir=ROOT/'fake-api';api_dir.mkdir(exist_ok=resume);start('fake-api',[FAKE,'api',api,api_dir]);wait_port(api_port)
 secret=ROOT/'fake-discord.key';public=run('fake-key',[FAKE,'keygen',secret]).strip()
 roster=ROOT/'roster.json';roster.write_text(json.dumps({'version':1,'users':{'111':'sponsor'}}))
 endpoint_port=port();addr=f'127.0.0.1:{endpoint_port}';spool=ROOT/'spool';spool.mkdir(exist_ok=resume)
 env=dict(os.environ,MINI_DISCORD_APPLICATION_ID='4242',MINI_DISCORD_PUBLIC_KEY=public,MINI_DISCORD_LISTEN=addr,MINI_DISCORD_API_BASE='http://'+api+'/api/v10',MINI_DISCORD_ROSTER=str(roster),MINI_DISCORD_ROSTER_OWNER_UID=str(os.getuid()),MINI_DISCORD_SPOOL=str(spool),MINI_SHELL_WRAPPER=str(SOURCE/'deploy/shell/mini-shell-ssh'),MINI_CLIENT=MINI,MINI_HOST=HOST,MINI_CONFIG=str(CONFIG),MINI_SOCKET=SOCKET,MINI_SESSIONS=str(HOME),MINI_SPONSOR='sponsor',MINI_SPONSOR_WORKSPACE=str(WORLD/'sponsor'))
 endpoint=start('entrance',[TARGET/'mini-discord'],env);wait_port(endpoint_port)
 def interact(label,id,command,opts=(),user='111'):
  out=run(label,[FAKE,'interact',addr,secret,'4242',user,str(id),'tok-'+str(id),command,*opts])
  response=json.loads(out.split('\n',1)[1])
  if response['type']==5:
   path=api_dir/('followup-tok-'+str(id)+'.json')
   for _ in range(400):
    if path.exists():return json.loads(path.read_text())['content']
    time.sleep(.025)
   raise RuntimeError('follow-up absent')
  return response['data']['content']
 view=interact('world-home',1,'mini-world');test('held navigation contains own room and doc','commons' in view and 'notes' in view)
 view=interact('world-selected',2,'mini-world',['--target','commons']);test('selected navigation is signed','source-checked' in view and 'Source target' in view)
 doc=interact('source-document',3,'mini',['--line','doc show notes']);test('same document via Discord','One shared source' in doc)
 denied=interact('stranger',4,'mini-world',user='222');test('stranger gets no discovery','not on this Mini' in denied and 'notes' not in denied)
 endpoint.terminate();endpoint.wait(timeout=5)
 endpoint=start('entrance-restart',[TARGET/'mini-discord'],env);wait_port(endpoint_port)
 repeat=interact('exact-repeat',3,'mini',['--line','doc show notes']);test('restart returns exact retained answer',repeat==doc)
 mirror_env=dict(env,MINI_MIRROR_ROOM='commons',MINI_MIRROR_HOME=str(HOME/'bridge'),MINI_MIRROR_WORKSPACE=str(HOME/'bridge/workspace'),MINI_MIRROR_WEBHOOK_URL='http://'+api+'/api/webhooks/55/fake-token',MINI_MIRROR_CHANNEL_URL='http://'+api+'/api/v10/channels/701/messages',MINI_MIRROR_BOT_TOKEN='fake-bot-token',MINI_MIRROR_PUBLISH_ROOM_TO_CHANNEL='yes')
 for i in range(3):run('mirror-up-'+str(i),[TARGET/'mini-discord-mirror','--once'],mirror_env)
 messages=json.loads((api_dir/'channel-701.json').read_text());test('all 23 native entries mirrored',sum('webhook_id' in m for m in messages)==23)
 body=json.dumps({'content':'hello from Discord','author':{'id':'888','username':'outside'}}).encode()
 if not any(m.get('author',{}).get('id')=='888' for m in messages):urllib.request.urlopen(urllib.request.Request('http://'+api+'/fake/channels/701/messages',data=body,headers={'Content-Type':'application/json'})).read()
 for i in range(5):run('mirror-down-'+str(i),[TARGET/'mini-discord-mirror','--once'],mirror_env)
 feed=shell('native-feed','sponsor','tail --in commons --json -n 100')
 imported=[json.loads(x) for x in feed.splitlines()[1:] if 'hello from Discord' in x]
 test('one imported event under bridge actor',len(imported)==1 and imported[0]['author']==subject and imported[0]['via']['id']=='888')
 operation=next((HOME/'bridge/requests').glob('discord-commons-*.operation.json'))
 before=hashlib.sha256(operation.read_bytes()).hexdigest()
 # Replay the exact source ID by putting the old down cursor back, retaining operation custody.
 state_path=HOME/'bridge/mirror/commons.json';state=json.loads(state_path.read_text());state['message']='1000';state['scan']=None;state_path.write_text(json.dumps(state))
 for i in range(4):run('mirror-replay-'+str(i),[TARGET/'mini-discord-mirror','--once'],mirror_env)
 feed=shell('native-feed-after-replay','sponsor','tail --in commons --json -n 100')
 test('native exact retry appended no duplicate',sum('hello from Discord' in x for x in feed.splitlines())==1)
 test('exact native operation retained',hashlib.sha256(operation.read_bytes()).hexdigest()==before)
 print('PASS fresh native Discord shared-world scenario: '+str(ROOT/'result.json'))
finally:
 for child in reversed(children):
  if child.poll() is None:child.terminate()
 for child in reversed(children):
  try:child.wait(timeout=5)
  except subprocess.TimeoutExpired:child.kill()
 pidfile=WORLD/'public/server.pid'
 if pidfile.exists():
  pid=int(pidfile.read_text());
  try:os.kill(pid,15)
  except ProcessLookupError:pass
 save()
