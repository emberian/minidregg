#!/usr/bin/env python3
"""Isolated actual SYSTEM-controller / USER-sandbox lifetime receiving.
Run as a Linux user with its running user manager and sudo for a new transient
controller only. Keeps logs, gates and process observations; cleans only its units.
"""
import os,sys,subprocess,time,json,pathlib,shutil,fcntl
src=pathlib.Path(sys.argv[1]).resolve(); root=pathlib.Path(sys.argv[2]); root.mkdir(mode=0o700)
task=str(time.time_ns()); controller=f'mini-grain-controller@{task}.service'; units=[]; rows=[]
def call(args,check=True,env=None):
 p=subprocess.run(args,text=True,capture_output=True,env=env)
 with (root/'commands.jsonl').open('a') as f: f.write(json.dumps({'argv':args,'rc':p.returncode,'out':p.stdout,'err':p.stderr})+'\n')
 if check and p.returncode: raise RuntimeError(f'{args}: {p.stderr}')
 return p

def props(unit,system=False):
 out=call((['sudo','-n'] if system else [])+['systemctl','--system' if system else '--user','show','-p','MainPID','-p','InvocationID','-p','ActiveState','-p','ControlGroup',unit]).stdout
 return dict(x.split('=',1) for x in out.splitlines() if '=' in x)
def wait(pred):
 for _ in range(100):
  if pred():return
  time.sleep(.1)
 raise RuntimeError('bounded observation timed out')
def passed(name,**kw):rows.append({'check':name,'passed':True,**kw});(root/'result.json').write_text(json.dumps(rows,indent=2))
(root/'state').mkdir(mode=0o700);(root/'workspace').mkdir();(root/'runtime').mkdir();(root/'launcher').mkdir()
for name in ['bwrap','launch-gate']:shutil.copy2(src/name,root/'launcher'/name)
for name in ['custody','task','host']:(root/name).write_text('fixture')
(root/'runtime'/'hold').write_text('#!/bin/sh\nset -eu\n(setsid /bin/sleep 600 & wait) &\necho ready > /workspace/ready\nwait\n');(root/'runtime'/'hold').chmod(0o755)
base=os.environ.copy();base.update(MINI_GRAIN_STATE_DIR=str(root/'state'),MINI_GRAIN_CUSTODY_KEY=str(root/'custody'),MINI_GRAIN_TASK_CONFIG=str(root/'task'),MINI_GRAIN_HOST_CONFIG=str(root/'host'),MINI_GRAIN_CONTROLLER_MANAGER='system',MINI_GRAIN_WORKER_MANAGER='user',MINI_GRAIN_CONTROLLER_UNIT=controller)
def environment():
 p=props(controller,True);return dict(base,MINI_GRAIN_CONTROLLER_PID=p['MainPID'],MINI_GRAIN_CONTROLLER_INVOCATION_ID=p['InvocationID'])
def arm(n,env):
 unit=f'mini-grain-t{task}-o{n}';units.append(unit+'.service');call([str(root/'launcher'/'launch-gate'),'init',str(root/'state'),unit],env=env);return unit

def launch(unit,env):
 (root/'workspace'/'ready').unlink(missing_ok=True)
 log=(root/f'{unit}.log').open('w');p=subprocess.Popen([str(root/'launcher'/'bwrap'),'--workspace',str(root/'workspace'),'--runtime-root',str(root/'runtime'),'--network','none','--','/agent/hold'],env=dict(env,MINI_GRAIN_UNIT=unit),stdout=log,stderr=log);wait(lambda:(root/'workspace'/'ready').exists());return p

def tree(unit):
 prop=props(unit+'.service');cg=pathlib.Path('/sys/fs/cgroup'+prop['ControlGroup']);pids=[]
 for f in cg.rglob('cgroup.procs'):pids.extend(int(x) for x in f.read_text().split())
 return cg,pids

def empty(cg):
 return not cg.exists() or all(not f.read_text().strip() for f in cg.rglob('cgroup.procs'))

def dead(pids):
 for pid in pids:
  try:
   stat=pathlib.Path(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()
   if stat[0]!='Z':return False
  except FileNotFoundError:pass
 return True
try:
 call(['sudo','-n','systemd-run','--unit='+controller,'--property=User='+str(os.getuid()),'--property=Type=exec','--property=Restart=no','--property=KillMode=control-group','/usr/bin/sleep','600'])
 env=environment()
 for n, altered in [(91,dict(env,MINI_GRAIN_CONTROLLER_PID='1')),(92,dict(env,MINI_GRAIN_CONTROLLER_INVOCATION_ID='0'*32))]:
  bad=f'mini-grain-t{task}-o{n}'
  result=call([str(root/'launcher'/'launch-gate'),'init',str(root/'state'),bad],check=False,env=altered);assert result.returncode
 passed('wrong PID and wrong invocation refuse before arming')
 u1=arm(1,env);u2=arm(2,env);u3=arm(3,env);p=launch(u1,env);cg,pids=tree(u1);assert len(pids)>=4,(pids,cg)
 # A queued USER launch reaches its gate only after controller crash/restart.
 call(['systemd-run','--user','--no-block','--unit='+u2,'--property=ExecStartPre=/usr/bin/sleep 3',str(root/'launcher'/'launch-gate'),'run',str(root/'state'),u2,'--','/usr/bin/touch',str(root/'late-ran')])
 assert props(u2+'.service')['ActiveState']=='activating'
 gate_lock=(root/'state'/f'{u1}.gate').open('r+')
 fcntl.flock(gate_lock,fcntl.LOCK_EX)
 monitor=int(props(u1+'.service')['MainPID'])
 call(['sudo','-n','systemctl','--system','kill','--kill-whom=main','--signal=KILL',controller])
 wait(lambda:dead([pid for pid in pids if pid!=monitor]))
 passed('gate lock contention cannot extend sandbox lifetime',monitor=monitor,sandboxPids=[pid for pid in pids if pid!=monitor])
 fcntl.flock(gate_lock,fcntl.LOCK_UN);gate_lock.close()
 wait(lambda:dead(pids) and empty(cg));p.wait(timeout=10)
 assert (root/'state'/f'{u1}.gate').read_text()=='fenced\n';passed('controller crash fences gate and kills sandbox descendants',pids=pids,cgroup=str(cg))
 call(['sudo','-n','systemctl','--system','start',controller]);new=environment();assert new['MINI_GRAIN_CONTROLLER_INVOCATION_ID']!=env['MINI_GRAIN_CONTROLLER_INVOCATION_ID']
 wait(lambda:props(u2+'.service')['ActiveState']=='failed');assert not(root/'late-ran').exists();passed('queued old launch refuses after controller restart')
 old=call([str(root/'launcher'/'launch-gate'),'run',str(root/'state'),u3,'--','/usr/bin/touch',str(root/'stolen')],check=False);assert old.returncode and not(root/'stolen').exists();passed('new controller cannot adopt armed prior incarnation')
 repeat=call([str(root/'launcher'/'launch-gate'),'init',str(root/'state'),u1],check=False,env=new);assert repeat.returncode;passed('restart cannot rearm fenced operation')
 u4=arm(4,new);p=launch(u4,new);cg,pids=tree(u4);main=int(props(u4+'.service')['MainPID']);call(['kill','-KILL',str(main)]);wait(lambda:dead(pids) and empty(cg));p.wait(timeout=10);passed('monitor crash kills sandbox and setsid descendants',pids=pids)
 u5=arm(5,new);p=launch(u5,new);cg,pids=tree(u5);call(['sudo','-n','systemctl','--system','stop',controller]);wait(lambda:dead(pids) and empty(cg));p.wait(timeout=10);passed('ordinary controller stop kills current worker',pids=pids)
 print(json.dumps(rows,indent=2))
finally:
 call(['sudo','-n','systemctl','--system','stop',controller],check=False)
 for unit in units:call(['systemctl','--user','stop',unit],check=False)
