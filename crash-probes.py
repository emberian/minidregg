#!/usr/bin/env python3
"""Owned subprocess crash probes: no shared files/processes, no secret log output."""
import os,pathlib,subprocess,sys,time,json
binary=pathlib.Path(sys.argv[1]).resolve()
root=pathlib.Path(sys.argv[2]).resolve()
root.mkdir(parents=True,exist_ok=False)
pool=root/"pool";anchor_root=root/"external-authority";local=root/"snapshot";evidence=[]
def run(*args,expected=0):
 p=subprocess.run([str(binary),*map(str,args)],capture_output=True,text=True)
 if p.returncode!=expected: raise AssertionError((args,p.returncode,p.stdout,p.stderr))
 return p
run("provision-test",pool,8)
def anchor(boot):
 socket=root/("anchor-"+str(boot)+".sock")
 f=(root/("anchor-"+str(boot)+".log")).open("wb")
 p=subprocess.Popen([str(binary),"anchor",str(anchor_root),str(socket)],stdout=f,stderr=f)
 for _ in range(100):
  if socket.exists():return p,f,socket
  if p.poll() is not None:raise AssertionError("anchor failed "+str(p.returncode))
  time.sleep(.02)
 raise AssertionError("anchor startup deadline")
process,log,socket=anchor(1)
try:
 for row,cut in enumerate(["before-anchor","after-anchor","after-snapshot","after-secret-read"]):
  output=root/("output-"+str(row))
  run("reserve",pool,row,socket,local,output,cut,expected=70)
  assert not output.exists()
  retry=root/("retry-"+str(row))
  run("reserve",pool,row,socket,local,retry,"none",expected=0 if row==0 else 1)
  assert retry.exists()==(row==0)
  evidence.append({"cut":cut,"secret_delivered_before_crash":False,"retry_refused":row!=0})
 # Explicit output available once only; output itself never logged.
 run("reserve",pool,4,socket,local,root/"output-4","none")
 assert (root/"output-4").read_bytes()==(pool/"row-4").read_bytes()
 run("reserve",pool,4,socket,local,root/"duplicate-4","none",expected=1)
 # Rollback of the owned local snapshot cannot roll back authoritative tombstones.
 empty=bytes.fromhex(run("journal-empty").stdout.strip())
 local.write_bytes(empty)
 restored=run("recover",socket,local)
 assert "5 permanent tombstones" in restored.stdout
 run("reserve",pool,1,socket,local,root/"rollback-retry","none",expected=1)
 evidence.append({"local_rollback":"repaired from independent authoritative frontier","tombstones":5})
 # Kill only this harness's authority process. Restart uses a fresh socket and same log.
 process.kill();process.wait();log.close()
 process,log,socket=anchor(2)
 assert "5 permanent tombstones" in run("recover",socket,local).stdout
 run("reserve",pool,2,socket,local,root/"restart-retry","none",expected=1)
 # Physical replacement detected after reservation; uncertain row remains burned.
 (pool/"row-5").write_bytes(b"malicious replacement")
 run("reserve",pool,5,socket,local,root/"bad-row","none",expected=1)
 assert not (root/"bad-row").exists()
 run("reserve",pool,5,socket,local,root/"bad-row-retry","none",expected=1)
 assert "6 permanent tombstones" in run("recover",socket,local).stdout
 # Exhaustion emits a refusal and leaves existing rows/source state intact.
 run("reserve",pool,100,socket,local,root/"exhausted","none",expected=1)
 assert "6 permanent tombstones" in run("recover",socket,local).stdout
 evidence.extend([{"authority_restart":"no row reassignment"},{"physical_substitution":"refused and burned"},{"exhaustion":"explicit independent refill required"}])
 (root/"RESULTS.json").write_text(json.dumps(evidence,indent=2)+"\n")
 print("PASS: crash cuts, one release, local rollback, authoritative restart, row substitution, exhaustion")
finally:
 if process.poll() is None:process.terminate();process.wait(timeout=10)
 log.close()
