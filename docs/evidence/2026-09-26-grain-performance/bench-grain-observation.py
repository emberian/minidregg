import json, struct, subprocess, sys, time, hashlib
host, config, intent_path, signed_path, challenge_path, view_path = sys.argv[1:]
expected={'challenge':open(challenge_path,'rb').read(),'query':open(view_path,'rb').read()}
frames=[('describe-1',0,b''),('describe-2',0,b'')] + [(f'challenge-{i}',4,open(intent_path,'rb').read()) for i in range(1,4)] + [(f'query-{i}',5,open(signed_path,'rb').read()) for i in range(1,4)]
p=subprocess.Popen([host,config,'stdio'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
rows=[]
for name,op,payload in frames:
 t=time.monotonic(); frame=bytes([op])+payload
 p.stdin.write(struct.pack('<I',len(frame))+frame);p.stdin.flush()
 raw=p.stdout.read(4)
 if len(raw)!=4: raise RuntimeError((name,'short response length',p.poll(),p.stderr.read().decode(errors='replace')))
 size=struct.unpack('<I',raw)[0];response=p.stdout.read(size)
 if len(response)!=size: raise RuntimeError((name,'short response',p.poll()))
 rows.append({'phase':name,'seconds':round(time.monotonic()-t,3),'opcode':response[0],'size':size,'sha256':hashlib.sha256(response).hexdigest(),'matches_recorded':response[1:]==expected[name.split('-')[0]] if name.split('-')[0] in expected else None})
 print(json.dumps(rows[-1]),flush=True)
p.stdin.close(); p.wait(timeout=10)
print(json.dumps({'host':host,'exit':p.returncode,'rows':rows}),flush=True)
