import hashlib,json,struct,subprocess,sys,time
host,config,call_path,outcome_path=sys.argv[1:]
call=open(call_path,'rb').read(); expected=open(outcome_path,'rb').read()
p=subprocess.Popen([host,config,'stdio'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
for name,opcode,payload in [('cold-describe',0,b''),('warm-describe',0,b''),('submit',2,call)]:
 t=time.monotonic(); frame=bytes([opcode])+payload;p.stdin.write(struct.pack('<I',len(frame))+frame);p.stdin.flush()
 raw=p.stdout.read(4)
 if len(raw)!=4:raise RuntimeError((name,'short response length',p.poll(),p.stderr.read().decode(errors='replace')))
 n=struct.unpack('<I',raw)[0];response=p.stdout.read(n)
 if len(response)!=n:raise RuntimeError((name,'short response',p.poll()))
 print(json.dumps({'phase':name,'seconds':round(time.monotonic()-t,3),'opcode':response[0],'size':n,'sha256':hashlib.sha256(response).hexdigest(),'matches_recorded':response[1:]==expected if name=='submit' else None}),flush=True)
p.stdin.close();p.wait(timeout=10);print(json.dumps({'host':host,'exit':p.returncode}),flush=True)
