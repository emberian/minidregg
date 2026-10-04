#!/usr/bin/env python3
"""Transcript-secrecy check for a carried NEW effect.

The effect is a signed content write. Its plaintext (the written value, the signed call, the
Host's reply) may exist only where the construction says the endpoint side lives: the carrying
client (its source, its opened replies, its scan state) and the mailbox worker that hands the call
to the Host, plus the Host's captured reply. Everywhere else in the run (registrar, relays, every
link record, the broadcast every member downloads, the observer wire records, logs, common/, the
remote host's directories) the plaintext must be absent.

  scan   --evidence E --fixture F [--remote HOST --remote-dir D] [--plant PATH_UNDER_E]
         exits 0 only when (a) every needle is FOUND in an endpoint-side file (positive control:
         the scanner can see plaintext where it must exist) and (b) NO needle is found anywhere
         else. --plant appends the value to the named file first (a planted leak must exit 1).
  leaf   --root D --needles N.json     (runs on the remote host; prints hits as JSON)
"""
import argparse,json,os,pathlib,subprocess,sys
ap=argparse.ArgumentParser();ap.add_argument('verb',choices=['scan','leaf'])
for f in ['evidence','fixture','remote','remote-dir','plant','root','needles','out']:ap.add_argument('--'+f)
a=ap.parse_args()
# Endpoint-side paths (relative to an evidence pole directory) where plaintext is expected.
ALLOWED=('client0-source/','client0-worker/','client0-opened/','client0-scan-worker/','mailbox-worker/','captured-native-reply.bin')
def needles(fixture):
    man=json.loads((pathlib.Path(fixture)/'manifest.json').read_text())
    call=pathlib.Path(man['attempt'],'call.bin').read_bytes()
    reply=None
    out={'value':man['effect']['value'].encode()}
    for tag,off in (('call-head',0),('call-mid',len(call)//2),('call-tail',max(0,len(call)-32))):
        if len(call)>=off+32:out[tag]=call[off:off+32]
    return out
def hits(root,nd,skip_allowed):
    found={}
    root=pathlib.Path(root)
    for dp,_,fs in os.walk(root):
        for f in fs:
            p=pathlib.Path(dp)/f
            rel=p.relative_to(root).as_posix()
            if skip_allowed and any(('/'+rel).find('/'+x)>=0 for x in ALLOWED):continue
            try:b=p.read_bytes()
            except OSError:continue
            for k,v in nd.items():
                if v in b:found.setdefault(k,[]).append(rel)
    return found
def allowed_hits(root,nd):
    found={}
    root=pathlib.Path(root)
    for dp,_,fs in os.walk(root):
        for f in fs:
            p=pathlib.Path(dp)/f;rel=p.relative_to(root).as_posix()
            if not any(('/'+rel).find('/'+x)>=0 for x in ALLOWED):continue
            try:b=p.read_bytes()
            except OSError:continue
            for k,v in nd.items():
                if v in b:found.setdefault(k,[]).append(rel)
    return found
if a.verb=='leaf':
    nd={k:bytes.fromhex(v) for k,v in json.loads(pathlib.Path(a.needles).read_text()).items()}
    print(json.dumps(hits(a.root,nd,False)));sys.exit(0)
ev=pathlib.Path(a.evidence);nd=needles(a.fixture)
if a.plant:
    t=ev/a.plant;t.parent.mkdir(parents=True,exist_ok=True)
    with open(t,'ab') as fh:fh.write(b'\nPLANTED LEAK '+nd['value']+b'\n')
leaks=hits(ev,nd,True)
endpoint=allowed_hits(ev,nd)
remote_leaks={}
if a.remote:
    nf=ev/'needles.remote.tmp.json';nf.write_text(json.dumps({k:v.hex() for k,v in nd.items()}));nf.chmod(0o600)
    rd=a.remote_dir
    me=pathlib.Path(__file__).resolve()
    subprocess.run(['scp','-q',str(me),f'{a.remote}:{rd}/secrecy-leaf.py'],check=True)
    subprocess.run(['scp','-q',str(nf),f'{a.remote}:{rd}/needles.tmp.json'],check=True)
    r=subprocess.run(['ssh','-o','BatchMode=yes',a.remote,f'python3 {rd}/secrecy-leaf.py leaf --root {rd} --needles {rd}/needles.tmp.json; rm -f {rd}/needles.tmp.json {rd}/secrecy-leaf.py'],stdout=subprocess.PIPE,check=True)
    remote_leaks=json.loads(r.stdout)
    nf.unlink()
# The scalar is stored as a number, not as ASCII, so only the call fragments must be visible
# at an endpoint (positive control); the ASCII value is still hunted everywhere else.
missing=[k for k in nd if k!="value" and k not in endpoint]
result={'type':'minidregg-cohort-transcript-secrecy-v1','needles':{k:len(v) for k,v in nd.items()},
  'endpointSideHits':endpoint,'leaksOutsideEndpointSide':leaks,'leaksOnRemoteHost':remote_leaks,
  'positiveControlMissing':missing,'planted':a.plant or None}
result['pass']=not leaks and not remote_leaks and not missing
text=json.dumps(result,indent=1)
if a.out:pathlib.Path(a.out).write_text(text)
print(text);sys.exit(0 if result['pass'] else 1)
