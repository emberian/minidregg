#!/usr/bin/env python3
"""Materialize the source worker launcher for an explicitly pinned deployment path."""
import argparse, hashlib, json, os, pathlib, stat
p=argparse.ArgumentParser()
p.add_argument('--physical-bwrap',required=True,choices=('/usr/bin/bwrap','/usr/local/libexec/mini-grain-bwrap'))
p.add_argument('--physical-sha256',required=True)
p.add_argument('--output',required=True)
a=p.parse_args()
physical=pathlib.Path(a.physical_bwrap)
s=physical.lstat()
if not stat.S_ISREG(s.st_mode) or s.st_uid!=0 or s.st_mode & 0o022:
    raise SystemExit('physical bwrap must be a root-owned non-writable regular executable')
if not s.st_mode & 0o111:
    raise SystemExit('physical bwrap is not executable')
if hashlib.sha256(physical.read_bytes()).hexdigest()!=a.physical_sha256:
    raise SystemExit('physical bwrap hash differs from selected deployment')
source=pathlib.Path(__file__).with_name('bwrap')
data=source.read_bytes()
needle=b'  /usr/bin/bwrap --die-with-parent --unshare-user --unshare-pid'
if data.count(needle)!=1:
    raise SystemExit('source launcher physical invocation is not unique')
result=data.replace(needle,b'  '+os.fsencode(a.physical_bwrap)+b' --die-with-parent --unshare-user --unshare-pid')
output=pathlib.Path(a.output)
with output.open('xb') as f:
    f.write(result); f.flush(); os.fsync(f.fileno())
output.chmod(0o555)
print(json.dumps({'sourcePath':str(source),'sourceSha256':hashlib.sha256(data).hexdigest(),'path':str(output),'sha256':hashlib.sha256(result).hexdigest(),'physicalBwrap':{'path':str(physical),'sha256':a.physical_sha256}}))

