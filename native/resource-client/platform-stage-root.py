#!/usr/bin/env python3
"""Root-stage a pinned candidate and source service hooks into a fresh frame.

No accounts, unit publication, ingest, mounts, listeners or services are created.
Output names the root variant manifest and source for platform-stage.py plan.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import pwd
import posixpath
import re
import shutil
import shlex
import stat
import tarfile
import tempfile

def need(ok, message):
    if not ok: raise RuntimeError(message)
def sha(path):
    with Path(path).open("rb") as stream:return hashlib.file_digest(stream,"sha256").hexdigest()
def read(path):return json.loads(Path(path).read_text())
def absolute(value):
    p=Path(value)
    need(p.is_absolute() and p.resolve()==p and ".." not in p.parts,"canonical absolute path required")
    return p
def custody(path):
    for p in [path,*path.parents]:
        st=p.lstat()
        need(st.st_uid==0 and not st.st_mode&0o022 and not p.is_symlink(),"root custody differs: "+str(p))
def rewrite(value, old, new):
    if isinstance(value,dict):return {k:rewrite(v,old,new) for k,v in value.items()}
    if isinstance(value,list):return [rewrite(v,old,new) for v in value]
    if isinstance(value,str) and (value==old or value.startswith(old+"/")):return new+value[len(old):]
    return value
def put(origin,destination,mode):
    need(not destination.exists() and not destination.is_symlink(),"staging destination exists")
    destination.parent.mkdir(mode=0o755,parents=True,exist_ok=True)
    with Path(origin).open("rb") as source,destination.open("xb") as out:
        shutil.copyfileobj(source,out);out.flush();os.fsync(out.fileno())
    os.chmod(destination,mode)
    need(sha(origin)==sha(destination),"staging copy changed")
def publish(path,value):
    with path.open("x") as out:
        json.dump(value,out,sort_keys=True,indent=2);out.write("\n");out.flush();os.fsync(out.fileno())
    os.chmod(path,0o444)
def metadata_variant(value,old,new,staged,rewritten):
    result=rewrite(value,str(old),str(new))
    for field in ("componentManifest","hostExecutionSupplement"):
        digest_field=field+"Sha256"
        if field not in result:continue
        need(digest_field in value,"metadata dependency hash absent: "+field)
        selected=Path(result[field]);need(selected.is_relative_to(new),"metadata dependency outside selected family: "+field)
        target=staged/selected.relative_to(new)
        need(target.is_file() and not target.is_symlink(),"metadata dependency absent: "+field)
        expected=value[digest_field]
        if target in rewritten:
            need(rewritten[target][0]==expected,"metadata dependency original pin differs: "+field)
            result[digest_field]=rewritten[target][1]
        else:
            need(sha(target)==expected,"metadata dependency original bytes differ: "+field)
            nested=rewrite(read(target),str(old),str(new))
            target.unlink();publish(target,nested)
            rewritten[target]=(expected,sha(target));result[digest_field]=rewritten[target][1]
    return result
def credential_wrapper(frame,operator):
    need(re.fullmatch(r"[a-z_][a-z0-9_-]{0,31}",operator) is not None,"operator account invalid")
    frame=absolute(frame)
    helper=frame/"usr/local/lib/mini/credential-namespace.py"
    return ("#!/bin/bash\nset -euo pipefail\n"
        "[[ $# == 2 ]] || { echo 'credential namespace needs SUBJECT PUBLIC_KEY' >&2; exit 2; }\n"
        "exec /usr/bin/python3 -I "+shlex.quote(str(helper))+" "+shlex.quote(str(frame))+" "+shlex.quote(operator)+' "$@"\n')
def safe_archive(archive):
    members=archive.getmembers()
    names={member.name:member for member in members}
    need(len(names)==len(members),"source archive contains duplicate paths")
    for member in members:
        p=Path(member.name)
        need(not p.is_absolute() and ".." not in p.parts and member.name not in ("","."),"source archive path escapes")
        if member.issym():
            # Git contains an intentional relative fixture link. Preserve only
            # direct links to regular archive members, never directory/link chains.
            target=posixpath.normpath(posixpath.join(posixpath.dirname(member.name),member.linkname))
            need(not Path(member.linkname).is_absolute() and not target.startswith("../")
                 and target in names and names[target].isfile(),"source archive contains unsafe link or special file")
        else:
            need(member.isfile() or member.isdir(),"source archive contains unsafe link or special file")
        need(".git" not in p.parts and "target" not in p.parts,"source archive contains mutable build/Git state")
    return members
def inspect(manifest, expected, frame, infra, pins):
    need(sha(manifest)==expected,"sealed manifest changed")
    value=read(manifest);family=manifest.parent
    need(re.fullmatch(r"[0-9a-f]{40}",value["sourceCommit"]) is not None,"full source commit required")
    need(not frame.exists() and not frame.is_symlink(),"fresh dedicated frame required")
    need(frame.parent.is_dir(),"frame parent absent")
    custody(frame.parent)
    archive=family/"source.tar"
    need(sha(archive)==value["sourceArchiveSha256"],"source archive changed")
    with tarfile.open(archive) as tar:safe_archive(tar)
    roles={}
    for role,pin in value["sha256"].items():
        origin=absolute(value[role])
        need(origin.is_file() and sha(origin)==pin,"sealed role bytes changed: "+role)
        if not origin.is_relative_to(family):
            need(role=="bwrap","role outside sealed family: "+role);custody(origin)
        roles[role]=origin
    need(set(("mini","host","store","verifier","spkHost","browserProxy","spkBroker"))<=set(roles),"required service role absent")
    for name,pin in pins.items():
        p=Path(name)
        need(not p.is_absolute() and ".." not in p.parts,"infra pin escapes")
        origin=infra/p
        need(origin.is_file() and not origin.is_symlink() and sha(origin)==pin,"infra hook bytes changed: "+name)
    required={"lib.sh","controller-entry.py","mini-controller-register","mini-service-config.py",
              "service-inventory.py","service-checkpoint.py","credential-namespace.py","mini-credential-namespace",
              "mini-backup","mini-restore-check","spk-browser-service.py","mini-grain-controller@.service","mini-grain-resident@.service"}
    need(required<=set(pins),"required checkpoint/BYOK/controller hooks absent")
    return value,roles

def stage(manifest,expected,frame,infra,pins,operator):
    need(os.geteuid()==0,"root custody staging requires root")
    value,roles=inspect(manifest,expected,frame,infra,pins)
    account=pwd.getpwnam(operator);need(account.pw_uid!=0,"operator must be unprivileged")
    family=manifest.parent;commit=value["sourceCommit"]
    # A failure leaves only an explicitly owned hidden stage, never a selected frame.
    temporary=Path(tempfile.mkdtemp(prefix="."+frame.name+".staging-",dir=frame.parent))
    os.chmod(temporary,0o755)
    relative=Path("var/lib/mini/candidate")/commit
    dest=temporary/relative;final=frame/relative;dest.mkdir(parents=True,mode=0o755)
    put(manifest,dest/"sealed-manifest.json",0o444)
    need(sha(dest/"sealed-manifest.json")==expected,"selected seal changed during copy")
    put(family/"source.tar",dest/"source.tar",0o444)
    need(sha(dest/"source.tar")==value["sourceArchiveSha256"],"source archive changed during copy")
    for role,origin in roles.items():
        if origin.is_relative_to(family):
            target=dest/origin.relative_to(family)
            if not target.exists():put(origin,target,0o555)
    # Retain support records named by the seal (provenance, execution supplement).
    for origin in [*family.glob("*"),*family.glob("launcher/*.json")]:
        if origin.is_file() and not origin.is_symlink() and origin!=manifest:
            target=dest/origin.relative_to(family)
            if not target.exists():put(origin,target,0o444)
    (dest/"source").mkdir(mode=0o755)
    with tarfile.open(dest/"source.tar") as tar:
        tar.extractall(dest/"source",members=safe_archive(tar),filter="data")
    root_manifest=rewrite(value,str(family),str(final))
    # Root path metadata has its own hashes; executable role bytes remain verbatim.
    rewritten_metadata={}
    for role in ("candidate","executionDependencies"):
        if role in roles:
            original=roles[role];target=dest/original.relative_to(family)
            metadata=metadata_variant(read(original),family,final,dest,rewritten_metadata)
            target.unlink();publish(target,metadata)
            rewritten_metadata[target]=(sha(original),sha(target))
            root_manifest["sha256"][role]=sha(target)
    if "executionDependencies" in roles:
        target=dest/roles["executionDependencies"].relative_to(family)
        metadata=read(target)
        for role,row in metadata.get("roles",{}).items():
            need(row["path"]==root_manifest[role],"dependency role path differs")
            row["sha256"]=root_manifest["sha256"][role]
        target.unlink();publish(target,metadata)
        root_manifest["sha256"]["executionDependencies"]=sha(target)
    # Aliased metadata roles retain the rewritten selected file's actual hash.
    for role,origin in roles.items():
        if origin.is_relative_to(family) and origin.suffix==".json":
            root_manifest["sha256"][role]=sha(dest/origin.relative_to(family))
    root_manifest.update(upstreamManifest=str(final/"sealed-manifest.json"),upstreamManifestSha256=expected,
                         rootStaging=str(frame/"staging.json"))
    for role,pin in root_manifest["sha256"].items():
        path=Path(root_manifest[role])
        observed=temporary/path.relative_to(frame) if path.is_relative_to(frame) else path
        need(sha(observed)==pin,"root variant role differs: "+role)
    publish(dest/"manifest.json",root_manifest)
    library=temporary/"usr/local/lib/mini";(library/"infra").mkdir(parents=True,mode=0o755)
    for name,pin in pins.items():
        origin=infra/name
        put(origin,library/"infra"/name,0o755 if os.access(origin,os.X_OK) else 0o444)
        need(sha(library/"infra"/name)==pin,"infra hook changed during copy: "+name)
        # Existing service hooks resolve siblings beside the command launcher.
        if "/" not in name and name not in ("lib.sh","mini-credential-namespace"):
            put(origin,library/name,0o755 if os.access(origin,os.X_OK) else 0o444)
    allocator=library/"mini-credential-namespace"
    with allocator.open("x") as out:
        out.write(credential_wrapper(frame,account.pw_name));out.flush();os.fsync(out.fileno())
    allocator.chmod(0o755)
    put(dest/"source/deploy/shell/mini-shell-ssh",library/"mini-shell-ssh",0o755)
    put(dest/"source/deploy/shell/mini-shell-ssh-credentials",library/"mini-shell-ssh-credentials",0o755)
    for helper in ("spk-ingest","spk-var-volume"):
        put(dest/"source/deploy/spk-host"/helper,library/helper,0o755)
    (temporary/"etc/mini").mkdir(parents=True,mode=0o755)
    store=temporary/"var/lib/mini/store";store.mkdir(mode=0o700)
    os.chown(store,account.pw_uid,account.pw_gid)
    controllers=temporary/"var/lib/mini/controllers";controllers.mkdir(mode=0o755)
    receiving_root=controllers/"8802";receiving_root.mkdir(mode=0o700)
    os.chown(receiving_root,account.pw_uid,account.pw_gid)
    credentials=temporary/"var/lib/mini/credentials";credentials.mkdir(mode=0o711)
    pool=credentials/"_pool";pool.mkdir(mode=0o700);os.chown(pool,account.pw_uid,account.pw_gid)
    spk=temporary/"spk";spk.mkdir(mode=0o755)
    (spk/"packages").mkdir(mode=0o755);(spk/"inbox").mkdir(mode=0o700)
    grains=temporary/"grains";grains.mkdir(mode=0o755)
    os.symlink(commit,temporary/"var/lib/mini/candidate/current")
    publish(temporary/"staging.json",{"protocol":"mini-service-root-staging-v1","frame":str(frame),
        "sourceCommit":commit,"manifest":str(final/"manifest.json"),"manifestSha256":sha(dest/"manifest.json"),
        "sealedManifestSha256":expected,"serviceSourcePins":pins,
        "generatedHooks":{"credentialNamespace":{"path":str(frame/"usr/local/lib/mini/mini-credential-namespace"),"sha256":sha(allocator),"operator":account.pw_name}},
        "effects":"immutable candidate/hooks and empty private Store; no units, accounts, SPK writes, or service starts"})
    for directory in sorted((p for p in temporary.rglob("*") if p.is_dir() and not p.is_symlink()),key=lambda p:len(p.parts),reverse=True):
        fd=os.open(directory,os.O_RDONLY|os.O_DIRECTORY);os.fsync(fd);os.close(fd)
    need(not frame.exists(),"frame collision before publication")
    # renameat2 RENAME_NOREPLACE prevents a concurrent frame from being replaced.
    import ctypes
    libc=ctypes.CDLL(None,use_errno=True)
    result=libc.renameat2(-100,os.fsencode(temporary),-100,os.fsencode(frame),1)
    need(result==0,"frame publication refused, errno "+str(ctypes.get_errno()))
    fd=os.open(frame.parent,os.O_RDONLY|os.O_DIRECTORY);os.fsync(fd);os.close(fd)
    return read(frame/"staging.json")
def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ("manifest","manifest-sha256","frame","infra","infra-pins","operator"):p.add_argument("--"+name,required=True)
    args=p.parse_args()
    print(json.dumps(stage(absolute(args.manifest),args.manifest_sha256,absolute(args.frame),
                           absolute(args.infra),read(args.infra_pins),args.operator),sort_keys=True))
if __name__=="__main__":main()
