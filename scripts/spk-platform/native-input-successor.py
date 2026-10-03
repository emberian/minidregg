#!/usr/bin/env python3
"""Continue an interrupted attachment after native compatible profile rebind.
This module does not upgrade, sign, submit, install, clear a phase or mint grants.
The native current-profile command validates the selected root-admitted lineage.
"""
import copy
import fcntl
import hashlib
import json
import os
from pathlib import Path

CHANGED={"manifest","expectedSourceCommit","miniConfig","miniConfigSha256","profileResult"}
def require(ok,why):
    if not ok:raise RuntimeError(why)
def load(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def durable(path,value):
    data=(json.dumps(value,indent=2,sort_keys=True)+"\n").encode()
    if path.exists() or path.is_symlink():
        require(not path.is_symlink() and path.read_bytes()==data,"retained native successor bytes differ")
        return
    fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
    with os.fdopen(fd,"wb") as out:out.write(data);out.flush();os.fsync(out.fileno())
    fd=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    try:os.fsync(fd)
    finally:os.close(fd)
def source_change(old,new):
    changed={k for k in set(old)|set(new) if old.get(k)!=new.get(k)}
    require(changed and changed<=CHANGED,"native successor changes application, authority, participant or Store coordinates")
    require(old["initStoreResult"]==new["initStoreResult"],"native successor must retain original Store initialization")
def current(root,*,allow_pending=False):
    source=load(root/"input.json");manifest=load(root/"manifest.json")
    previous=root/"input.json";last=None;index=1
    for index in range(1,100):
        receipt=root/f"native-input-successor-{index:02d}.json"
        if not receipt.exists():break
        record=load(receipt);request=Path(record["request"])
        require(record.get("protocol")=="mini-spk-native-input-successor-v1"
                and record.get("previousSha256")==sha(previous)
                and record.get("requestSha256")==sha(request),"native input successor lineage differs")
        intent=load(request)
        require(intent["oldInput"]==source and intent["oldManifest"]==manifest,"native successor prior inputs differ")
        source_change(source,intent["targetInput"])
        source,manifest=intent["targetInput"],intent["targetManifest"]
        previous,last=receipt,record
    else:raise RuntimeError("native input successor bound exceeded")
    fixture=load(root/"fixture.json")
    expected=None if last is None else {"request":last["request"],"requestSha256":last["requestSha256"]}
    if not allow_pending:
        require(fixture.get("nativeInputSuccessor")==expected,"native input adoption is incomplete; resume exact adoption")
    return source,manifest,previous,index,last
def adopt(adapter,old_path,target_path,reason):
    f=adapter.f
    old_input=load(old_path);target_input=load(target_path)
    root=f.absolute(old_input["root"]);f.protected_parent(root)
    require(isinstance(reason,str) and 0<len(reason)<=400,"native successor reason required")
    pins=f.adapter_pins(root)[0]
    require(str(Path(__file__).resolve()) in pins,"pin native continuation adapter with explicit adopt-adapter first")
    for source,expected in pins.items():require(sha(source)==expected,"retained continuation adapter source differs")
    fd=os.open(root/".native-input-successor.lock",os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600)
    with os.fdopen(fd,"r+") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        current_input,current_manifest,previous,index,last=current(root,allow_pending=True)
        if target_input==current_input and last:
            require(old_input==load(last["request"])["oldInput"],"completed native successor original input differs")
            current(root)
            return last
        require(not (root/"attachment-result.json").exists(),
                "completed attachment needs an explicit new lifecycle episode; its completed START cannot be replayed")
        require(old_input==current_input,"native successor must name exact retained current input")
        source_change(old_input,target_input)
        manifest,artifacts=adapter.validate(target_input)
        require(target_input["profileResult"]!=old_input["profileResult"],"retain original profile result; supply native rebind result")
        state,profile,profile_value=f.discover_profile(root,f.absolute(target_input["miniConfig"]),
            f.absolute(target_input["grainsRoot"]),artifacts,target_input.get("brokerSocket","/run/mini-spk-broker.sock"),
            f.absolute(target_input["profileResult"]),f.absolute(target_input["initStoreResult"]))
        rebound=load(target_input["profileResult"])
        require(rebound.get("protocol")=="mini-spk-profile-rebind-v1","native profile rebind result required")
        # current-profile authenticated this exact root admission. Join every
        # caller role, not merely the Host/SPK roles present in HostProfile.
        admission=load(rebound["admission"]);target=admission["target"]
        require(admission.get("protocol")=="mini-compatible-admission-v1"
                and target["manifest"]==manifest
                and target["configPath"]==target_input["miniConfig"]
                and target["configSha256"]==target_input["miniConfigSha256"],
                "caller native roles or configuration differ from admitted target")
        require(profile_value["miniOperatorSocket"]==target_input["privateSocket"],"native successor private Store differs")
        request=root/f"native-input-adoption-request-{index:02d}.json"
        if request.exists():
            intent=load(request)
            require(intent["oldInput"]==old_input and intent["targetInput"]==target_input
                    and intent["targetManifest"]==manifest and intent["reason"]==reason,
                    "pending native adoption differs; retain original request")
        else:
            before=load(root/"fixture.json")
            require(before["state"]==str(state),"native successor must retain same physical Store state")
            require(before.get("nativeInputSuccessor")==(None if last is None else
                {"request":last["request"],"requestSha256":last["requestSha256"]}),
                "another native adoption is pending")
            after=copy.deepcopy(before)
            after.update(artifacts=artifacts,profilePath=str(profile),candidateSource=manifest["sourceCommit"])
            after["attachment"]={k:target_input[k] for k in
                ("workspace","miniConfig","miniConfigSha256","publicSocket","privateSocket","genesis","profileResult","initStoreResult")}
            intent={"protocol":"mini-spk-native-input-adoption-request-v1","oldInput":old_input,
                "oldManifest":current_manifest,"targetInput":target_input,"targetManifest":manifest,
                "beforeFixture":before,"afterFixture":after,"reason":reason,
                "nativeRebindResult":target_input["profileResult"],
                "nativeRebindResultSha256":sha(target_input["profileResult"])}
            durable(request,intent)
        require(intent["nativeRebindResultSha256"]==sha(target_input["profileResult"]),
                "retained native rebind bytes changed")
        after=copy.deepcopy(intent["afterFixture"])
        after["nativeInputSuccessor"]={"request":str(request),"requestSha256":sha(request)}
        observed=load(root/"fixture.json")
        if observed!=after:
            require(observed==intent["beforeFixture"],"fixture advanced during pending native adoption")
            # Publish only the small adapter pin pointer; all preexisting source
            # receipts, step outcomes, resources, keys and journal files remain.
            temp=root/f".native-fixture-{index:02d}.json"
            durable(temp,after);os.replace(temp,root/"fixture.json")
            fd=os.open(root,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
            try:os.fsync(fd)
            finally:os.close(fd)
        record={"protocol":"mini-spk-native-input-successor-v1","previousSha256":sha(previous),
            "request":str(request),"requestSha256":sha(request),"profile":str(profile),
            "profileSha256":sha(profile),"status":"native profile lineage consumed; app admission remains current-law gated"}
        durable(root/f"native-input-successor-{index:02d}.json",record)
        current(root)
        return record
