#!/usr/bin/env python3
"""Receive ordinary Docuverse on four existing participants in one Store.

The shared protected receiving validator owns Store/artifact/custody validation.
This adapter supplies actual actor routes to the ordinary journey, without
participant creation, key copying, bootstrap, or shared service restart.
"""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value)
    return value

def check(condition,message):
    if not condition:
        raise RuntimeError(message)

def occupied(path):
    return path.exists() or path.is_symlink()

def preflight(actors):
    check(set(actors)=={"owner","member","reader","reviewer"}, "ordinary receiving requires four actual roles")
    check(len({actor[2] for actor in actors.values()})==4, "ordinary roles must be distinct native subjects")
    check(len({actor[0] for actor in actors.values()})==4, "ordinary roles must have distinct workspaces")
    proposals={"g-ben","g-amy","g-cal","g-rhea-read","g-rhea-annotate","n1","n2","n3","a1","a2","a3","r1","p1","p2","b9"}
    requests={"notes.md","p.md","rhea-read.json","rhea-annotate.json"}
    for workspace,home,_,_ in actors.values():
        check(not (home/"requests").is_symlink(), "native request directory must not be a symlink")
        for name in ("paper","notes"):
            check(not occupied(workspace/"refs"/(name+".json")), "ordinary receiving reference already present")
        for directory in ("proposals","attempts"):
            check(not any(occupied(workspace/directory/name) for name in proposals), "ordinary receiving operation already retained")
        check(not any(occupied(home/"requests"/name) for name in requests), "ordinary receiving request file already present")

def role_environment(actors):
    result={"JDV_SUPPLIED_STORE":"1"}
    for role,(workspace,home,_,password) in actors.items():
        result["JDV_"+role.upper()+"_WS"]=str(workspace)
        result["JDV_"+role.upper()+"_HOME"]=str(home)
        result["JDV_"+role.upper()+"_PASS"]=password.read_text().strip() if password else ""
    return result

def run(binding_path,output):
    validator_path=HERE/"protected-document-same-store.py"
    validator=module("docuverse_supplied_world",validator_path)
    custody=module("docuverse_receiving_custody",HERE/"spk-platform"/"checkpoint-app.py")
    binding_bytes=binding_path.read_bytes();binding=json.loads(binding_bytes)
    manifest,config,socket,store,actors=validator.validate(binding)
    preflight(actors)
    output.mkdir(mode=0o700,parents=True,exist_ok=True);custody.private_directory(output)
    lockpath=output/"receiving.lock"
    fd=os.open(lockpath,os.O_WRONLY|os.O_CREAT|os.O_NOFOLLOW,0o600)
    try:
        custody.private_file(lockpath);fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
        check(not occupied(output/"started.json"), "receiving already started; retain native attempts and inspect them")
        custody.save(output/"binding.json",binding)
        step=output/"ordinary";step.mkdir(mode=0o700,exist_ok=True)
        script=HERE.parent/"native"/"resource-client"/"journey.d"/"jdocuverse.sh"
        report={"protocol":"mini-docuverse-same-store-result-v1","manifestSha256":binding["manifestSha256"],
            "bindingSha256":hashlib.sha256(binding_bytes).hexdigest(),"runnerSha256":validator.digest(script),
            "validatorSha256":validator.digest(validator_path),"subjects":{role:actor[2] for role,actor in actors.items()},
            "configPath":str(config),"socketPath":str(socket),"storePath":str(store),"nativeCliOnly":True,
            "bootstrap":False,"serviceRestart":False,"coldAuditOwner":"shared-world-checkpoint","state":"running"}
        custody.save(output/"started.json",report)
        env=os.environ.copy();env.update(role_environment(actors))
        env.update(MINI=manifest["mini"],SHELL_BIN=manifest["mini"],HOST=manifest["host"],CONFIG=str(config),SOCKET=str(socket),
            JOURNEY_STEP_DIR=str(step),JOURNEY_RUN=str(output),JOURNEY_WORLD=str(store.parent))
        with (output/"receiving.log").open("x") as log:
            result=subprocess.run([str(script)],env=env,stdout=log,stderr=subprocess.STDOUT)
        report.update(state="passed" if result.returncode==0 else "failed",exitCode=result.returncode)
        custody.save(output/"result.json",report)
        print(json.dumps(report))
        return result.returncode
    finally:
        os.close(fd)

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binding",type=Path,required=True);parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args();os.umask(0o077)
    raise SystemExit(run(args.binding,args.output))
