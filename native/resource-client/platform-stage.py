#!/usr/bin/env python3
"""Prepare source-bound, isolated service plans; start nothing.

plan validates candidate/package bytes and writes a fresh private plan directory.
bind derives the world inventory and resident reference from one completed native
constructor. Neither command changes accounts, system units, or global SPK state.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import socket
import pwd
import grp
import subprocess

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def absolute(value):
    path = Path(value)
    need(path.is_absolute() and re.fullmatch(r"/[A-Za-z0-9_./-]+", str(path)) and ".." not in path.parts,
         "simple absolute path required")
    need(path.resolve() == path, "path must not traverse symlinks")
    return path

def write(path, value):
    with Path(path).open("x") as stream:
        stream.write(json.dumps(value, sort_keys=True, indent=2) + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.chmod(path, 0o600)

def candidate(manifest_path, expected, source):
    need(sha(manifest_path) == expected, "selected manifest changed")
    value = read(manifest_path)
    need(re.fullmatch(r"[0-9a-f]{40}", value["sourceCommit"]) is not None, "full source commit required")
    for role in ("mini", "host", "store", "verifier", "spkHost", "spkBroker", "browserProxy", "bwrap", "grainRuntime"):
        need(role in value and role in value["sha256"], "candidate missing role: " + role)
        path = absolute(value[role])
        need(path.is_file() and sha(path) == value["sha256"][role], "candidate role changed: " + role)
    for relative in ("native/resource-client/paid-entry-adapter.py", "deploy/shell/mini-shell-ssh",
                     "testing/journeys/shared-resident-fixture-acp",
                     "testing/journeys/shared-resident-fixture-provider.py"):
        need((source / relative).is_file(), "source recipe absent: " + relative)
    return value

def layout(frame, evidence, prefix, ports, uids, prepared=False):
    frame, evidence = absolute(frame), absolute(evidence)
    need(re.fullmatch(r"mini-[a-z0-9-]{1,40}", prefix) is not None, "distinct simple mini unit prefix required")
    need(frame != Path("/"), "dedicated frame required")
    if prepared:
        receipt=read(frame/"staging.json")
        need(receipt.get("protocol")=="mini-service-root-staging-v1" and receipt["frame"]==str(frame), "prepared frame receipt differs")
        metadata=(frame/"staging.json").stat()
        need(metadata.st_uid==0 and not metadata.st_mode&0o022,"prepared frame receipt custody differs")
        store=frame/"var/lib/mini/store"
        need(store.is_dir() and not any(store.iterdir()),"prepared Store root must be empty")
    else:
        need(not frame.exists(),"fresh dedicated frame required")
    need(not evidence.exists(), "fresh evidence directory required")
    need(len(ports) == len(set(ports)) and all(type(p) is int and 1024 <= p <= 65535 for p in ports),
         "distinct nonprivileged ports required")
    need(len(uids) >= 2 and len(set(uids)) == len(uids) and all(type(u) is int and 100 <= u < 65535 for u in uids),
         "distinct app UID/GID pool required")
    store = frame / "var/lib/mini/store"
    grains = frame / "grains"
    need(len(os.fsencode(store / "node/session/host.sock")) <= 100, "Store socket path too deep")
    # These are real source socket names, including the worst tested generation.
    need(len(os.fsencode(grains / ("a" * 16) / "host/apps/8502/g99/checkpoint-control.sock")) <= 107,
         "app checkpoint socket path too deep")
    return frame, evidence, store, grains

def collisions(frame, prefix, ports, uids, prepared=False):
    """Read-only probes; a free result is an observation, never a reservation."""
    need(prepared or not frame.exists(), "frame now exists")
    for uid in uids:
        for lookup in (pwd.getpwuid, grp.getgrgid):
            try:
                lookup(uid)
            except KeyError:
                continue
            raise RuntimeError("app UID or GID already allocated: " + str(uid))
    names=[prefix+"-"+suffix+".service" for suffix in ("store","ingress","sshd","broker")]
    names += ["mini-grain-controller@8802.service","mini-grain-resident@8802.service","mini-resident-fixture-provider@8802.service"]
    for name in names:
        need(not (Path("/etc/systemd/system") / name).exists(), "unit path already exists: " + name)
        reply = subprocess.run(["/usr/bin/systemctl", "show", name, "--property=LoadState"],
                               capture_output=True, text=True, timeout=10)
        need("LoadState=not-found" in reply.stdout, "unit already known: " + name)
    for port in ports:
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", port))

def plan(options, probe=True):
    source, manifest_path = absolute(options["source"]), absolute(options["manifest"])
    sealed = candidate(manifest_path, options["manifestSha256"], source)
    frame, evidence, store, grains = layout(options["frame"], options["evidence"],
        options["prefix"], options["ports"], options["appUids"], options.get("framePrepared",False))
    package = absolute(options["package"])
    need(package.is_file() and sha(package) == options["packageSha256"], "package bytes changed")
    if options.get("framePrepared",False):
        receipt=read(frame/"staging.json")
        need(receipt["manifest"]==str(manifest_path) and receipt["manifestSha256"]==options["manifestSha256"]
             and receipt["sourceCommit"]==sealed["sourceCommit"] and source==manifest_path.parent/"source", "prepared candidate differs from staging receipt")
    operator = options["operator"]
    need(re.fullmatch(r"[a-z_][a-z0-9_-]{0,31}", operator) is not None, "operator account invalid")
    uid = pwd.getpwnam(operator).pw_uid
    need(uid != 0 and uid not in options["appUids"], "operator must be independent of app accounts")
    if probe:
        collisions(frame, options["prefix"], options["ports"], options["appUids"], options.get("framePrepared",False))
    ports = options["ports"]
    need(len(ports) == 5, "ports must name SSH, two browser members, connector and scripted provider")
    prefix = options["prefix"]
    recipe_prefix = prefix.removeprefix("mini-")
    members = [{"name": "member-" + str(i), "entry": "paid", "weeks": 2, "funding": 1000000} for i in range(5)]
    members.append({"name": "connector-1", "entry": "sponsored", "funding": 1000000})
    units = {k: prefix + "-" + v + ".service" for k,v in
             {"operator":"store", "public":"ingress", "sshd":"sshd"}.items()}
    provision = {"type":"mini-platform-provision-v1", "root":str(store), "preparedEmptyRoot":True,
        "nodeDirectory":"node", "sourceRepo":str(source), "manifest":str(manifest_path),
        "manifestSha256":options["manifestSha256"],
        "sshLauncher":{"renderer":"mini-shell-ssh-credentials",
                       "path":str(frame / "usr/local/lib/mini/mini-shell-ssh-credentials"),
                       "sha256":sha(source / "deploy/shell/mini-shell-ssh-credentials")},
        "sshPort":ports[0], "prefix":recipe_prefix, "maxMembers":100, "maxConcurrency":8,
        "members":members,
        "rooms":{"shared":{"owner":"member-0","members":["member-"+str(i) for i in range(5)]},
                 "overlap":{"owner":"member-1","members":["member-0","member-1","member-2"]},
                 "disjoint":{"owner":"member-3","members":["member-3","member-4"]}},
        "workload":{"members":["member-"+str(i) for i in range(5)],"concurrency":5},
        "sweeps":[{"population":2,"concurrency":1},{"population":5,"concurrency":5}],
        "sponsorBalance":10000000,"toolBalance":1000000,"parentBudget":1000000,"toolBudget":1000000,
        "parentTask":7901,"toolTask":7902,"timeoutSeconds":3600,
        "paidEntryAdapter":{"path":str(source / "native/resource-client/paid-entry-adapter.py"),
                            "sha256":sha(source / "native/resource-client/paid-entry-adapter.py")},
        "payObserver":dict(zip(("subject","keyId","account","spendCapability","controlCapability",
            "factoryObserveCapability","capability","payControlCapability","enrolCapability"),
            ("30","7030","130","1030","2030","3030","4030","4031","4032"))),
        "operatorPolicy":{"grainBirthTariff":{"base":2,"perBirth":1},"providerServices":[{
            "providerResourceId":9000,"tariff":{"version":"1","model":"mini-hermes-completion-cut",
                "routes":{r:{"perOp":"1", **({} if r=="user" else {"inputMicroPerMillion":"0","outputMicroPerMillion":"0"})}
                          for r in ("user","pool","homelab")}}}]},
        "serviceManager":{"type":"systemd-system","systemctl":["/usr/bin/sudo","-n","/usr/bin/systemctl"],
                          "unitDirectory":"/etc/systemd/system","units":units}}
    room = recipe_prefix + "-r0"
    selection = {"protocol":"mini-spk-same-store-selection-v1","evidence":str(evidence / "app"),
        "grainsRoot":str(grains),"brokerSocket":str(grains / "broker.sock"),
        "package":{"path":str(package),"sha256":options["packageSha256"]},
        "app":{"owner":"member-0","room":room,"resources":"8502","capabilities":"9502",
               "members":{label:{"subject":"member-"+str(i),"expectedHost":label+".localhost:"+str(ports[i+1])}
                          for i,label in enumerate(("m0","m1"))}},
        "connector":{"subject":"connector-1","name":"csv","expectedHost":"csv.localhost:"+str(ports[3]),
            "sheet":"r2sheet","role":"1","task":"csv-task","document":"csv-doc",
            "resources":"8602","capabilities":"9602",
            "reader":{"subject":"member-0","document":room+"/notes"},
            "endpoint":"https://csv.localhost:"+str(ports[3])+"/",
            "ca":str(evidence / "app/browser-csv/tls.crt"),"operation":"r2-capture-1"}}
    broker = {"protocol":"mini-spk-broker-config-v1","grainsRoot":str(grains),
        "brokerSocket":str(grains / "broker.sock"),"spkRoot":str(frame/"spk"),"operatorUser":operator,"unitPrefix":prefix,
        "spkHost":sealed["spkHost"],"spkHostSha256":sealed["sha256"]["spkHost"],
        "ingestHelper":str(frame / "usr/local/lib/mini/spk-ingest"),
        "volumeHelper":str(frame / "usr/local/lib/mini/spk-var-volume"),"appUids":options["appUids"]}
    return {"provision-plan.json":provision,"app-selection-template.json":selection,"broker-plan.json":broker,
        "stage-options.json":dict(options, operatorUid=uid),
        "receiving-plan.json":{"protocol":"mini-service-staging-receiving-v1",
            "effects":"plans only; collision observations are not reservations",
            "candidate":{"manifest":str(manifest_path),"sha256":options["manifestSha256"],"sourceCommit":sealed["sourceCommit"]},
            "namespace":{"frame":str(frame),"operatorUid":uid,"appUidGidPool":options["appUids"],
                         "ports":ports,"units":units,"brokerUnit":prefix+"-broker.service"},
            "sourceProfile":"regenerate CanonicalRuntimeProfile from this exact Host/Store and fresh genesis",
            "requirements":["root-stage immutable candidate and pinned infra",
                "prepare operator-owned private empty Store root",
                "publish exact generated SYSTEM units",
                "isolate SPK package/inbox or qualify exact global immutable package before ingest",
                "attach then provision connector then create connector TLS route",
                "bind from native runtime only after constructor and room refs exist",
                "register exact controller ready.json before resume",
                "register app capture/quiesce/resume callbacks before composed checkpoint",
                "configure scripted BYOK credential namespace; no real provider secret required"]}}

def constructor_world(directory):
    directory = absolute(directory)
    options = read(directory / "stage-options.json")
    provision = read(directory / "provision-plan.json")
    root = Path(provision["root"])
    runtime, context = read(root / "runtime.json"), read(root / "platform-inputs.json")
    need(runtime["root"] == str(root) and context["manifest"] == provision["manifest"],
         "constructor belongs to another plan")
    need(sha(context["manifest"]) == provision["manifestSha256"] == context["identity"]["manifestSha256"]
         and sha(context["config"]) == context["identity"]["configSha256"], "constructor pins changed")
    names = runtime["allocationNames"]
    need(set(names) == {m["name"] for m in provision["members"]} and len(set(names.values())) == len(names),
         "constructor names differ")
    members = {}
    for name, subject in names.items():
        row = context["memberInventory"][subject]
        pin = read(Path(row["workspace"]) / "workspace.json")
        need(pin["subject"] == subject and pin["config"] == context["config"]
             and pin["socket"] == context["publicSocket"], "member belongs to another Store")
        members[name] = {k:row[k] for k in ("subject","workspace","home")}
    first = context["memberInventory"][names["member-0"]]
    ssh = first["ssh"]
    world = {"type":"mini-world-identity-v1","world":options["prefix"],"frame":options["frame"],
        "storeRoot":str(root),"storeNodeRoot":runtime["nodeRoot"],"domain":context["identity"]["domain"],
        "configSha256":context["identity"]["configSha256"],"unitUser":options["operator"],
        "members":members,"ssh":{"host":"127.0.0.1","port":ssh["port"],"knownHosts":ssh["knownHostsFile"]}}
    for name, row in members.items():
        row["sshKeyFile"] = context["memberInventory"][row["subject"]]["ssh"]["identityFile"]
    return options,provision,runtime,context,names,first,world

def inventory(directory):
    options,provision,runtime,context,names,first,world=constructor_world(directory)
    room=provision["prefix"]+"-r0"
    spec={"type":"mini-composed-scenario-v1","world":str(directory/"bootstrap-world.json"),
          "state":str(directory/"rooms-scenario"),"operationPrefix":"r2-rooms",
          "population":["member-"+str(i) for i in range(5)],"phases":["rooms"],
          "rooms":{"shared":{"name":room,"owner":"member-0",
                    "members":["member-"+str(i) for i in range(5)]}},"concurrency":2}
    alias="r2-captured-source"
    workspace=Path(first["workspace"])
    context_path=Path(provision["root"])/"platform-inputs.json"
    manifest=read(context["manifest"])
    alias_plan={"protocol":"mini-native-held-reference-plan-v1","platformInputs":str(context_path),
        "argv":[manifest["mini"],"workspace","--action","import","--dir",str(workspace),
                "--name",alias,"--from-ref",str(workspace/"refs"/(room+".notes.json"))],
        "sourceReference":str(workspace/"refs"/(room+".notes.json")),
        "destinationReference":str(workspace/"refs"/(alias+".json")),
        "receiving":"native alias import after actual room bootstrap; no new source authority"}
    root=Path(provision["root"])
    units=provision["serviceManager"]["units"]
    deployment={"protocol":"mini-service-deployment-binding-v1","dataRoot":str(root),
        "nodeRoot":runtime["nodeRoot"],"operatorSocket":context["privateSocket"],"publicSocket":context["publicSocket"],
        "storeUnit":units["operator"],"ingressUnit":units["public"],"unitManager":"system",
        "authorizedKeys":str(root/"ssh/authorized_keys"),"memberHomes":[members["home"] for members in world["members"].values()],
        "serviceUid":options["operatorUid"],"operatorWorkspace":context["operatorWorkspace"],
        "auxiliaryUnits":[{"unit":units["sshd"],"manager":"system","serviceUid":options["operatorUid"],"statePaths":[str(root/"ssh")]}]}
    return {"bootstrap-world.json":world,"rooms-scenario.json":spec,"held-reference-plan.json":alias_plan,
            "deployment-binding-plan.json":deployment}

def bind(directory):
    directory=absolute(directory)
    options,provision,runtime,context,names,first,world=constructor_world(directory)
    root=Path(provision["root"])
    room = provision["prefix"]+"-r0"
    # The constructor records homes/keys, but the room journey creates notes.
    # Refuse until that actual held reference exists; do not guess a target.
    reference = Path(first["workspace"]) / "refs/r2-captured-source.json"
    original=read(Path(first["workspace"])/"refs"/(room+".notes.json"))
    held = read(reference)
    need(held["kind"] == "object" and held.get("name")=="r2-captured-source"
         and re.fullmatch(r"[1-9][0-9]*",str(held["target"]))
         and held["target"]==original["target"] and held["observeCapability"]==original["observeCapability"],
         "actual simple founder alias differs from room notes source authority")
    source = Path(options["source"])
    base = Path(options["frame"])
    task = 8802
    binding = {"protocol":"mini-same-world-resident-binding-v1","platformInputs":str(root / "platform-inputs.json"),
        "base":str(base),"authors":["member-0","member-1"],"providerWitness":"member-2",
        "room":{"alias":room,"mode":"adopt"},"sharedDocumentReference":str(reference),
        "registration":str(directory / "resident-registration-receipt.json"),"task":task,
        "fixtureAcp":{"path":str(source / "testing/journeys/shared-resident-fixture-acp"),
                      "sha256":sha(source / "testing/journeys/shared-resident-fixture-acp")},
        "fixtureProvider":{"path":str(source / "testing/journeys/shared-resident-fixture-provider.py"),
                           "sha256":sha(source / "testing/journeys/shared-resident-fixture-provider.py")},
        "requestCounts":[1,1],"preserveOnSuccess":True}
    scenario = {"type":"mini-composed-scenario-v1","world":str(directory/"WORLD-IDENTITY.json"),
        "state":str(directory/"scenario"),"operationPrefix":"r2-service","population":list(names),
        "phases":["apps","connector","residents","restart"],"concurrency":2,
        "apps":{"sheet":{"worldInputs":{"platformInputs":str(root/"platform-inputs.json"),
                                       "selection":str(directory/"app-selection.json")}}},
        "connector":{"app":"sheet"},"residents":{"binding":str(directory/"resident-binding.json")},
        "restart":{"binding":str(directory/"resident-binding.json")}}
    receiving=base/"var/lib/mini/controllers"/str(task)/"receiving"
    entry=base/"usr/local/lib/mini/controller-entry.py"
    root_command=["/usr/bin/sudo","-n","/usr/bin/env","MINI_ROOT="+str(base),
                  "MINI_GRAIN_CONTROLLER_MANAGER=system","/usr/bin/python3","-I",str(entry)]
    receiving_commands={"protocol":"mini-service-receiving-command-plan-v1",
        "providerCopy":{"request":str(receiving/"provider-copy-request.json"),
            "argv":root_command+["provider-custody-copy",str(task),str(receiving/"provider-copy-request.json")],
            "ack":str(receiving/"provider-copy-ready.json")},
        "controllerRegistration":{"request":str(receiving/"ready.json"),
            "argvFromReady":"append register TASK ready.controller ready.resident to rootCommand",
            "rootCommand":root_command,"task":str(task),"receipt":binding["registration"]},
        "checkpoint":{"argv":["/usr/bin/sudo","-n","/usr/bin/env","MINI_ROOT="+str(base),
                       "/usr/bin/python3","-I",str(base/"usr/local/lib/mini/service-checkpoint.py")],
            "requires":["root backup age recipient","generated complete service inventory",
                        "registered app capture/quiesce/resume callbacks","source-quiescent controller"]},
        "effects":"commands only; use original request/ack on continuation; registration output is distinct from registry"}
    unit_plan={}
    for action in ("controller","resident"):
        name="mini-grain-"+action+"@"+str(task)+".service"
        unit_plan[name]="[Unit]\nDescription=Mini r2 "+action+"\nConditionPathExists="+str(base/"etc/mini/controllers"/(str(task)+".json"))+"\n[Service]\nType=exec\nUser="+options["operator"]+"\nGroup="+options["operator"]+"\nEnvironment=MINI_ROOT="+str(base)+"\nEnvironment=MINI_GRAIN_CONTROLLER_MANAGER=system\nExecStart=/usr/bin/python3 -I "+str(entry)+" "+("serve" if action=="controller" else "resident")+" "+str(task)+"\nRestart=on-failure\nRestartSec=2\nKillMode=control-group\nTimeoutStopSec=60\nUMask=0077\nProtectSystem=strict\nProtectHome=tmpfs\nPrivateTmp=yes\n"
    selection=read(directory/"app-selection-template.json")
    selection["connector"]["ca"]=str(Path(selection["grainsRoot"])/context["identity"]["configSha256"][:16]/"host/apps/8502/routes/csv/tls.crt")
    return {"WORLD-IDENTITY.json":world,"resident-binding.json":binding,"scenario.json":scenario,"app-selection.json":selection,"receiving-commands.json":receiving_commands,"controller-unit-plan.json":unit_plan}

def publish(directory, values):
    directory = absolute(directory)
    if not directory.exists():
        directory.mkdir(mode=0o700)
    need(directory.stat().st_uid == os.getuid() and directory.stat().st_mode & 0o777 == 0o700,
         "plan directory must be private and owned")
    for name in values:
        need(not (directory/name).exists(), "receiving output already exists: "+name)
    for name, value in values.items():
        write(directory/name,value)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command",choices=["plan","inventory","bind"])
    parser.add_argument("--options")
    parser.add_argument("--directory",required=True)
    args=parser.parse_args()
    if args.command=="plan":
        need(args.options is not None,"plan requires --options")
        values=plan(read(args.options))
    elif args.command=="inventory":
        values=inventory(absolute(args.directory))
    else:
        values=bind(args.directory)
    publish(args.directory,values)
    print(json.dumps({"protocol":"mini-service-staged-plan-v1","files":list(values),"effects":"owned plans only"}))

if __name__=="__main__":
    main()
