#!/usr/bin/env python3
"""Same-Store timings and real scalar growth; never constructs or restarts a service."""
import argparse, hashlib, importlib.util, json, os, re, statistics, subprocess, time
from pathlib import Path

def require(ok, why):
    if not ok: raise ValueError(why)
def read(path): return json.loads(Path(path).read_text())
def save(path, value): Path(path).write_text(json.dumps(value, indent=2)+"\n")
def accepted_count(value):
    require(value.get("type")=="confirmed","no confirmed native outcome; preserve exact attempt")
    count=value.get("acceptedCount")
    require(type(count) is str and re.fullmatch(r"[1-9][0-9]*",count),
            "missing canonical source acceptedCount")
    return int(count)
def cpu(pid):
    fields=Path(f"/proc/{pid}/stat").read_text().rsplit(")",1)[1].split()
    return fields[19], (int(fields[11])+int(fields[12]))/os.sysconf("SC_CLK_TCK")
def scalar(name, action, value, expected):
    change={"type":action,"key":{"type":"object","field":"101"},"value":str(value)}
    if expected is not None: change["expected"]=str(expected)
    return {"type":"minidregg-workspace-proposal-v1","action":"invoke",
            "targets":[{"name":name,"payload":{"type":"scalar","actions":[change]}}]}
def batches(workspace, prior):
    rows=[]; attempts=workspace/"attempts"
    for path in sorted(attempts.iterdir() if attempts.exists() else []):
        if path.name in prior or not path.is_dir(): continue
        for request in sorted(path.rglob("batch-request.json")):
            parent=request.parent
            children=sorted((p for p in parent.iterdir() if p.is_dir() and p.name.isdecimal()),
                            key=lambda p:int(p.name))
            coordinates=[]
            for child in children:
                if not (child/"challenge.json").exists(): continue
                challenge=read(child/"challenge.json")
                coordinates.append({f:challenge.get(f) for f in
                                    ("domain","semantics","worldRoot","height","authorityRoot")})
            if not coordinates: continue
            coherent=all(v is not None for c in coordinates for v in c.values()) and all(
                c==coordinates[0] for c in coordinates)
            rows.append({"directory":str(parent),"size":len(children),"sameImage":coherent,
                         "coordinates":coordinates[0],"completed":(parent/"batch-views.json").exists(),
                         "views":[read(p/"intent.json")["purpose"] for p in children
                                  if (p/"intent.json").exists()]})
    return rows

class Probe:
    def __init__(self,args):
        self.args=args; spec=read(args.spec); manifest=read(spec["manifest"])
        require(spec["manifestSha256"]==args.expected_manifest_sha,"manifest differs from owner-qualified family")
        driver=Path(manifest["sourcePath"])/"native/resource-client/joined-member-journey.py"
        loader=importlib.util.spec_from_file_location("qualified_joined",driver)
        module=importlib.util.module_from_spec(loader); loader.loader.exec_module(module)
        self.j=module.Journey(spec,args.output)
        require(args.member in spec["members"],"member must be an actual supplied inventory key")
        self.workspace=Path(spec["members"][args.member]["workspace"]); self.output=Path(args.output)
        self.operator_argv=[manifest["mini"],"operator-status","--socket",
                            spec["deployment"]["privateSocket"],"--host",
                            read(self.workspace/"workspace.json")["host"],
                            "--config",spec["deployment"]["config"]]
        self.host_sha=manifest["sha256"]["host"]
        self.config_sha=spec["deployment"]["configSha256"]
        self.instance=None
        initial_status=self.status("initial")
        require(hashlib.sha256(Path(f"/proc/{args.host_pid}/exe").read_bytes()).hexdigest()
                ==manifest["sha256"]["host"],"live Host bytes differ")
        self.start=cpu(args.host_pid)[0]; self.rows=[]
        save(self.output/"probe-contract.json",{"identity":self.j.identity,"mode":args.mode,
             "manifest":spec["manifest"],"driverSha256":hashlib.sha256(driver.read_bytes()).hexdigest(),
             "liveHostPid":args.host_pid,"liveHostStart":self.start,"member":args.member,
             "operatorInstance":self.instance,"operatorStatus":initial_status,
             "timingScope":"SSH action wall time; private status probes excluded",
             "hostCpuScope":"includes other clients unless constructor reserves a quiet window",
             "coldReopen":"service owner only; not performed by this adapter"})
    def status(self,label):
        # Owner-private control API is independent of the native request FIFO.
        result=subprocess.run(self.operator_argv,text=True,capture_output=True,timeout=5)
        save(self.output/(label+"-operator-status.json"),{
            "command":self.operator_argv,"returncode":result.returncode,
            "stdout":result.stdout,"stderr":result.stderr})
        require(result.returncode==0,"operator status failed; preserve exact held operation")
        status=json.loads(result.stdout)
        require(status.get("hostProcessId")==self.args.host_pid
                and status.get("hostSha256")==self.host_sha
                and status.get("configSha256")==self.config_sha,
                "CPU PID is not the supplied Store operator's current Host")
        require(status.get("phase")=="serving" and status.get("admissionClosed") is False,
                "supplied operator is not admitting requests")
        instance=(status.get("processId"),status.get("instanceId"))
        require(type(instance[0]) is int and type(instance[1]) is str
                and re.fullmatch(r"[0-9a-f]{64}",instance[1]),
                "operator instance identity is incomplete")
        if self.instance is None: self.instance=instance
        require(instance==self.instance,"supplied Store operator instance changed")
        return status
    def call(self,label,line):
        attempt=self.workspace/"attempts"
        prior={p.name for p in attempt.iterdir()} if attempt.exists() else set()
        self.status(label+"-before")
        before=cpu(self.args.host_pid); start=time.monotonic()
        text=self.j.shell(self.args.member,label,line)
        elapsed=time.monotonic()-start; after=cpu(self.args.host_pid)
        self.status(label+"-after")
        require(before[0]==after[0]==self.start,"Host restarted during measurement")
        batch=batches(self.workspace,prior)
        require(all(x["sameImage"] for x in batch),"batch coordinates disagree")
        self.rows.append({"id":label,"command":line,"seconds":elapsed,
                          "hostCpuSeconds":after[1]-before[1],"batches":batch})
        save(self.output/"timings.json",self.rows); return text
    def baseline(self):
        reference=self.args.reference
        require(re.fullmatch(r"[A-Za-z][A-Za-z0-9-]{0,23}/[A-Za-z0-9_-]+",reference or ""),
                "requires supplied shared reference")
        for n in range(3): self.call(f"resolve-{n+1}","room resolve "+reference)
        self.call("refs","refs"); self.call("guarded-read","read "+reference)
        require(any(x["completed"] and x["size"]>=3 for x in self.rows[-1]["batches"]),
                "no completed dependency+target batch retained")
    def growth(self):
        alias=self.args.alias
        require(re.fullmatch(r"[A-Za-z][A-Za-z0-9-]{0,23}",alias or ""),"requires fresh alias")
        require(not (self.workspace/"refs"/(alias+".json")).exists(),"alias exists; preserve held state")
        self.call("growth-create",'create '+alias+' declared {"type":"all","predicates":[]} 101')
        previous=0; serial=0; count=0; started=time.monotonic(); levels=[]
        def write(action,value,expected):
            nonlocal previous,serial,count
            require(time.monotonic()-started<=self.args.seconds_budget,"growth budget exhausted")
            serial+=1; operation=f"grow-{alias}-{serial:04d}"; start=time.monotonic()
            self.call(operation+"-prepare","propose "+operation+" "+json.dumps(
                scalar(alias,action,value,expected),separators=(",",":")))
            self.call(operation+"-submit","submit "+operation)
            outcome=self.workspace/"attempts"/operation/"outcome.json"
            current=accepted_count(read(outcome)); require(current>count,"source count did not advance")
            count=current; previous=value
            instrumented_elapsed=time.monotonic()-start
            elapsed=sum(row["seconds"] for row in self.rows[-2:])
            save(self.output/"growth-state.json",{"identity":self.j.identity,"alias":alias,"value":value,
                 "acceptedCount":count,"operation":operation,"outcome":str(outcome),"seconds":elapsed,
                 "instrumentedWallSeconds":instrumented_elapsed,
                 "timingScope":"propose plus submit SSH action durations; status probes excluded"})
            return elapsed
        write("create",0,None)
        for target in self.args.levels:
            while count<target: write("write",previous+1,previous)
            samples=[write("write",previous+1,previous) for _ in range(5)]
            self.call(f"level-{target}-read","read "+alias)
            levels.append({"requestedLevel":target,"actualAcceptedCount":count,"samples":samples,
                           "writeMedianSeconds":statistics.median(samples),"writeWorstSeconds":max(samples)})
            save(self.output/"growth-levels.json",levels)
            if len(levels)>=2 and all(x["writeMedianSeconds"]>5 for x in levels[-2:]) and (
                    levels[-1]["writeMedianSeconds"]>levels[-2]["writeMedianSeconds"]):
                raise ValueError("two increasing levels exceed whole-write bar; stop and preserve evidence")
        save(self.output/"growth-result.json",{"identity":self.j.identity,"actualAcceptedCount":count,
             "levels":levels,"barComplete":False,"requiredOutstanding":["service-owned cold reopen"],
             "wholeWriteBarQualified":count>=1000 and levels[-1]["writeMedianSeconds"]<=5})

def main():
    parser=argparse.ArgumentParser()
    for name in ("spec","output","member"): parser.add_argument("--"+name,required=True)
    parser.add_argument("--expected-manifest-sha",required=True)
    parser.add_argument("--host-pid",required=True,type=int)
    parser.add_argument("--mode",required=True,choices=("baseline","growth"))
    parser.add_argument("--reference"); parser.add_argument("--alias")
    parser.add_argument("--levels",type=lambda s:[int(x) for x in s.split(",")],default=[10,100,500,1000])
    parser.add_argument("--seconds-budget",type=float,default=3600)
    args=parser.parse_args()
    require(args.levels==sorted(set(args.levels)) and args.levels and all(1<=x<=1000 for x in args.levels),
            "levels must increase within 1..1000")
    probe=Probe(args)
    try:
        if args.mode=="baseline": probe.baseline()
        else: probe.growth()
    except BaseException as exc:
        save(probe.output/"probe-failure.json",{"error":str(exc),"identity":probe.j.identity,
             "effectRetry":"none; preserve held attempts and recover the original operation"})
        raise

if __name__=="__main__": main()
