#!/usr/bin/env python3
"""Add one independently enrolled document connector to a running same-Store app.

Provisioning uses explicit owner approval and retained Mini receipts. The runtime
workspace receives only its own scoped browser cookie or API token and delegated app/document/task grants.
A failed provision is retained for exact inspection; rerunning never repeats it.
"""
import argparse
import copy
import importlib.util
import json
import os
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("continuity", HERE / "ws-continuity-fixture.py")
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
load, save, require, absolute, sha, grant, entries = f.load, f.save, f.require, f.absolute, f.sha, f.grant, f.entries

class DelegatedConnector(f.Fixture):
    def birth_session(self, d):
        self.reserve(int(self.authority["tariff"]["base"])+2*int(self.authority["tariff"]["perBirth"]))
        tool, parent = self.query(self.creator, self.tool["task"], self.tool["observeCapability"]), self.query(self.creator, self.parent["task"], self.parent["observeCapability"])
        n = self.n()
        spec = {"genesis": load(self.genesis),
                "template": self.authority["template"],
                "creator": self.creator, "nonce": n, "sourceCapabilities": [self.accountcap], "funding": [], "feePayer": self.creator,
                "session": {"app": self.app, "session": d["session"], "descriptor": d.get("descriptor",str(int(d["session"])+1)),
                  "participant": d["subject"], "kind": d["sessionKind"], "sessionOwnerCapability": d["cap"],
                  "sessionControlCapability": d.get("sessionControlCapability",str(int(d["cap"])+1)),
                  "descriptorOwnerCapability": d.get("descriptorOwnerCapability",str(int(d["cap"])+2)),
                  "descriptorControlCapability": d.get("descriptorControlCapability",str(int(d["cap"])+3))}}
        def witness(q, t):
            return {"task": t["task"], "capability": t["capability"], "observeCapability": t["observeCapability"],
                    "targetRoot": q["view"]["cell"]["root"],
                    "before": {k: q["view"]["cell"]["grain"][k] for k in ["generation", "status", "remaining", "reserved"]}}
        source = self.fresh("session-source.json")
        save(source, {"subject": self.creator, "nonce": n, "grants": [grant(self.authority["factory"]["target"],self.authority["factory"]["capability"]), grant(self.creator,self.accountcap,"account"), *self.task_grants()],
            "applicationSessionGrainBirth": {"tariff": self.authority["tariff"], "applicationSessionBirth": spec,
                 "tool": witness(tool,self.tool), "parent": witness(parent,self.parent)}})
        author = self.fresh("session-author")
        self.mini("current-session-intent", "--source", source, "--dir", author)
        attempt = self.fresh("session-birth")
        self.mini("submit", "--intent", author / "intent.bin", "--intent-kind", "binary", "--key", self.key(self.creator), "--dir", attempt)
        o = load(attempt / "outcome.json")
        require(o.get("type") == "confirmed" and o.get("confirmation") == "installed", "session birth not confirmed")
        d.update(sessionSource=str(author / "source.json"), sessionReceipt=str(attempt / "outcome.json"))

    def issue(self, d):
        schema = load(self.pkg / "schema-inspection.json")
        descriptor = load(self.pkg / "descriptor-inspection.json")
        interface = next(i for i in descriptor["interfaces"] if i["kind"] == d["sessionKind"])
        q = self.query(self.owner, self.app, self.appcap)
        launch = load(self.state / f"apps/{self.app}/install/launch-descriptor/launch-inspection.json")
        self.reserve(3)
        ceiling = {"basis": self.role_basis, "added": [], "removed": [],
                   "roleSchemaRoot": schema["root"], "roleVersion": schema["version"]}
        spec = {"ticket": {"resource": d["ticket"], "scope": {"app": self.app,
                    "packageVersion": entries(q["view"])["2"], "packageRoot": launch["root"],
                    "interfaceId": interface["id"], "interfaceVersion": interface["version"],
                    "interfaceRoot": interface["root"], "schemaRoot": schema["root"], "schemaVersion": schema["version"]},
                "participant": {"session": d["session"], "descriptorResource": d.get("descriptor",str(int(d["session"])+1)),
                    "kind": d["sessionKind"], "subject": d["subject"], "origin": {"type": "human"},
                    "sessionCapability": d["cap"], "appObserveCapability": d["appObserve"],
                    "ticketObserveCapability": d["ticketObserve"]}, "ceiling": ceiling, "issueNonce": self.n()},
                "issuer": self.owner, "appDelegateCapability": self.appcap,
                "ticketOwnerCapability": d["ticketOwner"], "ticketControlCapability": d["ticketControl"]}
        req = {"spec": spec, "payer": self.creator, "funding": [], "sourceCapabilities": [self.accountcap],
               "tool": self.tool, "parent": self.parent}
        request, preview, approval, issue = (self.fresh(x) for x in ["ticket-request.json","ticket-preview","ticket-approval.json","ticket-issue"])
        save(request, req)
        self.mini("grain-share-issue-plan", "--request", request, "--dir", preview, operator=True)
        inspected = load(preview / "request-inspected.json")
        base = {"type": "minidregg-grain-share-issue-approval-v1", "requestSha256": sha(preview / "request.bin"),
                "canonicalSpec": inspected["canonicalSpec"], "issuer": spec["issuer"],
                "participantSubject": d["subject"], "appDelegateCapability": self.appcap, "ticketResource": d["ticket"]}
        base.update({k: inspected[k] for k in ["payer","funding","sourceCapabilities","tool","parent"]})
        self.approve(preview / "plan-inspected.json", "header", base, approval)
        self.mini("grain-share-issue-prepare", "--request", request, "--approval", approval, "--dir", issue, operator=True)
        self.run([self.m["mini"]["path"], "grain-share-issue-submit", "--socket", self.osock, "--attempt", issue])
        self.run([self.m["mini"]["path"], "grain-share-issue-lookup", "--socket", self.osock, "--attempt", issue])
        require((issue / "receipt-anchor.json").is_file(), "ticket receipt absent")
        d["issue"] = str(issue)
        self.delegate(d["ticket"], d["ticketOwner"], d["ticketObserve"], d["subject"])

    def enroll(self, d):
        schema = load(self.pkg / "schema-inspection.json")
        count = int(load(Path(d["issue"]) / "receipt-anchor.json")["receipt"]["acceptedCount"])
        request, attempt, approval = (self.fresh(x) for x in ["enrollment-request.json","enrollment","enrollment-approval.json"])
        save(request, {"issueIndex": str(count - 1), "ticketResource": d["ticket"], "packageManifest": self.package_manifest,
            "role": {"basis": self.role_basis, "added": [], "removed": [], "roleSchemaRoot": schema["root"], "roleVersion": schema["version"]},
            "descriptorCapability": d.get("descriptorOwnerCapability",str(int(d["cap"])+2)), "sessionObserveCapability": d["cap"],
            "descriptorObserveCapability": d.get("descriptorOwnerCapability",str(int(d["cap"])+2)), "manifestObserveCapability": d["pkgObserve"], "nonce": self.n()})
        self.run([self.m["mini"]["path"], "session-enrollment-plan", "--host", self.m["host"]["path"], "--config", self.config,
                  "--operator-socket", self.osock, "--request", request, "--dir", attempt])
        self.approve(attempt / "plan-inspected.json", "headerHex", {
            "type": "minidregg-session-enrollment-approval-v1", "requestSha256": sha(attempt/"request.bin"),
            "planSha256": sha(attempt/"plan.bin"), "planInspectionSha256": sha(attempt/"plan-inspected.json")}, approval)
        for command, extra in [("seal",["--approval",approval]), ("submit",[]), ("lookup",[])]:
            self.run([self.m["mini"]["path"], "session-enrollment-"+command,"--attempt",attempt,*extra])
        require((attempt/"receipt.json").is_file(), "enrollment receipt absent")
        d["enrollment"] = str(attempt)

    def route(self, name, d):
        request = self.fresh("connector-route-request.json")
        key = self.keys[d["subject"]]
        save(request, {"protocol":"mini-spk-grain-route-request-v1", "name":name,
            "expectedHost":d["expectedHost"], "displayName":"Document connector", "preferredHandle":name,
            "sessionSource":d["sessionSource"], "sessionReceipt":d["sessionReceipt"], "ticketIssue":d["issue"],
            "manifestObserveCapability":d["pkgObserve"], "exportCapture":True, "exportPath":"_/"+self.sheet+"/csv",
            "participantKey":{"keyId":key["keyId"],"keyEpoch":key["keyEpoch"],
                "publicKeyHex":absolute(key["publicKeyPath"]).read_bytes().hex(),"seedPath":str(self.key(d["subject"]))}})
        _,out,_ = self.run([self.m["spkHost"]["path"],"grain","route",self.profile,self.app,request])
        result = load(out)
        require(result["kind"] == d["sessionKind"], "route differs from source session kind")
        require((d["sessionKind"] == "web" and result["signedApiPath"] is None) or (d["sessionKind"] == "api" and result["signedApiPath"] in ("/_/", "/")), "route differs from source-signed interface")
        route = absolute(result["directory"])
        require(absolute(result["tokenFile"]) == route/("api.token" if d["sessionKind"] == "api" else "browser.token"), "route did not select independent API token")
        d["route"] = result
        d["endpoint"] = {"token":str(route/("api.token" if d["sessionKind"] == "api" else "browser.token")),"unix_socket":str(route/"http.sock"),"host":d["expectedHost"]}


def provision(path):
    c = load(path)
    require(set(c) == {"protocol","root","fixture","fixtureSha256","delegate","key","workspace","task","document","roleBasis","sheet"}, "explicit connector provisioning fields required")
    require(c["protocol"] == "mini-app-document-provision-v1", "unknown connector protocol")
    source = absolute(c["fixture"])
    require(sha(source) == c["fixtureSha256"], "source fixture changed")
    original = load(source)
    d = copy.deepcopy(c["delegate"])
    require(d["sessionKind"] in ("web","api"), "explicit source session kind required")
    require(re.fullmatch(r"[A-Za-z0-9_-]{1,128}",c["sheet"]), "exact simple EtherCalc sheet required")
    require(d["subject"] not in original["keys"], "connector needs independently enrolled key, separate from app founders")
    require(re.fullmatch(r"[a-z][a-z0-9-]{0,31}",d["name"]), "invalid connector route name")
    fields = ["subject","session","descriptor","cap","sessionControlCapability","descriptorOwnerCapability","descriptorControlCapability","ticket","appObserve","pkgObserve","ticketOwner","ticketControl","ticketObserve"]
    require(all(isinstance(d[k],str) and re.fullmatch(r"0|[1-9][0-9]*",d[k]) for k in fields), "canonical connector allocations required")
    require(len(set(d[k] for k in fields[1:])) == len(fields)-1, "connector allocations overlap")
    ws = absolute(c["workspace"])
    workspace = load(ws/"workspace.json")
    require(workspace["subject"] == d["subject"] and workspace["key"] == c["key"]["seedPath"], "connector workspace/key/subject mismatch")
    require(workspace["config"] == original["attachment"]["miniConfig"] and workspace["socket"] == original["attachment"]["publicSocket"], "connector workspace belongs to another world")
    require(len(absolute(c["key"]["seedPath"]).read_bytes()) == 32, "independent connector seed must be present")
    for name in (c["task"],c["document"]):
        require(re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]{0,63}",name), "held task/document reference required")
        require((ws/"refs"/(name+".json")).is_file(), "explicit connector reference absent: "+name)
    root = absolute(c["root"])
    require(not root.exists(), "provision already started; inspect exact retained hooks, never repeat uncertain calls")
    f.protected_parent(root.parent)
    root.mkdir(mode=0o700); (root/"hooks").mkdir(mode=0o700)
    save(root/"input.json",c)
    value = copy.deepcopy(original)
    value.update(root=str(root),delegates={d["name"]:d})
    value["keys"][d["subject"]] = c["key"]
    save(root/"source-inputs.json",{str(HERE/n):sha(HERE/n) for n in ["app-document-provision.py","ws-continuity-fixture.py"]})
    save(root/"fixture.json",value)
    x = DelegatedConnector(root/"fixture.json")
    descriptor = load(x.pkg/"descriptor-inspection.json")
    schema = load(x.pkg/"schema-inspection.json")
    require(any(i["kind"] == d["sessionKind"] for i in descriptor["interfaces"]), "signed package exposes no selected interface")
    basis = c["roleBasis"]
    require(isinstance(basis,dict), "explicit source role selection required")
    if basis.get("type") == "role":
        require(set(basis) == {"type","id"} and isinstance(basis["id"],str) and re.fullmatch(r"0|[1-9][0-9]*",basis["id"]), "canonical signed role id required")
        require(int(basis["id"]) < len(schema["roles"]), "selected role absent from signed schema")
    else:
        require(basis == {"type":"allAccess"} and not schema["roles"], "select a signed role when the package declares roles")
    x.role_basis = basis
    x.sheet = c["sheet"]
    save(root/"selected-role.json",{"basis":basis,"schema":schema,"interface":next(i for i in descriptor["interfaces"] if i["kind"] == d["sessionKind"])})
    # Current source confirms the selected serving generation before any birth.
    current = x.query(x.owner,x.app,x.appcap)
    require(entries(current["view"])["0"] == value["generation"] and entries(current["view"])["1"] == "4", "source app generation is no longer serving")
    # Held document/task authority must work under this principal, not the owner.
    for name in (c["task"],c["document"]):
        ref = load(ws/"refs"/(name+".json"))
        x.query(d["subject"],ref["target"],ref["observeCapability"],kind=ref["kind"])
    for stage, action in [
        ("birth",lambda:x.birth_session(d)),
        ("app-read-grant",lambda:x.delegate(x.app,x.appcap,d["appObserve"],d["subject"])),
        ("package-read-grant",lambda:x.delegate(x.package_manifest,x.pkgcap,d["pkgObserve"],d["subject"])),
        ("ticket",lambda:x.issue(d)), ("route",lambda:x.route(d["name"],d)), ("enrollment",lambda:x.enroll(d))]:
        save(root/(stage+"-started.json"),{"stage":stage,"delegate":copy.deepcopy(d)})
        action(); x.write_state()
        save(root/(stage+"-confirmed.json"),{"stage":stage,"delegate":copy.deepcopy(d)})
    x.run([x.m["mini"]["path"],"workspace","--action","import","--dir",ws,"--name","app",
        "--kind","object","--target",x.app,"--observe-capability",d["appObserve"],"--provenance",root/"app-read-grant-confirmed.json"])
    x.run([x.m["mini"]["path"],"workspace","--action","import","--dir",ws,"--name","package",
        "--kind","object","--target",x.package_manifest,"--observe-capability",d["pkgObserve"],"--provenance",root/"package-read-grant-confirmed.json"])
    result = {"protocol":"mini-app-document-provisioned-v1","fixture":str(x.path),"workspace":str(ws),
        "subject":d["subject"],"app":x.app,"generation":x.f["generation"],"route":d["route"],
        "delegate":d,"sheet":x.sheet,"packageManifest":x.package_manifest,"sessionKind":d["sessionKind"],"credentialKind":"cookie" if d["sessionKind"] == "web" else "bearer","registrationRequest":str(x.registration_request(d)),
        "receiving":"source enrolled; resident registration and HTTPS export remain required"}
    save(root/"result.json",result)
    return result

def main():
    os.umask(0o077)
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("input")
    args=parser.parse_args();print(json.dumps(provision(args.input)))
if __name__ == "__main__":
    try: main()
    except (RuntimeError,ValueError,KeyError,OSError) as error:
        print("app document connector: "+str(error),file=sys.stderr);sys.exit(1)
