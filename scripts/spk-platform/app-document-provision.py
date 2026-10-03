#!/usr/bin/env python3
"""Add one independently enrolled document connector to a running same-Store app.

Provisioning uses explicit owner approval and retained Mini receipts. The runtime
workspace receives only its own scoped browser cookie or API token and delegated app/document/task grants.
Provisioning is the same retained ledger of single-effect steps as app
attachment: entering its root again with the same input continues it, a
completed step never repeats, and an interrupted effect fences later steps
until it is settled from its own evidence.

  app-document-provision.py INPUT
  app-document-provision.py status INPUT
  app-document-provision.py settle INPUT STEP absent|confirmed EVIDENCE REASON
  app-document-provision.py adopt-adapter INPUT REASON
"""
import argparse
import copy
import importlib.util
import json
import os
from pathlib import Path
import re
import secrets
import subprocess
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("continuity", HERE / "ws-continuity-fixture.py")
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
load, save, require, absolute, sha, grant, entries = f.load, f.save, f.require, f.absolute, f.sha, f.grant, f.entries

class DelegatedConnector(f.Fixture):
    """The app fixture's own authors, for one independently held principal.

    Birth, ticket issue and enrollment are the fixture's; they read the session
    kind from the delegate and the signed role from `role_basis`. Only the
    route differs: it is confined to one export path.
    """
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
        # The native route names the credential a holder presents first: the API
        # bearer, or a browser's one-shot bootstrap token. A web connector holds
        # the session cookie value itself and never spends the bootstrap.
        require(absolute(result["tokenFile"]) == route/("api.token" if d["sessionKind"] == "api" else "bootstrap.token"), "route credential differs from its source session kind")
        d["route"] = result
        d["endpoint"] = {"token":str(route/("api.token" if d["sessionKind"] == "api" else "browser.token")),"unix_socket":str(route/"http.sock"),"host":d["expectedHost"]}


FIELDS = ["subject","session","descriptor","cap","sessionControlCapability","descriptorOwnerCapability","descriptorControlCapability","ticket","appObserve","pkgObserve","ticketOwner","ticketControl","ticketObserve"]
# Linux sun_path holds 108 bytes including its terminator.
SOCKET_BOUND = 107


def validate(c):
    require(set(c) == {"protocol","root","fixture","fixtureSha256","delegate","key","workspace","task","document","roleBasis","sheet"}, "explicit connector provisioning fields required")
    require(c["protocol"] == "mini-app-document-provision-v1", "unknown connector protocol")
    source = absolute(c["fixture"])
    require(sha(source) == c["fixtureSha256"], "source fixture changed")
    original = load(source)
    d = c["delegate"]
    require(d["sessionKind"] in ("web","api"), "explicit source session kind required")
    require(re.fullmatch(r"[A-Za-z0-9_-]{1,128}",c["sheet"]), "exact simple EtherCalc sheet required")
    require(d["subject"] not in original["keys"], "connector needs independently enrolled key, separate from app founders")
    require(re.fullmatch(r"[a-z][a-z0-9-]{0,31}",d["name"]), "invalid connector route name")
    require(all(isinstance(d[k],str) and re.fullmatch(r"0|[1-9][0-9]*",d[k]) for k in FIELDS), "canonical connector allocations required")
    require(len(set(d[k] for k in FIELDS[1:])) == len(FIELDS)-1, "connector allocations overlap")
    taken = {original["application"][k] for k in original["application"] if k != "owner"} | {row[k] for row in original["delegates"].values() for k in FIELDS[1:]}
    require(not taken & {d[k] for k in FIELDS[1:]}, "connector allocations overlap the attached app")
    route = absolute(original["state"]) / "apps" / original["app"] / "routes" / d["name"] / "http.sock"
    require(len(os.fsencode(route)) <= SOCKET_BOUND, "connector route socket pathname exceeds bound; shorten its route name")
    ws = absolute(c["workspace"])
    workspace = load(ws/"workspace.json")
    require(workspace["subject"] == d["subject"] and workspace["key"] == c["key"]["seedPath"], "connector workspace/key/subject mismatch")
    require(workspace["config"] == original["attachment"]["miniConfig"] and workspace["socket"] == original["attachment"]["publicSocket"], "connector workspace belongs to another world")
    require(len(absolute(c["key"]["seedPath"]).read_bytes()) == 32, "independent connector seed must be present")
    for name in (c["task"],c["document"]):
        require(re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]{0,63}",name), "held task/document reference required")
        require((ws/"refs"/(name+".json")).is_file(), "explicit connector reference absent: "+name)
    basis = c["roleBasis"]
    require(isinstance(basis,dict), "explicit source role selection required")
    return original, ws


def enter(path):
    """Bind a fresh evidence root to this exact input, or re-enter that root."""
    require(os.getuid() != 0, "run with Store operator authority")
    c = load(path)
    original, ws = validate(c)
    root = absolute(c["root"])
    f.protected_parent(root.parent)
    if root.exists() or root.is_symlink():
        require(root.is_dir() and not root.is_symlink(), "connector evidence root is not a directory")
        f.protected_parent(root)
        require(load(root/"input.json") == c, "retained connector input differs; a changed provision needs a fresh evidence root")
    else:
        d = copy.deepcopy(c["delegate"])
        value = copy.deepcopy(original)
        # The connector has its own ledger; the app's completed steps are not its.
        value.update(root=str(root), delegates={d["name"]:d}, steps={"done":[],"pending":None,"settled":[]})
        value["keys"][d["subject"]] = c["key"]
        staging = root.parent/("."+root.name+"."+secrets.token_hex(8))
        staging.mkdir(mode=0o700); (staging/"hooks").mkdir(mode=0o700)
        save(staging/"input.json",c)
        save(staging/"source-inputs.json",{str(HERE/n):sha(HERE/n) for n in ["app-document-provision.py","ws-continuity-fixture.py"]})
        save(staging/"fixture.json",value)
        os.rename(staging,root)
    x = DelegatedConnector(root/"fixture.json")
    x.role_basis = c["roleBasis"]
    x.sheet = c["sheet"]
    return c, root, ws, x


def observe(x, c, ws, d):
    descriptor = load(x.pkg/"descriptor-inspection.json")
    schema = load(x.pkg/"schema-inspection.json")
    require(any(i["kind"] == d["sessionKind"] for i in descriptor["interfaces"]), "signed package exposes no selected interface")
    basis = c["roleBasis"]
    if basis.get("type") == "role":
        require(set(basis) == {"type","id"} and isinstance(basis["id"],str) and re.fullmatch(r"0|[1-9][0-9]*",basis["id"]), "canonical signed role id required")
        require(int(basis["id"]) < len(schema["roles"]), "selected role absent from signed schema")
    else:
        require(basis == {"type":"allAccess"} and not schema["roles"], "select a signed role when the package declares roles")
    # Current source confirms the selected serving generation before any birth.
    current = x.query(x.owner,x.app,x.appcap)
    require(entries(current["view"])["0"] == x.f["generation"] and entries(current["view"])["1"] == "4", "source app generation is no longer serving")
    # Held document/task authority must work under this principal, not the owner.
    for name in (c["task"],c["document"]):
        ref = load(ws/"refs"/(name+".json"))
        x.query(d["subject"],ref["target"],ref["observeCapability"],kind=ref["kind"])
    x.f["selectedRole"] = {"basis":basis,"schema":schema,"interface":next(i for i in descriptor["interfaces"] if i["kind"] == d["sessionKind"])}
    x.write_state()


def register(x, d):
    # A route bound after START is served only once the running resident
    # admits it through its own typed control. Nothing else opens its socket.
    control = x.state / f"apps/{x.app}/g{x.f['generation']}/route-control.sock"
    require(control.is_socket(), "resident route control socket absent; this generation cannot admit the connector route")
    request = x.registration_request(d)
    d["registrationRequest"] = str(request)
    x.write_state()
    _,out,_ = x.run([x.m["spkHost"]["path"],"grain","register-route","--socket",control,"--request",request])
    f.check_registration(load(out),load(request),d)
    d["routeRegistration"] = str(out)
    require(Path(d["endpoint"]["unix_socket"]).is_socket(), "registered connector route socket missing")


def references(x, root, ws, d):
    provenance = root/"reference-provenance.json"
    if not provenance.exists():
        save(provenance,{"type":"mini-app-document-connector-grants-v1","authority":"hint-only-requires-current-source","fixture":str(x.path),
            "app":x.app,"generation":x.f["generation"],"subject":d["subject"]})
    for name,target,capability in [("app",x.app,d["appObserve"]),("package",x.package_manifest,d["pkgObserve"])]:
        retained = ws/"refs"/(name+".json")
        if retained.exists():
            prior = load(retained)
            require(prior["target"] == target and prior["observeCapability"] == capability, "existing connector reference differs: "+name)
        else:
            x.run([x.m["mini"]["path"],"workspace","--action","import","--dir",ws,"--name",name,
                "--kind","object","--target",target,"--observe-capability",capability,"--provenance",provenance])


def provision(path):
    c, root, ws, x = enter(path)
    retained = root/"result.json"
    if retained.exists():
        return load(retained)
    d = x.f["delegates"][c["delegate"]["name"]]
    x.step("observe",lambda:observe(x,c,ws,d),reentrant=True)
    x.step("connector:session-reserve",lambda:x.reserve(x.session_reserve()),effect_only=True)
    x.step("connector:session",lambda:x.birth_session(d,reserve=False))
    x.step("connector:app-observe",lambda:x.delegate(x.app,x.appcap,d["appObserve"],d["subject"]),effect_only=True)
    x.step("connector:package-observe",lambda:x.delegate(x.package_manifest,x.pkgcap,d["pkgObserve"],d["subject"]),effect_only=True)
    x.step("connector:ticket-reserve",lambda:x.reserve(3),effect_only=True)
    x.step("connector:ticket",lambda:x.issue(d,reserve=False,observe=False))
    x.step("connector:ticket-observe",lambda:x.delegate(d["ticket"],d["ticketOwner"],d["ticketObserve"],d["subject"]),effect_only=True)
    x.step("connector:route",lambda:x.route(d["name"],d))
    x.step("connector:enrollment",lambda:x.enroll(d))
    x.step("connector:registration",lambda:register(x,d))
    x.step("connector:references",lambda:references(x,root,ws,d),reentrant=True)
    result = {"protocol":"mini-app-document-provisioned-v1","fixture":str(x.path),"workspace":str(ws),
        "subject":d["subject"],"app":x.app,"generation":x.f["generation"],"route":d["route"],
        "delegate":d,"sheet":x.sheet,"packageManifest":x.package_manifest,"sessionKind":d["sessionKind"],"credentialKind":"cookie" if d["sessionKind"] == "web" else "bearer",
        "registrationRequest":d["registrationRequest"],"routeRegistration":d["routeRegistration"],
        "receiving":"source enrolled and route registered with the running resident; HTTPS export remains required"}
    save(retained,result)
    return result


def retained_root(path):
    c = load(path); root = absolute(c["root"]); f.protected_parent(root)
    require(load(root/"input.json") == c, "retained connector input differs")
    return root


def status(path):
    # Reads retained files only: no fixture hook directory, no native call.
    root = retained_root(path); value = load(root/"fixture.json")
    ledger = value.get("steps",{"done":[],"pending":None,"settled":[]})
    return {"protocol":"mini-app-document-provision-status-v1","root":str(root),"app":value["app"],"done":ledger["done"],"pending":ledger["pending"],
        "settled":ledger["settled"],"complete":(root/"result.json").exists()}


def main():
    os.umask(0o077)
    parser=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter);parser.add_argument("words",nargs="+")
    words=parser.parse_args().words
    if words[0] == "status" and len(words) == 2: result = status(words[1])
    elif words[0] == "settle" and len(words) == 6:
        result = DelegatedConnector(retained_root(words[1])/"fixture.json").settle(words[2],words[3],words[4],words[5])
    elif words[0] == "adopt-adapter" and len(words) == 3: result = f.adopt_adapter(retained_root(words[1]),words[2])
    elif len(words) == 1: result = provision(words[0])
    else: parser.error("unknown command")
    print(json.dumps(result))
if __name__ == "__main__":
    try: main()
    except (RuntimeError,ValueError,KeyError,OSError,subprocess.TimeoutExpired) as error:
        print("app document connector: "+str(error),file=sys.stderr);sys.exit(1)
