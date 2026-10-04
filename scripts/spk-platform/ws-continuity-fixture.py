#!/usr/bin/env python3
"""Actual private Mini fixtures/hooks for ws-continuity-journey.py. No mocks.

prepare INPUT.json creates a NEW Store and running EtherCalc app. Every subsequent
command accepts the generated fixture.json. Input is documented beside this file.
No command retries an uncertain write, deletes evidence, or changes an old fixture.
"""
import importlib.util as _importlib_util
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
_ledger_spec = _importlib_util.spec_from_file_location(
    "step_ledger", HERE.parent.parent / "native" / "resource-client" / "step_ledger.py")
step_ledger = _importlib_util.module_from_spec(_ledger_spec)
_ledger_spec.loader.exec_module(step_ledger)
SCHEMA = "spk-ws-continuity-fixture-v1"


def load(path):
    with open(path) as f:
        return json.load(f)


def save(path, value):
    with open(path, "x") as f:
        json.dump(value, f, indent=2)
        f.write("\n")


def confirmed_issue_receipt(attempt):
    """Use the retained native confirmation; lookup remains explicit recovery.

    Mini's own submit (or a later exact lookup) retains the confirmed outcome
    and anchors it to the exact reply bytes. A second historical lookup after a
    confirmed submit adds no evidence and can outlive its transport deadline.
    """
    attempt = Path(attempt)
    anchor = load(attempt / "receipt-anchor.json")
    source = anchor.get("source")
    require(anchor.get("type") == "minidregg-grain-share-issue-receipt-anchor-v1" and isinstance(source, str)
            and re.fullmatch(r"submit|lookup-[0-9]{4}", source) is not None,
            "ticket receipt anchor is not a retained native confirmation")
    outcome = load(attempt / (source + ".outcome.json"))
    receipt = anchor.get("receipt", {})
    require(outcome.get("type") == "confirmed" and outcome.get("confirmation") in ("installed", "replayed"),
            "ticket issue is not natively confirmed; preserve exact recovery")
    require(anchor.get("outcomeSha256") == sha(attempt / (source + ".outcome.bin")) and
            set(receipt) == {"eventId", "transactionId", "acceptedCount", "worldRoot"} and
            all(isinstance(outcome.get(k), str) and receipt[k] == outcome[k] for k in receipt),
            "ticket confirmation differs from retained historical anchor")
    return receipt


def logged_run(args, prefix, *, env=None, timeout=1800):
    """Retain elapsed time and uncertainty even when a command times out."""
    save(str(prefix)+".argv.json",[str(x) for x in args])
    started=time.monotonic()
    record={"exit":None,"timedOut":False,"startedMonotonic":started}
    try:
        with open(str(prefix)+".stdout","xb") as out,open(str(prefix)+".stderr","xb") as err:
            result=subprocess.run([str(x) for x in args],stdout=out,stderr=err,env=env,timeout=timeout)
        record["exit"]=result.returncode
        return result.returncode,Path(str(prefix)+".stdout"),Path(str(prefix)+".stderr")
    except BaseException as error:
        record.update(timedOut=isinstance(error,subprocess.TimeoutExpired),errorType=type(error).__name__)
        raise
    finally:
        ended=time.monotonic()
        record.update(endedMonotonic=ended,elapsedSeconds=ended-started)
        save(str(prefix)+".exit.json",record)


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1048576), b""):
            h.update(block)
    return h.hexdigest()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def absolute(path):
    p = Path(path)
    require(p.is_absolute() and str(p) == str(path) and ".." not in p.parts,
            "absolute canonical paths required")
    return p


def protected_parent(path):
    for p in [path, *path.parents]:
        s = p.lstat()
        require(p.is_dir() and not p.is_symlink() and s.st_uid in (0, os.getuid())
                and not s.st_mode & 0o022, f"unprotected directory: {p}")


def entries(view):
    return {x["key"]["field"]: x["value"] for x in view["cell"]["entries"]}


def grant(target, cap, kind="object"):
    return {"kind": kind, "target": str(target), "capability": str(cap)}


def discover_profile(root, config, grains, artifacts, broker="/run/mini-spk-broker.sock", result_path=None, init_path=None):
    """Consume the retained native/profile result, without deriving Store identity."""
    result_path = result_path or root / "evidence/profile-result.json"
    result = load(result_path)
    require(result.get("protocol") == "mini-spk-grain-profile-result-v1", "unknown profile result protocol")
    state = absolute(result["stateRoot"])
    profile_path = absolute(result["profilePath"])
    init_path = init_path or root / "evidence/init-store.json"
    require(state.is_relative_to(grains) and state != grains and state.resolve() == state,
            "native profile state is outside the pinned grains root or noncanonical")
    require(profile_path == state / "grain-host.json" and profile_path.resolve() == profile_path,
            "native profile path differs from its retained state")
    require(result.get("miniConfig") == str(config) and result.get("miniConfigSha256") == sha(config)
            and result.get("grainsRoot") == str(grains) and result.get("initStoreResult") == str(init_path),
            "profile result differs from fixture/config pins")
    initialized = load(init_path)
    require(initialized.get("protocol") == "mini-spk-grain-init-store-v1" and initialized.get("stateRoot") == str(state),
            "profile result differs from native Store initialization")
    profile = load(profile_path)
    require(profile.get("stateRoot") == str(state) and profile.get("miniConfig") == str(config)
            and profile.get("miniConfigSha256") == sha(config) and profile.get("grainsRoot") == str(grains),
            "profile differs from retained fixture/config pins")
    for role, path_field, hash_field in [("host","miniHost","miniHostSha256"),("spkHost","spkHost","spkHostSha256")]:
        require(profile.get(path_field) == artifacts[role]["path"] and profile.get(hash_field) == artifacts[role]["sha256"],
                "profile differs from pinned candidate artifacts")
    require(all(value.get("brokerSocket","/run/mini-spk-broker.sock") == broker
                for value in [result,initialized,profile]), "retained native broker endpoint differs from fixture pin")
    return state, profile_path, profile


def adapter_pins(root):
    """Retained adapter source pins: the original, then explicit successors.

    A repaired adapter never silently continues an evidence root. Each
    successor names the exact pin record it replaces and why.
    """
    previous = root / "source-inputs.json"
    pins = load(previous)
    for index in range(1, 100):
        successor = root / f"source-inputs-successor-{index:02d}.json"
        if not successor.exists():
            return pins, previous, index
        record = load(successor)
        require(record.get("type") == "mini-spk-adapter-successor-v1" and record.get("previousSha256") == sha(previous)
                and isinstance(record.get("reason"), str) and record["reason"] and isinstance(record.get("sources"), dict)
                and set(record["sources"]) == set(pins), "adapter successor record differs from its retained lineage")
        pins, previous = record["sources"], successor
    raise RuntimeError("adapter successor records exhausted")


def adopt_adapter(root, reason):
    """Pin the adapter's current bytes as an explicit successor for this root."""
    root = absolute(root)
    protected_parent(root)
    pins, previous, index = adapter_pins(root)
    require(isinstance(reason, str) and 0 < len(reason) <= 400, "adapter successor reason required")
    current = {source: sha(source) for source in pins}
    require(current != pins, "adapter bytes are unchanged; no successor needed")
    record = {"type": "mini-spk-adapter-successor-v1", "previousSha256": sha(previous), "sources": current, "reason": reason}
    save(root / f"source-inputs-successor-{index:02d}.json", record)
    return record


def check_registration(reply, request, delegate):
    fields = {"protocol","registrationNonceHex","routeIndex","app","appGeneration","session",
              "sessionGeneration","subject","ticketResource","sessionFingerprintHex","admittedHeight","admittedWorldRoot"}
    require(isinstance(reply,dict) and set(reply) == fields, "route registration reply shape differs")
    expected = {"protocol":"mini-spk-route-register-v1", "registrationNonceHex":request["registrationNonceHex"],
                "app":request["expectedApp"],"appGeneration":request["expectedAppGeneration"],
                "session":delegate["session"],"sessionGeneration":request["expectedSessionGeneration"],
                "subject":delegate["subject"],"ticketResource":delegate["ticket"]}
    require(all(reply[k] == v for k,v in expected.items()), "route registration identity differs")
    require(type(reply["routeIndex"]) is int and reply["routeIndex"] >= 0, "route registration index invalid")
    require(isinstance(reply["sessionFingerprintHex"],str) and
            re.fullmatch(r"[0-9a-f]{64}",reply["sessionFingerprintHex"]) is not None, "route registration fingerprint invalid")
    require(all(isinstance(reply[k],str) and re.fullmatch(r"0|[1-9][0-9]*",reply[k]) is not None
                for k in ["admittedHeight","admittedWorldRoot"]), "route registration source tip invalid")


class Fixture:
    def __init__(self, path):
        self.path = absolute(path)
        self.f = load(path)
        require(self.f["schema"] == SCHEMA, "wrong fixture schema")
        self.root = absolute(self.f["root"])
        protected_parent(self.root)
        for source, expected in adapter_pins(self.root)[0].items():
            require(sha(source) == expected, "fixture adapter source changed after preparation; adopt it explicitly or restore it")
        attached = self.f.get("attachment", {})
        self.wr = absolute(attached["workspace"]) if attached else self.root / "store/base/workroom"
        self.config = absolute(attached["miniConfig"]) if attached else self.wr / "deployment/pinned-config.json"
        self.psock = absolute(attached["publicSocket"]) if attached else self.root / "sock/participant/host.sock"
        self.osock = absolute(attached["privateSocket"]) if attached else self.root / "sock/operator/host.sock"
        if attached:
            require(sha(self.config) == attached["miniConfigSha256"], "attached Mini config changed")
        self.owner = self.f.get("authority", {}).get("owner", "8")
        self.authority = self.f.get("authority", {
            "owner":"8", "ownerAccountCapability":"42", "factory":{"target":"10","capability":"55"},
            "tool":{"task":"7902","capability":"81","observeCapability":"81"},
            "parent":{"task":"7901","capability":"73","observeCapability":"73"},
            "template":{"issuer":"5","ownerBudget":"100000","lifetime":"10000"},
            "tariff":{"base":"2","perBirth":"1"}})
        self.creator = self.authority.get("creator", self.owner)
        self.tool, self.parent = self.authority["tool"], self.authority["parent"]
        self.accountcap = self.authority.get("creatorAccountCapability", self.authority.get("ownerAccountCapability"))
        self.genesis = absolute(attached["genesis"]) if attached else self.wr / "genesis.json"
        self.keys = self.f.get("keys", {subject:{"keyId":keyid,"keyEpoch":"2",
            "seedPath":str(self.wr/name),"publicKeyPath":str((self.wr/name).with_suffix(".pub"))}
            for subject,keyid,name in [("7","7007","controller.key"),("8","8008","tool.key"),("9","9009","member.key")]})
        self.m = self.f["artifacts"]
        for a in self.m.values():
            require(sha(a["path"]) == a["sha256"], "candidate artifact changed")
        self.state, self.profile, _ = discover_profile(self.root,self.config,absolute(self.f["grainsRoot"]),self.m,self.f.get("brokerSocket","/run/mini-spk-broker.sock"),
            absolute(attached["profileResult"]) if attached else None,
            absolute(attached["initStoreResult"]) if attached else None)
        require(str(self.state) == self.f["state"] and str(self.profile) == self.f["profilePath"],
                "fixture state differs from retained native profile result")
        self.app = self.f["app"]
        self.appcap = self.f.get("application", {}).get("appOwnerCapability", "3101")
        self.pkgcap = self.f.get("application", {}).get("packageOwnerCapability", "3103")
        self.package_manifest = self.f.get("application", {}).get("packageManifest", str(int(self.app)+1))
        self.pkg = self.state / f"apps/{self.app}/install/launch-descriptor/package-v1"
        self.opdir = self.root / "hooks" / (str(time.time_ns()) + "-" + secrets.token_hex(4))
        self.opdir.mkdir(mode=0o700)
        self.serial = 0
        # Ordinary participants hold every signed permission; a caller that
        # enrolls a narrower signed role selects it before issue/enroll.
        self.role_basis = {"type": "allAccess"}
        # Nonces are independently random and are retained before each submission.
        self.nonce = secrets.randbits(112)

    def n(self):
        self.nonce += 1
        return str(self.nonce)

    def fresh(self, name):
        self.serial += 1
        return self.opdir / f"{self.serial:03d}-{name}"

    def step(self, name, action, reentrant=False, effect_only=False):
        """Enter one retained provisioning step; a completed step never repeats.

        The shared ledger (native/resource-client/step_ledger.py) owns the
        rules: one native effect per step, reentrant steps resume through their
        own native journal, any other interrupted step fences later steps until
        settled from evidence.
        """
        try:
            return step_ledger.StepLedger(self.f, self.write_state).step(name, action, self.opdir, reentrant=reentrant, effect_only=effect_only)
        except step_ledger.LedgerFenced as error:
            raise RuntimeError(str(error)) from None

    def settle(self, name, disposition, evidence, reason):
        """Settle an interrupted step from its retained native evidence.

        `absent`: the named retained artifact establishes that the attempt made
        no effect; the step is authored afresh. `confirmed`: the retained
        `outcome.json` is a native confirmation of an effect-only step.
        """
        def confirmed(path):
            outcome = load(path)
            return (path.name == "outcome.json" and outcome.get("type") == "confirmed"
                    and outcome.get("confirmation") in ("installed", "replayed"))
        def write_record(record):
            path = self.fresh("settlement.json")
            save(path, record)
            return path
        return step_ledger.StepLedger(self.f, self.write_state).settle(name, disposition, absolute(evidence), reason, self.root,
                                    write_record, confirmed=confirmed, sha=sha)

    def run(self, args, okay=True, env=None, timeout=1800):
        prefix = self.fresh("command")
        rc,out,err=logged_run(args,prefix,env=env,timeout=timeout)
        if okay:
            require(rc == 0, f"command failed; retained {prefix}.stderr")
        return rc,out,err

    def mini(self, *args, operator=False, okay=True):
        return self.run([self.m["mini"]["path"], *args, "--host", self.m["host"]["path"],
                         "--config", self.config, "--socket", self.osock if operator else self.psock], okay)

    def key(self, subject):
        return absolute(self.keys[str(subject)]["seedPath"])

    def query(self, subject, target, cap, view="resource", kind="object", denied=False):
        name = self.fresh("query")
        intent = {"subject": str(subject), "nonce": self.n(),
                  "purpose": {"type": "query", "kind": kind, "target": str(target), "view": view},
                  "grants": [grant(target, cap, kind)]}
        save(str(name) + ".json", intent)
        rc, out, err = self.mini("query", "--intent", str(name) + ".json", "--key", self.key(subject),
                                 "--view", view, "--dir", name, okay=not denied)
        if denied:
            require(rc != 0 and "observation refused" in err.read_text(),
                    "revoked delegate query did not produce the expected authority refusal")
            return {"refused": True, "evidence": str(err)}
        return {"view": load(name / "view.json"), "challenge": load(name / "challenge.json"),
                "dir": name}

    def submit(self, intent, subject, kind=None):
        source = self.fresh("intent.json")
        save(source, intent)
        target = self.fresh("attempt")
        args = ["submit", "--intent", source, "--key", self.key(subject), "--dir", target]
        if kind:
            args += ["--intent-kind", kind]
        self.mini(*args)
        outcome = load(target / "outcome.json")
        require(outcome.get("type") == "confirmed" and outcome.get("confirmation") == "installed",
                f"write not confirmed: {target}")
        return target

    def task_grants(self):
        return [grant(t["task"],cap) for t in [self.tool,self.parent]
                for cap in dict.fromkeys([t["capability"],t["observeCapability"]])]

    def reserve(self, amount):
        q = self.query(self.creator, self.tool["task"], self.tool["observeCapability"])
        n = self.n()
        grain = {k: q["view"]["cell"]["grain"][k] for k in ["generation", "status", "remaining", "reserved"]}
        return self.submit({"grain": {"task": self.tool["task"], "subject": self.creator, "capability": self.tool["capability"],
            "observeCapability": self.tool["observeCapability"], "schemaVersion": "1", "expectedTargetRoot": q["view"]["cell"]["root"],
            "context": {"operationId": n, "payload": "stream continuity fixture"}, "before": grain,
            "operation": {"type": "reserve", "amount": str(amount)}, "publications": []},
            "grants": [grant(self.tool["task"],cap) for cap in dict.fromkeys([self.tool["capability"],self.tool["observeCapability"]])], "intentNonce": n}, self.creator, "grain-intent")

    def session_reserve(self):
        return int(self.authority["tariff"]["base"])+2*int(self.authority["tariff"]["perBirth"])

    def birth_session(self, d, reserve=True):
        if reserve:
            self.reserve(self.session_reserve())
        tool, parent = self.query(self.creator, self.tool["task"], self.tool["observeCapability"]), self.query(self.creator, self.parent["task"], self.parent["observeCapability"])
        n = self.n()
        spec = {"genesis": load(self.genesis),
                "template": self.authority["template"],
                "creator": self.creator, "nonce": n, "sourceCapabilities": [self.accountcap], "funding": [], "feePayer": self.creator,
                "session": {"app": self.app, "session": d["session"], "descriptor": d.get("descriptor",str(int(d["session"])+1)),
                  "participant": d["subject"], "kind": d.get("sessionKind", "web"), "sessionOwnerCapability": d["cap"],
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

    def delegate(self, target, parent, child, holder):
        c = self.query(self.owner, target, parent, "capability")
        head = self.fresh("cap-head.json")
        self.run([self.m["host"]["path"], self.config, "inspect", "view-object-capability", c["dir"] / "view.bin", head])
        p = load(head)["head"]
        q = self.query(self.owner, target, parent)
        new = copy.deepcopy(p)
        new.update(id=str(child), parent=p["id"], holder={"type": "subject", "subject": str(holder)},
                   targets=[str(target)], verbs=["observe"], ancestors=sorted(set(p["ancestors"] + [p["id"]])))
        return self.submit({"subject": self.owner, "nonce": self.n(), "purpose": {"type": "prepare", "draft": {
            "type": "delegate-source", "command": {"kind": "object", "domain": q["challenge"]["domain"],
                "semantics": q["challenge"]["semantics"], "subject": self.owner, "nonce": self.n(),
                "expectedTargetRoot": q["view"]["cell"]["root"], "parentId": p["id"], "target": str(target),
                "expectedPreRoot": q["challenge"]["authorityRoot"], "child": new}}},
                "grants": [grant(target,parent)]}, self.owner)

    def approve(self, plan, header, base, out):
        signers = []
        for slot in load(plan)["slots"]:
            subject = next((subject for subject,key in self.keys.items()
                if key["keyId"] == slot["signing"]["keyId"] and key["keyEpoch"] == slot["signing"]["keyEpoch"]), None)
            require(subject is not None, "source requested an unavailable signer")
            key = self.key(subject)
            signers.append({"role": slot["role"], "index": slot["index"],
                "keyId": slot["signing"]["keyId"], "keyEpoch": slot["signing"]["keyEpoch"],
                "publicKey": absolute(self.keys[str(subject)]["publicKeyPath"]).read_bytes().hex(),
                "headerSha256": hashlib.sha256(bytes.fromhex(slot[header])).hexdigest(), "keyPath": str(key)})
        save(out, dict(base, signers=signers))

    def issue(self, d, reserve=True, observe=True):
        kind = d.get("sessionKind", "web")
        schema = load(self.pkg / "schema-inspection.json")
        descriptor = load(self.pkg / "descriptor-inspection.json")
        interface = next(i for i in descriptor["interfaces"] if i["kind"] == kind)
        q = self.query(self.owner, self.app, self.appcap)
        launch = load(self.state / f"apps/{self.app}/install/launch-descriptor/launch-inspection.json")
        if reserve:
            self.reserve(3)
        ceiling = {"basis": self.role_basis, "added": [], "removed": [],
                   "roleSchemaRoot": schema["root"], "roleVersion": schema["version"]}
        spec = {"ticket": {"resource": d["ticket"], "scope": {"app": self.app,
                    "packageVersion": entries(q["view"])["2"], "packageRoot": launch["root"],
                    "interfaceId": interface["id"], "interfaceVersion": interface["version"],
                    "interfaceRoot": interface["root"], "schemaRoot": schema["root"], "schemaVersion": schema["version"]},
                "participant": {"session": d["session"], "descriptorResource": d.get("descriptor",str(int(d["session"])+1)),
                    "kind": kind, "subject": d["subject"], "origin": {"type": "human"},
                    "sessionCapability": d["cap"], "appObserveCapability": d["appObserve"],
                    "ticketObserveCapability": d["ticketObserve"]}, "ceiling": ceiling, "issueNonce": self.n(), "notAfter": "1000000000"},
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
        # The exact attempt is named before its one submission, so an
        # interrupted issue is recovered by lookup of this directory only.
        d["issueAttempt"] = str(issue)
        self.write_state()
        self.run([self.m["mini"]["path"], "grain-share-issue-submit", "--socket", self.osock, "--attempt", issue])
        confirmed_issue_receipt(issue)
        d["issue"] = str(issue)
        if observe:
            self.delegate(d["ticket"], d["ticketOwner"], d["ticketObserve"], d["subject"])

    def enroll(self, d):
        schema = load(self.pkg / "schema-inspection.json")
        count = int(confirmed_issue_receipt(d["issue"])["acceptedCount"])
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
        key = self.key(d["subject"])
        request = self.fresh("route-request.json")
        save(request, {"protocol": "mini-spk-grain-route-request-v1", "name": name, "expectedHost": d.get("expectedHost","grain.test"),
            "displayName": "Continuity delegate " + d["subject"], "preferredHandle": name,
            "sessionSource": d["sessionSource"], "sessionReceipt": d["sessionReceipt"], "ticketIssue": d["issue"],
            "manifestObserveCapability": d["pkgObserve"],
            "participantKey": {"keyId": self.keys[d["subject"]]["keyId"], "keyEpoch": self.keys[d["subject"]]["keyEpoch"],
                "publicKeyHex": absolute(self.keys[d["subject"]]["publicKeyPath"]).read_bytes().hex(), "seedPath": str(key)}})
        self.run([self.m["spkHost"]["path"], "grain", "route", self.profile, self.app, request])
        route = self.state / f"apps/{self.app}/routes/{name}"
        d["endpoint"] = {"token": str(route/"browser.token"), "unix_socket": str(route/"http.sock"), "host": d.get("expectedHost","grain.test")}

    def close_session(self, d):
        q = self.query(d["subject"],d["session"],d["cap"])
        fields = entries(q["view"])
        require(fields["3"] == "1", "regrant expects an active web session")
        n = self.n()
        target = {"kind":"object","target":d["session"],"capability":d["cap"],"observeCapability":d["cap"],
            "schemaVersion":"1","expectedTargetRoot":q["view"]["cell"]["root"],"payload":{"type":"scalar","actions":[
                {"type":"write","key":{"type":"object","resource":d["session"],"field":"2"},"expected":fields["2"],"value":str(int(fields["2"])+1)},
                {"type":"write","key":{"type":"object","resource":d["session"],"field":"3"},"expected":"1","value":"2"}]}}
        self.submit({"subject":d["subject"],"nonce":n,"grants":[grant(d["session"],d["cap"])],
            "purpose":{"type":"prepare","draft":{"type":"invoke","command":{"subject":d["subject"],"nonce":n,"targets":[target]}}}},d["subject"])

    def registration_request(self, d):
        current = self.query(d["subject"],d["session"],d["cap"])
        enrollment = load(Path(d["enrollment"])/"plan-inspected.json")["enrollment"]
        require(entries(current["view"])["2"] == enrollment["sessionGeneration"] and
                entries(current["view"])["1"] == self.f["generation"], "restored enrollment changed before route registration")
        directory = Path(d["endpoint"]["token"]).parent
        request = self.fresh("register-route.json")
        save(request,{"protocol":"mini-spk-route-register-v1", "registrationNonceHex":secrets.token_hex(32),
            "expectedApp":self.app, "expectedAppGeneration":self.f["generation"],
            "expectedSessionGeneration":enrollment["sessionGeneration"], "directory":str(directory),
            "dispatchCustody":str(directory/"dispatch-custody.json"),
            "dispatchCustodySha256":sha(directory/"dispatch-custody.json"),
            "custodianSha256":sha(directory/"custodian.json"),
            "displayName":"Continuity delegate "+d["subject"], "preferredHandle":directory.name})
        return request

    def write_state(self):
        # Update only this fixture's state. Historical versions stay in the hook directory.
        save(self.fresh("fixture-state.json"), self.f)
        temp = self.root / ("fixture-" + secrets.token_hex(8) + ".json")
        save(temp, self.f)
        os.replace(temp, self.path)

    def snapshot(self):
        app = self.query(self.owner, self.app, self.appcap)
        generation = entries(app["view"])["0"]
        require(entries(app["view"])["1"] == "4", "snapshot requires source serving phase 4")
        require(generation == self.f["generation"], "application generation changed unexpectedly")
        observations = [app]
        delegates = {}
        for label, d in self.f["delegates"].items():
            s = self.query(d["subject"], d["session"], d["cap"])
            observations.append(s)
            ticket = self.query(d["subject"], d["ticket"], d["ticketObserve"], denied=d.get("revoked",False))
            if not d.get("revoked",False):
                observations.append(ticket)
            session = entries(s["view"])
            active = (session["0"] == self.app and session["1"] == generation and
                      session["3"] == "1" and not d.get("revoked",False))
            delegates[label] = {"subject": d["subject"], "session": d["session"], "active": active}
        payer = self.query(self.creator,self.creator,self.accountcap,kind="account")
        observations.append(payer)
        tip = payer["challenge"]
        require(all(q["challenge"]["height"] == tip["height"] and q["challenge"]["worldRoot"] == tip["worldRoot"] for q in observations),
                "Store changed during snapshot; evidence retained, no automatic retry")
        balance = next(int(v) for asset,v in payer["view"]["balances"] if asset == "0")
        journal = self.state / f"apps/{self.app}/g{generation}"
        dispatches = []
        for p in journal.glob("dispatch-op-*/inspection.json"):
            if re.fullmatch(r"dispatch-op-[0-9]+",p.parent.name):
                obj = load(p)
                require("receipt" in obj and "request" in obj, "malformed committed dispatch inspection")
                dispatches.append({"path":str(p), "acceptedCount":obj["receipt"]["acceptedCount"]})
        result = {"schema":"spk-ws-continuity-snapshot-v1", "app":self.app,"generation":generation,
            "dispatchCount":len(dispatches), "billingCount":None,
            "billingEvidence":"No source-exported billing event counter. Source-verified Store height must remain unchanged during renewal; payer balance is recorded independently.",
            "storeHeight":int(tip["height"]), "delegates":delegates,
            "evidence":[str(q["dir"] / "challenge.json") for q in observations],
            "payerBalances":{self.creator+":0":str(balance)}, "worldRoot":tip["worldRoot"],
            "provenance":{"storeHeight":"source-verified signed current queries at one unchanged tip",
                "dispatchCount":"resident committed-permit inspection journal; NOT a source history event count",
                "billing":"no fabricated event counter: unchanged authenticated Store height excludes new billing writes",
                "evidence":str(self.opdir)}, "dispatchInspections":dispatches}
        save(self.opdir/"snapshot.json",result)
        return result

    def action(self, action):
        # Retain a one-shot mutation marker before any source write. A failed or
        # interrupted hook needs explicit evidence-based recovery, never a new nonce retry.
        marker = self.root / ("action-" + action + "-started.json")
        require(not marker.exists(), "action already attempted; inspect retained outcome instead of retrying")
        if action == "regrantA":
            require(self.f.get("enableHotRegrant") is True, "regrant disabled until the candidate has the typed hot-route consumer")
        save(marker, {"action":action, "evidence":str(self.opdir)})
        d = self.f["delegates"]["a"]
        if action == "revokeA":
            require(not d.get("revoked",False), "A already revoked; refusing duplicate mutation")
            q = self.query(self.owner,d["ticket"],d["ticketOwner"])
            artifact = self.submit({"subject":self.owner,"nonce":self.n(),"purpose":{"type":"prepare","draft":{
                "type":"revoke-source","command":{"kind":"object","subject":self.owner,"nonce":self.n(),"target":d["ticket"],
                  "victimKind":"object","capability":d["ticketObserve"],"controlCapability":d["ticketControl"],
                  "expectedTargetRoot":q["view"]["cell"]["root"],"expectedAuthorityRoot":q["challenge"]["authorityRoot"]}}},
                "grants":[grant(d["ticket"],d["ticketOwner"])]},self.owner)
            self.query(d["subject"],d["ticket"],d["ticketObserve"],denied=True)
            b = self.f["delegates"]["b"]
            self.query(b["subject"],b["ticket"],b["ticketObserve"])
            d["revoked"] = True
            self.write_state()
        elif action == "regrantA":
            require(self.f.get("enableHotRegrant") is True, "regrant disabled until the candidate has the typed hot-route consumer")
            control = self.state / f"apps/{self.app}/g{self.f['generation']}/route-control.sock"
            require(control.is_socket(), "typed resident route control socket absent; no regrant mutation attempted")
            require(d.get("revoked",False), "regrant requires the retained revoked ticket")
            self.close_session(d)
            save(self.opdir/"old-delegate-a.json",d)
            # Issue a fresh ticket; never reuse the permanently revoked grant.
            d.update(ticket=str(int(self.app)+40),ticketOwner="3260",ticketControl="3261",ticketObserve="3262")
            self.issue(d)
            self.enroll(d)
            self.route("delegate-a-restored",d)
            request = self.registration_request(d)
            _,registration_out,_ = self.run([self.m["spkHost"]["path"],"grain","register-route","--socket",control,"--request",request])
            check_registration(load(registration_out),load(request),d)
            d["routeRegistration"] = str(registration_out)
            require(Path(d["endpoint"]["unix_socket"]).is_socket(), "registered A route socket missing")
            d["revoked"] = False
            artifact = Path(d["enrollment"])/"receipt.json"
            self.write_state()
        elif action == "generationStop":
            self.run([self.m["spkHost"]["path"],"grain","stop",self.profile,self.app])
            rc,out,err = self.run([self.m["spkHost"]["path"],"grain","status",self.profile,self.app])
            status = load(out)
            require(not any(r["state"] == "running" for r in status["runs"]), "STOP still reports running generation")
            q = self.query(self.owner,self.app,self.appcap)
            require(entries(q["view"])["1"] == "2", "STOP did not reach source stopped phase 2")
            receipt = self.state / f"apps/{self.app}/g{self.f['generation']}/stop-completion"
            for _ in range(8):
                if (receipt / "receipt-anchor.json").is_file():
                    break
                receipt /= "replan"
            require((receipt / "receipt-anchor.json").is_file(), "STOP receipt anchor absent")
            artifact = receipt / "receipt-anchor.json"
        else:
            raise ValueError(action)
        result = {"schema":"spk-ws-continuity-action-v1","action":action,"confirmed":True,
                  "artifact":str(self.opdir/"checked-action.json"),"authorityEvidence":str(artifact)}
        if action == "regrantA":
            result["endpoint"] = d["endpoint"]
            result["routeRegistration"] = d["routeRegistration"]
        save(self.opdir/"checked-action.json",result)
        return result


def prepare(path):
    c = load(path)
    root = absolute(c["root"])
    require(not root.exists() and not root.is_symlink(), "fresh fixture root required")
    require(str(root).startswith("/var/lib/minidregg/") or str(root).startswith("/home/ember/"), "use persistent private fixture storage")
    protected_parent(root.parent)
    require(os.getuid() != 0, "run as the isolated broker's operator, not root")
    manifest_path = absolute(c["manifest"])
    m = load(manifest_path)
    require(m["sourceCommit"] == c["expectedSourceCommit"], "candidate source differs from explicit pin")
    require(all(name in m and name in m.get("sha256",{}) for name in ["host","mini","store","verifier","spkHost"]),
            "candidate manifest lacks required SPK/native artifacts or hashes")
    if c.get("enableSameIngressRace") is True:
        require("integration-qualification" in m.get("spkHostFeatures",[]), "race needs explicitly feature-built candidate manifest")
    artifacts = {}
    for name in ["host","mini","store","verifier","spkHost"]:
        p = absolute(m[name])
        require(p.is_file() and os.access(p,os.X_OK), f"missing candidate artifact: {name}")
        require(sha(p) == m["sha256"][name], f"candidate hash mismatch: {name}")
        artifacts[name] = {"path":str(p),"sha256":m["sha256"][name]}
    # grain-journey expects these names in BIN; refuse mismatches rather than
    # constructing an unreviewed mix of candidate artifacts.
    bindir = Path(m["host"]).parent
    for name,basename in [("host","minidregg-host"),("mini","mini"),("store","minidregg-link-sqlite-store"),
                          ("verifier","minidregg-credential-signature-verifier"),("spkHost","spk-host")]:
        require(Path(m[name]) == bindir/basename, "candidate requires a coherent standard-named bin directory")
    spk = absolute(c["spk"])
    require(sha(spk) == c["spkSha256"], "signed EtherCalc SPK hash mismatch")
    prefix = str(c.get("appPrefix","46"))
    require(re.fullmatch(r"[1-9][0-9]",prefix) is not None, "two-digit appPrefix required")
    require(prefix not in {"70","75","79","80","83"}, "appPrefix overlaps standard workroom resources")
    lease = int(c.get("leaseSeconds",120))
    require(lease > 0, "positive lease required")
    grains = absolute(c["grainsRoot"])
    broker = str(absolute(c.get("brokerSocket","/run/mini-spk-broker.sock")))
    require(broker in ("/run/mini-spk-broker.sock",str(grains/"broker.sock")), "isolated broker must belong to grains root")
    root.mkdir(mode=0o700)
    (root/"hooks").mkdir(mode=0o700)
    save(root/"input.json",c)
    save(root/"manifest.json",m)
    save(root/"source-inputs.json",{str(HERE/name):sha(HERE/name) for name in ["grain-journey.sh","grain-store.sh","ws-continuity-fixture.py","ws-continuity-regressions.py","ws-continuity-supervision.py"]})
    env = dict(os.environ, BIN=str(bindir),GRAIN_HOST=m["host"],GRAINS_ROOT=str(grains),BROKER_SOCKET="" if broker == "/run/mini-spk-broker.sock" else broker,SPK=str(spk),GRAIN_A=prefix,KIND_A="web",ROLE_BASIS_A='{"type":"allAccess"}')
    def phases(*names):
        p = root/("phase-"+"-".join(names))
        rc,_,_=logged_run([str(HERE/"grain-journey.sh"),"phase",str(root),*names],p,env=env,timeout=7200)
        require(rc == 0,f"fixture phase failed; inspect {p}.stderr; preserve all evidence")
    phases("store","services","workroom","profile")
    config = root/"store/base/workroom/deployment/pinned-config.json"
    state, profile_path, profile = discover_profile(root,config,grains,artifacts,broker)
    phases("birth-a","install-a")
    save(root/"profile-before-lease.json",profile)
    profile["wsAuthorityLeaseSeconds"] = lease
    tmp = state/("profile-"+secrets.token_hex(8)+".json")
    save(tmp,profile)
    os.replace(tmp,profile_path)
    f = {"schema":SCHEMA,"root":str(root),"app":prefix+"01","artifacts":artifacts,"state":str(state),"profilePath":str(profile_path),"grainsRoot":str(grains),
         "candidateSource":m["sourceCommit"],"brokerSocket":broker,"leaseSeconds":lease,"enableHotRegrant":c.get("enableHotRegrant",False),"enableSealRecovery":c.get("enableSealRecovery",False),"sealSupervisor":c.get("sealSupervisor"),"enableSameIngressRace":c.get("enableSameIngressRace",False),"delegates":{}}
    for label,subject,session,cap,base in [("a","7",prefix+"10","3211",3230),("b","9",prefix+"12","3221",3240)]:
        f["delegates"][label] = {"subject":subject,"session":session,"cap":cap,"ticket":prefix+("20" if label=="a" else "22"),
            "expectedHost":c.get("delegateHosts",{}).get(label,"grain.test"),"appObserve":str(base),"pkgObserve":str(base+1),"ticketOwner":str(base+2),"ticketControl":str(base+3),"ticketObserve":str(base+4)}
    save(root/"fixture.json",f)
    fixture = Fixture(root/"fixture.json")
    for label,d in fixture.f["delegates"].items():
        fixture.birth_session(d)
        fixture.delegate(fixture.app,fixture.appcap,d["appObserve"],d["subject"])
        fixture.delegate(str(int(fixture.app)+1),fixture.pkgcap,d["pkgObserve"],d["subject"])
        fixture.issue(d)
        fixture.route("delegate-"+label,d)
        fixture.write_state()
    phases("start-a")
    for d in fixture.f["delegates"].values():
        fixture.enroll(d)
        fixture.write_state()
    q = fixture.query(8,fixture.app,fixture.appcap)
    fixture.f["generation"] = entries(q["view"])["0"]
    fixture.write_state()
    # A full source audit is retained before the timing journey; renew snapshots
    # use source-verified signed current observations instead of repeatedly replaying.
    fixture.run([m["mini"],"audit","--host",m["host"],"--config",config])
    journey = {"room":"continuity","roomSuffix":secrets.token_hex(8),"leaseSeconds":lease,
        "delegates":{k:{n:d[n] for n in ["subject","session","endpoint"]} for k,d in fixture.f["delegates"].items()},
        "hooks":{a:[sys.executable,str(HERE/"ws-continuity-fixture.py"),a,str(root/"fixture.json")]
                 for a in ["snapshot","revokeA","generationStop"]}}
    if c.get("enableHotRegrant") is True:
        control = state / f"apps/{fixture.app}/g{fixture.f['generation']}/route-control.sock"
        require(control.is_socket(), "hot regrant requested but joined resident control is absent")
        journey["hooks"]["regrantA"] = [sys.executable,str(HERE/"ws-continuity-fixture.py"),"regrantA",str(root/"fixture.json")]
    journey["hooks"]["replayAcceptedA"] = [sys.executable,str(HERE/"ws-continuity-regressions.py"),"replayAcceptedA",str(root/"fixture.json")]
    if c.get("enableSealRecovery") is True:
        journey["hooks"]["sealRecovery"] = [sys.executable,str(HERE/"ws-continuity-regressions.py"),"sealRecovery",str(root/"fixture.json")]
    if c.get("enableSameIngressRace") is True:
        require("integration-qualification" in m.get("spkHostFeatures",[]), "race needs explicitly feature-built candidate manifest")
        journey["hooks"]["sameIngressRace"] = [sys.executable,str(HERE/"ws-continuity-regressions.py"),"sameIngressRace",str(root/"fixture.json")]
    if c.get("stopAfterJourney",True) is False:
        journey["hooks"].pop("generationStop")
    save(root/"journey.json",journey)
    return {"fixture":str(root/"fixture.json"),"journey":str(root/"journey.json"),"prepared":True}


def main():
    os.umask(0o077)
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("action",choices=["prepare","snapshot","revokeA","regrantA","generationStop"])
    p.add_argument("config")
    a = p.parse_args()
    if a.action == "prepare":
        result = prepare(a.config)
    else:
        f = Fixture(a.config)
        result = f.snapshot() if a.action == "snapshot" else f.action(a.action)
    print(json.dumps(result))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError,ValueError,KeyError,OSError,subprocess.TimeoutExpired) as e:
        print(f"continuity fixture: {e}",file=sys.stderr)
        sys.exit(1)
