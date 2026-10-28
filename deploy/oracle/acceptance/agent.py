#!/usr/bin/env python3
"""Operator harness for Oracle agent provisioning; Mini admits every grant.

This is not a verifier. It retains native attempts and refuses implicit retries.
It never writes a Store, controller journal, or a synthetic birth receipt.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import secrets
import subprocess


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    data = (json.dumps(value, indent=2) + "\n").encode() if not isinstance(value, bytes) else value
    with os.fdopen(os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600), "wb") as out:
        out.write(data)
        out.flush()
        os.fsync(out.fileno())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def receipt(value):
    if value.get("type") != "confirmed" or value.get("confirmation") not in ("installed", "replayed"):
        raise ValueError("native confirmation absent")
    return {key: value[key] for key in ("transactionId", "eventId", "acceptedCount", "worldRoot")}


def require_current_start(start, status):
    """Reject stale caller records before using their native unit selection."""
    if status.get("protocol") != "mini-spk-grain-status-v2" or status.get("app") != start["app"]:
        raise ValueError("current native status names a different application")
    running = [run for run in status["runs"] if run["state"] == "running"]
    if len(running) != 1 or any(running[0].get(key) != start.get(key) for key in ("generation", "unit")) or running[0].get("unitActiveState") != "active":
        raise ValueError("START record is not the current active native generation")


def controller_host_metadata(path):
    """Copy only the fresh world's public settings and protected-file paths."""
    raw = Path(path).read_bytes()
    value = json.loads(raw)
    allowed = {"domain", "federation", "factoryId", "resourceBookId", "authorityCellId", "issuer",
               "ownerBudget", "lifetime", "birthSlack", "tariffBase", "tariffPerBirth", "tariffPerGrant",
               "tariffPerInitialPayloadByte", "collector", "asset", "genesisHeight", "expectedSeed",
               "storageBinary", "storageRoot", "signatureBinary", "checkpointKey", "checkpointEvery",
               "grainBirthTariff", "completionCustodianKey", "lifecycleManagement",
               "agentLifetimeDispatchTargets", "nockFSync", "disabledEvaluators"}
    if any(value[key] is not None for key in set(value) - allowed):
        raise ValueError("fresh Host settings include unreviewed controller-visible fields")
    for name in ("storageBinary", "storageRoot", "signatureBinary", "checkpointKey"):
        if value.get(name) is not None and (not isinstance(value[name], str) or not Path(value[name]).is_absolute()):
            raise ValueError("Host storage/checkpoint setting must remain an absolute path, never key bytes")
    public = value.get("completionCustodianKey")
    if public is not None and (not isinstance(public, str) or len(public) != 64 or bytes.fromhex(public).hex() != public):
        raise ValueError("completion custodian public key shape differs")
    return raw


class Operator:
    def __init__(self, run, phase="setup"):
        self.run = run
        self.root = run / "agent-lifetime"
        repair = self.root / "repair-payer-custody"
        if repair.exists() and not (repair / "complete.json").is_file():
            raise ValueError("payer custody successor publication is incomplete")
        self.workroom = run / "world/store/base/workroom"
        self.config = self.workroom / "deployment/pinned-config.json"
        self.host = run / "bin/minidregg-host"
        self.mini = run / "bin/mini"
        self.public = run / "world/sock/participant/host.sock"
        self.operator = run / "world/sock/operator/host.sock"
        self.evidence = run / "world/evidence"
        self.allocation = read(self.root / "allocation.json")
        if len(self.allocation["agents"]) != 1:
            raise ValueError("one explicitly allocated Oracle controller required")
        self.agent = self.allocation["agents"][0]
        self.calls = self.root / ("native-" + phase)
        self.calls.mkdir(mode=0o700)

    def call(self, label, args):
        # Logs contain native source/output, never raw signing key bytes.
        with (self.calls / (label + ".stdout")).open("xb") as out, (self.calls / (label + ".stderr")).open("xb") as err:
            result = subprocess.run([str(x) for x in args], stdout=out, stderr=err)
        if result.returncode:
            raise RuntimeError(f"{label} failed ({result.returncode}); retain attempt, do not resubmit")

    def query(self, label, subject, target, capability, key, view="resource"):
        intent = self.calls / (label + "-intent.json")
        output = self.calls / label
        write(intent, {"subject": subject, "nonce": str(secrets.randbits(120)),
                       "purpose": {"type": "query", "kind": "object", "target": target, "view": view},
                       "grants": [{"kind": "object", "target": target, "capability": capability}]})
        self.call(label, [self.mini, "query", "--host", self.host, "--config", self.config,
                         "--socket", self.public, "--intent", intent, "--key", key, "--view", view, "--dir", output])
        return output

    def delegate_observe(self, label, target, parent, child, holder):
        key = self.workroom / "tool.key"
        capability = self.query(label + "-capability", "8", target, parent, key, "capability")
        inspected = self.calls / (label + "-capability.json")
        self.call(label + "-inspect-capability", [self.host, self.config, "inspect", "view-object-capability",
                                                   capability / "view.bin", inspected])
        current = self.query(label + "-current", "8", target, parent, key)
        head = read(inspected)["head"]
        challenge = read(current / "challenge.json")
        grant = dict(head, id=child, parent=head["id"], holder={"type": "subject", "subject": holder},
                     targets=[target], verbs=["observe"], ancestors=sorted(set(head["ancestors"] + [head["id"]])))
        intent = {"subject": "8", "nonce": str(secrets.randbits(120)),
                  "purpose": {"type": "prepare", "draft": {"type": "delegate-source", "command": {
                      "kind": "object", "domain": challenge["domain"], "semantics": challenge["semantics"],
                      "subject": "8", "nonce": str(secrets.randbits(120)),
                      "expectedTargetRoot": read(current / "view.json")["cell"]["root"],
                      "parentId": head["id"], "target": target, "child": grant}}},
                  "grants": [{"kind": "object", "target": target, "capability": head["id"]}]}
        source = self.calls / (label + "-intent.json")
        write(source, intent)
        attempt = self.calls / (label + "-attempt")
        self.call(label + "-submit", [self.mini, "submit", "--host", self.host, "--config", self.config,
                                     "--socket", self.public, "--intent", source, "--key", key, "--dir", attempt])
        return receipt(read(attempt / "outcome.json"))

    def dispatch_config(self, home, layout):
        a, caps = self.agent, self.agent["plannedCaps"]
        if layout["controllerHome"] != str(home):
            raise ValueError("dispatch layout names another controller home")
        return {"task": a["dispatch"]["task"], "subject": a["dispatch"]["subject"],
            "capability": caps["dispatchOwner"], "queryCapability": caps["dispatchOwner"],
            "custodyKey": str(home / "custody/dispatch.key"),
            "parentCapability": caps["parentDispatchWitness"], "parentObserveCapability": caps["parentDispatchWitness"],
            "reserve": "1", "charge": "1", "socketPath": layout["reverseSocket"], "hostUid": os.getuid(),
            "operatorSocket": layout["operatorSocket"], "operatorPeerUid": layout["operatorPeerUid"],
            "reserveSigner": {"role": "4", "index": "0",
                "publicKey": (self.workroom / "agents" / a["route"] / "dispatch.pub").read_bytes().hex(),
                "keyId": a["dispatch"]["keyId"], "keyEpoch": "2"}}

    def prepare_bootstrap_dispatch(self, layout_file):
        """Render the real dispatch role for a pre-attachment continuation."""
        layout = read(layout_file)
        home = Path(layout["controllerHome"])
        config = read(self.root / "controller-stage/controller.json")
        if config.get("dispatchTask") is not None:
            raise ValueError("bootstrap already configures dispatch; no replacement permitted")
        config["dispatchTask"] = self.dispatch_config(home, layout)
        bundle = self.calls / "controller-update"
        bundle.mkdir(mode=0o700)
        write(bundle / "controller.json", config)
        return bundle / "controller.json"

    def prepare_controller(self, home):
        """Earn discovery grants, then render an installable private candidate.

        The caller installs this candidate under a dedicated account using the
        supported operator installer. Rendering does not launch a controller.
        """
        a, caps = self.agent, self.agent["plannedCaps"]
        app_birth = read(self.evidence / "a-app-author/source.json")["applicationGrainBirth"]["applicationBirth"]["application"]
        if {key: app_birth[key] for key in ("app", "packageManifest", "snapshotManifest")} != {
            key: self.allocation[key] for key in ("app", "packageManifest", "snapshotManifest")
        }:
            raise ValueError("actual app birth differs from allocation")
        issue_dir = self.evidence / "a-ticket-9120/issue"
        issue_request = read(self.evidence / "a-ticket-9120/request.json")
        ticket = issue_request["spec"]["ticket"]
        if ticket["scope"]["app"] != app_birth["app"]:
            raise ValueError("bootstrap discovery ticket names a different app")
        grants = [
            ("app", app_birth["app"], app_birth["appOwnerCapability"], caps["appObserve"]),
            ("manifest", app_birth["packageManifest"], app_birth["packageOwnerCapability"], caps["manifestObserve"]),
            ("snapshot", app_birth["snapshotManifest"], app_birth["snapshotOwnerCapability"], caps["snapshotObserve"]),
            ("discovery-ticket", ticket["resource"], issue_request["spec"]["ticketOwnerCapability"], caps["bootstrapTicketObserve"]),
        ]
        grant_receipts = {}
        for name, target, parent, child in grants:
            grant_receipts[name] = self.delegate_observe(name, target, parent, child, a["tool"]["subject"])
        # The controller participant needs its own app and manifest reads for
        # later signed ticket/lifetime plans; these are separate capabilities.
        for name, target, parent, child in [
            ("controller-app", app_birth["app"], app_birth["appOwnerCapability"], caps["controllerAppObserve"]),
            ("controller-manifest", app_birth["packageManifest"], app_birth["packageOwnerCapability"], caps["controllerManifestObserve"]),
        ]:
            grant_receipts[name] = self.delegate_observe(name, target, parent, child, a["controller"]["subject"])
        stage = self.root / "controller-stage"
        stage.mkdir(mode=0o700)
        for name in ("custody", "state", "state/shared-app-refs", "workspace"):
            (stage / name).mkdir(mode=0o700)
        for role in ("controller", "tool", "dispatch", "provider"):
            source = self.workroom / "agents" / a["route"] / (role + ".key")
            write(stage / "custody" / (role + ".key"), source.read_bytes())
        write(stage / "host-config.json", controller_host_metadata(self.config))
        birth_call = self.evidence / "a-app-attempt/call.bin"
        issue_call = issue_dir / "ingress.bin"
        write(stage / "state/shared-app-refs/app-birth.bin", birth_call.read_bytes())
        write(stage / "state/shared-app-refs/bootstrap-ticket.bin", issue_call.read_bytes())
        born = receipt(read(self.evidence / "a-app-attempt/outcome.json"))
        issued = read(issue_dir / "receipt-anchor.json")["receipt"]
        shared = {"name": "oracle-bootstrap-app", "applicationFamily": "oracle", "appTarget": app_birth["app"],
                  "manifestTarget": app_birth["packageManifest"], "snapshotTarget": app_birth["snapshotManifest"],
                  "ticketTarget": ticket["resource"], "appObserveCapability": caps["appObserve"],
                  "manifestObserveCapability": caps["manifestObserve"], "snapshotObserveCapability": caps["snapshotObserve"],
                  "ticketObserveCapability": caps["bootstrapTicketObserve"],
                  "birth": {**born, "call": str(home / "state/shared-app-refs/app-birth.bin"), "callSha256": sha(birth_call)},
                  "issue": {**issued, "kind": "grainBackedEvent22", "ingress": str(home / "state/shared-app-refs/bootstrap-ticket.bin"),
                            "ingressSha256": sha(issue_call)}}
        profile = {"genesis": read(self.workroom / "genesis.json"),
                   "template": {"issuer": "5", "ownerBudget": "100000", "lifetime": "10000"},
                   "factoryTarget": "10", "factoryObserveCapability": a["tool"]["factoryObserveCapability"],
                   "payerAccount": a["tool"]["account"], "payerCapability": caps["toolSpend"],
                   "payerObserveCapability": caps["toolSpend"], "tariffBase": "2", "tariffPerBirth": "1"}
        family = {"name": "oracle-session", "applicationFamily": "oracle", "kind": "api",
                  "participantSubject": a["controller"]["subject"], "profile": profile,
                  "namespace": {"session": a["session"], "descriptor": a["descriptor"],
                      "sessionOwnerCapability": caps["sessionOwner"], "sessionControlCapability": caps["sessionControl"],
                      "descriptorOwnerCapability": caps["descriptorOwner"], "descriptorControlCapability": caps["descriptorControl"]},
                  "maxBirths": 1, "maxResultBytes": 65536}
        config = {"mini": str(home / "bin/mini"), "host": str(home / "bin/minidregg-host"),
                  "hostConfig": str(home / "host-config.json"), "hostSocket": str(self.public),
                  "custodyKey": str(home / "custody/controller.key"), "stateDir": str(home / "state"),
                  "controlSocket": str(home / "state/control.sock"), "cwd": str(home / "workspace"),
                  "task": a["controller"]["task"], "subject": a["controller"]["subject"],
                  "capability": caps["parentOwner"], "queryCapability": caps["parentOwner"],
                  "policyControlCapability": caps["parentControl"], "foregroundTool": {"reserve": "1", "charge": "0"},
                  "toolTask": {"task": a["tool"]["task"], "subject": a["tool"]["subject"],
                      "capability": caps["toolOwner"], "queryCapability": caps["toolOwner"],
                      "custodyKey": str(home / "custody/tool.key"), "parentCapability": caps["parentToolWitness"],
                      "parentObserveCapability": caps["parentToolWitness"], "reserve": "5", "charge": "0",
                      "allowedPublications": [], "registeredSharedApplications": [shared],
                      "allowedSessionFamilies": [family], "currentBirthHostSha256": sha(self.host)}, "commands": []}
        config["dispatchTask"] = self.dispatch_config(home, read(self.root / "controller-create.json"))
        write(stage / "controller.json", config)
        write(self.root / "controller-stage.json", {"protocol": "mini-oracle-controller-stage-v1",
              "stage": str(stage), "home": str(home), "configSha256": sha(stage / "controller.json"),
              "hostSha256": sha(self.host), "runtimeSha256": sha(self.run / "bin/grain-runtime"),
              "discoveryGrantReceipts": grant_receipts,
              "nextTool": {"name": "mini_create_application_session", "arguments": {"family": "oracle-session", "application": "oracle-bootstrap-app"}}})
        return self.root / "controller-stage.json"

    def prepare_worker_policy(self, config_file):
        """Owner-authorized narrowing for the actual initial controller roles.

        This is deliberately limited to the untouched, paused bootstrap parent.
        Native signed reads, policy authoring, consent and the ordinary install
        receiver establish the transition; this harness supplies no authority.
        """
        a, caps = self.agent, self.agent["plannedCaps"]
        config = read(config_file)
        controller = a["controller"]
        if (config.get("task"), config.get("subject"), config.get("capability"),
                config.get("queryCapability"), config.get("policyControlCapability")) != (
                controller["task"], controller["subject"], caps["parentOwner"],
                caps["parentOwner"], caps["parentControl"]):
            raise ValueError("bootstrap controller differs from allocated owner authority")
        workers = []
        for field, role in (("toolTask", "tool"), ("dispatchTask", "dispatch"), ("providerTask", "provider")):
            task = config.get(field)
            if task is not None:
                if (task.get("task"), task.get("subject")) != (a[role]["task"], a[role]["subject"]):
                    raise ValueError("bootstrap worker differs from actual allocated role")
                workers.append(task["subject"])
        if not workers or len(workers) == 3:
            raise ValueError("bootstrap repair requires a strict nonempty worker subset")
        key = self.workroom / "agents" / a["route"] / "controller.key"
        parent = self.query("parent-before-policy", controller["subject"], controller["task"], caps["parentOwner"], key)
        grain = read(parent / "view.json")["cell"]["grain"]
        if any(grain.get(k) != v for k, v in {"task": controller["task"], "generation": "0", "status": "0", "reserved": "0"}.items()):
            raise ValueError("bootstrap owner repair requires untouched paused generation zero")
        before = self.query("policy-before", controller["subject"], controller["task"], caps["parentOwner"], key, "policy")
        view = read(before / "view.json")
        if view.get("policyId") != controller["task"] or view.get("version") != "0" or view.get("previous") is not None:
            raise ValueError("bootstrap policy is not the original source policy")

        def authored(label, kind, value):
            source, output = self.calls / (label + ".json"), self.calls / (label + ".bin")
            write(source, value)
            self.call(label, [self.mini, "author", "--host", self.host, "--config", self.config,
                             "--socket", self.public, "--kind", kind, "--input", source, "--output", output])
            return output.read_bytes()

        original = {"owner": controller["subject"], "workerSubjects": [a[role]["subject"] for role in ("tool", "dispatch", "provider")], "workerGeneration": "1"}
        if authored("original-allocation-law", "grain-policy", original) != authored("current-law", "predicate", view["predicate"]):
            raise ValueError("current source policy differs from exact allocated worker law")
        desired = {"owner": controller["subject"], "workerGeneration": "1",
                   "workerSubject" if len(workers) == 1 else "workerSubjects": workers[0] if len(workers) == 1 else workers}
        expected = authored("configured-worker-law", "grain-policy", desired)
        source = dict(desired, subject=controller["subject"], intentNonce=str(secrets.randbits(120)),
                      declarationNonce=str(secrets.randbits(120)), task=controller["task"], control=caps["parentControl"],
                      domain=view["domain"], semantics=view["semantics"],
                      expectedPreRoot=read(before / "challenge.json")["authorityRoot"],
                      expectedVersion=view["version"], expectedAddress=view["address"], currentSourceHex=view["canonical"],
                      grants=[{"kind": "object", "target": controller["task"], "capability": caps["parentOwner"]}])
        intent, attempt = self.calls / "owner-policy-install.json", self.calls / "owner-policy-attempt"
        write(intent, source)
        self.call("owner-policy-install", [self.mini, "submit", "--host", self.host, "--config", self.config,
                  "--socket", self.public, "--intent", intent, "--intent-kind", "grain-policy-install-intent",
                  "--key", key, "--dir", attempt])
        confirmed = receipt(read(attempt / "outcome.json"))
        after = self.query("policy-after", controller["subject"], controller["task"], caps["parentOwner"], key, "policy")
        installed = read(after / "view.json")
        if (installed.get("policyId"), installed.get("version"), installed.get("previous")) != (controller["task"], "1", view["address"]):
            raise ValueError("installed owner policy does not extend exact observed source")
        if authored("installed-worker-law", "predicate", installed["predicate"]) != expected:
            raise ValueError("installed owner policy differs from actual configured workers")
        result = self.calls / "worker-policy.json"
        write(result, {"protocol": "mini-oracle-bootstrap-worker-policy-v1", "controllerConfigSha256": sha(config_file),
                      "workers": workers, "workerGeneration": "1", "attempt": str(attempt), "receipt": confirmed,
                      "before": str(before), "after": str(after)})
        return result

    def slot_signers(self, slots, header_name):
        known = {"8008": (self.workroom / "tool.key", self.workroom / "tool.pub"),
                 "7007": (self.workroom / "controller.key", self.workroom / "controller.pub")}
        for role in ("controller", "tool", "dispatch", "provider"):
            directory = self.workroom / "agents" / self.agent["route"]
            known[self.agent[role]["keyId"]] = (directory / (role + ".key"), directory / (role + ".pub"))
        answer = []
        for slot in slots:
            signing = slot["signing"]
            if signing["decoded"] is not True or signing["algorithm"] != "1" or signing["keyEpoch"] != "2":
                raise ValueError("source signing slot is outside enrolled custody")
            key, public = known[signing["keyId"]]
            if len(key.read_bytes()) != 32 or len(public.read_bytes()) != 32:
                raise ValueError("enrolled signer key shape differs")
            header = bytes.fromhex(slot[header_name])
            if not header:
                raise ValueError("empty source signing header")
            answer.append({"role": slot["role"], "index": slot["index"], "keyId": signing["keyId"],
                           "keyEpoch": signing["keyEpoch"], "publicKey": public.read_bytes().hex(),
                           "headerSha256": hashlib.sha256(header).hexdigest(), "keyPath": str(key)})
        return answer

    def reserve_issuer_tool(self):
        key = self.workroom / "tool.key"
        current = self.query("issuer-tool", "8", "7902", "81", key)
        view = read(current / "view.json")
        nonce = str(secrets.randbits(120))
        intent = {"grain": {"task": "7902", "subject": "8", "capability": "81", "observeCapability": "81",
                  "schemaVersion": "1", "expectedTargetRoot": view["cell"]["root"],
                  "context": {"operationId": nonce, "payload": "Oracle agent ticket issuance"},
                  "before": {k: view["cell"]["grain"][k] for k in ("generation", "status", "remaining", "reserved")},
                  "operation": {"type": "reserve", "amount": "3"}, "publications": []},
                  "grants": [{"kind": "object", "target": "7902", "capability": "81"}], "intentNonce": nonce}
        source = self.calls / "issuer-reserve.json"
        write(source, intent)
        attempt = self.calls / "issuer-reserve"
        self.call("issuer-reserve", [self.mini, "submit", "--host", self.host, "--config", self.config,
                  "--socket", self.public, "--intent", source, "--intent-kind", "grain-intent", "--key", key, "--dir", attempt])
        receipt(read(attempt / "outcome.json"))

    def issue_grant(self, session_result):
        """Issue actual event22 and event27 from a completed runtime session tool.

        The native author rereads the actual installed session; this result
        merely selects our allocated session and links acceptance evidence.
        """
        result = read(session_result)
        if result.get("type") != "tool-complete" or result.get("isError") is not False or result["result"].get("isError") is not False:
            raise ValueError("session foreground tool did not complete")
        body = json.loads(result["result"]["text"])
        a, caps = self.agent, self.agent["plannedCaps"]
        if body.get("type") != "confirmed-mini-application-birth-v1" or body.get("route") != "session":
            raise ValueError("runtime did not return a session birth")
        if {r["target"] for r in body["bornResources"]} != {a["session"], a["descriptor"]}:
            raise ValueError("runtime session birth differs from allocated pair")
        write(self.calls / "session-tool-result.json", Path(session_result).read_bytes())
        controller_key = self.workroom / "agents" / a["route"] / "controller.key"
        current = self.query("controller-parent", a["controller"]["subject"], a["controller"]["task"],
                             caps["parentOwner"], controller_key)
        generation = read(current / "view.json")["cell"]["grain"]["generation"]
        self.query("agent-session", a["controller"]["subject"], a["session"], caps["sessionOwner"], controller_key)
        app = read(self.evidence / "a-app-author/source.json")["applicationGrainBirth"]["applicationBirth"]["application"]
        app_current = self.query("issuing-app", "8", app["app"], app["appOwnerCapability"], self.workroom / "tool.key")
        entries = read(app_current / "view.json")["cell"]["entries"]
        package_version = next(e["value"] for e in entries if e["key"]["field"] == "2")
        state = Path(read(self.evidence / "profile-result.json")["stateRoot"])
        package_dir = state / "apps" / app["app"] / "install/launch-descriptor/package-v1"
        schema = read(package_dir / "schema-inspection.json")
        interface = next(i for i in read(package_dir / "descriptor-inspection.json")["interfaces"] if i["kind"] == "api")
        launch_root = read(package_dir.parent / "launch-inspection.json")["root"]
        ceiling = {"basis": {"type": "role", "id": "0"}, "added": [], "removed": [],
                   "roleSchemaRoot": schema["root"], "roleVersion": schema["version"]}
        request = {"spec": {"ticket": {"resource": a["ticket"],
            "scope": {"app": app["app"], "packageVersion": package_version, "packageRoot": launch_root,
                      "interfaceId": interface["id"], "interfaceVersion": interface["version"],
                      "interfaceRoot": interface["root"], "schemaRoot": schema["root"], "schemaVersion": schema["version"]},
            "participant": {"session": a["session"], "descriptorResource": a["descriptor"], "kind": "api",
                            "subject": a["controller"]["subject"], "origin": {"type": "agent", "task": a["controller"]["task"], "generation": generation},
                            "sessionCapability": caps["sessionOwner"], "appObserveCapability": caps["controllerAppObserve"],
                            "ticketObserveCapability": caps["ticketObserve"]},
            "ceiling": ceiling, "issueNonce": str(secrets.randbits(120)), "notAfter": "1000000000"},
            "issuer": "8", "appDelegateCapability": app["appOwnerCapability"],
            "ticketOwnerCapability": caps["ticketOwner"], "ticketControlCapability": caps["ticketControl"]},
            "payer": "8", "funding": [], "sourceCapabilities": ["42"],
            "tool": {"task": "7902", "capability": "81", "observeCapability": "81"},
            "parent": {"task": "7901", "capability": "73", "observeCapability": "73"}}
        self.reserve_issuer_tool()
        source = self.calls / "ticket-request.json"
        write(source, request)
        preview = self.calls / "ticket-preview"
        self.call("ticket-plan", [self.mini, "grain-share-issue-plan", "--host", self.host, "--config", self.config,
                                   "--socket", self.operator, "--request", source, "--dir", preview])
        inspected = read(preview / "request-inspected.json")
        approved = {"type": "minidregg-grain-share-issue-approval-v1", "requestSha256": sha(preview / "request.bin"),
                    "canonicalSpec": inspected["canonicalSpec"], "issuer": inspected["spec"]["issuer"],
                    "participantSubject": inspected["spec"]["ticket"]["participant"]["subject"],
                    "appDelegateCapability": inspected["spec"]["appDelegateCapability"],
                    "ticketResource": inspected["spec"]["ticket"]["resource"],
                    **{key: inspected[key] for key in ("payer", "funding", "sourceCapabilities", "tool", "parent")},
                    "signers": self.slot_signers(read(preview / "plan-inspected.json")["slots"], "header")}
        approval = self.calls / "ticket-approval.json"
        write(approval, approved)
        ticket_attempt = self.calls / "ticket-issue"
        self.call("ticket-prepare", [self.mini, "grain-share-issue-prepare", "--host", self.host, "--config", self.config,
                  "--socket", self.operator, "--request", source, "--approval", approval, "--dir", ticket_attempt])
        self.call("ticket-submit", [self.mini, "grain-share-issue-submit", "--socket", self.operator, "--attempt", ticket_attempt])
        self.call("ticket-lookup", [self.mini, "grain-share-issue-lookup", "--socket", self.operator, "--attempt", ticket_attempt])
        issued = read(ticket_attempt / "receipt-anchor.json")["receipt"]
        looked_up_ticket = read(self.calls / "ticket-lookup.stdout")
        if looked_up_ticket.get("confirmation") != "replayed" or receipt(looked_up_ticket) != issued or int(issued["acceptedCount"]) <= 0:
            raise ValueError("ticket lookup differs from exact accepted issue receipt")
        issue_index = str(int(issued["acceptedCount"]) - 1)
        # Read the source-authored ticket digest; never reconstruct its hash.
        self.call("ticket-source-plan", [self.host, self.config, "inspect", "application-share-issue-grain-plan",
                                          ticket_attempt / "plan.bin", self.calls / "ticket-source-plan.json"])
        spec = read(self.calls / "ticket-source-plan.json")["request"]["spec"]
        self.delegate_observe("agent-ticket-controller", a["ticket"], caps["ticketOwner"], caps["ticketObserve"], a["controller"]["subject"])
        self.delegate_observe("agent-ticket-tool", a["ticket"], caps["ticketOwner"], caps["agentTicketToolObserve"], a["tool"]["subject"])
        grant_request = {"grant": {"source": {"resource": a["persistentGrant"], "issueIndex": issue_index,
                         "issueReceipt": issued, "ticketResource": a["ticket"], "ticketDigest": spec["ticket"]["ticketDigest"]},
                         "participant": {"app": app["app"], "session": a["session"], "subject": a["controller"]["subject"],
                         "parentTask": a["controller"]["task"], "originalGeneration": generation, "grantObserveCapability": caps["grantObserve"]},
                         "approval": {"issuer": spec["issuer"], "delegateCapability": spec["appDelegateCapability"],
                                      "ceiling": ceiling, "nonce": str(secrets.randbits(120))}},
                         "grantOwnerCapability": caps["grantOwner"], "grantControlCapability": caps["grantControl"],
                         "payer": "8", "funding": [], "sourceCapabilities": ["42"]}
        grant_source = self.calls / "grant-request.json"
        write(grant_source, grant_request)
        grant_attempt = self.calls / "grant-issue"
        self.call("grant-plan", [self.mini, "agent-lifetime-grant-plan", "--host", self.host, "--config", self.config,
                  "--operator-socket", self.operator, "--request", grant_source, "--dir", grant_attempt])
        plan = read(grant_attempt / "plan-inspected.json")
        if bytes.fromhex(plan["canonicalPlanHex"]) != (grant_attempt / "plan.bin").read_bytes():
            raise ValueError("source grant plan bytes differ")
        grant_approval = self.calls / "grant-approval.json"
        write(grant_approval, {"type": "minidregg-agent-lifetime-grant-approval-v1",
              "requestSha256": sha(grant_attempt / "request.bin"), "planSha256": sha(grant_attempt / "plan.bin"),
              **{key: plan[key] for key in ("request", "birthBoundary", "finalizedDraftHex")},
              "signers": self.slot_signers(plan["birthSlots"] + [plan["appSlot"]], "headerHex")})
        self.call("grant-seal", [self.mini, "agent-lifetime-grant-seal", "--attempt", grant_attempt, "--approval", grant_approval])
        self.call("grant-submit", [self.mini, "agent-lifetime-grant-submit", "--attempt", grant_attempt])
        self.call("grant-lookup", [self.mini, "agent-lifetime-grant-lookup", "--attempt", grant_attempt])
        looked_up = read(self.calls / "grant-lookup.stdout")
        confirmed = receipt(looked_up)
        if looked_up["confirmation"] != "replayed":
            raise ValueError("grant lacks exact native replay confirmation")
        write(self.root / "issued-grant.json", {"protocol": "mini-oracle-issued-agent-grant-v1", "ticketAttempt": str(ticket_attempt),
              "ticketReceipt": issued, "grantAttempt": str(grant_attempt), "grantReceipt": confirmed,
              "sessionToolResultSha256": sha(session_result), "originalGeneration": generation})
        return self.root / "issued-grant.json"

    def prepare_route(self, repo, layout_file):
        layout = read(layout_file)
        a, caps = self.agent, self.agent["plannedCaps"]
        for field in ("controllerHome", "listenerSocket", "reverseSocket", "operatorSocket"):
            if not Path(layout[field]).is_absolute():
                raise ValueError("controller layout paths must be absolute")
        if not isinstance(layout["controllerUid"], int) or layout["controllerUid"] in (0, os.getuid()):
            raise ValueError("dedicated non-root controller UID required")
        issued = read(self.root / "issued-grant.json")
        grant = Path(issued["grantAttempt"])
        lookups = sorted(grant.glob("lookup-????.outcome.json"))
        if not lookups:
            raise ValueError("retained native grant lookup absent")
        identity = self.workroom / "agents" / a["route"]
        def pin(role, index, actor):
            return {"role": str(role), "index": str(index), "keyId": a[actor]["keyId"], "keyEpoch": "2",
                    "publicKeyHex": (identity / (actor + ".pub")).read_bytes().hex(),
                    "seedPath": str(identity / (actor + ".key"))}
        # These are operator key-selection pins, not signatures or authority.
        # NativeHost.prepareInvokeOn signs session/parent target+observation,
        # then authority; ApplicationDispatchAuthoring adds four observations.
        app_signers = [pin(role, index, "controller") for role, index in
                       [(4, 0), (4, 1), (8, 0), (8, 1), (1, 0), (9, 0), (9, 1), (9, 2), (9, 3)]]
        payer = [pin(role, 0, "dispatch") for role in (4, 1)]
        for signer in payer:
            del signer["seedPath"]
        pins = {"controllerRouteName": "oracle-app", "socketPath": layout["listenerSocket"],
                "hostUid": os.getuid(), "hostUnit": None, "signedApiPath": "/",
                "packageManifest": self.allocation["packageManifest"], "snapshotManifest": self.allocation["snapshotManifest"],
                "sessionObserveCapability": caps["sessionOwner"], "manifestObserveCapability": caps["controllerManifestObserve"],
                "enrollmentObserveCapability": caps["descriptorOwner"], "parentCapability": caps["parentOwner"],
                "parentObserve": caps["parentOwner"], "purseCapability": caps["dispatchOwner"], "purseObserve": caps["dispatchOwner"],
                "purseResource": a["dispatch"]["task"], "payerSubject": a["dispatch"]["subject"],
                "reserveAmount": "1", "maximumCharge": "1", "appSigners": app_signers,
                "grantSigner": pin(9, 4, "controller"), "payerPins": payer}
        pins_file = self.calls / "operator-pins.json"
        write(pins_file, pins)
        route_dir = self.calls / "source-route"
        self.call("render-custody", ["sh", repo / "scripts/spk-platform/prepare-lifetime-route.sh", "--custody-only",
            self.host, self.config, grant, lookups[-1], pins_file, route_dir, sha(self.host),
            self.root / "allocation.json", a["route"]])
        request = {"protocol": "mini-spk-grain-agent-route-v1", "name": "oracle-agent-v1", "signedApiPath": "/",
            "socket": layout["listenerSocket"], "controllerUid": layout["controllerUid"],
            "custody": str(route_dir / "resident-custody-v3.json"), "reverseSocket": layout["reverseSocket"],
            "routeName": "oracle-app", "displayName": "Oracle agent", "preferredHandle": "oracle-agent",
            "reverseTimeoutSeconds": 1740, "controllerWorkerWallSeconds": 1800}
        request_file = self.calls / "route-request.json"
        write(request_file, request)
        profile = read(self.evidence / "profile-result.json")["profilePath"]
        self.call("route-register", [self.run / "bin/spk-host", "grain", "agent-route", profile, self.allocation["app"], request_file])
        write(self.root / "registered-agent-route.json", {"protocol": "mini-oracle-registered-agent-route-v1",
            "layout": layout, "layoutSha256": sha(layout_file), "pins": str(pins_file), "sourceRoute": str(route_dir),
            "grantAttempt": str(grant), "lookup": str(lookups[-1]), "request": str(request_file),
            "registration": read(self.calls / "route-register.stdout")})
        return self.root / "registered-agent-route.json"

    def activate(self, repo, start_result):
        start = read(start_result)
        a, caps = self.agent, self.agent["plannedCaps"]
        if start.get("protocol") != "mini-spk-grain-start-v1" or start.get("app") != self.allocation["app"]:
            raise ValueError("actual native START result for selected app required")
        profile = read(self.evidence / "profile-result.json")["profilePath"]
        def check_current(label):
            self.call(label, [self.run / "bin/spk-host", "grain", "status", profile, self.allocation["app"]])
            require_current_start(start, read(self.calls / (label + ".stdout")))
        check_current("current-start-before-enrollment")
        registration = read(self.root / "registered-agent-route.json")
        layout = registration["layout"]
        home = Path(layout["controllerHome"])
        identity = self.workroom / "agents" / a["route"]
        # Session enrollment is source-owned and generation-specific. Renew by
        # the ordinary owner close followed by the same native event28 path.
        observed = self.query("session-before-enrollment", a["controller"]["subject"], a["session"], caps["sessionOwner"], identity / "controller.key")
        view = read(observed / "view.json")
        fields = {entry["key"]["field"]: entry["value"] for entry in view["cell"]["entries"]}
        if fields["3"] == "5":
            nonce = str(secrets.randbits(120))
            close = {"subject": a["controller"]["subject"], "nonce": nonce,
                "grants": [{"kind": "object", "target": a["session"], "capability": caps["sessionOwner"]}],
                "purpose": {"type": "prepare", "draft": {"type": "invoke", "command": {
                    "subject": a["controller"]["subject"], "nonce": nonce, "targets": [{
                        "kind": "object", "target": a["session"], "capability": caps["sessionOwner"],
                        "observeCapability": caps["sessionOwner"], "schemaVersion": "1", "expectedTargetRoot": view["cell"]["root"],
                        "payload": {"type": "scalar", "actions": [
                            {"type": "write", "key": {"type": "object", "resource": a["session"], "field": field},
                             "expected": fields[field], "value": str(int(fields[field]) + 1)} for field in ("2", "3")]}}]}}}}
            write(self.calls / "session-close.json", close)
            self.call("session-close", [self.mini, "submit", "--host", self.host, "--config", self.config,
                "--socket", self.public, "--intent", self.calls / "session-close.json", "--key", identity / "controller.key",
                "--dir", self.calls / "session-close"])
            receipt(read(self.calls / "session-close/outcome.json"))
        issued = read(self.root / "issued-grant.json")
        ticket = read(Path(issued["ticketAttempt"]).parent / "ticket-request.json")["spec"]["ticket"]
        request = {"issueIndex": str(int(issued["ticketReceipt"]["acceptedCount"]) - 1), "ticketResource": a["ticket"],
                   "packageManifest": self.allocation["packageManifest"], "role": ticket["ceiling"],
                   "descriptorCapability": caps["descriptorOwner"], "sessionObserveCapability": caps["sessionOwner"],
                   "descriptorObserveCapability": caps["descriptorOwner"], "manifestObserveCapability": caps["controllerManifestObserve"],
                   "nonce": str(secrets.randbits(120))}
        request_file = self.calls / "enrollment-request.json"
        write(request_file, request)
        attempt = self.calls / "enrollment"
        self.call("enrollment-plan", [self.mini, "session-enrollment-plan", "--host", self.host, "--config", self.config,
            "--operator-socket", self.operator, "--request", request_file, "--dir", attempt])
        plan = read(attempt / "plan-inspected.json")
        approval = self.calls / "enrollment-approval.json"
        write(approval, {"type": "minidregg-session-enrollment-approval-v1", "requestSha256": sha(attempt / "request.bin"),
            "planSha256": sha(attempt / "plan.bin"), "planInspectionSha256": sha(attempt / "plan-inspected.json"),
            "signers": self.slot_signers(plan["slots"], "headerHex")})
        self.call("enrollment-seal", [self.mini, "session-enrollment-seal", "--attempt", attempt, "--approval", approval])
        self.call("enrollment-submit", [self.mini, "session-enrollment-submit", "--attempt", attempt])
        self.call("enrollment-lookup", [self.mini, "session-enrollment-lookup", "--attempt", attempt])
        looked_up_enrollment = read(self.calls / "enrollment-lookup.stdout")
        accepted_enrollment = read(attempt / "receipt.json")
        if looked_up_enrollment.get("confirmation") != "replayed" or receipt(looked_up_enrollment) != {
            key: accepted_enrollment[key] for key in ("transactionId", "eventId", "acceptedCount", "worldRoot")
        }:
            raise ValueError("enrollment lookup differs from exact accepted receipt")
        pins = read(registration["pins"])
        pins["hostUnit"] = start["unit"]
        pins_file = self.calls / "operator-pins.json"
        write(pins_file, pins)
        routes = self.calls / "source-route"
        self.call("render-controller-route", ["sh", repo / "scripts/spk-platform/prepare-lifetime-route.sh",
            self.host, self.config, registration["grantAttempt"], registration["lookup"], pins_file,
            routes, sha(self.host), self.root / "allocation.json", a["route"]])
        if (routes / "resident-custody-v3.json").read_bytes() != (Path(registration["sourceRoute"]) / "resident-custody-v3.json").read_bytes():
            raise ValueError("controller route reinspection changed registered resident custody")
        bundle = self.calls / "controller-update"
        bundle.mkdir(mode=0o700)
        for path in ("state", "state/shared-app-refs", "state/oracle-grant"):
            (bundle / path).mkdir(mode=0o700)
        config = read(self.root / "controller-stage/controller.json")
        reference = dict(config["toolTask"]["registeredSharedApplications"][0])
        ticket_call = Path(issued["ticketAttempt"]) / "ingress.bin"
        reference.update(name="oracle-app", ticketTarget=a["ticket"], ticketObserveCapability=caps["agentTicketToolObserve"],
                         issue={**issued["ticketReceipt"], "kind": "grainBackedEvent22", "ingress": str(home / "state/shared-app-refs/agent-ticket.bin"),
                                "ingressSha256": sha(ticket_call)})
        config["toolTask"]["registeredSharedApplications"].append(reference)
        write(bundle / "state/shared-app-refs/agent-ticket.bin", ticket_call.read_bytes())
        for name in ("seal.json", "call.bin", "submit-marker.json", "receipt.json"):
            write(bundle / "state/oracle-grant" / name, (Path(issued["grantAttempt"]) / name).read_bytes())
        route = read(routes / "controller-route-v3.json")
        route["grantAttemptDir"] = str(home / "state/oracle-grant")
        config["toolTask"].update(allowedApplicationLifetimeRoutes=[route], lifetimeApiHostSha256=sha(self.host),
                                 applicationServices=[{"application": "oracle-app", "protocol": "oracle-operations-v1"}])
        config["dispatchTask"] = self.dispatch_config(home, layout)
        check_current("current-start-before-publication")
        write(bundle / "controller.json", config)
        write(self.calls / "activation.json", {"protocol": "mini-oracle-agent-activation-v1", "bundle": str(bundle),
            "unit": start["unit"], "generation": start["generation"], "enrollmentReceipt": read(attempt / "receipt.json"),
            "configSha256": sha(bundle / "controller.json"), "next": "install stopped controller update, then start and probe"})
        return self.calls / "activation.json"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["prepare-controller", "prepare-bootstrap-dispatch", "prepare-worker-policy", "issue-grant", "prepare-route", "activate"])
    parser.add_argument("run", type=Path)
    parser.add_argument("input", type=Path, help="controller home for prepare; retained session tool result for issue")
    parser.add_argument("--repo", type=Path)
    args = parser.parse_args()
    if not args.run.is_absolute() or not args.input.is_absolute():
        parser.error("run and controller home must be absolute")
    os.umask(0o077)
    phase = args.command
    if phase == "activate":
        generation = read(args.input).get("generation", "")
        if not isinstance(generation, str) or not generation.isascii() or not generation.isdecimal():
            parser.error("native START generation absent")
        phase += "-" + generation
    operator = Operator(args.run, phase)
    if args.command == "prepare-controller":
        result = operator.prepare_controller(args.input)
    elif args.command == "prepare-worker-policy":
        result = operator.prepare_worker_policy(args.input)
    elif args.command == "prepare-bootstrap-dispatch":
        result = operator.prepare_bootstrap_dispatch(args.input)
    elif args.command == "issue-grant":
        result = operator.issue_grant(args.input)
    elif args.command == "prepare-route":
        result = operator.prepare_route(args.repo, args.input)
    else:
        result = operator.activate(args.repo, args.input)
    print(result)


if __name__ == "__main__":
    main()
