#!/usr/bin/env python3
"""Harness checks only; mocked transport is never native lifetime qualification."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import socket
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
HELPER = ROOT / "scripts/oracle-agent-lifetime-journey.sh"
ALLOCATION_CHECK = ROOT / "scripts/spk-platform/check-agent-allocation.sh"
AGENT_LIBRARY = ROOT / "scripts/workroom/agent-enrollment.sh"


def factory_lean_probe(predicate, agents):
    """Render emitted JSON syntax into production Pred.eval checks; no evaluator here."""
    def lean(node):
        if node["type"] == "eq" and set(node) == {"type","slot","value"}:
            return "(.eq " + json.dumps(node["slot"]) + " " + str(int(node["value"])) + ")"
        if node["type"] == "eqSlots" and set(node) == {"type","left","right"}:
            return "(.eqSlots " + json.dumps(node["left"]) + " " + json.dumps(node["right"]) + ")"
        if node["type"] in ("all","any") and set(node) == {"type","predicates"}:
            return "(." + node["type"] + " [" + ",".join(map(lean,node["predicates"])) + "])"
        raise ValueError("unexpected emitted factory predicate syntax")
    lines = ["import Pred.Core", "open Minidregg.Pred", "def fixtureLaw : Pred := " + lean(predicate)]
    for subject in (7,8,9,70,20010,20011,20012,20013):
        for verb, mode in ((1,False),(2,False),(2,True)):
            slots = [("request/subject",subject),("request/verb",verb)]
            if mode: slots.append(("birth/mode/grain-backed",1))
            state = "⟨[" + ",".join("("+json.dumps(k)+","+str(v)+")" for k,v in slots) + "]⟩"
            expected = subject == 7 or (subject in ((8,20011) if agents else (8,)) and (verb == 1 or mode))
            lines.append("#guard eval fixtureLaw ⟨[]⟩ " + state + " == " + str(expected).lower())
    # Factory permission requires all four source-projected coordinates. The
    # actual grant post root varies with later receipts, so presence is tested
    # using eqSlots (missing slots fail closed), never writeOnce.
    for subject in (None,8,9,20010,20011):
        for verb in (None,0,2,3):
            for count in (None,0,1,2):
                for resource in (None,29520,29530,29531):
                    slots = []
                    if subject is not None: slots.append(("request/subject",subject))
                    if verb is not None: slots.append(("request/verb",verb))
                    if count is not None: slots.append(("birth/count",count))
                    if resource is not None: slots.append(("birth/"+str(resource),123456))
                    state = "⟨[" + ",".join("("+json.dumps(k)+","+str(v)+")" for k,v in slots) + "]⟩"
                    expected = agents and subject == 8 and verb == 2 and count == 1 and resource == 29530
                    lines.append("#guard eval fixtureLaw ⟨[]⟩ " + state + " == " + str(expected).lower())
    return "\n".join(lines) + "\n"


class HarnessTests(unittest.TestCase):
    def test_owner_worker_policy_uses_exact_native_source_and_readback(self):
        spec = importlib.util.spec_from_file_location("oracle_agent_policy", ROOT / "deploy/oracle/acceptance/agent.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        allocation = json.loads((ROOT / "deploy/oracle/acceptance/agent-allocation.json").read_text())["agents"][0]
        for fault in (None, "active", "changed-policy", "wrong-readback", "unknown-worker"):
            with self.subTest(fault=fault), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                op = object.__new__(module.Operator)
                op.agent, op.calls, op.workroom = allocation, root, root
                op.mini, op.host, op.config, op.public = map(Path, ("/mini", "/host", "/config", "/socket"))
                a, caps = allocation, allocation["plannedCaps"]
                config = {"task": a["controller"]["task"], "subject": a["controller"]["subject"],
                    "capability": caps["parentOwner"], "queryCapability": caps["parentOwner"],
                    "policyControlCapability": caps["parentControl"],
                    "toolTask": {key:a["tool"][key] for key in ("task", "subject")},
                    "dispatchTask": {key:a["dispatch"][key] for key in ("task", "subject")}}
                if fault == "unknown-worker": config["dispatchTask"]["subject"] = "777"
                config_path = root / "controller.json"
                module.write(config_path, config)
                original = {"owner":a["controller"]["subject"], "workerSubjects":[a[role]["subject"] for role in ("tool", "dispatch", "provider")], "workerGeneration":"1"}
                desired = dict(original, workerSubjects=[a[role]["subject"] for role in ("tool", "dispatch")])
                calls = []
                def query(label, subject, task, capability, key, view="resource"):
                    path = root / label
                    path.mkdir()
                    if view == "resource":
                        value = {"cell":{"grain":{"task":task,"generation":"0","status":"2" if fault == "active" else "0","reserved":"0"}}}
                    else:
                        after = label == "policy-after"
                        value = {"policyId":task,"version":"1" if after else "0", "previous":"old-address" if after else None,
                            "domain":"10","semantics":"20","address":"old-address","canonical":"aa",
                            "predicate":desired if after else original}
                        if fault == "changed-policy" and not after: value["predicate"] = {"changed":True}
                        if fault == "wrong-readback" and after: value["previous"] = "wrong"
                    module.write(path / "view.json", value)
                    module.write(path / "challenge.json", {"authorityRoot":"source-root"})
                    return path
                def call(label, args):
                    calls.append((label,args))
                    if args[1] == "author":
                        source = Path(args[args.index("--input")+1])
                        output = Path(args[args.index("--output")+1])
                        module.write(output, json.dumps(module.read(source),sort_keys=True).encode())
                    elif args[1] == "submit":
                        self.assertEqual(args[args.index("--intent-kind")+1], "grain-policy-install-intent")
                        source = module.read(args[args.index("--intent")+1])
                        self.assertEqual(source["currentSourceHex"],"aa")
                        self.assertEqual(source["expectedPreRoot"],"source-root")
                        self.assertEqual(source["expectedVersion"],"0")
                        self.assertEqual(source["control"],caps["parentControl"])
                        self.assertEqual(source["workerSubjects"],desired["workerSubjects"])
                        path = Path(args[args.index("--dir")+1]); path.mkdir()
                        module.write(path / "outcome.json", {"type":"confirmed","confirmation":"installed", "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"})
                    else: self.fail("unexpected native operation")
                op.query, op.call = query, call
                if fault is None:
                    report = module.read(op.prepare_worker_policy(config_path))
                    self.assertEqual(report["workers"],desired["workerSubjects"])
                    self.assertEqual(report["receipt"]["acceptedCount"],"3")
                else:
                    with self.assertRaises(ValueError): op.prepare_worker_policy(config_path)
                    self.assertEqual(sum(args[1] == "submit" for _,args in calls), 1 if fault == "wrong-readback" else 0)

    def test_complete_grain_store_configuration_before_bootstrap(self):
        # Run the real grain-store -> positive-base -> native-share-member
        # configuration and enrollment composition. Stub native executables,
        # stopping at bootstrap before a Store exists.
        inputs = ["scripts/workroom/provision.sh",
                  "scripts/workroom/agent-enrollment.sh",
                  "scripts/spk-platform/check-agent-allocation.sh",
                  "scripts/spk-platform/grain-store.sh",
                  "native/resource-client/scenario-genesis.sh",
                  "native/resource-client/genesis.sh",
                  "native/resource-client/genesis-params.example.json",
                  "scripts/application-share-issue/native-positive-base.sh",
                  "scripts/grain-birth/native-share-member.sh",
                  "native/resource-client/journey.d/lib/genesis-params.sh",
                  "deploy/candidate/params.sh"]
        for mode in ("legacy", "agents", "unrelated-keywords", "reformatted", "custom-balances",
                     "extra-policy", "custody-conflict", "targets-conflict",
                     "multiple-policy", "unknown-policy", "expected-config", "config-mismatch"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                has_agents = mode not in ("legacy", "expected-config", "config-mismatch")
                repo = root / "repo"
                for name in inputs:
                    path = repo / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes((ROOT / name).read_bytes())
                provision = repo / "scripts/workroom/provision.sh"
                original = provision.read_text()
                line = '"$MINI" bootstrap --host '
                if mode == "reformatted":
                    reformatted = original.replace(line, '"$MINI"  bootstrap  --host ')
                    self.assertNotEqual(reformatted, original)
                    provision.write_text(reformatted)
                elif mode == "unrelated-keywords":
                    provision.write_text(original + "\n# lifecycleManagement agentLifetimeDispatchTargets grainBirthTariff\n")
                native = root / "native"
                native.write_text('''#!/usr/bin/env python3
import hashlib,json,os,pathlib,sys
args=sys.argv[1:]
if args[0]=='keygen':
 for option in ('--secret','--public'):
  path=pathlib.Path(args[args.index(option)+1]);path.write_bytes(hashlib.sha256(str(path).encode()).digest())
elif len(args)==2 and args[1]=='profile':
 (pathlib.Path(os.environ['OVERLAY_CAPTURE'])/'profile-called').write_text('yes')
 print(json.dumps({'semantics':'1'}))
elif args[0]=='bootstrap':
 out=pathlib.Path(os.environ['OVERLAY_CAPTURE'])
 for option,name in (('--config','config.json'),('--source','genesis.json')):
  (out/name).write_bytes(pathlib.Path(args[args.index(option)+1]).read_bytes())
 sys.exit(77)
else: raise SystemExit('unexpected native command: '+repr(args))
''')
                native.chmod(0o700)
                capture = root / "capture"
                capture.mkdir()
                env = {key: value for key, value in os.environ.items()
                       if key not in ("CANDIDATE", "SPK_AGENT_ALLOCATION", "GENESIS_PARAMS_TREE", "MEMBER_INITIAL_BALANCE",
                                          "GENESIS_PAY_OBSERVER", "EXTRA_CLOCK_TICKERS", "EXTRA_GENESIS_ENROLLMENTS",
                                          "GENESIS_NOW", "MAX_STEP_SECONDS")
                       and not key.startswith("WORKROOM_")}
                env.update(OVERLAY_CAPTURE=str(capture), GENESIS_PARAMS_TREE=str(repo))
                if has_agents:
                    env["SPK_AGENT_ALLOCATION"] = str(ROOT / "deploy/oracle/acceptance/agent-allocation.json")
                if mode == "custom-balances":
                    env.update(WORKROOM_SPONSOR_BALANCE="12345", WORKROOM_TOOL_BALANCE="23456")
                policies = {
                    "extra-policy": {"providerServices": []},
                    "custody-conflict": {"completionCustodianKey": "00" * 32},
                    "targets-conflict": {"agentLifetimeDispatchTargets": []},
                    "multiple-policy": {},
                    "unknown-policy": {"storageRoot": "/not-the-fixture-store"},
                }
                if mode in policies:
                    policy = root / "operator-policy.json"
                    policy.write_text(json.dumps(policies[mode]) + ("\n{}" if mode == "multiple-policy" else ""))
                    env["WORKROOM_OPERATOR_POLICY"] = str(policy)
                if mode in ("expected-config", "config-mismatch"):
                    completion = root / "new-world/custody/completion.pub"
                    expected = {"domain":8501,"federation":9,"factoryId":10,"resourceBookId":11,
                        "authorityCellId":12,"issuer":5,"ownerBudget":100000,"lifetime":10000,
                        "tariffBase":3,"tariffPerBirth":2,"tariffPerGrant":1,"tariffPerInitialPayloadByte":1,
                        "collector":99,"asset":0,"genesisHeight":10,"expectedSeed":0,
                        "storageBinary":str(native),"storageRoot":str(root / "new-world/base/workroom/store"),
                        "signatureBinary":str(native),"grainBirthTariff":{"base":2,"perBirth":1},
                        "completionCustodianKey":hashlib.sha256(str(completion).encode()).hexdigest(),
                        "lifecycleManagement":{"managementSubject":8,"managementKeyId":8008}}
                    if mode == "config-mismatch": expected["lifetime"] += 1
                    expected_path = root / "expected-operator.json"
                    expected_path.write_text(json.dumps(expected))
                    env["WORKROOM_EXPECTED_OPERATOR_CONFIG"] = str(expected_path)
                result = subprocess.run(["sh", str(repo / "scripts/spk-platform/grain-store.sh"),
                                         str(root / "new-world"), *([str(native)] * 4)],
                                        env=env, capture_output=True, text=True)
                if mode == "config-mismatch":
                    diagnostics = result.stderr + "\n".join(p.read_text() for p in root.rglob("*.stderr"))
                    self.assertEqual(result.returncode, 2, diagnostics)
                    self.assertTrue((capture / "profile-called").exists())
                    self.assertFalse((capture / "config.json").exists())
                    self.assertFalse((root / "new-world/base/workroom/deployment").exists())
                    self.assertIn("differs", diagnostics)
                    continue
                if mode in ("custody-conflict", "targets-conflict", "multiple-policy", "unknown-policy"):
                    self.assertEqual(result.returncode, 2)
                    self.assertFalse((capture / "config.json").exists())
                    continue
                diagnostics = result.stderr + "\n".join(p.read_text() for p in root.rglob("*.stderr"))
                self.assertEqual(result.returncode, 77, diagnostics)
                config = json.loads((capture / "config.json").read_text())
                genesis = json.loads((capture / "genesis.json").read_text())
                self.assertEqual(config["lifecycleManagement"], {"managementSubject": 8, "managementKeyId": 8008})
                self.assertEqual(config["grainBirthTariff"], {"base": 2, "perBirth": 1})
                self.assertEqual(config["tariffPerInitialPayloadByte"], 1)
                self.assertEqual(genesis["tariffPerInitialPayloadByte"], "1")
                balances = {entry["key"]["subject"]: entry["initialBalance"] for entry in genesis["enrollments"]}
                expected_balances = {"7": "12345", "8": "23456", "9": "1"} if mode == "custom-balances" else {
                    "7": "1000000", "8": "1000000", "9": "1"}
                self.assertEqual({subject: balances[subject] for subject in ("7", "8", "9")},
                                 expected_balances)
                if mode == "extra-policy":
                    self.assertEqual(config["providerServices"], [])
                self.assertEqual(genesis["clockControlCapability"], "4093")
                clock = next(entry for entry in genesis["enrollments"] if entry["key"]["subject"] == "70")
                self.assertEqual(clock["key"]["keyId"], "7070")
                self.assertEqual(clock["accountId"], "70")
                self.assertEqual(clock["initialBalance"], "0")
                self.assertEqual([clock[key] for key in ("spendCapabilityId", "controlCapabilityId", "factoryObserveCapabilityId")],
                                 ["4071", "4072", "4073"])
                self.assertEqual(genesis["clockTickers"], [{"subject": "70", "capability": "4074"}])
                self.assertEqual(genesis["platform"], {
                    "ownerBudget": str(config["ownerBudget"]),
                    "lifetime": str(config["lifetime"]),
                    "grainBirthTariff": {"base": "2", "perBirth": "1"},
                    "completionCustodianKey": config["completionCustodianKey"],
                })
                self.assertFalse((root / "new-world/base/workroom/deployment").exists())
                # This is the actual predicate passed through production configuration,
                # not a separately generated test policy.
                original_law = {"type":"any","predicates":[
                    {"type":"eq","slot":"request/subject","value":"7"},
                    {"type":"all","predicates":[
                        {"type":"eq","slot":"request/subject","value":"8"},
                        {"type":"any","predicates":[
                            {"type":"eq","slot":"request/verb","value":"1"},
                            {"type":"eq","slot":"birth/mode/grain-backed","value":"1"}]}]}]}
                expected_law = json.loads(json.dumps(original_law))
                if has_agents:
                    addition = json.loads(json.dumps(original_law["predicates"][1]))
                    addition["predicates"][0]["value"] = "20011"
                    expected_law["predicates"].append(addition)
                    expected_law["predicates"].append({"type":"all","predicates":[
                        {"type":"eq","slot":"request/subject","value":"8"},
                        {"type":"eq","slot":"request/verb","value":"2"},
                        {"type":"eq","slot":"birth/count","value":"1"},
                        {"type":"eqSlots","left":"birth/29530","right":"birth/29530"}]})
                self.assertEqual(genesis["factoryPredicate"], expected_law)
                predicate_file = next(root.glob("new-world/base/workroom.source-stage/factory-predicate.json"))
                self.assertEqual(json.loads(predicate_file.read_bytes()), expected_law)
                if not has_agents:
                    # Exact canonical predicate bytes retain the original literal.
                    self.assertEqual(predicate_file.read_text(), json.dumps(original_law,separators=(",",":"))+"\n")
                else:
                    pin = predicate_file.with_name("agent-factory-allocation.sha256").read_text().split()[0]
                    self.assertEqual(pin,hashlib.sha256((ROOT / "deploy/oracle/acceptance/agent-allocation.json").read_bytes()).hexdigest())
                evidence = os.environ.get("ORACLE_FACTORY_EVIDENCE")
                if evidence:
                    destination = Path(evidence) / (mode + "-predicate.json")
                    with destination.open("x") as out: json.dump(genesis["factoryPredicate"],out,sort_keys=True)
                    with destination.with_suffix(".lean").open("x") as out:
                        out.write(factory_lean_probe(genesis["factoryPredicate"],has_agents))
                if not has_agents:
                    self.assertNotIn("agentLifetimeDispatchTargets", config)
                    self.assertEqual(len(genesis["enrollments"]), 4)
                else:
                    targets = config["agentLifetimeDispatchTargets"]
                    self.assertEqual(len(targets), 1)
                    self.assertEqual(targets[0]["grantResource"], 29530)
                    self.assertEqual(targets[0]["legacy"]["ticketResource"], 29520)
                    self.assertNotIn("issueIndex", targets[0]["legacy"])
                    self.assertNotIn("grantIssueIndex", targets[0])
                    self.assertEqual(len(genesis["enrollments"]), 8)

    def test_actual_factory_allocation_guard(self):
        source = (ROOT / "scripts/grain-birth/native-share-member.sh").read_text()
        start = source.index("FACTORY_PREDICATE=")
        end = source.index("# Configuration inputs",start)
        for fault in (None,"empty","relative","missing","symlink","duplicate","other-role","owner","nonnumeric",
                      "missing-grant","grant-nonnumeric","grant-leading-zero","grant-session","grant-task","grant-app",
                      "duplicate-grant","relocated-grant"):
            with self.subTest(fault=fault), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                allocation = json.loads((ROOT / "deploy/oracle/acceptance/agent-allocation.json").read_bytes())
                if fault == "duplicate": allocation["agents"].append(allocation["agents"][0])
                if fault == "other-role": allocation["agents"][0]["tool"]["subject"] = allocation["agents"][0]["dispatch"]["subject"]
                if fault == "owner": allocation["agents"][0]["tool"]["subject"] = "7"
                if fault == "nonnumeric": allocation["agents"][0]["tool"]["subject"] = "20011|invalid"
                if fault == "missing-grant": del allocation["agents"][0]["persistentGrant"]
                if fault == "grant-nonnumeric": allocation["agents"][0]["persistentGrant"] = "29530|invalid"
                if fault == "grant-leading-zero": allocation["agents"][0]["persistentGrant"] = "029530"
                if fault == "grant-session": allocation["agents"][0]["persistentGrant"] = allocation["agents"][0]["session"]
                if fault == "grant-task": allocation["agents"][0]["persistentGrant"] = allocation["agents"][0]["tool"]["task"]
                if fault == "grant-app": allocation["agents"][0]["persistentGrant"] = allocation["app"]
                if fault == "duplicate-grant":
                    other = json.loads(json.dumps(allocation["agents"][0]))
                    other["tool"]["subject"] = "20111"
                    allocation["agents"].append(other)
                if fault == "relocated-grant": allocation["agents"][0]["persistentGrant"] = "39530"
                path = root / "allocation.json";path.write_text(json.dumps(allocation))
                selected = str(path)
                if fault == "empty": selected = ""
                if fault == "relative": selected = "allocation.json"
                if fault == "missing": selected = str(root / "absent")
                if fault == "symlink":
                    linked = root / "link.json";linked.symlink_to(path);selected = str(linked)
                env = dict(os.environ,STAGE=str(root),SPK_AGENT_ALLOCATION=selected)
                result = subprocess.run(["sh","-eu"],input=source[start:end],env=env,capture_output=True,text=True)
                valid = fault in (None,"relocated-grant")
                self.assertEqual(result.returncode,0 if valid else 2,result.stderr)
                self.assertEqual((root / "factory-predicate.json").exists(),valid)
                if valid:
                    atom = json.loads((root / "factory-predicate.json").read_bytes())["predicates"][-1]["predicates"][-1]
                    slot = "birth/" + allocation["agents"][0]["persistentGrant"]
                    self.assertEqual(atom,{"type":"eqSlots","left":slot,"right":slot})

    def test_fixed_allocation_guard(self):
        for fault in (None,"empty","relative","missing","symlink","duplicate","other-role","owner","nonnumeric",
                      "missing-grant","grant-nonnumeric","grant-leading-zero","grant-session","grant-task","grant-app",
                      "duplicate-grant","relocated-grant","shell-route","no-agents","multiple-documents",
                      "clock-subject","clock-account","clock-key","clock-task","clock-grant",
                      "pay-control","clock-control","clock-spend","clock-account-control",
                      "clock-observe","clock-tick"):
            with self.subTest(fault=fault), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                allocation = json.loads((ROOT / "deploy/oracle/acceptance/agent-allocation.json").read_bytes())
                if fault == "duplicate": allocation["agents"].append(allocation["agents"][0])
                if fault == "other-role": allocation["agents"][0]["tool"]["subject"] = allocation["agents"][0]["dispatch"]["subject"]
                if fault == "owner": allocation["agents"][0]["tool"]["subject"] = "7"
                if fault == "nonnumeric": allocation["agents"][0]["tool"]["subject"] = "20011|invalid"
                if fault == "missing-grant": del allocation["agents"][0]["persistentGrant"]
                if fault == "grant-nonnumeric": allocation["agents"][0]["persistentGrant"] = "29530|invalid"
                if fault == "grant-leading-zero": allocation["agents"][0]["persistentGrant"] = "029530"
                if fault == "grant-session": allocation["agents"][0]["persistentGrant"] = allocation["agents"][0]["session"]
                if fault == "grant-task": allocation["agents"][0]["persistentGrant"] = allocation["agents"][0]["tool"]["task"]
                if fault == "grant-app": allocation["agents"][0]["persistentGrant"] = allocation["app"]
                if fault == "duplicate-grant":
                    other = json.loads(json.dumps(allocation["agents"][0]))
                    other["tool"]["subject"] = "20111"
                    allocation["agents"].append(other)
                if fault == "relocated-grant": allocation["agents"][0]["persistentGrant"] = "39530"
                if fault == "shell-route": allocation["agents"][0]["route"] = "oracle;touch-bad"
                if fault == "no-agents": allocation["agents"] = []
                clock_fields = {"clock-subject": ("subject", "70"), "clock-account": ("account", "70"),
                                "clock-key": ("keyId", "7070"), "clock-task": ("task", "70")}
                if fault in clock_fields:
                    field, value = clock_fields[fault]
                    allocation["agents"][0]["tool"][field] = value
                if fault == "clock-grant": allocation["agents"][0]["persistentGrant"] = "70"
                clock_caps = {"pay-control": "4031", "clock-control": "4093", "clock-spend": "4071",
                              "clock-account-control": "4072", "clock-observe": "4073", "clock-tick": "4074"}
                if fault in clock_caps: allocation["agents"][0]["plannedCaps"]["grantObserve"] = clock_caps[fault]
                path = root / "allocation.json"
                path.write_text(json.dumps(allocation) + ("\n{}" if fault == "multiple-documents" else ""))
                selected = str(path)
                if fault == "empty": selected = ""
                if fault == "relative": selected = "allocation.json"
                if fault == "missing": selected = str(root / "absent")
                if fault == "symlink":
                    linked = root / "link.json";linked.symlink_to(path);selected = str(linked)
                before = set(root.iterdir())
                result = subprocess.run(["sh", str(ALLOCATION_CHECK), selected],
                                        cwd=root, capture_output=True, text=True)
                valid = fault in (None,"relocated-grant")
                self.assertEqual(result.returncode,0 if valid else 2,result.stderr)
                self.assertEqual(set(root.iterdir()), before)  # data validation creates no source or keys

    def test_fixed_cases_cover_bounded_operations_and_errors(self):
        cases = json.loads((ROOT / "deploy/oracle/acceptance/agent-cases.json").read_text())
        self.assertEqual(len(cases), 9)
        self.assertEqual(len({case["name"] for case in cases}), len(cases))
        calls = [case for case in cases if case["tool"] == "mini_oracle_call"]
        self.assertEqual(len({case["arguments"]["requestId"] for case in calls}), len(calls))
        self.assertEqual({case["status"] for case in cases}, {200, 400, 404})
        for case in cases:
            self.assertNotIn("application", case["arguments"])
            self.assertLess(len(json.dumps(case["arguments"]).encode()), 65536)
        self.assertTrue(any(case["bodyContains"].get("reply", {}).get("status") == "withheld" for case in calls))
        self.assertTrue(any(case["arguments"].get("operationId") == "artist.compose" for case in calls))

    def test_activation_requires_current_native_generation(self):
        spec = importlib.util.spec_from_file_location("oracle_agent", ROOT / "deploy/oracle/acceptance/agent.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        start = {"app": "9101", "generation": "2", "unit": "oracle-g2.service"}
        active = {"generation": "2", "unit": "oracle-g2.service", "state": "running", "unitActiveState": "active"}
        def status(runs):
            return {"protocol": "mini-spk-grain-status-v2", "app": "9101", "runs": runs}
        module.require_current_start(start, status([active]))
        for runs in [[], [active, active], [dict(active, generation="1")],
                     [dict(active, unit="wrong.service")], [dict(active, state="stopped")],
                     [dict(active, unitActiveState="inactive")]]:
            with self.subTest(runs=runs), self.assertRaises(ValueError):
                module.require_current_start(start, status(runs))

    def test_native_route_payer_pins_match_two_source_slots(self):
        spec = importlib.util.spec_from_file_location("oracle_route_pins", ROOT / "deploy/oracle/acceptance/agent.py")
        module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        allocation = json.loads((ROOT / "deploy/oracle/acceptance/agent-allocation.json").read_text())
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); op=object.__new__(module.Operator)
            op.agent=allocation["agents"][0]; op.allocation=allocation
            op.root=op.calls=op.workroom=root
            identity=root/"agents"/op.agent["route"]; identity.mkdir(parents=True)
            for actor in ("controller","dispatch"):
                (identity/(actor+".pub")).write_bytes(bytes([7 if actor=="dispatch" else 8])*32)
            grant=root/"grant"; grant.mkdir(); (grant/"lookup-0000.outcome.json").write_text('{}')
            (root/"issued-grant.json").write_text(json.dumps({"grantAttempt":str(grant)}))
            layout=root/"layout.json"; layout.write_text(json.dumps({
                "controllerHome":"/home/controller","listenerSocket":"/private/api.sock",
                "reverseSocket":"/private/reverse.sock","operatorSocket":"/private/operator.sock", "controllerUid":os.getuid()+10001}))
            op.mini=op.host=op.config=Path(__file__)
            class BeforeNative(Exception): pass
            def call(label,args):
                self.assertEqual(label,"render-custody"); raise BeforeNative()
            op.call=call
            with self.assertRaises(BeforeNative): op.prepare_route(ROOT,layout)
            pins=json.loads((root/"operator-pins.json").read_text())
            self.assertEqual(pins["payerPins"],[{"role":role,"index":"0","keyId":op.agent["dispatch"]["keyId"],
                "keyEpoch":"2","publicKeyHex":(bytes([7])*32).hex()} for role in ("4","1")])
            self.assertEqual([(p["role"],p["index"]) for p in pins["appSigners"]],
                [("4","0"),("4","1"),("8","0"),("8","1"),("1","0"),("9","0"),("9","1"),("9","2"),("9","3")])

    def test_route_renderer_legacy_and_explicit_allocation_guards(self):
        source = (ROOT / "scripts/spk-platform/prepare-lifetime-route.sh").read_text()
        # Execute the renderer's actual jq guard, not a parallel validator.
        expression = re.search(r'''jq -e --argjson expected "\$EXPECTED" --argjson custodyOnly "\$CUSTODY_ONLY" '(.*?)' "\$PINS"''',
                               source, re.S).group(1)
        pins = dict.fromkeys([
            "enrollmentObserveCapability", "manifestObserveCapability", "maximumCharge",
            "parentCapability", "parentObserve", "purseCapability", "purseObserve",
            "reserveAmount", "sessionObserveCapability"], "1")
        pins.update(appSigners=[{}], grantSigner={}, payerPins=[{"role":"4","index":"0"},{"role":"1","index":"0"}],
                    hostUid=1000, hostUnit="oracle.service", socketPath="/private/agent.sock",
                    controllerRouteName="workroom-app", signedApiPath="/repo.git/",
                    packageManifest="8402", snapshotManifest="8403", purseResource="7940", payerSubject="10")
        expected = {"packageManifest": "9102", "snapshotManifest": "9103",
                    "purseResource": "27940", "payerSubject": "20012"}
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "pins.json"
            def check(value, selected, custody_only=False):
                path.write_text(json.dumps(value))
                return subprocess.run(["jq", "-e", "--argjson", "expected", json.dumps(selected),
                                       "--argjson", "custodyOnly", json.dumps(custody_only), expression, str(path)], capture_output=True).returncode == 0
            self.assertTrue(check(pins, None))
            modern = dict(pins, **expected, controllerRouteName="oracle-app", signedApiPath="/")
            self.assertTrue(check(modern, expected))
            for payer in [list(reversed(modern["payerPins"])), modern["payerPins"][:1],
                          [modern["payerPins"][0], {"role":"8","index":"0"}, modern["payerPins"][1]]]:
                self.assertFalse(check(dict(modern, payerPins=payer), expected))
            self.assertTrue(check(dict(modern, hostUnit=None), expected, True))
            self.assertFalse(check(dict(modern, hostUnit=None), expected))
            self.assertFalse(check(modern, None))
            self.assertFalse(check(dict(modern, payerSubject="20010"), expected))
            for bad in ["relative/", "/../", "/?q=x/", "/%2e/"]:
                self.assertFalse(check(dict(modern, signedApiPath=bad), expected))

    def test_allocation_old_and_oracle_validate_without_native_work(self):
        for filename in ["scripts/spk-platform/allocation-v1.json",
                         "deploy/oracle/acceptance/agent-allocation.json"]:
            with self.subTest(filename=filename), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                result = subprocess.run(["sh", str(ALLOCATION_CHECK), str(ROOT / filename)],
                                        cwd=root, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(list(root.iterdir()), [])

    def test_fixed_agent_birth_phase_preserves_existing_resources(self):
        allocation_path = ROOT / "deploy/oracle/acceptance/agent-allocation.json"
        allocation = json.loads(allocation_path.read_text())
        with tempfile.TemporaryDirectory() as tmp:
            evidence = Path(tmp)
            (evidence / "agents").mkdir()
            existing = {"kind": "object", "storage": "content", "target": "8001", "owner": "7"}
            original = {"subject": "7", "birth": {"resources": [existing], "feePayer": "7"}, "grants": []}
            birth = evidence / "birth-intent.json"
            birth.write_text(json.dumps(original))
            result = subprocess.run(["sh", "-eu", "-c",
                '. "$1"; EVIDENCE=$2; WORKROOM_AGENT_ALLOCATION=$3; workroom_agent_extend_birth',
                "birth-phase", str(AGENT_LIBRARY), str(evidence), str(allocation_path)],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            result = json.loads(birth.read_text())
            resources = result["birth"].pop("resources")
            original["birth"].pop("resources")
            self.assertEqual(result, original)  # authority and fee selectors are preserved
            self.assertEqual(resources[0], existing)
            born = {resource["target"]: resource for resource in resources[1:]}
            roles = [(agent, role) for agent in allocation["agents"]
                     for role in ("controller", "tool", "dispatch", "provider")]
            self.assertEqual(set(born), {agent[role]["task"] for agent, role in roles})
            self.assertEqual(len(resources) - 1, len(born))  # no duplicate births
            for agent, role in roles:
                resource = born[agent[role]["task"]]
                self.assertEqual((resource["kind"], resource["storage"]), ("object", "grain"))
                self.assertEqual(resource["owner"], agent[role]["subject"])
                caps = agent["plannedCaps"]
                owner_cap = "parentOwner" if role == "controller" else role + "Owner"
                control_cap = "parentControl" if role == "controller" else role + "TaskControl"
                self.assertEqual(resource["ownerCapability"], caps[owner_cap])
                self.assertEqual(resource["controlCapability"], caps[control_cap])
                self.assertEqual(resource["budget"], "100" if role == "controller" else "50")
                if role == "controller":
                    self.assertEqual(resource["workerSubjects"],
                                     [agent[worker]["subject"] for worker in ("tool", "dispatch", "provider")])
                    self.assertEqual(resource["workerGeneration"], "1")
                else:
                    self.assertNotIn("workerSubjects", resource)
            self.assertFalse((evidence / "genesis.json").exists())

    def run_probe(self, mode):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            # Fake executable emits the already-verified result shapes only.
            # This exercises the probe's evidence joins, not Mini signatures.
            runtime = root / "runtime"
            runtime.write_text('''#!/usr/bin/env python3
import json, os, pathlib, sys
r=pathlib.Path(__file__).parent
mode=os.environ['PROBE_TEST_MODE']
request='a'*32
receipt={'transactionId':'1','eventId':'2','acceptedCount':'3','worldRoot':'4'}
http={'protocol':'mini-spk-agent-api-v3','type':'http-v3','operationId':'10',
 'status':200,'bodyText':json.dumps({'protocol':'oracle-operations-v1'}),
 'bindingSha256':'b'*64,'operationFingerprint':'123',
 'committedReceipt':receipt,'responseSha256':'c'*64}
if mode=='receiving': http['type']='http'
if mode=='wrong-body': http['bodyText']='{}'
attempt={'operationId':10,'routeName':'oracle-app','phase':'definite','reported':True,
 'bindingSha256':http['bindingSha256'],'operationFingerprint':http['operationFingerprint'],
 'lifetimeCommittedReceipt':receipt,'lifetimeSettledResponseSha256':http['responseSha256'],
 'lifetimeSettlement':{'forwardOperationId':10,'settlement':{'operation':'dispatch settle'}}}
if mode=='unsettled': attempt.pop('lifetimeSettlement')
result={'type':'tool-complete','requestId':request,'isError':False,
 'result':{'isError':False,'text':json.dumps(http)}}
if sys.argv[1]=='tool-id': print(request)
elif sys.argv[1]=='tool':
 args=json.loads(pathlib.Path(sys.argv[6]).read_text())
 assert args['application']=='oracle-app'
 (r/'journal.json').write_text(json.dumps({'applicationApiHistory':[attempt]}))
 print(json.dumps(result))
elif sys.argv[1]=='tool-result': print(json.dumps(result))
elif sys.argv[1]=='tool-ack': print('{}')
else: sys.exit(2)
''')
            runtime.chmod(0o700)
            host = root / "host"
            host.write_bytes(b"host-pin-only")
            digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
            config = root / "controller.json"
            config.write_text(json.dumps({
                "host": str(host), "controlSocket": str(root / "control.sock"), "stateDir": str(root),
                "task": "1", "subject": "1", "foregroundTool": {"reserve": "1", "charge": "0"},
                "toolTask": {"task": "2", "subject": "2", "lifetimeApiHostSha256": digest(host),
                    "applicationServices": [{"application": "oracle-app", "protocol": "oracle-operations-v1"}],
                    "allowedApplicationLifetimeRoutes": [{"name": "oracle-app"}]},
                "dispatchTask": {"task": "3", "subject": "3", "operatorSocket": "/unused", "reserveSigner": {}}
            }))
            cases = root / "cases.json"
            cases.write_text(json.dumps([{"name": "discovery", "tool": "mini_oracle_discover", "arguments": {},
                                          "status": 200, "bodyContains": {"protocol": "oracle-operations-v1"}}]))
            env = dict(os.environ, QUALIFIED_RUNTIME_SHA256=digest(runtime),
                       QUALIFIED_LIFETIME_HOST_SHA256=digest(host), PROBE_TEST_MODE=mode)
            with socket.socket(socket.AF_UNIX) as server:
                server.bind(str(root / "control.sock"))
                result = subprocess.run(["sh", str(HELPER), str(runtime), str(config), "oracle-app",
                                         str(cases), str(root / "evidence")], env=env, capture_output=True, text=True)
            if mode == "pass":
                self.assertEqual(result.returncode, 0, result.stderr)
            else:
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse((root / "evidence/result.json").exists())

    def test_probe_requires_lifetime_and_settlement_and_body(self):
        for mode in ["pass", "receiving", "unsettled", "wrong-body"]:
            with self.subTest(mode=mode):
                self.run_probe(mode)


if __name__ == "__main__":
    unittest.main()
