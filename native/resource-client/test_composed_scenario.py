#!/usr/bin/env python3
"""Composed scenario runner: spec checking and the resumable step ledger.

No SSH is ever started: `Scenario.ssh` is replaced by a scripted member shell
that keeps per-member attempts and proposals the way the client retains them.
"""
import importlib.util
import json
import os
from pathlib import Path
import re
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("composed", HERE / "composed-scenario.py")
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


def world(root, names):
    members = {}
    for index, name in enumerate(names):
        ws = root / name / "workspace"
        (ws / "attempts").mkdir(parents=True)
        (ws / "proposals").mkdir()
        members[name] = {"subject": str(1000 + index), "workspace": str(ws), "home": str(root / name),
                         "sshKeyFile": str(root / name / "key"), "entry": "sponsored" if name == "helper" else "paid"}
    value = {"type": "mini-world-identity-v1", "unitUser": "hbox", "members": members,
             "ssh": {"host": "127.0.0.1", "port": 22027, "knownHosts": str(root / "known_hosts")}}
    path = root / "WORLD.json"
    path.write_text(json.dumps(value))
    return path, value


class Shell:
    """A member shell that admits or refuses like the client: proposals are
    local, `submit OP`/`room new`/`doc range|transclude` create an attempt."""

    def __init__(self, members):
        self.members, self.calls, self.fail = members, [], {}
        self.notes, self.refs, self.receipts = [], {}, {}

    def ws(self, who):
        return Path(self.members[who]["workspace"])

    def attempt(self, who, name, outcome):
        (self.ws(who) / "attempts" / name).mkdir(exist_ok=True)
        self.receipts[(who, name)] = outcome

    def __call__(self, who, label, line, into):
        self.calls.append((who, line))
        rc, out, err = self.answer(who, line)
        stem = Path(into) / f"{len(self.calls):04d}"
        stem.with_suffix(".out").write_text(out)
        return rc, out, err, stem, {"rc": rc, "seconds": 0.01, "loadBefore": ["1"], "loadAfter": ["1"]}

    def answer(self, who, line):
        for pattern, reply in list(self.fail.items()):
            if re.fullmatch(pattern, line):
                del self.fail[pattern]
                if reply == "undecided-after-attempt":
                    name = line.split()[1] if line.startswith("submit ") else "birth-x"
                    self.attempt(who, name, "undecided")
                    return 4, "", "undecided: Host"
                if reply == "undecided-before-attempt":
                    return 4, "", "ssh: connection reset"
        words = line.split()
        confirmed = json.dumps({"type": "confirmed", "confirmation": "installed", "transactionId": "7",
                                "acceptedCount": "9", "worldRoot": "1"})
        if words[0] == "submit":
            if words[1].endswith("-kick"):
                self.kicked = getattr(self, "kicked", set()) | {words[1]}
            if words[1].endswith("-blocked") or words[1].endswith("-repair"):
                self.attempt(who, words[1], "refused")
                return 3, "", "refused: law-denied"
            self.attempt(who, words[1], "confirmed")
            return 0, confirmed, ""
        if words[0] == "lookup":
            state = self.receipts.get((who, words[1]))
            return (0, confirmed, "") if state == "confirmed" else (4, "", "undecided")
        if words[:2] in (["room", "invite"], ["room", "kick"], ["doc", "append"]) or words[0] == "law":
            op = words[2] if words[0] != "law" else words[1]
            if words[0] == "law" and "unauth" in op:
                return 1, "", "error: workspace record lacks controlCapability"
            (self.ws(who) / "proposals" / op).mkdir(exist_ok=True)
            (self.ws(who) / "proposals" / op / "proposal.json").write_text("{}")
            if words[:2] == ["doc", "append"]:
                self.notes.append(json.loads(line.split(" ", 4)[4]))
            return 0, "{}", ""
        if words[:2] == ["room", "new"]:
            self.attempt(who, "birth-" + words[2], "confirmed")
            self.refs.setdefault(who, set()).add(words[2])
            return 0, "", ""
        if words[0] == "refs":
            return 0, json.dumps({"references": [{"name": n, "target": "55"} for n in sorted(self.refs.get(who, ()))]}), ""
        if words[0] == "publish":
            self.attempt(who, "publish-" + words[1], "confirmed")
            return 0, "", ""
        if words[0] == "export":
            subject = next(m["subject"] for m in self.members.values()
                           if words[1].endswith("-" + [k for k, v in self.members.items() if v is m][0]))
            return 0, json.dumps({"recipient": subject}), ""
        if words[0] == "import":
            self.refs.setdefault(who, set()).add(words[1])
            return 0, "", ""
        if words[:2] == ["room", "resolve"]:
            return 0, json.dumps({"target": "77"}), ""
        if words[:2] == ["doc", "show"]:
            if getattr(self, "kicked", None) and who == "cy" and not words[2].split("/")[0].endswith("-again"):
                return 3, "", "refused: no-grant"
            if words[2].endswith("/tasks"):
                return 0, "  1  " + self.notes[0] + "\n", ""
            return 0, "".join(f"  {i + 1}  {t}\n" for i, t in enumerate(self.notes)), ""
        if words[:2] in (["doc", "range"], ["doc", "transclude"]):
            self.attempt(who, words[1] + "-" + str(len(self.calls)), "confirmed")
            return 0, "", ""
        if words[:2] == ["doc", "new"]:
            self.attempt(who, "birth-" + words[2], "confirmed")
            return 0, "", ""
        raise AssertionError("unscripted line " + line)


class ComposedTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.names = ["ada", "bo", "cy", "helper"]
        self.world, self.value = world(self.root, self.names)
        self.state = self.root / "state"

    def spec(self, **extra):
        value = {"type": "mini-composed-scenario-v1", "world": str(self.world), "state": str(self.state),
                 "operationPrefix": "t1", "population": {"entry": "paid"},
                 "rooms": {"overlap": {"name": "lab-r1", "owner": "bo", "members": ["ada", "bo", "cy"]}},
                 "phases": ["rooms"]}
        value.update(extra)
        return value

    def scenario(self, value, shell):
        s = c.Scenario(value, "spec.json")
        s.ssh = shell
        return s

    def test_check_resolves_inventory_names_and_reports_unbuilt_and_blocked_phases(self):
        value = self.spec(phases=list(c.PHASES))
        p = c.plan(value)
        self.assertEqual(p["population"], ["ada", "bo", "cy"])
        ready = c.readiness(value, p)
        self.assertTrue(ready["apps"].startswith("blocked: no apps input"))
        self.assertTrue(ready["residents"].startswith("blocked"))
        self.assertTrue(ready["restart"].startswith("blocked"))
        self.assertIn("protected: blocked", ready["documents"])
        for broken, message in [
            ({"rooms": {"x": {"name": "lab", "owner": "zed", "members": ["ada", "zed"]}}}, "not in the world inventory"),
            ({"rooms": {"x": {"name": "lab", "owner": "cy", "members": ["ada", "bo"]}}}, "owner must be one of"),
            ({"rooms": {"x": {"name": "lab", "owner": "ada", "members": ["ada", "helper"]}}}, "outside the population"),
            ({"rooms": {"x": {"name": "lab", "owner": "ada", "members": ["ada"]}}}, "another member"),
            ({"operationPrefix": "Bad Prefix"}, "operationPrefix"),
            ({"phases": ["rooms", "rooms"]}, "repeated phase"),
        ]:
            with self.assertRaisesRegex(ValueError, message):
                c.plan(self.spec(**broken))
        self.assertFalse(self.state.exists(), "check must not create scenario state")

    def test_derived_connector_requires_named_world_app_binding(self):
        bad = self.spec(phases=["connector"], connector={"app": "sheet"})
        with self.assertRaisesRegex(ValueError, "requires an app"):
            c.plan(bad)
        good = self.spec(phases=["apps", "connector"],
            apps={"sheet": {"worldInputs": {"platformInputs": "/world/platform-inputs.json", "selection": "/world/selection.json"}}},
            connector={"app": "sheet"})
        self.assertEqual(c.readiness(good, c.plan(good))["connector"], "ready")

    def test_derived_world_inputs_feed_actual_adapters_in_order_and_are_retained(self):
        fixture_spec = importlib.util.spec_from_file_location("input_fixture_tests",
            HERE.parent.parent / "scripts/spk-platform/tests/test_same_store_inputs.py")
        fixture = importlib.util.module_from_spec(fixture_spec); fixture_spec.loader.exec_module(fixture)
        root = self.root / "supplied"; root.mkdir()
        w = fixture.World(root)
        w.selection["app"]["owner"] = "person-1"
        for index, row in enumerate(w.selection["app"]["members"].values()):
            row["subject"] = "person-" + str(index)
        w.selection["connector"] = {"subject": "person-3", "name": "csv", "expectedHost": "csv.spk.localhost:18443",
            "sheet": "lab-sheet", "role": "1", "task": "task", "document": "document", "resources": "650001", "capabilities": "980001",
            "reader": {"subject": "person-0", "document": "shared-notes"}, "endpoint": "https://csv.spk.localhost:18443/", "ca": None, "operation": "export-1"}
        (root / "platform-inputs.json").write_text(json.dumps(w.ctx))
        (root / "selection.json").write_text(json.dumps(w.selection))
        inventory = {"type": "mini-world-identity-v1", "unitUser": "hbox",
            "ssh": self.value["ssh"], "members": {
                "person-" + str(i): dict(row, sshKeyFile="/keys/" + str(i), entry="paid")
                for i, row in enumerate(w.ctx["memberInventory"].values())}}
        self.world.write_text(json.dumps(inventory))
        value = self.spec(phases=["apps", "connector"], population=list(inventory["members"]), rooms={},
            apps={"sheet": {"worldInputs": {"platformInputs": str(root / "platform-inputs.json"), "selection": str(root / "selection.json")}}},
            connector={"app": "sheet"})
        calls = []
        def run(argv, **kwargs):
            if len(argv) > 1 and argv[1] == "key-status":
                return w.key_status(argv)
            calls.append(Path(argv[1]).name)
            binding = c.read(argv[2])
            if calls[-1] == "same-store-app.py":
                target = Path(binding["root"]); target.mkdir()
                fixture_path = target / "fixture.json"
                fixture_path.write_text(json.dumps({"keys": binding["keys"], "application": binding["application"], "delegates": binding["delegates"]}))
                (target / "attachment-result.json").write_text(json.dumps({"protocol": "mini-spk-same-store-attached-v1",
                    "miniConfigSha256": w.ctx["identity"]["configSha256"], "fixture": str(fixture_path), "appId": binding["application"]["app"]}))
                output = b"{}"
            elif calls[-1] == "app-document-provision.py":
                target = Path(binding["root"]); target.mkdir()
                connector_fixture = target / "fixture.json"; connector_fixture.write_text("{}")
                (target / "result.json").write_text(json.dumps({"protocol": "mini-app-document-provisioned-v1",
                    "subject": binding["delegate"]["subject"], "fixture": str(connector_fixture)}))
                output = b"{}"
            else:
                self.assertEqual(calls[-1], "app-document-journey.py")
                output = json.dumps({"protocol": "mini-app-document-journey-result-v1", "status": "saved", "operation": binding["operation"],
                    "callSha256": "a" * 64, "receipt": {"bodySha256": "b" * 64, "bodyBytes": "11"}}).encode()
            return mock.Mock(returncode=0, stdout=output, stderr=b"")
        with mock.patch.object(c, "input_builder", return_value=fixture.inputs), \
                mock.patch.object(fixture.inputs.f, "protected_parent"), mock.patch.object(c.subprocess, "run", side_effect=run):
            first = c.Scenario(value, "spec.json").run()
            self.assertEqual(first["phases"], {"apps": "pass", "connector": "pass"})
            second = c.Scenario(value, "spec.json").run()
            self.assertEqual(second["phases"], first["phases"])
        self.assertEqual(calls, ["same-store-app.py", "app-document-provision.py", "app-document-journey.py"])
        state = c.read(self.state / "state.json")
        self.assertEqual(set(state["derivedInputPins"]), {"sheet:attach", "sheet:connector", "sheet:journey"})
        (root / "selection.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "source input bytes changed"):
            scenario = c.Scenario(value, "spec.json")
            scenario.close()

    def test_typed_resident_and_restart_retain_same_binding_and_fixed_source_adapter(self):
        binding = self.root / "resident-binding.json"; binding.write_text("{}")
        connector = self.root / "connector-result.json"; connector.write_text("{}")
        value = self.spec(phases=["residents", "restart"], residents={"binding": str(binding)}, restart={"binding": str(binding)})
        calls = []
        def run(argv, **kwargs):
            calls.append(argv)
            through = argv[argv.index("--through") + 1]
            return mock.Mock(returncode=0, stderr=b"", stdout=json.dumps({"protocol": "mini-same-world-resident-result-v1",
                "passed": True, "through": through, "bindingSha256": c.sha(binding)}).encode())
        scenario = c.Scenario(value, "spec.json")
        scenario.state["connectorResultPin"] = {"path": str(connector), "sha256": c.sha(connector)}
        scenario.persist()
        with mock.patch.object(c.subprocess, "run", side_effect=run):
            result = scenario.run()
        self.assertEqual(result["phases"], {"residents": "pass", "restart": "pass"})
        self.assertEqual([argv[argv.index("--through") + 1] for argv in calls], ["verify", "retain"])
        self.assertTrue(all(Path(argv[1]).name == "same-world-resident.py" for argv in calls))
        self.assertTrue(all(argv[argv.index("--connector-result") + 1] == str(connector) for argv in calls))
        with self.assertRaisesRegex(ValueError, "same resident binding"):
            c.plan(self.spec(phases=["residents", "restart"], residents={"binding": str(binding)}, restart={"binding": "/another.json"}))

    def test_typed_resident_cannot_run_without_actual_connector_result(self):
        binding = self.root / "resident-binding.json"; binding.write_text("{}")
        value = self.spec(phases=["residents"], residents={"binding": str(binding)})
        with mock.patch.object(c.subprocess, "run") as native:
            result = c.Scenario(value, "spec.json").run()
        self.assertIn("requires retained actual connector", result["phases"]["residents"])
        native.assert_not_called()

    def test_rooms_phase_composes_create_invite_import_and_one_document(self):
        shell = Shell(self.value["members"])
        result = self.scenario(self.spec(), shell).run()
        self.assertEqual(result["phases"], {"rooms": "pass"})
        lines = [line for _, line in shell.calls]
        self.assertEqual(sum(l.startswith("room new") for l in lines), 1)
        self.assertEqual(sum(l.startswith("room invite") for l in lines), 2)
        self.assertEqual(sum(l.startswith("import lab-r1") for l in lines), 2)

    def test_rerun_after_completion_repeats_nothing(self):
        shell = Shell(self.value["members"])
        self.scenario(self.spec(), shell).run()
        count = len(shell.calls)
        self.assertEqual(self.scenario(self.spec(), shell).run()["phases"], {"rooms": "pass"})
        self.assertEqual(len(shell.calls), count)

    def test_undecided_submit_is_decided_by_exact_lookup_never_resubmitted(self):
        shell = Shell(self.value["members"])
        shell.fail[r"submit t1-overlap-invite-ada"] = "undecided-after-attempt"
        first = self.scenario(self.spec(), shell).run()
        self.assertTrue(first["phases"]["rooms"].startswith("stopped"))
        self.assertEqual(first["pending"]["name"], "room:overlap:invite:ada:submit")
        shell.receipts[("bo", "t1-overlap-invite-ada")] = "confirmed"
        second = self.scenario(self.spec(), shell).run()
        self.assertEqual(second["phases"], {"rooms": "pass"})
        submits = [l for _, l in shell.calls if l == "submit t1-overlap-invite-ada"]
        self.assertEqual(len(submits), 1)
        self.assertIn(("bo", "lookup t1-overlap-invite-ada"), shell.calls)

    def test_interruption_before_any_attempt_reauthors_once(self):
        shell = Shell(self.value["members"])
        shell.fail[r"submit t1-overlap-invite-ada"] = "undecided-before-attempt"
        self.scenario(self.spec(), shell).run()
        self.assertEqual(self.scenario(self.spec(), shell).run()["phases"], {"rooms": "pass"})
        submits = [l for _, l in shell.calls if l == "submit t1-overlap-invite-ada"]
        self.assertEqual(len(submits), 2)
        self.assertNotIn(("bo", "lookup t1-overlap-invite-ada"), shell.calls)

    def test_still_undecided_lookup_stays_fenced_until_settled_from_evidence(self):
        shell = Shell(self.value["members"])
        shell.fail[r"submit t1-overlap-invite-ada"] = "undecided-after-attempt"
        self.scenario(self.spec(), shell).run()
        again = self.scenario(self.spec(), shell).run()
        self.assertTrue(again["phases"]["rooms"].startswith("stopped"))
        self.assertIn("undecided", again["phases"]["rooms"])
        s = self.scenario(self.spec(), shell)
        pending = s.ledger.pending()
        evidence = next(Path(pending["evidence"][0]).glob("*.out"))
        with self.assertRaisesRegex(RuntimeError, "outside|another step|evidence"):
            s.ledger.settle(pending["name"], "absent", self.root / "WORLD.json", "x", s.root, lambda r: None)
        s.ledger.settle(pending["name"], "absent", evidence, "Host refused: rc4 was transport, attempt never admitted",
                        s.root, lambda r: s.root / "settlement.json")
        s.close()
        self.assertEqual(self.scenario(self.spec(), shell).run()["phases"], {"rooms": "pass"})

    def test_existing_room_is_adopted_by_signed_reads_not_created_again(self):
        shell = Shell(self.value["members"])
        shell.refs["ada"] = {"lab-r0"}
        value = self.spec(rooms={"shared": {"name": "lab-r0", "owner": "ada", "members": "population", "existing": True}})
        self.assertEqual(self.scenario(value, shell).run()["phases"], {"rooms": "pass"})
        self.assertFalse(any(l.startswith(("room new", "room invite")) for _, l in shell.calls))
        self.assertEqual(sum(l.startswith("room resolve") for _, l in shell.calls), 3)

    def test_documents_publish_a_range_before_transcluding_and_check_the_hosted_text(self):
        shell = Shell(self.value["members"])
        value = self.spec(phases=["rooms", "documents"], concurrency=3, documents={"rooms": ["overlap"]})
        result = self.scenario(value, shell).run()
        self.assertTrue(result["phases"]["documents"].startswith("pass; blocked rows: documents:protected"))
        lines = [l for _, l in shell.calls]
        self.assertLess(lines.index("doc range lab-r1/notes 1 1"),
                        lines.index("doc transclude lab-r1/tasks lab-r1/notes 1 1 snapshot"))
        self.assertEqual(len(shell.notes), 3)

    def test_churn_kicks_refuses_rejoins_under_a_new_reference_and_locks_out(self):
        shell = Shell(self.value["members"])
        value = self.spec(phases=["rooms", "churn", "documents"], documents={"rooms": ["overlap"]},
                          churn={"rooms": {"overlap": {"member": "cy"}}, "lockout": {"room": "overlap"}})
        result = self.scenario(value, shell).run()
        self.assertEqual(result["phases"]["churn"], "pass")
        self.assertEqual(result["failed"], [])
        lines = [l for w, l in shell.calls]
        self.assertIn("import lab-r1-again", " ".join(lines))
        self.assertIn(("cy", "doc show lab-r1-again/notes"), shell.calls)
        # After churn, the rejoined member writes through its new reference.
        self.assertTrue(any(w == "cy" and l.startswith("doc append t1-overlap-w-cy lab-r1-again/notes")
                            for w, l in shell.calls))
        self.assertIn(("bo", "submit t1-law-blocked"), shell.calls)

    def test_later_phases_block_on_missing_input_or_prerequisite(self):
        shell = Shell(self.value["members"])
        value = self.spec(phases=["rooms", "apps", "connector", "residents", "restart"])
        result = self.scenario(value, shell).run()
        self.assertEqual(result["phases"]["rooms"], "pass")
        self.assertTrue(result["phases"]["apps"].startswith("blocked: no apps input"))
        self.assertTrue(result["phases"]["connector"].startswith("blocked: prerequisite apps"))
        self.assertTrue(result["phases"]["residents"].startswith("blocked"))

    def test_inventory_pin_ignores_recorded_rooms_but_not_members(self):
        value = self.spec(inventorySha256=c.inventory_sha(self.value))
        c.plan(value)
        self.value["rooms"] = {"created": {"x": {"name": "lab-r1"}}}
        self.world.write_text(json.dumps(self.value))
        c.plan(value)
        self.value["members"]["ada"]["subject"] = "999"
        self.world.write_text(json.dumps(self.value))
        with self.assertRaisesRegex(ValueError, "member inventory changed"):
            c.plan(value)

    def test_a_stopped_phase_reports_later_phases_as_not_reached(self):
        shell = Shell(self.value["members"])
        shell.fail[r"submit t1-overlap-invite-ada"] = "undecided-after-attempt"
        result = self.scenario(self.spec(phases=["rooms", "apps", "residents"]), shell).run()
        self.assertTrue(result["phases"]["rooms"].startswith("stopped"))
        self.assertTrue(result["phases"]["apps"].startswith("not reached: stopped at rooms; would be blocked"))
        self.assertTrue(result["phases"]["residents"].startswith("not reached: stopped at rooms; would be blocked"))

    def connector_spec(self):
        journey = self.root / "journey-input.json"
        journey.write_text(json.dumps({"operation": "export-1"}))
        return self.spec(phases=["connector"], connector={
            "input": str(self.root / "provision-input.json"), "journeyInput": str(journey)})

    def saved_export(self, **changes):
        value = {"protocol": "mini-app-document-journey-result-v1", "status": "saved",
                 "operation": "export-1", "callSha256": "a" * 64,
                 "receipt": {"bodyBytes": "3", "bodySha256": "b" * 64}}
        value.update(changes)
        return value

    def adapter_response(self, value):
        return c.subprocess.CompletedProcess([], 0, json.dumps(value).encode(), b"")

    def test_connector_requires_capture_journey_binding_before_provisioning(self):
        value = self.spec(phases=["connector"], connector={"input": "/provision.json"})
        self.assertIn("blocked: no connector journeyInput", c.readiness(value, c.plan(value))["connector"])
        with mock.patch.object(c.subprocess, "run") as run:
            result = c.Scenario(value, "spec.json").run()
        self.assertTrue(result["phases"]["connector"].startswith("blocked"))
        run.assert_not_called()

    def test_connector_runs_capture_readback_after_provision_and_repeats_nothing(self):
        value = self.connector_spec()
        with mock.patch.object(c.subprocess, "run", side_effect=[
                self.adapter_response({"protocol": "mini-app-document-provisioned-v1"}),
                self.adapter_response(self.saved_export())]) as run:
            result = c.Scenario(value, "spec.json").run()
            self.assertEqual(result["phases"]["connector"], "pass")
            self.assertEqual(Path(run.call_args_list[0].args[0][1]).name, "app-document-provision.py")
            self.assertEqual(Path(run.call_args_list[1].args[0][1]).name, "app-document-journey.py")
            c.Scenario(value, "spec.json").run()
            self.assertEqual(run.call_count, 2)

    def test_zero_exit_source_uncertain_is_not_success_and_resume_skips_provision(self):
        value = self.connector_spec()
        with mock.patch.object(c.subprocess, "run", side_effect=[
                self.adapter_response({}),
                self.adapter_response(self.saved_export(status="source-uncertain")),
                self.adapter_response(self.saved_export())]) as run:
            first = c.Scenario(value, "spec.json").run()
            self.assertTrue(first["phases"]["connector"].startswith("stopped:"))
            self.assertEqual(first["pending"]["name"], "connector:journey")
            second = c.Scenario(value, "spec.json").run()
            self.assertEqual(second["phases"]["connector"], "pass")
            names = [Path(call.args[0][1]).name for call in run.call_args_list]
            self.assertEqual(names.count("app-document-provision.py"), 1)
            self.assertEqual(names.count("app-document-journey.py"), 2)

    def test_pending_connector_cannot_switch_to_new_capture_at_same_input_path(self):
        value = self.connector_spec()
        with mock.patch.object(c.subprocess, "run", side_effect=[
                self.adapter_response({}), self.adapter_response(self.saved_export(status="uncertain"))]) as run:
            first = c.Scenario(value, "spec.json").run()
        self.assertEqual(first["pending"]["name"], "connector:journey")
        Path(value["connector"]["journeyInput"]).write_text(json.dumps({"operation": "export-2"}))
        with mock.patch.object(c.subprocess, "run") as run:
            second = c.Scenario(value, "spec.json").run()
        run.assert_not_called()
        self.assertIn("journey input changed", second["phases"]["connector"])
        self.assertEqual(second["pending"]["name"], "connector:journey")

    def test_old_provision_only_pass_must_receive_the_export_before_passing(self):
        value = self.connector_spec()
        scenario = c.Scenario(value, "spec.json")
        scenario.ledger.step("connector", lambda: None, scenario.attempt("old-provision"), reentrant=True)
        scenario.state["phases"]["connector"] = "pass"
        scenario.persist()
        scenario.close()
        with mock.patch.object(c.subprocess, "run", return_value=self.adapter_response(self.saved_export())) as run:
            result = c.Scenario(value, "spec.json").run()
        self.assertEqual(result["phases"]["connector"], "pass")
        self.assertEqual(run.call_count, 1)
        self.assertEqual(Path(run.call_args.args[0][1]).name, "app-document-journey.py")

    def test_saved_export_for_another_operation_or_without_verified_bytes_stays_pending(self):
        value = self.connector_spec()
        for response in (self.saved_export(operation="foreign"), self.saved_export(receipt={}),
                         self.saved_export(callSha256="")):
            with mock.patch.object(c.subprocess, "run", return_value=self.adapter_response(response)):
                result = c.Scenario(value, "spec.json").run()
            self.assertTrue(result["phases"]["connector"].startswith("stopped:"))
            self.assertEqual(result["pending"]["name"], "connector:journey")

    def test_changed_spec_needs_a_fresh_state_directory(self):
        shell = Shell(self.value["members"])
        self.scenario(self.spec(), shell).run()
        with self.assertRaisesRegex(ValueError, "spec differs"):
            self.scenario(self.spec(operationPrefix="t2"), shell)


if __name__ == "__main__":
    unittest.main()
