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
        self.assertTrue(ready["residents"].startswith("unbuilt"))
        self.assertTrue(ready["restart"].startswith("unbuilt"))
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
        self.assertTrue(result["phases"]["residents"].startswith("unbuilt"))

    def test_changed_spec_needs_a_fresh_state_directory(self):
        shell = Shell(self.value["members"])
        self.scenario(self.spec(), shell).run()
        with self.assertRaisesRegex(ValueError, "spec differs"):
            self.scenario(self.spec(operationPrefix="t2"), shell)


if __name__ == "__main__":
    unittest.main()
