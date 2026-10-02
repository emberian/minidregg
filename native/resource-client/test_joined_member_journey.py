"""Contract regressions: no service, SSH, provider, or native process is launched."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

module = importlib.util.spec_from_file_location("joined", Path(__file__).with_name("joined-member-journey.py"))
joined = importlib.util.module_from_spec(module)
module.loader.exec_module(joined)


class ReceivingContract(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.journey = object.__new__(joined.Journey)
        self.journey.spec = {}
        self.journey.identity = {"id": "one-store"}
        self.journey.output = self.root
        self.journey.rows = []
        self.journey.serial = 0
        self.journey.context = {"roomTarget": "42"}

    def tearDown(self):
        self.tmp.cleanup()

    def call(self, rc, err, expected=3):
        with patch.object(joined, "validate", return_value=self.journey.identity), \
                patch.object(joined.subprocess, "run", return_value=subprocess.CompletedProcess([], rc, b"", err)):
            return self.journey.execute("refusal", ["never-executed"], expected, "law-denied")

    def test_success_cannot_satisfy_expected_refusal(self):
        with self.assertRaises(ValueError):
            self.call(0, b"law-denied")
        self.assertEqual((self.root / "001-refusal.rc").read_text(), "0\n")
        self.assertEqual(self.journey.rows[-1]["status"], "fail")

    def test_other_failure_cannot_satisfy_native_refusal(self):
        with self.assertRaises(ValueError):
            self.call(255, b"SSH failed: law-denied")
        with self.assertRaises(ValueError):
            self.call(3, b"no-grant")
        self.call(3, b"refused: law-denied: inherited restriction")

    def test_changed_deployment_stops_before_process(self):
        with patch.object(joined, "validate", return_value={"id": "another-store"}), \
                patch.object(joined.subprocess, "run") as run:
            with self.assertRaises(ValueError):
                self.journey.execute("mutation", ["never-executed"])
            run.assert_not_called()

    def test_hook_cannot_return_a_separate_world_pass(self):
        self.journey.spec["hooks"] = {"hermes": {"executable": "/not-run"}}
        joined.save(self.root / "hermes-run-result.json", {
            "type": "mini-joined-member-hook-result-v1", "identity": {"id": "another-store"},
            "role": "hermes", "phase": "run", "status": "pass"})
        with patch.object(self.journey, "execute", return_value=""):
            with self.assertRaisesRegex(ValueError, "other deployment"):
                self.journey.hook("hermes")

    def test_missing_adapter_is_not_a_pass(self):
        self.assertIsNone(self.journey.hook("spk"))
        result = json.loads((self.root / "result.json").read_text())
        self.assertFalse(result["automatedComplete"])
        self.assertFalse(result["barComplete"])
        self.assertEqual(result["requiredOutstanding"], ["spk-run"])

    def test_prepared_proposal_needs_real_submission_refusal(self):
        def shell(who, label, line, expected, reason):
            self.journey.last_rc = 0 if label.endswith("prepare") else 3
        with patch.object(self.journey, "shell", side_effect=shell) as call:
            self.journey.proposal_refused("alice", "law", "law x", "x", "law-denied")
        self.assertEqual(call.call_count, 2)
        self.assertEqual(call.call_args.args[2], "submit x")


if __name__ == "__main__":
    unittest.main()

class MultiuserWorkload(unittest.TestCase):
    def spec(self, size=5):
        keys = [str(1000 + i) for i in range(size)]
        return {"prefix": "receiving", "members": {key: {"subject": key} for key in keys},
                "maxConcurrency": 16}

    def test_arbitrary_subject_inventory_has_no_named_pair(self):
        plan = joined.workload(self.spec())
        self.assertEqual(plan["members"], ["1000", "1001", "1002", "1003", "1004"])
        self.assertEqual(plan["rooms"]["shared"]["owner"], "1000")

    def test_selected_sweeps_are_pairs_and_cover_overlapping_disjoint_groups(self):
        spec = self.spec(100)
        small = joined.selected_spec(spec, {"population": 5, "concurrency": 4}, 2)
        plan = joined.workload(small)
        self.assertEqual((len(plan["members"]), plan["concurrency"]), (5, 4))
        self.assertEqual(set(plan["rooms"]), {"shared", "overlap", "disjoint"})
        self.assertEqual(set(plan["rooms"]["overlap"]["members"]) & set(plan["rooms"]["disjoint"]["members"]), set())
        with self.assertRaisesRegex(ValueError, "resource limit"):
            joined.selected_spec(spec, {"population": 20, "concurrency": 17}, 0)
        with self.assertRaisesRegex(ValueError, "provisioned members"):
            joined.selected_spec(spec, {"population": 101, "concurrency": 1}, 0)

    def test_exact_room_schema_boundary_is_not_global_population_capacity(self):
        spec = self.spec(500)
        self.assertEqual(len(joined.workload(spec)["rooms"]["shared"]["members"]), 500)
        with self.assertRaisesRegex(ValueError, "499 non-founder"):
            joined.workload(self.spec(501))
        spec = self.spec(1000)
        keys = list(spec["members"])
        spec["rooms"] = {"first": {"owner": keys[0], "members": keys[:500]},
                         "second": {"owner": keys[500], "members": keys[500:]}}
        self.assertEqual(len(joined.workload(spec)["members"]), 1000)

    def test_duplicate_display_aliases_have_distinct_owner_and_room_scope(self):
        spec = self.spec()
        keys = list(spec["members"])
        spec["rooms"] = {"first": {"name": "lab", "owner": keys[0], "members": keys[:3]},
                         "second": {"name": "lab", "owner": keys[3], "members": keys[3:]}}
        self.assertEqual(len(joined.workload(spec)["rooms"]), 2)
        spec["rooms"]["second"]["owner"] = keys[0]
        spec["rooms"]["second"]["members"].append(keys[0])
        with self.assertRaisesRegex(ValueError, "duplicate room aliases"):
            joined.workload(spec)

    def test_unassigned_member_and_duplicate_selection_are_refused(self):
        spec = self.spec()
        spec["rooms"] = {"small": {"owner": "1000", "members": ["1000", "1001"]}}
        with self.assertRaisesRegex(ValueError, "no workload group"):
            joined.workload(spec)
        spec["workload"] = {"members": ["1000", "1000"], "concurrency": 1}
        with self.assertRaisesRegex(ValueError, "selected member"):
            joined.workload(spec)

    def test_member_alias_is_used_in_actual_write_command(self):
        journey = object.__new__(joined.Journey)
        journey.spec = {"prefix": "joined"}
        room = {"name": "lab", "memberNames": {"1001": "joined-r2"}}
        with patch.object(journey, "shell", return_value="") as shell, \
                patch.object(journey, "json_shell", return_value={"transactionId": "7"}):
            write = journey.member_write(2, room, 1, "1001")
        self.assertIn("joined-r2/notes", shell.call_args.args[2])
        self.assertEqual(write["member"], "1001")


class NamedSweepAliases(unittest.TestCase):
    def test_explicit_group_aliases_are_fresh_on_each_selected_pair(self):
        spec = {"prefix": "receiving", "members": {"1000": {}, "1001": {}, "1002": {}},
                "rooms": {"work": {"name": "lab", "owner": "1000", "members": ["1000", "1001", "1002"]}}}
        first = joined.selected_spec(spec, {"population": 2, "concurrency": 1}, 0)
        second = joined.selected_spec(spec, {"population": 3, "concurrency": 2}, 1)
        self.assertEqual(joined.workload(first)["rooms"]["work"]["name"], "lab-s0")
        self.assertEqual(joined.workload(second)["rooms"]["work"]["name"], "lab-s1")
        self.assertEqual(spec["rooms"]["work"]["name"], "lab")
