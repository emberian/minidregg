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
