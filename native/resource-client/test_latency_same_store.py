#!/usr/bin/env python3
import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


latency = load("latency_same_store", "latency-same-store.py")
prebaseline = load("latency_prebaseline", "latency-prebaseline.py")


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))


class AcceptedCountTests(unittest.TestCase):
    def test_requires_confirmed_outcome(self):
        with self.assertRaises(ValueError):
            latency.accepted_count({"type": "held", "acceptedCount": "3"})

    def test_requires_canonical_decimal_string(self):
        for bad in (3, "0", "03", "-1", None, "3.0"):
            with self.assertRaises(ValueError):
                latency.accepted_count({"type": "confirmed", "acceptedCount": bad})
        self.assertEqual(latency.accepted_count({"type": "confirmed", "acceptedCount": "17"}), 17)


class ScalarProposalTests(unittest.TestCase):
    def test_create_has_no_expected_value(self):
        proposal = latency.scalar("grow", "create", 0, None)
        change = proposal["targets"][0]["payload"]["actions"][0]
        self.assertEqual(change, {"type": "create", "key": {"type": "object", "field": "101"}, "value": "0"})

    def test_write_binds_expected_value(self):
        change = latency.scalar("grow", "write", 5, 4)["targets"][0]["payload"]["actions"][0]
        self.assertEqual((change["value"], change["expected"]), ("5", "4"))


class BatchTests(unittest.TestCase):
    def coordinates(self, height):
        return {"domain": "d", "semantics": "s", "worldRoot": "w", "height": height, "authorityRoot": "a"}

    def make_batch(self, workspace, attempt, heights, completed):
        batch = workspace / "attempts" / attempt / "batch"
        write(batch / "batch-request.json", {})
        for index, height in enumerate(heights):
            write(batch / str(index) / "challenge.json", self.coordinates(height))
            write(batch / str(index) / "intent.json", {"purpose": f"view-{index}"})
        if completed:
            write(batch / "batch-views.json", {})
        return batch

    def test_reports_coherent_completed_batch_and_skips_prior_attempts(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            self.make_batch(workspace, "old", [1, 1], True)
            self.make_batch(workspace, "new", [7, 7, 7], True)
            rows = latency.batches(workspace, {"old"})
            self.assertEqual(len(rows), 1)
            self.assertEqual(rows[0]["size"], 3)
            self.assertTrue(rows[0]["sameImage"])
            self.assertTrue(rows[0]["completed"])
            self.assertEqual(rows[0]["views"], ["view-0", "view-1", "view-2"])

    def test_disagreeing_coordinates_are_not_coherent(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            self.make_batch(workspace, "a", [1, 2], False)
            rows = latency.batches(workspace, set())
            self.assertFalse(rows[0]["sameImage"])
            self.assertFalse(rows[0]["completed"])


@unittest.skipUnless(Path("/proc/self/stat").exists(), "needs Linux /proc")
class ProcessTests(unittest.TestCase):
    def test_cpu_reports_start_time_and_nonnegative_seconds(self):
        start, seconds = latency.cpu(os.getpid())
        self.assertTrue(start.isdigit())
        self.assertGreaterEqual(seconds, 0.0)
        self.assertEqual(latency.cpu(os.getpid())[0], start)


class PreRoomTests(unittest.TestCase):
    def test_adapter_is_the_sibling_file(self):
        self.assertEqual(prebaseline.ADAPTER, HERE / "latency-same-store.py")

    @unittest.skipUnless(Path("/proc/loadavg").exists(), "needs Linux /proc")
    def test_prebaseline_runs_the_member_action_list_and_records_load(self):
        probe = prebaseline.PreRoom.__new__(prebaseline.PreRoom)
        with tempfile.TemporaryDirectory() as tmp:
            probe.output = Path(tmp)
            probe.rows = []
            seen = []

            def call(label, line):
                seen.append((label, line))
                probe.rows.append({"id": label, "seconds": 1.0 + len(seen), "hostCpuSeconds": 0.1, "batches": []})
                return "ok"

            original = prebaseline.latency.Probe.call
            prebaseline.latency.Probe.call = lambda self, label, line: call(label, line)
            try:
                summary = probe.prebaseline(2)
            finally:
                prebaseline.latency.Probe.call = original
            self.assertEqual([line for _, line in seen[:4]], ["whoami", "refs", "read account", "read factory"])
            self.assertEqual(len(seen), 8)
            self.assertEqual(set(summary), {"session", "discovery", "signed-read-account", "signed-read-factory"})
            for row in probe.rows:
                self.assertEqual(len(row["loadavgBefore"]), 3)
                self.assertEqual(len(row["loadavgAfter"]), 3)
            self.assertTrue((probe.output / "timings.json").exists())


if __name__ == "__main__":
    unittest.main()
