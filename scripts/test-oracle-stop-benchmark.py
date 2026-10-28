#!/usr/bin/env python3
"""Focused artifact guards; no claim to execute the native STOP receiver."""
import importlib.util
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest

spec = importlib.util.spec_from_file_location("stop_probe", Path(__file__).with_name("oracle-stop-inspection-probe.py"))
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)

spec = importlib.util.spec_from_file_location("authority_probe", Path(__file__).with_name("oracle-agent-authority-probe.py"))
authority = importlib.util.module_from_spec(spec)
spec.loader.exec_module(authority)


class BenchmarkGuards(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.configs = []
        for name in ("source", "copy"):
            root = self.root / name / "store"
            root.mkdir(parents=True)
            (root / "forward-link.sqlite3").write_bytes(b"retained database")
            Path(str(root) + ".head-anchor").write_bytes(b"retained anchor")
            config = root.parent / "config.json"
            config.write_text(json.dumps({"storageRoot": str(root), "expectedSeed": 7}))
            self.configs.append(config)

    def test_native_reference_requires_actual_success_and_same_host_bytes(self):
        paths={key:self.root/(key+'.json') for key in ('host_binary','stop_receipt','command_result','control_claim')}
        paths['host_binary'].write_bytes(b'qualified Host')
        paths['control_claim'].write_bytes(b'canonical claim checked by later native negative control')
        paths['stop_receipt'].write_text(json.dumps({'protocol':'mini-spk-grain-stop-v1','activeState':'inactive','generation':'2'}))
        paths['command_result'].write_text(json.dumps({'exitCode':0}))
        value={'schema':'mini-oracle-native-stop-reference-v1','host_sha256':probe.file_digest(paths['host_binary']).hex(),
               **{key:{'path':str(path),'sha256':probe.file_digest(path).hex()} for key,path in paths.items()}}
        reference=self.root/'reference.json';reference.write_text(json.dumps(value))
        self.assertEqual(probe.checked_native_reference(reference,paths['host_binary']),value)
        value['host_sha256']='0'*64;reference.write_text(json.dumps(value))
        with self.assertRaisesRegex(RuntimeError,'selected Host'):probe.checked_native_reference(reference,paths['host_binary'])
        value['host_sha256']=value['host_binary']['sha256'];reference.write_text(json.dumps(value))
        paths['command_result'].write_text(json.dumps({'exitCode':1}))
        with self.assertRaisesRegex(RuntimeError,'file differs'):probe.checked_native_reference(reference,paths['host_binary'])
        value['command_result']['sha256']=probe.file_digest(paths['command_result']).hex();reference.write_text(json.dumps(value))
        with self.assertRaisesRegex(RuntimeError,'completed native stop'):probe.checked_native_reference(reference,paths['host_binary'])

    def test_current_snapshot_refuses_wal_before_any_native_process(self):
        config=self.configs[0];root=Path(json.loads(config.read_bytes())['storageRoot'])
        (root/'forward-link.sqlite3-wal').write_bytes(b'uncheckpointed write')
        out=self.root/'snapshot'
        with self.assertRaisesRegex(RuntimeError,'quiescent WAL'):
            probe.snapshot_current(['--host','/missing','--mini','/missing','--source-config',str(config),
                '--plan','/missing','--committed','/missing','--mismatched-committed','/missing','--out',str(out)])
        self.assertFalse(list(out.glob('*.pid')))

    def test_authority_refusal_requires_exact_current_reason(self):
        reason = "lifetime grant absent from admitted history"
        outcome = {"type": "refused", "effect": "no-record", "phase": b"op 80".hex(),
                   "detail": reason.encode().hex()}
        self.assertEqual(reason, authority.classify_refusal(outcome, [reason]))
        for key, value in (("type", "uncertain"), ("effect", "undecided"),
                           ("phase", b"op 155".hex()), ("detail", ("prefix " + reason).encode().hex())):
            with self.assertRaises(RuntimeError):
                authority.classify_refusal(dict(outcome, **{key: value}), [reason])

    def test_current_definite_stop_refusal_only(self):
        outcome = {"type": "refused", "effect": "no-record", "phase": b"op 155".hex(),
                   "detail": b"noncanonical committed launch claim-v3".hex()}
        self.assertEqual("source", probe.require_refusal("trailing-claim", b"\xfdframe", lambda _: outcome))
        for tag in (b"\xff", b"\xfe", b"\x9b"):
            with self.assertRaisesRegex(RuntimeError, "definite"):
                probe.require_refusal("trailing-claim", tag + b"frame", lambda _: outcome)
        for key, value in (("type", "uncertain"), ("effect", "undecided"),
                           ("phase", b"op 2".hex()), ("detail", b"busy".hex())):
            with self.assertRaisesRegex(RuntimeError, "expected STOP"):
                probe.require_refusal("trailing-claim", b"\xfdframe", lambda _: dict(outcome, **{key: value}))

    def test_independent_copy_and_coordination_files(self):
        first = probe.benchmark_snapshot(*self.configs)
        root = self.root / "copy/store"
        (root / "forward-link.sqlite3-shm").write_bytes(b"reader locks")
        (root / "forward-link.sqlite3-wal").write_bytes(b"")
        self.assertEqual(first, probe.benchmark_snapshot(*self.configs))

    def test_uncheckpointed_wal_is_not_omitted(self):
        (self.root / "source/store/forward-link.sqlite3-wal").write_bytes(b"uncheckpointed admission")
        with self.assertRaisesRegex(RuntimeError, "WAL"):
            probe.benchmark_snapshot(*self.configs)

    def test_copy_cannot_change_seed_or_share_database_inode(self):
        path = self.configs[1]
        config = json.loads(path.read_text())
        config["expectedSeed"] = 8
        path.write_text(json.dumps(config))
        with self.assertRaisesRegex(RuntimeError, "configurations differ"):
            probe.benchmark_snapshot(*self.configs)
        config["expectedSeed"] = 7
        path.write_text(json.dumps(config))
        database = self.root / "copy/store/forward-link.sqlite3"
        database.unlink()
        database.hardlink_to(self.root / "source/store/forward-link.sqlite3")
        with self.assertRaisesRegex(RuntimeError, "must not share files"):
            probe.benchmark_snapshot(*self.configs)

    def test_changes_to_both_stores_cannot_acquire_success_receipt(self):
        before = probe.benchmark_snapshot(*self.configs)
        for name in ("source", "copy"):
            (self.root / name / "store/forward-link.sqlite3").write_bytes(b"same new admission")
        args = SimpleNamespace(benchmark_source_config=self.configs[0], config=self.configs[1], out=self.root)
        with self.assertRaisesRegex(RuntimeError, "changed"):
            probe.write_benchmark(args, {"passed": True}, before)
        self.assertFalse((self.root / "benchmark.json").exists())

    def test_missing_canonical_refusal_cannot_acquire_success_receipt(self):
        before = probe.benchmark_snapshot(*self.configs)
        args = SimpleNamespace(benchmark_source_config=self.configs[0], config=self.configs[1], out=self.root)
        with self.assertRaisesRegex(RuntimeError, "canonical wrong-claim"):
            probe.write_benchmark(args, {"passed": True, "cold_comparison": "passed",
                                         "canonical_wrong_claim_checked": False}, before)
        self.assertFalse((self.root / "benchmark.json").exists())


if __name__ == "__main__":
    unittest.main()
