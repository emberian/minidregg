#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import tempfile
import unittest
spec=importlib.util.spec_from_file_location("connector_authority",Path(__file__).resolve().parents[1]/"connector-authority.py")
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class CustodyTests(unittest.TestCase):
    def test_exact_call_selects_recovery_and_incomplete_attempt_fences(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/"attempt"
            self.assertEqual(m.pending_action(p),"submit")
            p.mkdir();self.assertEqual(m.pending_action(p),"unresolved")
            (p/"call.bin").write_bytes(b"exact")
            self.assertEqual(m.pending_action(p),"recover")
    def test_retained_binding_cannot_redirect_after_crash(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/"input.json"
            m.retain(p,{"target":"12"});m.retain(p,{"target":"12"})
            with self.assertRaisesRegex(RuntimeError,"differs"):
                m.retain(p,{"target":"13"})
            self.assertEqual(m.load(p),{"target":"12"})
if __name__=="__main__":unittest.main()
