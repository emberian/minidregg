"""The S0 conformance suite run on the reference and on a stand-in anchoring backend."""
import hashlib
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import chat_backend as cb  # noqa: E402

SEED = hashlib.sha256(b"fleet-interfaces test key chat-1").digest()


class Conformance(unittest.TestCase):
    def assert_conforms(self, make):
        run = cb.run_suite(make, SEED)
        self.assertEqual(run["controls"], {k: "red" for k in cb.CONTROLS}, run)
        self.assertEqual([v for _, v in run["results"]], ["ok"] * len(cb.INVARIANTS), run)

    def test_none_is_the_reference(self):
        self.assert_conforms(cb.NoneBackend)

    def test_anchoring_backend(self):
        self.assert_conforms(lambda s: cb.FakeAnchorBackend(s, admit_s=0.2))

    def test_failed_proofs_leave_rows_valid(self):
        self.assert_conforms(lambda s: cb.FakeAnchorBackend(s, admit_s=0.05, fail_proofs=True))

    def test_each_control_reads_red_on_its_own_invariant(self):
        expect = {"blocks-sign": "inv1_sign_is_local", "weakens-anchor": "inv4_only_strengthens",
                  "restamps-row": "inv5_backend_never_changes_bytes"}
        for name, inv in expect.items():
            reds = {n for n, e in cb.check(lambda s, c=cb.CONTROLS[name]: c(s, admit_s=0.1), SEED) if e}
            self.assertIn(inv, reds, name)


if __name__ == "__main__":
    unittest.main()
