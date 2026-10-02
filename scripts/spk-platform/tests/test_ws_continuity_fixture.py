#!/usr/bin/env python3
"""Adapter logic only; synthetic views do not qualify Mini or EtherCalc."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock

MODULE = Path(__file__).resolve().parents[1]/"ws-continuity-fixture.py"
spec = importlib.util.spec_from_file_location("fixture",MODULE)
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)


def view(fields, height="30"):
    return {"view":{"cell":{"root":"99","entries":[{"key":{"field":k},"value":v} for k,v in fields.items()]},"balances":[["0","123"]]},
            "challenge":{"height":height,"worldRoot":"100","authorityRoot":"200"},"dir":Path("/unused")}


class AdapterTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.x = f.Fixture.__new__(f.Fixture)
        self.x.root = Path(self.tmp.name)
        self.x.opdir = self.x.root/"hook"
        self.x.opdir.mkdir()
        self.x.state = self.x.root/"state"
        self.x.app = "4601"
        self.x.appcap = "3101"
        self.x.nonce = 100
        self.x.f = {"app":"4601","generation":"4","delegates":{
            "a":{"subject":"7","session":"4610","cap":"3211","ticket":"4620","ticketOwner":"3232","ticketControl":"3233","ticketObserve":"3234"},
            "b":{"subject":"9","session":"4612","cap":"3221","ticket":"4622","ticketOwner":"3242","ticketControl":"3243","ticketObserve":"3244"}}}
        self.x.submit = Mock(return_value=self.x.opdir/"native-attempt")
        self.x.write_state = Mock()
        self.x.query = Mock(return_value=view({"0":"4601","1":"4","2":"2","3":"1"}))

    def test_owner_revokes_only_a_ticket_child(self):
        b = copy.deepcopy(self.x.f["delegates"]["b"])
        result = self.x.action("revokeA")
        intent, signer = self.x.submit.call_args.args
        c = intent["purpose"]["draft"]["command"]
        self.assertEqual(signer,8)
        self.assertEqual((c["subject"],c["target"],c["capability"],c["controlCapability"]),
                         ("8","4620","3234","3233"))
        self.assertEqual(self.x.query.call_args_list[1].kwargs,{"denied":True})
        self.assertEqual(self.x.query.call_args_list[2].args,("9","4622","3244"))
        self.assertEqual(b,self.x.f["delegates"]["b"])
        self.assertTrue(self.x.f["delegates"]["a"]["revoked"])
        self.assertTrue(Path(result["artifact"]).is_file())

    def test_failed_confirmation_does_not_permit_second_mutation(self):
        self.x.query.side_effect = [view({}),RuntimeError("wrong refusal")]
        with self.assertRaisesRegex(RuntimeError,"wrong refusal"):
            self.x.action("revokeA")
        with self.assertRaisesRegex(RuntimeError,"already attempted"):
            self.x.action("revokeA")
        self.assertEqual(self.x.submit.call_count,1)
        self.x.write_state.assert_not_called()

    def test_regrant_without_hot_consumer_is_nonmutating(self):
        with self.assertRaisesRegex(RuntimeError,"regrant disabled"):
            self.x.action("regrantA")
        self.x.submit.assert_not_called()
        self.x.query.assert_not_called()
        self.assertFalse((self.x.root/"action-regrantA-started.json").exists())

    def snapshots(self, different_tip=False):
        app=view({"0":"4","1":"4"})
        a=view({"0":"4601","1":"4","2":"2","3":"1"})
        b=copy.deepcopy(a)
        payer=view({},height="31" if different_tip else "30")
        self.x.query.side_effect=[app,a,view({}),b,view({}),payer]

    def test_snapshot_does_not_fabricate_billing_counter(self):
        self.snapshots()
        result=self.x.snapshot()
        self.assertIsNone(result["billingCount"])
        self.assertEqual(result["payerBalances"],{"8:0":"123"})
        self.assertEqual(result["storeHeight"],30)
        self.assertIn("NOT a source history",result["provenance"]["dispatchCount"])
        self.assertTrue(result["delegates"]["a"]["active"])
        self.x.submit.assert_not_called()

    def test_snapshot_rejects_mixed_source_tips(self):
        self.snapshots(different_tip=True)
        with self.assertRaisesRegex(RuntimeError,"Store changed"):
            self.x.snapshot()

    def test_stale_session_generation_is_inactive(self):
        self.snapshots()
        values=list(self.x.query.side_effect)
        values[1]=view({"0":"4601","1":"3","2":"2","3":"1"})
        self.x.query.side_effect=values
        result=self.x.snapshot()
        self.assertFalse(result["delegates"]["a"]["active"])
        self.assertTrue(result["delegates"]["b"]["active"])


class RegistrationTests(unittest.TestCase):
    def setUp(self):
        self.request={"registrationNonceHex":"a"*64,"expectedApp":"4601","expectedAppGeneration":"4","expectedSessionGeneration":"4"}
        self.delegate={"session":"4610","subject":"7","ticket":"4641"}
        self.reply={"protocol":"mini-spk-route-register-v1","registrationNonceHex":"a"*64,"routeIndex":2,
            "app":"4601","appGeneration":"4","session":"4610","sessionGeneration":"4","subject":"7","ticketResource":"4641",
            "sessionFingerprintHex":"b"*64,"admittedHeight":"123","admittedWorldRoot":"456"}

    def test_exact_binding(self):
        f.check_registration(self.reply,self.request,self.delegate)

    def test_other_ticket_replay_refused(self):
        self.reply["ticketResource"]="4620"
        with self.assertRaisesRegex(RuntimeError,"identity differs"):
            f.check_registration(self.reply,self.request,self.delegate)

    def test_other_nonce_refused(self):
        self.reply["registrationNonceHex"]="c"*64
        with self.assertRaisesRegex(RuntimeError,"identity differs"):
            f.check_registration(self.reply,self.request,self.delegate)

    def test_unsupported_reply_field_refused(self):
        self.reply["accepted"]=True
        with self.assertRaisesRegex(RuntimeError,"shape differs"):
            f.check_registration(self.reply,self.request,self.delegate)


if __name__ == "__main__":
    unittest.main()
