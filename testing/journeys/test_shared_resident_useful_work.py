#!/usr/bin/env python3
"""Room-write crash recovery boundaries; no native/provider command is started."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

path = Path(__file__).with_name("shared-resident-useful-work.py")
spec = importlib.util.spec_from_file_location("resident_fixture", path)
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)


class RoomWriteRecoveryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name) / "progress.json"

    def test_lost_reply_after_commit_stays_fenced_across_restart_and_tail_eviction(self):
        feed = []
        def write():
            feed.append("this operation")
            raise r.Unknown("reply lost after native commit")
        with self.assertRaises(r.Unknown):
            r.journaled_room_write(r.Journal(self.path), "ask-1", write)
        feed.extend("unrelated" for _ in range(501))
        self.assertNotIn("this operation", feed[-500:])
        retry = mock.Mock()
        with self.assertRaisesRegex(r.Unknown, "started earlier"):
            r.journaled_room_write(r.Journal(self.path), "ask-1", retry)
        retry.assert_not_called()
        self.assertEqual(r.Journal(self.path).state("ask-1"), "started")

    def test_matching_text_in_another_entry_does_not_confirm_a_pending_operation(self):
        journal = r.Journal(self.path)
        journal.begin("ask-1")
        retry = mock.Mock(return_value=True)
        with self.assertRaises(r.Unknown):
            r.journaled_room_write(r.Journal(self.path), "ask-1", retry)
        retry.assert_not_called()
        self.assertEqual(r.Journal(self.path).state("ask-1"), "started")

    def test_filler_resume_retains_unknown_row_even_when_recent_feed_would_hide_it(self):
        journal = r.Journal(self.path)
        r.journaled_room_write(journal, "held-000", lambda: True)
        def lost():
            raise r.Unknown("written but reply lost")
        with self.assertRaises(r.Unknown):
            r.journaled_room_write(journal, "held-001", lost)
        reopened = r.Journal(self.path)
        self.assertEqual(r.unfinished_room_rows(reopened, "held", 3), [1, 2])
        write = mock.Mock()
        with self.assertRaises(r.Unknown):
            r.journaled_room_write(reopened, "held-001", write)
        write.assert_not_called()

    def test_acknowledged_write_is_not_repeated_after_restart(self):
        write = mock.Mock(return_value=True)
        self.assertTrue(r.journaled_room_write(r.Journal(self.path), "say-1", write))
        self.assertTrue(r.journaled_room_write(r.Journal(self.path), "say-1", write))
        write.assert_called_once_with()

class ExactRoomWriteTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.workspace = self.root / 'member'
        self.attempt = self.workspace / 'attempts' / 'native-1'
        self.attempt.mkdir(parents=True)
        self.operation = self.root / 'operation.json'
        self.journal_path = self.root / 'progress.json'
        self.binding = {'workspace': str(self.workspace), 'room': 'shared', 'text': 'request', 'to': '42'}
        self.confirmed = {'type': 'confirmed', 'confirmation': 'installed', 'transactionId': '7'}

    def record(self, signed=True):
        self.operation.write_text(json.dumps({'type': 'minidregg-exact-operation-v1', 'kind': 'workspace',
            'identity': {'workspace': str(self.workspace)}, 'attempt': str(self.attempt),
            'binding': {'request': {'targets': [{'payload': {'text': json.dumps({'type': 'say', 'text': 'request'}), 'to': '42'}}]}}}))
        if signed:
            (self.attempt / 'call.bin').write_bytes(b'exact original signed call')

    def result(self, status):
        return {'type': 'minidregg-operation-recovery-v1', 'operationRecord': str(self.operation),
                'attempt': str(self.attempt), 'status': status,
                'outcome': self.confirmed if status == 'confirmed' else None}

    def invoke(self, write, lookup, retry, binding=None):
        return r.journaled_room_write(r.Journal(self.journal_path), 'request-1', write,
            self.operation, lookup, retry, binding or self.binding)

    def lost(self, path):
        self.record()
        raise r.Unknown('lost reply after sending')

    def test_lost_commit_recovers_after_tail_eviction_without_second_write(self):
        with self.assertRaises(r.Unknown):
            self.invoke(self.lost, mock.Mock(), mock.Mock())
        write, retry = mock.Mock(), mock.Mock()
        result = self.invoke(write, lambda path: self.result('confirmed'), retry)
        self.assertEqual(result['status'], 'confirmed')
        write.assert_not_called()
        retry.assert_not_called()

    def test_unobserved_signed_call_resubmits_only_native_exact_attempt_then_confirms(self):
        with self.assertRaises(r.Unknown):
            self.invoke(self.lost, mock.Mock(), mock.Mock())
        original = (self.attempt / 'call.bin').read_bytes()
        write, retry = mock.Mock(), mock.Mock()
        lookup = mock.Mock(side_effect=[self.result('uncertain'), self.result('confirmed')])
        self.assertEqual(self.invoke(write, lookup, retry)['status'], 'confirmed')
        retry.assert_called_once_with(self.attempt)
        write.assert_not_called()
        self.assertEqual((self.attempt / 'call.bin').read_bytes(), original)

    def test_unsigned_record_cannot_author_another_proposal(self):
        def lost(path):
            self.record(signed=False)
            raise r.Unknown('cut before signing')
        with self.assertRaises(r.Unknown):
            self.invoke(lost, mock.Mock(), mock.Mock())
        write, retry = mock.Mock(), mock.Mock()
        with self.assertRaisesRegex(r.Unknown, 'not-submitted'):
            self.invoke(write, lambda path: self.result('not-submitted'), retry)
        write.assert_not_called()
        retry.assert_not_called()

    def test_lookup_for_another_attempt_is_rejected_before_retry(self):
        with self.assertRaises(r.Unknown):
            self.invoke(self.lost, mock.Mock(), mock.Mock())
        wrong = self.result('uncertain'); wrong['attempt'] += '-other'
        retry = mock.Mock()
        with self.assertRaises(r.Refused):
            self.invoke(mock.Mock(), lambda path: wrong, retry)
        retry.assert_not_called()

    def test_changed_request_cannot_take_over_the_record(self):
        with self.assertRaises(r.Unknown):
            self.invoke(self.lost, mock.Mock(), mock.Mock())
        with self.assertRaisesRegex(r.Refused, 'binding changed'):
            self.invoke(mock.Mock(), mock.Mock(), mock.Mock(), dict(self.binding, text='another request'))

    def test_native_request_collision_is_not_a_confirmation(self):
        with self.assertRaises(r.Unknown):
            self.invoke(self.lost, mock.Mock(), mock.Mock())
        record = json.loads(self.operation.read_text())
        record['binding']['request']['targets'][0]['payload']['text'] = json.dumps({'type': 'say', 'text': 'other'})
        self.operation.write_text(json.dumps(record))
        lookup = mock.Mock(return_value=self.result('confirmed'))
        with self.assertRaisesRegex(r.Refused, 'request differs'):
            self.invoke(mock.Mock(), lookup, mock.Mock())
        lookup.assert_not_called()

    def test_shell_recovery_envelope_is_parsed_before_display_text(self):
        output = json.dumps(self.result('confirmed'), indent=2) + '\nsaid: request\n'
        self.assertEqual(r.operation_result(output), self.result('confirmed'))


class PaymentAccountingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'room-operations').mkdir()
        self.outcomes = {}

    def payment(self, name, status='confirmed'):
        attempt = self.root / 'attempts' / name; attempt.mkdir(parents=True)
        transfer = {'destination': '5', 'asset': '6', 'amount': '1'}
        (attempt / 'plan.json').write_text(json.dumps({'command': {'transfer': transfer, 'fee': '2'}}))
        path = self.root / 'room-operations' / (name + '-payment.json')
        path.write_text(json.dumps({'kind': 'fleet', 'attempt': str(attempt), 'binding': {'transfer': transfer}}))
        self.outcomes[path] = {'type': 'minidregg-operation-recovery-v1', 'operationRecord': str(path),
            'attempt': str(attempt), 'status': status, 'outcome': {'type': 'confirmed', 'confirmation': 'installed', 'transactionId': name}}
        return path

    def test_status_costs_are_counted_separately_from_model_outputs_and_never_truncated_to_controller_tail(self):
        for i in range(66):
            self.payment('model' + str(i))
        for i in range(3):
            self.payment('rs' + str(i))
        self.payment('refused', 'refused')
        snapshot = r.exact_payment_snapshot(self.root, self.outcomes.__getitem__)
        self.assertEqual((snapshot['modelPayments'], snapshot['payments'], snapshot['prices'], snapshot['fees']), (66, 69, 69, 138))
        self.assertEqual(sum(p['statusNotice'] for p in snapshot['paymentEvidence']), 3)

    def test_undecided_payment_fences_accounting_instead_of_disappearing(self):
        self.payment('rs1', 'uncertain')
        with self.assertRaisesRegex(r.Unknown, 'unresolved'):
            r.exact_payment_snapshot(self.root, self.outcomes.__getitem__)

    def test_another_attempt_or_changed_native_plan_cannot_be_counted(self):
        path = self.payment('model1')
        self.outcomes[path]['attempt'] += '-other'
        with self.assertRaises(r.Unknown):
            r.exact_payment_snapshot(self.root, self.outcomes.__getitem__)
        self.outcomes[path]['attempt'] = str(self.root / 'attempts/model1')
        plan = self.root / 'attempts/model1/plan.json'
        plan.write_text(json.dumps({'command': {'transfer': {'amount': '100'}, 'fee': '2'}}))
        with self.assertRaisesRegex(r.Refused, 'plan differs'):
            r.exact_payment_snapshot(self.root, self.outcomes.__getitem__)


if __name__ == "__main__":
    unittest.main()
