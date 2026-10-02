#!/usr/bin/env python3
"""Local adapter/protocol tests only. Synthetic replies do not qualify Mini."""
import copy
import importlib.util
import os
from pathlib import Path
import socket
import struct
import tempfile
import threading
import unittest
from unittest.mock import Mock,patch

spec=importlib.util.spec_from_file_location('regressions',Path(__file__).resolve().parents[1]/'ws-continuity-regressions.py')
r=importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)


class ReplayChecks(unittest.TestCase):
    def test_earliest_delivered_skips_explicit_uncertain_and_rejects_ambiguity(self):
        with tempfile.TemporaryDirectory() as temp:
            journal=Path(temp); candidates=[]
            for operation,phase in [('1','uncertain'),('2','delivered'),('3','delivered')]:
                attempt=journal/('dispatch-op-'+operation);attempt.mkdir()
                path=attempt/'inspection.json'
                r.save(path,{'request':{'operationId':operation},'receipt':{'transactionId':'t'+operation,'eventId':'e'+operation}})
                r.save(journal/('dispatch-op-hash'+operation+'.json'),{'phase':phase,'identity':{'operation_id':operation,
                    'app':4601,'app_generation':4,'dispatch_transaction':'t'+operation,'dispatch_event':'e'+operation}})
                candidates.append(path)
            selected,_,statuses=r.select_delivered(list(reversed(candidates)),journal,'4601','4')
            self.assertEqual(selected,candidates[1])
            self.assertEqual([v['phase'] for v in statuses],['uncertain','delivered','delivered'])
            duplicate=r.load(journal/'dispatch-op-hash2.json')
            r.save(journal/'dispatch-op-duplicate.json',duplicate)
            with self.assertRaisesRegex(RuntimeError,'ambiguous'):
                r.select_delivered(candidates,journal,'4601','4')

    def test_original_receipt_only(self):
        receipt=dict(transactionId='12',eventId='13',acceptedCount='14',worldRoot='15')
        outcome=dict(type='confirmed',confirmation='replayed',**receipt)
        r.checked_historical(outcome,receipt)
        for key in receipt:
            changed=dict(outcome,**{key:'99'})
            with self.assertRaisesRegex(RuntimeError,'differs'):
                r.checked_historical(changed,receipt)
        with self.assertRaisesRegex(RuntimeError,'historical'):
            r.checked_historical(dict(outcome,confirmation='installed'),receipt)

    def test_cas_loser_can_retain_installed_confirmation(self):
        receipt=dict(transactionId='1',eventId='2',acceptedCount='3',worldRoot='4')
        allowed=('installed','replayed','recoveredAfterUncertainResponse')
        for confirmation in allowed:
            r.checked_historical(dict(type='confirmed',confirmation=confirmation,**receipt),receipt,allowed)
        with self.assertRaisesRegex(RuntimeError,'historical'):
            r.checked_historical(dict(type='confirmed',confirmation='unknown',**receipt),receipt,allowed)

    def test_height_balance_and_physical_inspection_must_all_stay_flat(self):
        before=dict(storeHeight=5,worldRoot='66',dispatchCount=2,payerBalances={'8:0':'100'})
        r.equal_no_write(before,copy.deepcopy(before))
        for key,value in [('storeHeight',6),('worldRoot','67'),('dispatchCount',3),('payerBalances',{'8:0':'99'})]:
            with self.assertRaisesRegex(RuntimeError,key):
                r.equal_no_write(before,dict(before,**{key:value}))

    def test_uncertain_action_never_retried(self):
        with tempfile.TemporaryDirectory() as temp:
            x=r.Regressions.__new__(r.Regressions)
            x.f=Mock(root=Path(temp),opdir=Path(temp)/'evidence')
            x.replay=Mock(side_effect=RuntimeError('uncertain'))
            with self.assertRaisesRegex(RuntimeError,'uncertain'):
                x.run('replayAcceptedA')
            with self.assertRaises(FileExistsError):
                x.run('replayAcceptedA')
            self.assertEqual(x.replay.call_count,1)


@unittest.skipUnless(hasattr(socket,'SO_PEERCRED'),'Linux private operator peer contract')
class PrivateWire(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.path=self.root/'operator.sock'
        self.server=socket.socket(socket.AF_UNIX,socket.SOCK_STREAM)
        self.server.bind(str(self.path)); self.path.chmod(0o600); self.server.listen()
        self.server.settimeout(2)
        self.addCleanup(self.server.close)
        self.errors=[]; self.received=[]

    def launch(self, reply):
        def server():
            try:
                with self.server.accept()[0] as client:
                    prefix=client.recv(4)
                    size=struct.unpack('<I',prefix)[0]
                    body=bytearray()
                    while len(body)<size:
                        body.extend(client.recv(size-len(body)))
                    self.received.append(bytes(body))
                    if reply is not None: client.sendall(reply)
            except BaseException as error:
                self.errors.append(error)
        thread=threading.Thread(target=server); thread.start()
        self.addCleanup(lambda:thread.join(3))
        return thread

    def exchange(self):
        # Temporary-directory ancestry is deliberately relaxed only in this local
        # framing test; socket mode and actual peer UID checks remain exercised.
        with patch.object(r.fixture,'protected_parent'):
            return r.private_exchange(self.path,b'config','ab'*32,34,b'signed-ingress',self.root,timeout=1)

    def test_exact_pinned_v2_envelope_and_response(self):
        reply=b'\x22historical'
        thread=self.launch(struct.pack('<I',len(reply))+reply)
        self.assertEqual(self.exchange(),(34,b'historical'))
        thread.join(2)
        self.assertFalse(self.errors)
        self.assertEqual(self.received,[b'\x02'+struct.pack('<I',6)+b'config'+bytes.fromhex('ab'*32)+b'\x22signed-ingress'])
        self.assertEqual((self.root/'response-frame.bin').read_bytes(),struct.pack('<I',len(reply))+reply)

    def test_response_loss_retains_request_and_does_not_retry(self):
        thread=self.launch(None)
        with self.assertRaisesRegex(RuntimeError,'uncertain private response EOF'):
            self.exchange()
        thread.join(2)
        self.assertEqual(len(self.received),1)
        self.assertTrue((self.root/'request-frame.bin').is_file())
        self.assertFalse((self.root/'response-frame.bin').exists())

    def test_oversized_response_refused(self):
        self.launch(struct.pack('<I',r.MAX_FRAME+1))
        with self.assertRaisesRegex(RuntimeError,'response size'):
            self.exchange()

    def test_public_socket_mode_refused_before_send(self):
        self.path.chmod(0o666)
        with self.assertRaisesRegex(RuntimeError,'private'):
            self.exchange()
        self.assertFalse((self.root/'request-frame.bin').exists())


class RootHelperFileSafety(unittest.TestCase):
    def module(self):
        path=Path(__file__).resolve().parents[1]/'ws-continuity-supervision.py'
        spec=importlib.util.spec_from_file_location('supervision',path)
        module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        return module

    def record(self, module, root):
        override=root/'override.conf'; record=root/'setup.json'
        r.save(record,{'override':str(override),'overrideSha256':module.hashlib.sha256(module.BODY).hexdigest()})
        return record,override

    def test_install_interrupted_before_dropin_can_restore(self):
        module=self.module()
        with tempfile.TemporaryDirectory() as temp:
            record,override=self.record(module,Path(temp))
            reload=Mock(return_value='original policy')
            module.restore_owned(record,override,reload)
            module.restore_owned(record,override,reload)
            self.assertEqual(reload.call_count,1)
            self.assertFalse(override.exists())

    def test_restore_interrupted_after_unlink_can_finish(self):
        module=self.module()
        with tempfile.TemporaryDirectory() as temp:
            record,override=self.record(module,Path(temp));override.write_bytes(module.BODY)
            with self.assertRaisesRegex(RuntimeError,'reload failed'):
                module.restore_owned(record,override,Mock(side_effect=RuntimeError('reload failed')))
            self.assertFalse(override.exists())
            self.assertFalse(record.with_suffix('.restored.json').exists())
            module.restore_owned(record,override,Mock(return_value='original policy'))
            self.assertTrue(record.with_suffix('.restored.json').exists())

    def test_modified_override_is_never_removed(self):
        module=self.module()
        with tempfile.TemporaryDirectory() as temp:
            record,override=self.record(module,Path(temp));override.write_bytes(b'other session')
            reload=Mock()
            with self.assertRaisesRegex(RuntimeError,'changed'):
                module.restore_owned(record,override,reload)
            self.assertEqual(override.read_bytes(),b'other session');reload.assert_not_called()

    def test_reappeared_override_after_restore_is_refused(self):
        module=self.module()
        with tempfile.TemporaryDirectory() as temp:
            record,override=self.record(module,Path(temp))
            module.restore_owned(record,override,Mock(return_value='original policy'))
            override.write_bytes(module.BODY)
            with self.assertRaisesRegex(RuntimeError,'reappeared'):
                module.restore_owned(record,override,Mock())
            self.assertTrue(override.exists())

    def test_exclusive_override_never_overwrites_prior_file(self):
        path=Path(__file__).resolve().parents[1]/'ws-continuity-supervision.py'
        spec=importlib.util.spec_from_file_location('supervision',path)
        module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as temp:
            override=Path(temp)/'override.conf'
            override.write_bytes(b'prior policy')
            with self.assertRaises(FileExistsError): module.exclusive(override,module.BODY)
            self.assertEqual(override.read_bytes(),b'prior policy')
            link=Path(temp)/'alias.conf';link.symlink_to(override)
            with self.assertRaises(FileExistsError): module.exclusive(link,module.BODY)
            self.assertEqual(override.read_bytes(),b'prior policy')


if __name__=='__main__': unittest.main()
