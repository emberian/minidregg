#!/usr/bin/env python3
"""Exercise recovery boundary refusals; native lifecycle acceptance is separate."""
import base64
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('recovery', Path(__file__).resolve().parents[1] /
                                            'deploy/oracle/acceptance/recover_activation.py')
recovery = importlib.util.module_from_spec(spec)
spec.loader.exec_module(recovery)


class RecoveryBoundary(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.run = Path(temporary.name)
        def save(name, value):
            path = self.run / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(value))
            return path
        self.save = save
        save('world-identity.json', {'store': 'test-store'})
        save('exit.json', {'execution_exit': 1, 'cleanup_exit': 0, 'namespace_preserved': True})
        self.journal = {'connection': 'soft', 'binding': {'config': {'toolTask': {}}}}
        for name in ('pending', 'toolPending', 'providerPending', 'child', 'settlementDue',
                     'parentHold', 'toolHold', 'dispatchPending', 'dispatchHold', 'dispatchAttempt',
                     'applicationApiAttempt', 'providerHold', 'providerAttempt', 'providerSettlement',
                     'foregroundAttempt', 'birthOperation', 'birthPending'):
            self.journal[name] = None
        before = save('agent-lifetime/enrollment-initial/before.json', self.journal)
        save('agent-lifetime/controller-final-journal.json', self.journal)
        request = save('agent-lifetime/enrollment-initial/request.json', {
            'protocol': 'mini-controller-application-enrollment-v1', 'mode': 'application',
            'expectedBindingSha256': recovery.binding_sha(self.journal['binding']),
            'targetConfigSha256': 'a' * 64})
        (request.parent / 'stderr').write_text('unknown variant `binding-v3`')
        def entry(path):
            raw = path.read_bytes()
            return {'base64': base64.b64encode(raw).decode(), 'sha256': hashlib.sha256(raw).hexdigest()}
        self.export = {'protocol': 'mini-spk-controller-evidence-v1', 'store': 'test-store',
                       'files': {'journal.json': entry(before),
                                 'application-enrollments/' + recovery.sha(request) + '/request.json': entry(request)}}
        binary = self.run / 'bin/grain-runtime'; binary.parent.mkdir(); binary.write_bytes(b'old runtime')
        self.status = {'stopped': True, 'store': 'test-store', 'controllerConfigSha256': 'a' * 64,
                       'runtimeSha256': recovery.sha(binary)}
        save('world/evidence/start-a.stdout', {'protocol': 'mini-spk-grain-start-v1', 'app': '9101',
             'generation': '2', 'unit': 'recorded.service', 'completion': {'completionReceipt': {'acceptedCount': '53'}}})
        save('world/evidence/profile-result.json', {'stateRoot': str(self.run / 'state')})
        save('state/apps/9101/g2/record.json', {'phase': 'running', 'dispatch_in_flight': None,
             'identity': {'unit': 'recorded.service', 'generation': 2}})
        (self.run / 'state/apps/9201').mkdir(parents=True)
        self.manager = {'Id': 'recorded.service', 'LoadState': 'loaded', 'ActiveState': 'inactive',
                        'SubState': 'dead', 'MainPID': '0', 'InvocationID': '', 'Job': ''}
        birth = save('agent-lifetime/session-birth.result.json', {'isError': False})
        save('agent-lifetime/session-birth.retained-result.json', {'isError': False})
        save('agent-lifetime/issued-grant.json', {'protocol': 'mini-oracle-issued-agent-grant-v1',
             'sessionToolResultSha256': recovery.sha(birth), 'grantReceipt': {'acceptedCount': '50'}})

    def check(self):
        return recovery.checked_boundary(self.run, self.export, self.status, self.manager)

    def test_exact_stopped_boundary_is_inspection_only(self):
        value = self.check()
        self.assertFalse(value['permits_same_generation_relaunch'])
        self.assertFalse(value['permits_enrollment_replay'])
        self.assertFalse((self.run / 'continuations').exists())

    def test_local_enrollment_record_refuses(self):
        name = next(name for name in self.export['files'] if name.startswith('application-enrollments/'))
        self.export['files'][name.replace('request.json', 'record.json')] = self.export['files'][name]
        with self.assertRaisesRegex(ValueError, 'commit record'):
            self.check()

    def test_changed_journal_refuses(self):
        self.save('agent-lifetime/controller-final-journal.json', dict(self.journal, nextOperationId=999))
        with self.assertRaisesRegex(ValueError, 'journal changed'):
            self.check()

    def test_live_incarnation_and_changed_runtime_refuse(self):
        for target, key, value in ((self.manager, 'MainPID', '123'), (self.status, 'runtimeSha256', 'b' * 64)):
            old = target[key]; target[key] = value
            with self.assertRaises(ValueError):
                self.check()
            target[key] = old

    def test_later_agent_work_refuses(self):
        (self.run / 'agent-lifetime/probe').mkdir()
        with self.assertRaisesRegex(ValueError, 'later qualification'):
            self.check()


if __name__ == '__main__':
    unittest.main()
