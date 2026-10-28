#!/usr/bin/env python3
"""Exercise recovery boundary refusals; native lifecycle acceptance is separate."""
import contextlib
import io
import subprocess
import sys
import os
import socket
import shutil
import base64
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('recovery', Path(__file__).resolve().parents[1] /
                                            'deploy/oracle/acceptance/recover_activation.py')
sys.path.insert(0, str(Path(spec.origin).parent))
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
        save('state/apps/9101/g2/record.json', {'phase': 'running', 'dispatch_in_flight': None, 'invocation_id': 'original-invocation',
             'identity': {'unit': 'recorded.service', 'generation': 2}})
        (self.run / 'state/apps/9201').mkdir(parents=True)
        self.manager = {'Id': 'recorded.service', 'LoadState': 'loaded', 'ActiveState': 'inactive',
                        'SubState': 'dead', 'MainPID': '0', 'InvocationID': '', 'Job': ''}
        birth = save('agent-lifetime/session-birth.result.json', {'isError': False})
        save('agent-lifetime/session-birth.retained-result.json', {'isError': False})
        save('agent-lifetime/issued-grant.json', {'protocol': 'mini-oracle-issued-agent-grant-v1',
             'sessionToolResultSha256': recovery.sha(birth), 'grantReceipt': {'acceptedCount': '50'}})

    def read_only_fixture(self):
        self.journal['connection']='detached'
        self.save('agent-lifetime/controller-final-journal.json',self.journal)
        previous=self.run/'continuations/application-api-recovery-6'
        start=self.save('continuations/application-api-recovery-6/successor-start.json', {
            'protocol':'mini-spk-grain-start-v1','app':'9101','generation':'16','unit':'sixteen.service',
            'completion':{'completionReceipt':{'eventId':'actual','acceptedCount':'136'}}})
        self.save(str(previous.relative_to(self.run)/'exit.json'), {'execution_exit':1,'cleanup_exit':0,'namespace_preserved':True})
        self.save(str(previous.relative_to(self.run)/'terminal-journal.json'),self.journal)
        self.save(str(previous.relative_to(self.run)/'observations/controller-status.json'),self.status)
        self.save('state/apps/9101/g16/record.json',{'phase':'running','dispatch_in_flight':None,
            'identity':{'unit':'sixteen.service','generation':16}})
        self.save('agent-lifetime/registered-agent-route.json',{'registration':{'name':'oracle-agent-v2'}})
        self.save('agent-lifetime/allocation.json',{'agents':[{'controller':{'subject':'20010'},'session':'29420',
            'plannedCaps':{'sessionOwner':'20241'}}]})
        attempt=self.run/'agent-lifetime/native-activate-16';attempt.mkdir()
        for name in ('current-start-before-enrollment.stdout','current-start-before-enrollment.stderr',
                     'session-before-enrollment.stdout'):(attempt/name).write_text('')
        (attempt/'session-before-enrollment.stderr').write_text('mini: resident codec Host failed to start (exit status: 1)')
        intent={'subject':'20010','nonce':'7','purpose':{'type':'query','kind':'object','target':'29420','view':'resource'},
                'grants':[{'kind':'object','target':'29420','capability':'20241'}]}
        self.save('agent-lifetime/native-activate-16/session-before-enrollment-intent.json',intent)
        self.save('agent-lifetime/native-activate-16/session-before-enrollment/intent.json',intent)
        self.save('agent-lifetime/native-activate-16/session-before-enrollment/config.json',{})
        self.save('agent-lifetime/native-activate-16/session-before-enrollment/attempt.json',{'operation':'query',
            'config':str(attempt/'session-before-enrollment/config.json'),'host':str(self.run/'bin/minidregg-host'),
            'socket':str(self.run/'world/sock/participant/host.sock')})
        shutil.rmtree(self.run/'agent-lifetime/enrollment-initial')
        observations=self.run/'read-observations';observations.mkdir()
        raw=json.dumps(self.journal).encode()
        self.export['files']['journal.json']={'base64':base64.b64encode(raw).decode(),'sha256':hashlib.sha256(raw).hexdigest()}
        (observations/'controller-export.json').write_text(json.dumps(self.export))
        (observations/'controller-status.json').write_text(json.dumps(self.status))
        (observations/'runtime.sha256').write_text(self.status['runtimeSha256'])
        (observations/'manager.txt').write_text('Id=sixteen.service\nMainPID=0\nActiveState=inactive\nJob=\n')
        return observations,attempt

    def test_read_only_activation_requires_no_enrollment_or_signed_query(self):
        observations,attempt=self.read_only_fixture()
        result=recovery.checked_read_only_activation(self.run,observations)
        self.assertEqual(result['old_generation'],'16')
        self.assertFalse(result['permits_same_generation_relaunch'])
        for relative in ('session-close.json','session-before-enrollment/challenge.json',
                         'session-before-enrollment/signed-observation.bin'):
            path=attempt/relative;path.write_text('{}')
            with self.assertRaises(ValueError):recovery.checked_read_only_activation(self.run,observations)
            path.unlink()
        path=self.run/'agent-lifetime/enrollment-initial';path.mkdir()
        with self.assertRaisesRegex(ValueError,'later enrollment'):recovery.checked_read_only_activation(self.run,observations)

    def test_read_only_prepare_preserves_failure_and_refuses_second_preparation(self):
        observations,attempt=self.read_only_fixture()
        (self.run/'input-sha256.txt').write_text('')
        (self.run/'agent-lifetime/activate-initial.stderr').write_text('retained startup refusal')
        with contextlib.redirect_stdout(io.StringIO()): recovery.prepare_read_only_activation(self.run,observations)
        output=self.run/'continuations/activation-read-16'
        prepared=recovery.read(output/'prepared.json')
        self.assertEqual(prepared['boundary']['old_generation'],'16')
        self.assertEqual((output/'prior/activate-initial.stderr').read_text(),'retained startup refusal')
        self.assertTrue((attempt/'session-before-enrollment/intent.json').is_file())
        with self.assertRaisesRegex(ValueError,'already prepared'):
            recovery.prepare_read_only_activation(self.run,observations)

    def test_read_only_activation_refuses_changed_journal_or_live_incarnation(self):
        observations,attempt=self.read_only_fixture()
        (observations/'manager.txt').write_text('Id=sixteen.service\nMainPID=87\nActiveState=active\nJob=\n')
        with self.assertRaisesRegex(ValueError,'physically stopped'):recovery.checked_read_only_activation(self.run,observations)
        (observations/'manager.txt').write_text('Id=sixteen.service\nMainPID=0\nActiveState=inactive\nJob=\n')
        self.journal['nextOperationId']=999
        self.save('agent-lifetime/controller-final-journal.json',self.journal)
        with self.assertRaisesRegex(ValueError,'controller changed'):recovery.checked_read_only_activation(self.run,observations)

    def check(self):
        return recovery.checked_boundary(self.run, self.export, self.status, self.manager)

    def prepare_fixture(self):
        observations = self.run / 'observations'; observations.mkdir()
        (observations / 'controller-export.json').write_text(json.dumps(self.export))
        (observations / 'controller-status.json').write_text(json.dumps(self.status))
        (observations / 'manager.txt').write_text('\n'.join(k + '=' + v for k, v in self.manager.items()))
        (self.run / 'input-sha256.txt').write_text('')
        store = self.run / 'store'; store.mkdir()
        (store / 'forward-link.sqlite3').write_bytes(b'retained fixture')
        Path(str(store) + '.head-anchor').write_bytes(b'anchor')
        self.save('world/store/base/workroom/deployment/pinned-config.json', {'storageRoot': str(store)})
        with contextlib.redirect_stdout(io.StringIO()):
            recovery.prepare(self.run, observations)
        return observations, self.run / 'continuations/activation-recovery-1'

    def test_prepared_directory_can_record_real_phase_and_refuses_retry_after_marker(self):
        observations, output = self.prepare_fixture()
        controller = Path(__file__).resolve().parents[1] / 'deploy/oracle/acceptance/continue_controller.py'
        subprocess.run([sys.executable, str(controller), '--locked-exec', str(self.run),
                        sys.executable, str(controller), '--phase', str(self.run),
                        str(output / 'phases'), 'runtime-upgrade', 'started'], check=True)
        self.assertTrue((output / 'phases/runtime-upgrade.started.json').is_file())
        with self.assertRaisesRegex(ValueError, 'effect may have started'):
            recovery.prepare(self.run, observations)

    def test_prepared_untouched_boundary_resumes_but_store_change_refuses(self):
        observations, output = self.prepare_fixture()
        (output / 'exit.json').write_text(json.dumps({'execution_exit': 1, 'cleanup_exit': 0,
                                                      'namespace_preserved': True}))
        with contextlib.redirect_stdout(io.StringIO()):
            recovery.prepare(self.run, observations)
        self.assertTrue((output / 'pre-effect-attempts/1/exit.json').is_file())
        (self.run / 'store/forward-link.sqlite3').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'Store changed'):
            recovery.prepare(self.run, observations)

    def test_completed_upgrade_reuses_receipt_before_retrying_stopped_services(self):
        observations, output = self.prepare_fixture()
        (output / 'bin').mkdir()
        (output / 'bin/grain-runtime').write_bytes(b'corrected runtime')
        self.status['runtimeSha256'] = recovery.sha(output / 'bin/grain-runtime')
        (observations / 'controller-status.json').write_text(json.dumps(self.status))
        upgrade = output / 'runtime-upgrade.json'
        upgrade.write_text(json.dumps({'store': 'test-store',
            'previousRuntimeSha256': recovery.sha(self.run / 'bin/grain-runtime'),
            'runtimeSha256': self.status['runtimeSha256']}))
        controller = Path(__file__).resolve().parents[1] / 'deploy/oracle/acceptance/continue_controller.py'
        def phase(name, action, *evidence):
            subprocess.run([sys.executable, str(controller), '--locked-exec', str(self.run),
                sys.executable, str(controller), '--phase', str(self.run), str(output / 'phases'),
                name, action, *map(str, evidence)], check=True)
        phase('runtime-upgrade', 'started')
        phase('runtime-upgrade', 'completed', upgrade)
        phase('services', 'started')
        (output / 'exit.json').write_text(json.dumps({'execution_exit': 1, 'cleanup_exit': 0,
                                                      'namespace_preserved': True}))
        with contextlib.redirect_stdout(io.StringIO()):
            recovery.prepare(self.run, observations)
        self.assertTrue((output / 'pre-effect-attempts/1/services.started.json').is_file())
        self.assertTrue((output / 'phases/runtime-upgrade.completed.json').is_file())
        self.assertFalse((output / 'phases/services.started.json').exists())
        phase('services', 'started')
        phase('supervise', 'started')
        with self.assertRaisesRegex(ValueError, 'lifecycle effect may have started'):
            recovery.prepare(self.run, observations)

    def successor_fixture(self):
        observations, predecessor = self.prepare_fixture()
        old_record = json.loads((self.run / 'state/apps/9101/g2/record.json').read_bytes())
        old_record['phase'] = 'stopped'
        self.save('state/apps/9101/g2/record.json', old_record)
        (predecessor / 'bin').mkdir(); (predecessor / 'bin/grain-runtime').write_bytes(b'corrected runtime')
        self.status['runtimeSha256'] = recovery.sha(predecessor / 'bin/grain-runtime')
        (observations / 'controller-status.json').write_text(json.dumps(self.status))
        failure = predecessor / 'socket-failure'; failure.mkdir()
        stale = self.run / 'stale.sock'
        listener = socket.socket(socket.AF_UNIX); listener.bind(str(stale)); listener.close()
        metadata = stale.lstat()
        config = self.save('state/apps/9101/g4/resident.json', {'agents': [{'socket': str(stale), 'controllerUid': os.getuid()+1}]})
        retained = {'store': 'test-store', 'old_generation': '2', 'successor_generation': '4',
                    'old_record': old_record, 'g4_config_sha256': recovery.sha(config),
                    'socket': {'path': str(stale), 'device': metadata.st_dev, 'inode': metadata.st_ino,
                               'uid': metadata.st_uid, 'mode': oct(metadata.st_mode & 0o777)}}
        (failure / 'boundary.json').write_text(json.dumps(retained))
        (failure / 'g4-unit.log').write_text('resident bootstrap refused: agent socket preflight pin refused')
        for name in ('runtime-upgrade', 'public-listener', 'services'):
            for action in ('started', 'completed'):
                (predecessor / 'phases' / (name+'.'+action+'.json')).write_text('{}')
        (predecessor / 'phases/supervise.started.json').write_text('{}')
        (predecessor / 'supervise.json').write_bytes(b'')
        (predecessor / 'supervise.stderr').write_text('resident unit failed before START completion')
        (predecessor / 'exit.json').write_text(json.dumps({'execution_exit':1,'cleanup_exit':0,'namespace_preserved':True}))
        receipt = self.save('state/apps/9101/g2/stop-completion/receipt-anchor.json', {'eventId':'stopped','worldRoot':'root'})
        shutil.copytree(receipt.parent, failure / 'stop-completion')
        pins = {str(self.run/'store/forward-link.sqlite3'):recovery.sha(self.run/'store/forward-link.sqlite3'),
                str(self.run/'store.head-anchor'):recovery.sha(self.run/'store.head-anchor')}
        (failure / 'native-store-pins.json').write_text(json.dumps(pins))
        (observations / 'manager-successor.txt').write_text('Id=mini-spk-stest-store-a9101-g4.service\nActiveState=failed\nMainPID=0\nJob=\n')
        return observations, predecessor

    def test_stopped_predecessor_and_never_begun_successor_boundary(self):
        observations, predecessor = self.successor_fixture()
        result = recovery.prepare_successor(self.run, observations, predecessor, check_only=True)
        self.assertEqual(result['old_record']['phase'], 'stopped')
        self.assertFalse((self.run / 'continuations/activation-successor-1').exists())
        self.save('state/apps/9101/g4/start-admitted-v3.json', {'unexpected': 'admission'})
        with self.assertRaisesRegex(ValueError, 'may have begun START'):
            recovery.prepare_successor(self.run, observations, predecessor, check_only=True)

    def test_successor_refuses_changed_stopped_store(self):
        observations, predecessor = self.successor_fixture()
        (self.run / 'store/forward-link.sqlite3').write_bytes(b'changed after refusal')
        with self.assertRaisesRegex(ValueError, 'Store changed after successor refusal'):
            recovery.prepare_successor(self.run, observations, predecessor, check_only=True)

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
