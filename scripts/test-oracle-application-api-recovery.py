#!/usr/bin/env python3
"""Refute unsafe qualification continuations; native recovery is tested separately."""
import base64
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('recovery', Path(__file__).resolve().parents[1] /
    'deploy/oracle/acceptance/recover_application_api.py')
recovery = importlib.util.module_from_spec(spec); spec.loader.exec_module(recovery)


class ApplicationRecoveryBoundary(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(); self.addCleanup(temporary.cleanup)
        self.run = Path(temporary.name); self.request_id = 'a' * 32
        def save(name, value):
            path = self.run / name; path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(value)); return path
        self.save = save
        save('world-identity.json', {'store': 'test-store'})
        save('agent-lifetime/registered-agent-route.json', {'registration':{'name':'oracle-agent-v1'}})
        save('continuations/activation-successor-1/exit.json', {'execution_exit': 2, 'cleanup_exit': 0, 'namespace_preserved': True})
        save('continuations/activation-successor-1/successor-start.json', {'generation':'4', 'unit':'test.service'})
        request_path = self.run / 'agent-lifetime/probe/discover-core-query.request-id'
        request_path.parent.mkdir(parents=True); request_path.write_text(self.request_id)
        runtime = self.run / 'continuations/activation-recovery-1/bin/grain-runtime'
        runtime.parent.mkdir(parents=True); runtime.write_bytes(b'pinned runtime')
        active = save('agent-lifetime/controller-active-initial.json', {'config': 'pinned'})
        save('agent-lifetime/issued-grant.json', {'grantReceipt': {'acceptedCount':'50'}})
        save('world/evidence/profile-result.json', {'stateRoot':str(self.run/'state')})
        save('state/apps/9101/g4/record.json', {'phase':'running', 'identity':{'unit':'test.service'}, 'invocation_id':'old-invocation'})
        self.observations = self.run / 'observations'; self.observations.mkdir()
        (self.observations / 'manager.txt').write_text('Id=test.service\nMainPID=0\nActiveState=inactive\nJob=\n')
        save('observations/controller-status.json', {'store':'test-store', 'stopped':True,
            'runtimeSha256':recovery.sha(runtime), 'controllerConfigSha256':recovery.sha(active)})
        self.request = {'requestId':self.request_id, 'name':'mini_oracle_discover',
            'arguments':{'application':'oracle-app', 'availability':'live_direct', 'limit':1, 'query':'core.query'}}
        self.forward = {'bindingSha256':'binding', 'bodyHex':'', 'headers':[{'name':'accept','value':'application/json'}],
            'method':'GET', 'operationId':'41', 'path':'operations', 'protocol':'mini-spk-agent-api-v3',
            'query':'offset=0&limit=1&q=core.query&availability=live_direct', 'type':'dispatch-v3'}
        self.journal = {'binding':{'config':{'dispatchTask':{'task':'27940'}}}, 'foregroundAttempt': {'requestId':self.request_id,'operationId':35,'name':'mini_oracle_discover',
            'phase':'uncertain','resultPath':None,'resultSha256':None,'reported':False,'requestPath':'/native/foreground.json'},
            'applicationApiAttempt': {'operationId':41,'routeName':'oracle-app','phase':'uncertain','reported':False,
            'bindingSha256':'binding','hostInvocation':'old-invocation','requestPath':'/native/api.json'},
            'parentHold':{'reserveConfirmed':True,'reserveRefused':False,'reserve':'1','charge':'0'}}
        for key in ('operationFingerprint','lifetimeCommittedReceipt','lifetimeSettledResponseSha256','lifetimeSettlement','replyPath','replySha256'):
            self.journal['applicationApiAttempt'][key] = None
        for key in ('dispatchAttempt','dispatchPending','dispatchHold','toolPending','toolHold','pending','child'):
            self.journal[key] = None
        native = self.run / 'state/apps/9101/g4/agent-oracle-agent-v1-attempts'
        (native/'agent-lifetime-dispatch-op-41').mkdir(parents=True)
        client = save('state/apps/9101/g4/agent-oracle-agent-v1-attempts/agent-lifetime-client-op-41/forward-request-v3.json', self.forward)
        save(str((client.parent/'received-v3.json').relative_to(self.run)), {'forwardSha256':recovery.sha(client)})
        self.refresh()

    def refresh(self):
        def entry(raw):
            return {'base64':base64.b64encode(raw).decode(), 'sha256':hashlib.sha256(raw).hexdigest()}
        request = json.dumps(self.request).encode(); forward = json.dumps(self.forward).encode()
        if self.journal['foregroundAttempt'] is not None:
            self.journal['foregroundAttempt']['requestSha256'] = hashlib.sha256(request).hexdigest()
        if self.journal['applicationApiAttempt'] is not None:
            self.journal['applicationApiAttempt']['requestSha256'] = hashlib.sha256(forward).hexdigest()
        self.save('agent-lifetime/controller-final-journal.json', self.journal)
        self.save('observations/controller-export.json', {'protocol':'mini-spk-controller-evidence-v1','store':'test-store',
            'files':{'journal.json':entry(json.dumps(self.journal).encode()),'foreground.json':entry(request),'api.json':entry(forward),**{k:entry(json.dumps(v).encode()) for k,v in getattr(self,'extra_files',{}).items()}}})

    def check(self):
        return recovery.checked_boundary(self.run,self.observations,self.request_id)

    def test_exact_retained_boundary_is_read_only(self):
        self.assertFalse(self.check()['retransmit'])
        self.assertFalse((self.run/'continuations/application-api-recovery-1').exists())

    def test_possible_delivery_or_reserve_refuses(self):
        self.journal['applicationApiAttempt']['operationFingerprint']='not-empty'; self.refresh()
        with self.assertRaisesRegex(ValueError,'delivery or settlement'): self.check()
        self.journal['applicationApiAttempt']['operationFingerprint']=None
        self.journal['dispatchAttempt']={'id':42}; self.refresh()
        with self.assertRaisesRegex(ValueError,'custody is pending'): self.check()

    def test_changed_discovery_and_live_process_refuse(self):
        self.request['arguments']['query']='other'; self.refresh()
        with self.assertRaisesRegex(ValueError,'discovery arguments'): self.check()
        self.request['arguments']['query']='core.query'; self.refresh()
        (self.observations/'manager.txt').write_text('Id=test.service\nMainPID=99\nActiveState=active\nJob=\n')
        with self.assertRaisesRegex(ValueError,'physically stopped'): self.check()

    def native_terminal(self):
        boundary = self.check()
        output = self.run / 'continuation'; output.mkdir()
        self.save('continuation/prepared.json', {'boundary':boundary})
        proof = {'decisionId':'44','queryStartOperationId':'42','processFirstOperationId':'42',
            'action':'recover-unreserved-foreground-api','noDispatch':True,'requestId':self.request_id,
            'foregroundOperationId':'35','apiOperationId':'41',
            'requestSha256':boundary['foreground']['requestSha256'],
            'forwardRequestSha256':boundary['api']['requestSha256'],'bindingSha256':'binding',
            'signedPurse':{'grain':{'task':'27940','status':'2','reserved':'0'}}}
        self.save('continuation/native-recovery.json', {'type':'mini-foreground-api-unreserved-recovery-v1',
            'proof':proof,'foregroundRemains':True})
        api = dict(self.journal['applicationApiAttempt'],phase='no-dispatch',reported=True)
        foreground = dict(self.journal['foregroundAttempt'],phase='audited',reported=True)
        journal = dict(self.journal,applicationApiAttempt=None,applicationApiHistory=[api],
            foregroundAttempt=None,foregroundHistory=[foreground],parentHold=None,
            reconciliationLog=[proof,{'action':'foreground-audited-terminal','operationId':'35',
                                     'requestSha256':foreground['requestSha256']}])
        for key in ('birthPending','birthOperation','providerPending','providerHold','providerAttempt','settlementDue'):
            journal[key]=None
        self.save('continuation/terminal-journal.json',journal)
        recovery.check_native(output,terminal=True)
        return output, journal

    def stopped_resumption_fixture(self):
        output,journal=self.native_terminal()
        directory=self.run/'continuations/application-api-recovery-1'; output.rename(directory)
        prepared=recovery.read(directory/'prepared.json'); prepared.update(preserved={},archived={})
        active=self.run/'agent-lifetime/controller-active-initial.json'
        archived=directory/'prior-controller.json'; active.rename(archived)
        prepared['archived'][str(active)]={'path':str(archived),'sha256':recovery.sha(archived)}
        self.save(str((directory/'prepared.json').relative_to(self.run)),prepared)
        (directory/'recovery-input-sha256.txt').write_text('')
        self.save('continuations/application-api-recovery-1/exit.json',{'execution_exit':143,'cleanup_exit':0,'namespace_preserved':True})
        self.save('continuations/application-api-recovery-1/phases/retire-incarnation.started.json',{'state':'started'})
        self.save('continuations/application-api-recovery-1/stop.json',{'protocol':'mini-spk-grain-stop-v1','app':'9101','generation':'4','unit':'test.service'})
        runtime=directory/'bin/grain-runtime'; runtime.parent.mkdir(); runtime.write_bytes(b'qualified runtime')
        status=recovery.read(self.observations/'controller-status.json');status['runtimeSha256']=recovery.sha(runtime)
        self.save('observations/controller-status.json',status)
        journal['connection']='detached'
        raw=json.dumps(journal).encode()
        self.save('observations/controller-export.json',{'files':{'journal.json':{'base64':base64.b64encode(raw).decode(),'sha256':hashlib.sha256(raw).hexdigest()}}})
        record=recovery.read(self.run/'state/apps/9101/g4/record.json'); record['phase']='stopped'
        self.save('state/apps/9101/g4/record.json',record)
        self.save('state/apps/9101/g4/stop-completion/receipt-anchor.json',{'eventId':'native','worldRoot':'root'})
        (self.run/'agent-lifetime/probe/discover-core-query.request-id').unlink()
        return directory

    def test_stopped_resumption_preserves_native_terminal_and_rejects_successor(self):
        directory=self.stopped_resumption_fixture()
        original=(directory/'native-recovery.json').read_bytes()
        result=recovery.checked_stopped_resume(self.run,directory,self.observations)
        self.assertFalse(result['retransmit'])
        self.assertEqual((directory/'native-recovery.json').read_bytes(),original)
        self.assertFalse((directory/'resumption').exists())
        (self.run/'state/apps/9101/g6').mkdir()
        with self.assertRaisesRegex(ValueError,'successor generation'):
            recovery.checked_stopped_resume(self.run,directory,self.observations)

    def test_stopped_resumption_rejects_live_or_uncompleted_stop(self):
        directory=self.stopped_resumption_fixture()
        manager=self.observations/'manager.txt'; old=manager.read_text();manager.write_text(old.replace('MainPID=0','MainPID=1'))
        with self.assertRaisesRegex(ValueError,'physical stopped'):
            recovery.checked_stopped_resume(self.run,directory,self.observations)
        manager.write_text(old)
        self.save('continuations/application-api-recovery-1/stop.json',{'protocol':'mini-spk-grain-stop-v1','app':'9101','generation':'2','unit':'test.service'})
        with self.assertRaisesRegex(ValueError,'physical stopped'):
            recovery.checked_stopped_resume(self.run,directory,self.observations)

    def test_prepared_resumption_can_continue_only_before_custody_migration(self):
        import contextlib,io
        directory=self.stopped_resumption_fixture()
        with contextlib.redirect_stdout(io.StringIO()): recovery.prepare_stopped_resume(self.run,directory,self.observations)
        resumed=directory/'resumption'; (resumed/'bin').mkdir(); runtime=resumed/'bin/grain-runtime';runtime.write_bytes(b'new exact runtime')
        self.save(str((resumed/'runtime-upgrade.json').relative_to(self.run)),{'previousRuntimeSha256':recovery.sha(directory/'bin/grain-runtime'),'runtimeSha256':recovery.sha(runtime)})
        self.save(str((directory/'phases/resume-runtime-upgrade.completed.json').relative_to(self.run)),{'evidence':{}})
        (resumed/'source-input-sha256.txt').write_text('')
        status=recovery.read(self.observations/'controller-status.json');status['runtimeSha256']=recovery.sha(runtime)
        self.save('observations/controller-status.json',status)
        self.save(str((directory/'exit.json').relative_to(self.run)),{'execution_exit':1,'cleanup_exit':0,'namespace_preserved':True})
        self.assertEqual(recovery.checked_stopped_resume(self.run,directory,self.observations)['runtime_sha256'],recovery.sha(runtime))
        with contextlib.redirect_stdout(io.StringIO()): recovery.prepare_stopped_resume(self.run,directory,self.observations)
        self.assertEqual(recovery.read(resumed/'retries/1/prior-exit.json')['execution_exit'],1)
        self.assertEqual(recovery.read(resumed/'retries/1/prepared.json')['runtime_sha256'],recovery.sha(runtime))
        (resumed/'payer-successor-request.json').write_text('{}')
        with self.assertRaisesRegex(ValueError,'migration was prepared'):
            recovery.checked_stopped_resume(self.run,directory,self.observations)

    def test_stopped_resumption_refuses_fenced_controller(self):
        directory=self.stopped_resumption_fixture()
        export=recovery.read(self.observations/'controller-export.json')
        journal=json.loads(recovery.exported(export,'journal.json')); journal['connection']='fenced'
        raw=json.dumps(journal).encode();export['files']['journal.json']={'base64':base64.b64encode(raw).decode(),'sha256':hashlib.sha256(raw).hexdigest()}
        self.save('observations/controller-export.json',export)
        with self.assertRaisesRegex(ValueError,'custody changed'):
            recovery.checked_stopped_resume(self.run,directory,self.observations)

    def test_stopped_resumption_preflight_failure_does_not_consume_boundary(self):
        directory=self.stopped_resumption_fixture()
        self.save('continuations/application-api-recovery-1/phases/services.completed.json',
            {'evidence':{str(self.run/'world-identity.json'):'bad-digest'}})
        with self.assertRaisesRegex(ValueError,'phase evidence changed'):
            recovery.prepare_stopped_resume(self.run,directory,self.observations)
        self.assertFalse((directory/'resumption').exists())
        self.assertEqual(list(directory.glob('resumption-prepared.*')),[])

    def test_recovery_selects_current_registered_successor_route(self):
        original=self.run/'state/apps/9101/g4/agent-oracle-agent-v1-attempts'
        original.rename(original.with_name('agent-oracle-agent-v2-attempts'))
        self.save('agent-lifetime/registered-agent-route.json',{'registration':{'name':'oracle-agent-v2'}})
        self.assertFalse(self.check()['retransmit'])

    def test_native_proof_and_audited_terminal_do_not_claim_an_answer(self):
        output, journal = self.native_terminal()
        foreground = journal['foregroundHistory'][0]
        foreground['resultPath']='/fabricated/result.json'
        self.save('continuation/terminal-journal.json',journal)
        with self.assertRaisesRegex(ValueError,'fabricated result'):
            recovery.check_native(output,terminal=True)

    def test_second_recovery_preserves_prior_proof_and_selects_exact_successor(self):
        import contextlib
        import io
        import shutil
        output, journal = self.native_terminal()
        previous = self.run / 'continuations/application-api-recovery-1'
        output.rename(previous)
        prepared = recovery.read(previous/'prepared.json')
        prepared.update(preserved={}, archived={})
        self.save(str((previous/'prepared.json').relative_to(self.run)), prepared)
        self.save('continuations/application-api-recovery-1/exit.json',
                  {'execution_exit':2, 'cleanup_exit':0, 'namespace_preserved':True})
        self.save('continuations/application-api-recovery-1/phases/enrollment.completed.json', {'evidence':{}})
        self.save('continuations/application-api-recovery-1/successor-start.json',
                  {'generation':'6','unit':'test.service'})
        runtime = previous/'bin/grain-runtime'; runtime.parent.mkdir(); runtime.write_bytes(b'new runtime')
        status = recovery.read(self.observations/'controller-status.json')
        status['runtimeSha256'] = recovery.sha(runtime)
        self.save('observations/controller-status.json',status)
        shutil.copytree(self.run/'state/apps/9101/g4',self.run/'state/apps/9101/g6')
        with self.assertRaisesRegex(ValueError,'audited request'): self.check()
        self.request_id = 'b'*32; self.request['requestId'] = self.request_id
        self.journal['foregroundAttempt']['requestId'] = self.request_id
        (self.run/'agent-lifetime/probe/discover-core-query.request-id').write_text(self.request_id)
        self.refresh()
        self.assertEqual(self.check()['old_generation'],'6')
        self.assertEqual(self.check()['previous_execution'],str(previous))
        (self.run/'input-sha256.txt').write_text('')
        original_proof = (previous/'native-recovery.json').read_bytes()
        with contextlib.redirect_stdout(io.StringIO()):
            recovery.prepare(self.run,self.observations,self.request_id)
        self.assertTrue((self.run/'continuations/application-api-recovery-2/prepared.json').exists())
        self.assertEqual((previous/'native-recovery.json').read_bytes(), original_proof)
        self.assertEqual(recovery.retained_paths(self.run,after=previous)[str(self.run/'agent-lifetime/probe/discover-core-query.request-id')]['sha256'],hashlib.sha256(self.request_id.encode()).hexdigest())

    def test_incomplete_recovery_sequence_refuses(self):
        (self.run/'continuations/application-api-recovery-2').mkdir()
        with self.assertRaisesRegex(ValueError,'sequence is incomplete'): self.check()

    def make_startup_refusal(self):
        import shutil
        self.journal.update(connection='fenced',nextOperationId=153,foregroundAttempt=None,
                            applicationApiAttempt=None,parentHold=None)
        self.journal['binding']['config'].update(task='27920',subject='20010',queryCapability='20201')
        self.query = {'grants':[{'capability':'20201','kind':'object','target':'27920'}],
                      'nonce':'152','purpose':{'kind':'object','target':'27920','type':'query','view':'resource'},
                      'subject':'20010'}
        self.extra_files = {'query-0000000000000152/intent-source.json':self.query,
                            'query-0000000000000152/attempt/attempt.json':{'operation':'query'}}
        self.save('agent-lifetime/probe/discover-core-query.request.json',self.request)
        self.refusal = {'isError':True,'operationId':None,'requestId':self.request_id,
                        'result':'foreground tool requires an attached, reconciled idle task',
                        'type':'tool-complete','v':1}
        self.save('agent-lifetime/probe/discover-core-query.result.json',self.refusal)
        shutil.rmtree(self.run/'state/apps/9101/g4/agent-oracle-agent-v1-attempts')
        self.refresh()

    def test_read_only_startup_refusal_has_no_fabricated_api_audit(self):
        self.make_startup_refusal()
        boundary = self.check()
        self.assertEqual(boundary['kind'],'startup-refusal')
        self.assertIsNone(boundary['api']); self.assertIsNone(boundary['foreground'])
        self.assertEqual(boundary['pre_admission']['query'],'query-0000000000000152')
        self.assertFalse(boundary['retransmit'])

    def test_startup_refusal_rejects_pending_effect_or_nonquery_helper(self):
        self.make_startup_refusal()
        self.journal['pending']={'uncertain':'effect'};self.refresh()
        with self.assertRaisesRegex(ValueError,'retained native custody'):self.check()
        self.journal['pending']=None
        self.query['purpose']['type']='admit';self.refresh()
        with self.assertRaisesRegex(ValueError,'read-only query'):self.check()
        self.query['purpose']['type']='query';self.refresh()
        self.refusal['operationId']='153'
        self.save('agent-lifetime/probe/discover-core-query.result.json',self.refusal)
        with self.assertRaisesRegex(ValueError,'pre-admission refusal'):self.check()

    def make_readiness_refusal(self):
        import shutil
        self.make_startup_refusal()
        self.journal['connection'] = 'soft'
        shutil.rmtree(self.run/'agent-lifetime/probe')
        self.save('continuations/activation-successor-1/exit.json',
                  {'execution_exit':1,'cleanup_exit':0,'namespace_preserved':True})
        (self.run/'agent-lifetime/readiness-probe.json').write_bytes(b'')
        (self.run/'agent-lifetime/readiness-probe.stderr').write_text(
            'grain-runtime admin: error: controller readiness lacks a signed idle task\n')
        self.extra_files.update({
            'query-0000000000000152/attempt/view.json': {'type':'resource','cell':{
                'grain':{'task':'27920','status':'2','reserved':'0'}}},
            'query-0000000000000152/attempt/challenge.json':{'intent':self.query,'height':'125','worldRoot':'999'},
            'query-0000000000000152/attempt/signed-observation.bin':'retained native bytes'})
        self.refresh()
        self.request_id = None

    def test_readiness_refusal_is_exact_and_allocates_no_request(self):
        self.make_readiness_refusal()
        boundary = self.check()
        self.assertEqual(boundary['kind'],'readiness-refusal')
        self.assertIsNone(boundary['request_id'])
        self.assertTrue(boundary['pre_admission']['no_tool_request'])
        self.assertIsNone(boundary['api'])
        self.assertFalse((self.run/'continuations/application-api-recovery-1').exists())
        self.save('agent-lifetime/probe/request.json',{'new':'request'})
        with self.assertRaisesRegex(ValueError,'already has a tool probe'): self.check()

    def test_readiness_refusal_rejects_pending_and_wrong_signed_state(self):
        self.make_readiness_refusal()
        self.journal['parentHold'] = {'reserve':'1'}; self.refresh()
        with self.assertRaisesRegex(ValueError,'retained native custody'): self.check()
        self.journal['parentHold'] = None
        self.extra_files['query-0000000000000152/attempt/view.json']['cell']['grain']['status']='4'
        self.refresh()
        with self.assertRaisesRegex(ValueError,'signed attached-idle evidence'): self.check()

    def test_resident_dispatch_artifact_refuses(self):
        self.save('state/apps/9101/g4/agent-oracle-agent-v1-attempts/agent-lifetime-dispatch-op-41/reserve.json', {'possible':'reserve'})
        with self.assertRaisesRegex(ValueError,'dispatch evidence'): self.check()


class BrokerStoppedEvidence(unittest.TestCase):
    def test_stale_socket_is_observed_without_unlinking_and_live_socket_refuses(self):
        import socket,os
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);endpoint=root/'broker.sock'
            (root/'broker-manager.txt').write_text('Id=own.service\nMainPID=0\nControlGroup=\nActiveState=inactive\n')
            self.assertEqual(recovery.checked_stopped_broker(root,endpoint,'own.service',os.getuid())['state'],'absent')
            with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as server:
                server.bind(str(endpoint));endpoint.chmod(0o600);server.listen()
                with self.assertRaisesRegex(ValueError,'accepts connections'):
                    recovery.checked_stopped_broker(root,endpoint,'own.service',os.getuid())
            inode=endpoint.stat().st_ino
            result=recovery.checked_stopped_broker(root,endpoint,'own.service',os.getuid())
            self.assertEqual(result['state'],'stale-refused');self.assertEqual(endpoint.stat().st_ino,inode)
            (root/'broker-manager.txt').write_text('Id=own.service\nMainPID=123\nControlGroup=\nActiveState=inactive\n')
            with self.assertRaisesRegex(ValueError,'owner unit'):
                recovery.checked_stopped_broker(root,endpoint,'own.service',os.getuid())

class OperatorUpgradeEvidence(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location('report', Path(__file__).resolve().parents[1] /
            'deploy/oracle/acceptance/report.py')
        self.report = importlib.util.module_from_spec(spec); spec.loader.exec_module(self.report)
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup); self.root = Path(tmp.name)
        (self.root/'bin').mkdir(); (self.root/'bin/mini').write_bytes(b'new qualified client')
        self.old = 'a'*64; self.new = self.report.sha(self.root/'bin/mini')
        (self.root/'mini-before.sha256').write_text(self.old+'  /exact/controller/bin/mini\n')
        self.write('mini-upgrade.json', {'store':'s','miniSha256':self.new,'previousMiniSha256':self.old})
        self.write('consent-memory.json', {'store':'s','memoryMiB':4096,'nativeOperationSubmitted':False})
        for name, memory in [('before',2147483648),('after',4294967296)]:
            (self.root/f'consent-memory-{name}.properties').write_text(
                f'Id=mini-spk-controller-consent-s.service\nMainPID=0\nActiveState=inactive\nMemoryMax={memory}\nMemorySwapMax=0\n')
    def write(self, name, value): (self.root/name).write_text(json.dumps(value))
    def check(self):
        def require(label, condition): self.assertTrue(condition, label)
        return self.report.operator_upgrade_evidence(self.root, 's', require)
    def test_exact_pair_and_memory_receipts(self):
        result, phases = self.check()
        self.assertEqual(phases, ['consent-memory','mini-upgrade'])
        self.assertEqual(result['consent_memory']['receipt']['memoryMiB'],4096)
    def test_wrong_client_or_old_pin_refuses(self):
        for key in ('miniSha256','previousMiniSha256'):
            receipt={'store':'s','miniSha256':self.new,'previousMiniSha256':self.old}; receipt[key]='f'*64
            self.write('mini-upgrade.json',receipt)
            with self.assertRaisesRegex(AssertionError,'controller_mini'): self.check()
    def test_live_or_wrong_memory_manager_refuses(self):
        p=self.root/'consent-memory-after.properties'; original=p.read_text()
        for old,new in [('MainPID=0','MainPID=123'),('MemoryMax=4294967296','MemoryMax=2147483648'),('MemorySwapMax=0','MemorySwapMax=1')]:
            p.write_text(original.replace(old,new))
            with self.assertRaisesRegex(AssertionError,'consent_memory'): self.check()

if __name__ == '__main__': unittest.main()
