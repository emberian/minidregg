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

    def test_resident_dispatch_artifact_refuses(self):
        self.save('state/apps/9101/g4/agent-oracle-agent-v1-attempts/agent-lifetime-dispatch-op-41/reserve.json', {'possible':'reserve'})
        with self.assertRaisesRegex(ValueError,'dispatch evidence'): self.check()


if __name__ == '__main__': unittest.main()
