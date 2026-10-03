import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock,patch

HERE=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('same_store_app',HERE/'same-store-app.py');app=importlib.util.module_from_spec(spec);spec.loader.exec_module(app)
f=app.f
class AttachTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
        self.c={'protocol':'mini-spk-same-store-attach-v1','expectedSourceCommit':'a'*40,'namespace':{'domain':'17','semantics':'23'},'room':{'target':'800001','capability':'900001'}}
        for key in ['root','manifest','miniConfig','publicSocket','privateSocket','workspace','genesis','profileResult','initStoreResult','grainsRoot','spk']:self.c[key]=str(self.root/key)
        (self.root/'miniConfig').write_text('{}');(self.root/'spk').write_bytes(b'package')
        self.c['miniConfigSha256']=f.sha(self.c['miniConfig']);self.c['spkSha256']=f.sha(self.c['spk'])
        m={'sourceCommit':'a'*40,'sha256':{}}
        for role in ['host','mini','store','verifier','spkHost']:
            p=self.root/role;p.write_bytes(b'image');p.chmod(0o700);m[role]=str(p);m['sha256'][role]=f.sha(p)
        (self.root/'manifest').write_text(json.dumps(m))
        self.c['authority']={'owner':'70007','creator':'80008','creatorAccountCapability':'42042','factory':{'target':'10','capability':'55'},'tool':{'task':'7902','capability':'81','observeCapability':'82'},'parent':{'task':'7901','capability':'73','observeCapability':'74'},'template':{'issuer':'5','ownerBudget':'10000','lifetime':'10000'},'tariff':{'base':'2','perBirth':'1'}}
        names=['app','packageManifest','snapshotManifest','appOwnerCapability','appControlCapability','packageOwnerCapability','packageControlCapability','snapshotOwnerCapability','snapshotControlCapability']
        self.c['application']={key:str(500001+index*7) for index,key in enumerate(names)}
        self.c['keys']={}
        for subject in ['70007','80008','123123','987987']:
            seed=self.root/(subject+'.key');seed.write_bytes(bytes(32));seed.chmod(0o600);public=self.root/(subject+'.pub');public.write_bytes(bytes(32))
            self.c['keys'][subject]={'keyId':str(int(subject)+1000000),'keyEpoch':'11','seedPath':str(seed),'publicKeyPath':str(public)}
        fields=['session','descriptor','cap','sessionControlCapability','descriptorOwnerCapability','descriptorControlCapability','ticket','appObserve','pkgObserve','ticketOwner','ticketControl','ticketObserve']
        self.c['delegates']={label:dict({key:str(100000+index*1000+offset*13) for offset,key in enumerate(fields)},subject=subject,expectedHost=label+'.localhost:18450') for index,(label,subject) in enumerate([('member-one','123123'),('member-two','987987')])}
    def validate(self):
        with patch.object(f,'protected_parent'):return app.validate(self.c)
    def test_arbitrary_members_descriptors_and_signing_epochs(self):
        _,artifacts=self.validate();self.assertEqual(len(artifacts),5);self.assertEqual(self.c['delegates']['member-two']['subject'],'987987')
    def test_joined_numeric_and_uppercase_member_keys_use_safe_bounded_routes(self):
        first,second=self.c['delegates'].values()
        self.c['delegates']={'1000':first,'MEMBER_1001':second}
        self.validate()
        names=[app.route_name(key) for key in self.c['delegates']]
        self.assertEqual(len(set(names)),2)
        self.assertTrue(all(len(name)==13 for name in names))
        self.assertEqual(app.route_name('1000'),names[0])
        self.c['delegates']={'A'*64:first,'1001':second};self.validate()
        self.assertLessEqual(len(app.route_name('A'*64)),32)
    def test_actual_fixture_route_socket_paths_fit_before_source_writes(self):
        self.c['grainsRoot']='/var/lib/minidregg/pv1-20261002-a2/grains'
        self.validate()
        self.c['application']['app']='18446744073709551615'
        with self.assertRaisesRegex(RuntimeError,'socket pathname exceeds bound'):self.validate()
    def test_overlapping_sessions_caps_or_unknown_signer_refuse(self):
        original=copy.deepcopy(self.c)
        self.c['delegates']['member-two']['descriptor']=self.c['application']['app']
        with self.assertRaisesRegex(RuntimeError,'overlap'):self.validate()
        self.c=original;self.c['delegates']['member-two']['ticketObserve']=self.c['application']['appOwnerCapability']
        with self.assertRaisesRegex(RuntimeError,'overlap'):self.validate()
        self.c=copy.deepcopy(original);self.c['delegates']['member-two']['subject']='555555'
        with self.assertRaisesRegex(RuntimeError,'signer'):self.validate()
    def test_pin_changes_refuse_before_provisioning(self):
        (self.root/'spk').write_bytes(b'changed')
        with self.assertRaisesRegex(RuntimeError,'package pin'):self.validate()
    def test_explicit_lifecycle_input_binds_owner_world_host_and_key(self):
        workspace=self.root/'owner-ws';workspace.mkdir();(workspace/'workspace.json').write_text(json.dumps({'subject':'70007','config':self.c['miniConfig'],'socket':self.c['publicSocket'],'key':self.c['keys']['70007']['seedPath'],'host':str(self.root/'host')}))
        self.c['lifecycleDelegation']={'ownerWorkspace':str(workspace),'manager':'80008','requestId':'hosting-1'}
        self.validate()
        self.c['lifecycleDelegation']['requestId']='bad/path'
        with self.assertRaisesRegex(RuntimeError,'request ID'):self.validate()
        self.c['lifecycleDelegation']['requestId']='hosting-1'
        pin=f.load(workspace/'workspace.json');pin['subject']='80008';(workspace/'workspace.json').write_text(json.dumps(pin))
        with self.assertRaisesRegex(RuntimeError,'different owner/world'):self.validate()
    def test_owner_workflow_imports_roots_and_uses_own_source_cli(self):
        workspace=self.root/'owner-ws';workspace.mkdir();(workspace/'refs').mkdir()
        self.c['lifecycleDelegation']={'ownerWorkspace':str(workspace),'manager':'80008','requestId':'hosting-1'}
        x=Mock();x.app=self.c['application']['app'];x.owner='70007';x.m={'mini':{'path':'/pinned/mini'}}
        source=self.root/'birth-source.json';source.write_text('{}');receipt=self.root/'birth-receipt.json';receipt.write_text('{}');x.f={'applicationSource':str(source),'applicationReceipt':str(receipt)}
        counter=iter(range(30));x.fresh.side_effect=lambda name:self.root/(str(next(counter))+'-'+name)
        selector=self.root/'selector.json';selector.write_text(json.dumps({'appOwner':'70007','managementSubject':'80008','selector':{k:self.c['application'][k] for k in ['app','packageManifest','snapshotManifest']}}))
        phases=['app-policy','package-policy','snapshot-policy','app-grant','package-grant','snapshot-grant'];calls=[];index=0
        def run(args):
            nonlocal index
            calls.append(args)
            result={'type':'mini-member-app-lifecycle-result-v1','owner':'70007','manager':'80008','complete':False,'phase':phases[index]}
            if '--op' in args and args[args.index('--op')+1]=='submit':
                index+=1
                result.update(complete=index==6)
                if index<6:result['phase']=phases[index]
                else:result['managementSelector']=str(selector)
            out=self.root/('reply-'+str(len(calls))+'.json');out.write_text(json.dumps(result));return 0,out,None
        x.run.side_effect=run
        self.assertEqual(app.delegate_lifecycle(x,self.c),selector)
        self.assertEqual(len([a for a in calls if 'import' in a]),3)
        self.assertEqual(len([a for a in calls if 'app-lifecycle' in a]),12)
        self.assertTrue(all(a[a.index('--dir')+1]==workspace for a in calls))
        self.assertFalse(any('--key' in a or '--socket' in a for a in calls))
        self.assertEqual(x.f['lifecycleDelegation']['selectorSha256'],f.sha(selector))
    def test_dormant_or_held_tasks_refuse_before_reserving(self):
        x=Mock();x.creator='80008';x.parent=self.c['authority']['parent'];x.tool=self.c['authority']['tool'];x.f={}
        def read(generation,status,reserved):
            return dict(dir=self.root/'query',view=dict(cell=dict(grain=dict(generation=generation,status=status,reserved=reserved,remaining='20'))))
        for parent,tool in [(read('0','0','0'),read('0','0','0')),(read('1','4','1'),read('1','4','3'))]:
            x.query.side_effect=[parent,tool]
            with self.assertRaisesRegex(RuntimeError,'birth (parent|tool)'):app.check_task_readiness(x)
            x.reserve.assert_not_called();x.submit.assert_not_called()
        x.query.side_effect=[read('1','4','1'),read('1','2','0')]
        app.check_task_readiness(x)
        self.assertEqual(x.f['taskReadiness']['parent'],str(self.root/'query'))
    def test_birth_distinguishes_sponsor_and_app_owner_and_task_observation_caps(self):
        x=Mock();x.owner='70007';x.creator='80008';x.accountcap='42042';x.authority=self.c['authority'];x.tool=x.authority['tool'];x.parent=x.authority['parent'];x.f={'application':self.c['application']};x.genesis=self.root/'genesis';x.genesis.write_text('{}');x.n.return_value='9000001';x.key.side_effect=lambda subject:self.root/(subject+'.key')
        calls=[]
        def query(subject,target,cap):
            reserved=True
            return dict(dir=self.root/('query-'+target),view=dict(cell=dict(root='42',grain=dict(generation='2',status='3' if reserved else '2',remaining='10',reserved='5' if reserved else '0'))))
        x.query.side_effect=query
        counter=iter(range(10));x.fresh.side_effect=lambda name:self.root/(str(next(counter))+'-'+name)
        def mini(*args):
            calls.append(args)
            if args[0]=='current-application-intent':
                source=Path(args[2]);author=Path(args[4]);author.mkdir();(author/'source.json').write_bytes(source.read_bytes())
            else:
                attempt=Path(args[-1]);attempt.mkdir();(attempt/'outcome.json').write_text('{"type":"confirmed","confirmation":"installed"}')
        x.mini.side_effect=mini;app.birth_app(x)
        source=f.load(x.f['applicationSource']);spec=source['applicationGrainBirth']['applicationBirth']
        self.assertEqual((source['subject'],spec['creator'],spec['feePayer'],spec['application']['owner']),('80008','80008','80008','70007'))
        self.assertEqual(source['applicationGrainBirth']['tool']['observeCapability'],'82')
        self.assertEqual([call.args for call in x.query.call_args_list],[('80008','7902','82'),('80008','7901','74')])
        # The reservation is a separate retained step; birth authors one effect.
        x.reserve.assert_not_called();self.assertEqual(app.app_reserve(x),5)
        self.assertEqual(calls[-1][-3],self.root/'80008.key')

class Ledger:
    """The retained state a Fixture step needs, without a native world."""
    step=f.Fixture.step;settle=f.Fixture.settle
    def __init__(self,root):
        self.root=root;self.f={};self.serial=0;self.states=0;self.enter()
    def enter(self):
        self.opdir=self.root/('hooks-'+str(self.states)+'-'+str(self.serial));self.opdir.mkdir()
    def fresh(self,name):
        self.serial+=1;return self.opdir/(str(self.serial)+'-'+name)
    def write_state(self):self.states+=1

class StepTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.x=Ledger(Path(self.tmp.name))
    def boom(self):raise RuntimeError('native command failed')
    def test_completed_step_never_repeats_and_state_is_retained_around_the_effect(self):
        effect=Mock()
        self.assertTrue(self.x.step('app:birth',effect));before=self.x.states
        self.assertFalse(self.x.step('app:birth',effect));effect.assert_called_once()
        self.assertEqual((self.x.f['steps']['done'],self.x.f['steps']['pending'],before),(['app:birth'],None,2))
    def test_interrupted_effect_fences_every_later_step_and_its_own_reauthoring(self):
        with self.assertRaises(RuntimeError):self.x.step('member:a:session',self.boom)
        later=Mock();self.x.enter()
        for name in ['member:a:session','member:a:ticket']:
            with self.assertRaisesRegex(RuntimeError,'member:a:session is unsettled'):self.x.step(name,later)
        later.assert_not_called()
    def test_native_journaled_step_reenters_only_itself(self):
        with self.assertRaises(RuntimeError):self.x.step('install',self.boom,reentrant=True)
        self.x.enter();other=Mock()
        with self.assertRaisesRegex(RuntimeError,'install is unsettled'):self.x.step('start',other,reentrant=True)
        with self.assertRaisesRegex(RuntimeError,'install is unsettled'):self.x.step('install',other)
        self.assertTrue(self.x.step('install',other,reentrant=True));other.assert_called_once()
        self.assertEqual(len(set(self.x.f['steps'].get('pending') or [])),0)
    def test_absent_settlement_needs_this_steps_retained_evidence_then_reauthors(self):
        with self.assertRaises(RuntimeError):self.x.step('member:a:session',self.boom)
        stderr=self.x.opdir/'refusal.stderr';stderr.write_text('source refused: stale witness')
        foreign=self.x.root/'elsewhere.txt';foreign.write_text('x')
        with self.assertRaisesRegex(RuntimeError,'another step'):self.x.settle('member:a:session','absent',foreign,'refused')
        with self.assertRaisesRegex(RuntimeError,'no such unsettled'):self.x.settle('member:b:session','absent',stderr,'refused')
        record=self.x.settle('member:a:session','absent',stderr,'definite source refusal before admission')
        self.assertEqual((record['disposition'],record['evidenceSha256']),('absent',f.sha(stderr)))
        effect=Mock();self.assertTrue(self.x.step('member:a:session',effect));effect.assert_called_once()
    def test_confirmed_settlement_is_only_for_resultless_effects_with_native_confirmation(self):
        with self.assertRaises(RuntimeError):self.x.step('member:a:session',self.boom)
        attempt=self.x.opdir/'attempt';attempt.mkdir();outcome=attempt/'outcome.json'
        outcome.write_text(json.dumps({'type':'confirmed','confirmation':'installed'}))
        with self.assertRaisesRegex(RuntimeError,'exact continuation'):self.x.settle('member:a:session','confirmed',outcome,'reply lost')
        self.x.settle('member:a:session','absent',outcome,'test reset')
        with self.assertRaises(RuntimeError):self.x.step('app:reserve',self.boom,effect_only=True)
        outcome.write_text(json.dumps({'type':'uncertain'}))
        with self.assertRaisesRegex(RuntimeError,'native confirmation'):self.x.settle('app:reserve','confirmed',outcome,'reply lost')
        outcome.write_text(json.dumps({'type':'confirmed','confirmation':'installed'}))
        self.x.settle('app:reserve','confirmed',outcome,'reply lost after admission')
        effect=Mock();self.assertFalse(self.x.step('app:reserve',effect,effect_only=True));effect.assert_not_called()

class AdapterPinTests(unittest.TestCase):
    def test_repaired_adapter_needs_an_explicit_successor_bound_to_its_lineage(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)/'root';root.mkdir(mode=0o700);source=Path(temp)/'adapter.py';source.write_text('one')
            f.save(root/'source-inputs.json',{str(source):f.sha(source)})
            with patch.object(f,'protected_parent'):
                with self.assertRaisesRegex(RuntimeError,'unchanged'):f.adopt_adapter(root,'no change')
                source.write_text('two')
                self.assertNotEqual(f.adapter_pins(root)[0][str(source)],f.sha(source))
                f.adopt_adapter(root,'ticket receipt repair')
                self.assertEqual(f.adapter_pins(root)[0][str(source)],f.sha(source))
                source.write_text('three');f.adopt_adapter(root,'second repair')
            self.assertEqual(f.adapter_pins(root)[2],3)
            first=root/'source-inputs-successor-01.json';record=f.load(first);record['reason']='edited';first.write_text(json.dumps(record))
            with self.assertRaisesRegex(RuntimeError,'lineage'):f.adapter_pins(root)

class RuntimeReadyTests(unittest.TestCase):
    def test_unready_broker_or_unowned_runtime_refuses_before_any_birth(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);state=root/'0123456789abcdef'/'host';state.mkdir(parents=True)
            pins={}
            for role in ['bwrap','spkHost']:
                image=root/role;image.write_bytes(role.encode());image.chmod(0o755);pins[role]=str(image);pins[role+'Sha256']=f.sha(image)
            profile=state/'grain-host.json';profile.write_text(json.dumps(pins))
            reply={'protocol':'mini-spk-runtime-status-v1','brokerProtocol':'mini-spk-broker-runtime-v1','store':'0123456789abcdef','state':'baseline','spkHost':pins['spkHost'],'spkHostSha256':pins['spkHostSha256']}
            x=Mock();x.profile=profile;x.state=state;x.m={'spkHost':{'path':pins['spkHost']}};x.f={}
            def run(args,timeout):
                out=root/'status.json';out.write_text(json.dumps(reply));return 0,out,None
            x.run.side_effect=run
            actual=os.lstat
            def owned(path):
                meta=actual(path);return os.stat_result((meta.st_mode,meta.st_ino,meta.st_dev,meta.st_nlink,0,meta.st_gid,meta.st_size,0,0,0))
            with self.assertRaisesRegex(RuntimeError,'outside root custody'):app.runtime_ready(x)
            x.run.assert_not_called()
            with patch.object(app.os,'lstat',owned):
                app.runtime_ready(x);self.assertEqual(x.run.call_args.args[0][1:3],['grain','runtime-status'])
                for field,value in [('state','adopting'),('spkHostSha256','0'*64),('store','fedcba9876543210')]:
                    good=reply[field];reply[field]=value
                    with self.assertRaisesRegex(RuntimeError,'no app was born'):app.runtime_ready(x)
                    reply[field]=good

class ConfirmedTicketTests(unittest.TestCase):
    def retained(self,attempt,source):
        outcome={'type':'confirmed','confirmation':'installed','eventId':'22','transactionId':'33','acceptedCount':'112','worldRoot':'44'}
        (attempt/(source+'.outcome.bin')).write_bytes(b'\x01exact-reply');(attempt/(source+'.outcome.json')).write_text(json.dumps(outcome))
        anchor={'type':'minidregg-grain-share-issue-receipt-anchor-v1','source':source,'outcomeSha256':f.sha(attempt/(source+'.outcome.bin')),
            'receipt':{k:outcome[k] for k in ('eventId','transactionId','acceptedCount','worldRoot')}}
        (attempt/'receipt-anchor.json').write_text(json.dumps(anchor));return outcome,anchor
    def test_native_submit_or_exact_lookup_confirmation_continues_without_another_lookup(self):
        for source in ['submit','lookup-0000']:
            with tempfile.TemporaryDirectory() as temp:
                attempt=Path(temp);outcome,anchor=self.retained(attempt,source)
                self.assertEqual(f.confirmed_issue_receipt(attempt),anchor['receipt'])
    def test_anchor_binds_exact_reply_bytes_not_their_presentation(self):
        with tempfile.TemporaryDirectory() as temp:
            attempt=Path(temp);outcome,anchor=self.retained(attempt,'submit')
            # The native anchor hashes the retained reply bytes; the JSON beside
            # it is a Host presentation and has a different digest.
            self.assertNotEqual(anchor['outcomeSha256'],f.sha(attempt/'submit.outcome.json'))
            (attempt/'submit.outcome.bin').write_bytes(b'other reply')
            with self.assertRaisesRegex(RuntimeError,'differs'):f.confirmed_issue_receipt(attempt)
    def test_unconfirmed_changed_or_foreign_anchor_refuses(self):
        for change in [lambda o,a:o.update(type='uncertain'),lambda o,a:o.update(confirmation='unknown'),lambda o,a:a['receipt'].update(acceptedCount='999'),
                       lambda o,a:a.update(source='../submit'),lambda o,a:a.update(type='other'),lambda o,a:a['receipt'].pop('worldRoot')]:
            with tempfile.TemporaryDirectory() as temp:
                attempt=Path(temp);outcome,anchor=self.retained(attempt,'submit');change(outcome,anchor)
                (attempt/'submit.outcome.json').write_text(json.dumps(outcome));(attempt/'receipt-anchor.json').write_text(json.dumps(anchor))
                with self.assertRaises(RuntimeError):f.confirmed_issue_receipt(attempt)
if __name__=='__main__':unittest.main()
