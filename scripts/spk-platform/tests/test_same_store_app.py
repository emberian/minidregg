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
    def test_birth_distinguishes_sponsor_and_app_owner_and_task_observation_caps(self):
        x=Mock();x.owner='70007';x.creator='80008';x.accountcap='42042';x.authority=self.c['authority'];x.tool=x.authority['tool'];x.parent=x.authority['parent'];x.f={'application':self.c['application']};x.genesis=self.root/'genesis';x.genesis.write_text('{}');x.n.return_value='9000001';x.key.side_effect=lambda subject:self.root/(subject+'.key')
        calls=[];x.query.side_effect=lambda *args:dict(view=dict(cell=dict(root='42',grain=dict(generation='2',status='3',remaining='10',reserved='5'))))
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
        self.assertEqual(x.query.call_args_list[0].args,('80008','7902','82'))
        self.assertEqual(calls[-1][-3],self.root/'80008.key')
if __name__=='__main__':unittest.main()
