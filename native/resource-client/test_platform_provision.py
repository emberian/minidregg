"""Provisioning contract checks; these do not claim native enrollment evidence."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import pwd
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('provision', Path(__file__).with_name('platform-provision.py'))
p = importlib.util.module_from_spec(spec); spec.loader.exec_module(p)

class ProvisioningContract(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='platform-contract-')
        self.root = Path(self.temp.name)
        source = self.root / 'source'
        for relative in ('scripts/workroom/provision.sh', 'deploy/shell/mini-shell-ssh', 'deploy/shell/render-shell-key'):
            path=source / relative;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('WORKROOM_OPERATOR_POLICY\n')
        binary=self.root/'binary';binary.write_text('contract fixture, never launched');binary.chmod(0o700)
        manifest={role:str(binary) for role in ('mini','host','store','verifier','payWatcher')}
        manifest['sha256']={role:p.digest(binary) for role in manifest}
        p.save(self.root/'manifest.json',manifest)
        self.plan={'type':'mini-platform-provision-v1','root':str(self.root/'world'),'sourceRepo':str(source),
                   'manifest':str(self.root/'manifest.json'),'manifestSha256':p.digest(self.root/'manifest.json'),
                   'members':[{'name':'member-'+str(i)} for i in range(5)],'sshPort':19201,
                   'rooms':{'all':{'owner':'member-0','members':['member-'+str(i) for i in range(5)]}}}
    def tearDown(self): self.temp.cleanup()
    def test_arbitrary_inventory_and_groups(self):
        root,_,_=p.validate(self.plan)
        self.assertFalse(root.exists())
        self.assertEqual(len(self.plan['members']),5)
    def test_prepared_private_root_and_explicit_node(self):
        root=Path(self.plan['root']);root.mkdir(mode=0o700)
        self.plan.update(preparedEmptyRoot=True,nodeDirectory='node')
        self.assertEqual(p.root_layout(self.plan),(root,root/'node'))
        p.validate(self.plan)
        self.assertEqual(list(root.iterdir()),[])
        (root/'retained').write_text('an earlier receiving attempt')
        with self.assertRaisesRegex(ValueError,'must be empty'):p.validate(self.plan)
        self.assertEqual((root/'retained').read_text(),'an earlier receiving attempt')
    def test_prepared_root_refuses_public_or_symlink_custody(self):
        root=Path(self.plan['root']);root.mkdir(mode=0o755)
        self.plan['preparedEmptyRoot']=True
        with self.assertRaisesRegex(ValueError,'private'):p.validate(self.plan)
        root.chmod(0o700)
        link=self.root/'linked';link.symlink_to(root)
        plan=dict(self.plan,root=str(link))
        with self.assertRaisesRegex(ValueError,'canonical'):p.validate(plan)
        with self.assertRaisesRegex(ValueError,'fresh provisioning'):p.validate(dict(self.plan,preparedEmptyRoot=False))
        with self.assertRaisesRegex(ValueError,'boolean'):p.validate(dict(self.plan,preparedEmptyRoot='true'))
    def test_node_directory_cannot_escape_or_replace_custody(self):
        for name in ('../other','a/b','sock','custody','hooks'):
            with self.assertRaisesRegex(ValueError,'nodeDirectory'):p.validate(dict(self.plan,nodeDirectory=name))
        self.assertFalse(Path(self.plan['root']).exists())
    def test_selected_ssh_launcher_requires_exact_source_and_root_custody(self):
        executable=Path('/usr/bin/true').resolve()
        source=Path(self.plan['sourceRepo'])/'deploy/shell/mini-shell-ssh'
        source.write_bytes(executable.read_bytes())
        plan=dict(self.plan,sshLauncher={'path':str(executable),'sha256':p.digest(executable)})
        p.validate(plan)
        copied=self.root/'launcher';copied.write_bytes(executable.read_bytes());copied.chmod(0o700)
        with self.assertRaisesRegex(ValueError,'root-owned custody'):
            p.validate(dict(plan,sshLauncher={'path':str(copied),'sha256':p.digest(copied)}))
        source.write_text('changed source')
        with self.assertRaisesRegex(ValueError,'pinned source renderer'):p.validate(plan)
    def test_selected_names_map_to_actual_subjects_and_keep_concurrency(self):
        self.plan['workload']={'members':['member-0','member-1'],'concurrency':8}
        p.validate(self.plan)
        allocated=p.allocated_workload(self.plan, {'member-'+str(i):str(9010+i*100) for i in range(5)})
        self.assertEqual(allocated, {'workload':{'members':['9010','9110'],'concurrency':8}})
        self.assertEqual(self.plan['workload']['members'],['member-0','member-1'])
    def test_paid_entry_requires_separate_noncolliding_genesis_observer(self):
        observer=dict(subject='30',keyId='7030',account='130',spendCapability='1030',controlCapability='2030',factoryObserveCapability='3030',capability='4030',payControlCapability='4031',enrolCapability='4032')
        self.plan['members'][0]['entry']='paid'
        with self.assertRaisesRegex(ValueError,'separate genesis pay observer'):p.validate(self.plan)
        self.plan['payObserver']=observer
        adapter=self.root/'adapter.py';adapter.write_text('synthetic source adapter never launched')
        self.plan['paidEntryAdapter']={'path':str(adapter),'sha256':p.digest(adapter)}
        recipe=Path(self.plan['sourceRepo'])/'scripts/workroom/provision.sh';recipe.write_text('WORKROOM_OPERATOR_POLICY WORKROOM_PAY_OBSERVER')
        p.validate(self.plan)
        self.assertFalse((self.root/'world').exists())
        for field,value in [('subject','7'),('capability','4031'),('keyId','07030')]:
            plan=copy.deepcopy(self.plan);plan['payObserver'][field]=value
            with self.assertRaises(ValueError):p.validate(plan)
        adapter.write_text('changed')
        with self.assertRaisesRegex(ValueError,'adapter changed'):p.validate(self.plan)
    def test_preflight_refuses_group_and_allocation_errors(self):
        for mutate in (lambda x:x['members'].append(x['members'][0]),
                       lambda x:x['rooms']['all'].update(owner='missing'),
                       lambda x:x.update(parentTask='7902',toolTask=7902),
                       lambda x:x.update(sponsorBalance=500),
                       lambda x:x.update(operatorPolicy={'storageRoot':'elsewhere'})):
            plan=copy.deepcopy(self.plan);mutate(plan)
            with self.assertRaises(ValueError):p.validate(plan)
        self.assertFalse((self.root/'world').exists())
    def test_pin_change_refused_before_launch(self):
        (self.root/'binary').write_text('changed')
        with self.assertRaises(ValueError):p.validate(self.plan)
    def test_boundary_reference_must_match_exact_document(self):
        m=importlib.util.spec_from_file_location('boundary',Path(__file__).with_name('platform-native-hooks.py'))
        boundary=importlib.util.module_from_spec(m);m.loader.exec_module(boundary)
        refs={'references':[{'target':'100','observeCapability':'20'},{'target':'101','observeCapability':'21'}]}
        self.assertEqual(boundary.foreign_reference(refs,'101')['observeCapability'],'21')
        with self.assertRaises(ValueError):boundary.foreign_reference(refs,'102')
    def test_boundary_requires_exact_host_no_grant_outcome(self):
        m=importlib.util.spec_from_file_location('boundary',Path(__file__).with_name('platform-native-hooks.py'))
        boundary=importlib.util.module_from_spec(m);m.loader.exec_module(boundary)
        outcome={'type':'refused','reason':'no-grant','phase':'observation'.encode().hex()}
        line=('  outcome (decoded by the Host): '+json.dumps(outcome)+'\n').encode()
        result=lambda rc=3,out=b'',err=line:subprocess.CompletedProcess([],rc,out,err)
        self.assertEqual(boundary.native_refusal(result()),outcome)
        self.assertEqual(boundary.native_refusal(result(out=json.dumps(outcome).encode())),outcome)
        for invalid in (result(rc=1),result(err=b'undisclosed\n'),result(err=line+line),
                        result(out=b'{"type":"refused","reason":"stale-root"}')):
            with self.assertRaises(ValueError):boundary.native_refusal(invalid)
    def test_hook_bundle_retains_independent_pinned_copies(self):
        run=self.root/'hooks-test';run.mkdir()
        retained=p.retain_hooks(run)
        for name in ('platform-provision.py','joined-member-journey.py','platform-native-hooks.py'):
            self.assertEqual(p.digest(retained/name),p.digest(p.HERE/name))
            self.assertTrue(os.access(retained/name,os.X_OK))
            source_pin=p.digest(p.HERE/name)
            self.assertNotEqual((retained/name).stat().st_ino,(p.HERE/name).stat().st_ino)
            (retained/name).write_bytes(b'local-copy-change')
            self.assertEqual(p.digest(p.HERE/name),source_pin)
    def test_command_retains_path_arguments(self):
        run=self.root/'commands';run.mkdir();(run/'logs').mkdir()
        world=p.World(run)
        self.assertEqual(world.run('path-argument',[Path(sys.executable),'-c','print("ok")']), 'ok\n')
        command=json.loads((run/'logs/0001-path-argument.command.json').read_text())
        self.assertEqual(command[0],str(Path(sys.executable)))
    def managed_plan(self):
        root=Path(self.plan['root']);root.mkdir(mode=0o700)
        units=self.root/'units';units.mkdir()
        return dict(self.plan,preparedEmptyRoot=True,nodeDirectory='node',sshd=str(Path('/usr/bin/true').resolve()),
                    serviceManager={'type':'systemd-system','systemctl':['/usr/bin/sudo','-n','/usr/bin/systemctl'],'unitDirectory':str(units),
                                    'units':{'operator':'world-store.service','public':'world-ingress.service','sshd':'world-sshd.service'}}),units
    def test_service_units_are_a_function_of_the_plan(self):
        plan,_=self.managed_plan();root=Path(plan['root']);binary=str(self.root/'binary')
        rendered=p.rendered_units(plan,p.load(self.root/'manifest.json'))
        self.assertEqual(set(rendered),{'world-store.service','world-ingress.service','world-sshd.service'})
        words=lambda *argv:'ExecStart='+' '.join(json.dumps(str(word)) for word in argv)+'\n'
        store,ingress,entrance=(rendered['world-'+name+'.service'] for name in ('store','ingress','sshd'))
        self.assertIn(words(binary,'serve-operator','--host',binary,'--config',root/'node/deployment/pinned-config.json','--socket',root/'sock/operator.sock'),store)
        self.assertIn(words(binary,'serve-public-proxy','--socket',root/'sock/public.sock','--upstream',root/'sock/operator.sock','--config',root/'node/deployment/pinned-config.json'),ingress)
        self.assertIn(words(plan['sshd'],'-D','-e','-f',root/'ssh/sshd_config'),entrance)
        for text in rendered.values():
            self.assertIn('User='+pwd.getpwuid(os.getuid()).pw_name+'\n',text)
            self.assertIn('WorkingDirectory='+str(root)+'\n',text)
            # The single-socket public `serve` is never a published topology.
            self.assertNotIn('"serve"',text)
        # Rendering publishes and creates nothing.
        self.assertEqual(list(root.iterdir()),[])
    def test_unpublished_or_different_units_refuse_before_genesis(self):
        plan,units=self.managed_plan();manifest=p.load(self.root/'manifest.json')
        shown={'LoadState':'loaded','ActiveState':'inactive','MainPID':'0','DropInPaths':'','NeedDaemonReload':'no'}
        show=lambda name:dict(shown,FragmentPath=str(units/name))
        exact=p.rendered_units(plan,manifest)
        with patch.object(p,'root_custody'),patch.object(p,'systemd_show',side_effect=show):
            with self.assertRaisesRegex(ValueError,'not published'):p.validate(plan)
            p.validate(plan,published=False)
            for name,text in exact.items():(units/name).write_text(text)
            p.validate(plan)
            # A descriptor naming the private pair while a public serve runs is refused here.
            (units/'world-store.service').write_text(exact['world-store.service'].replace('serve-operator','serve'))
            with self.assertRaisesRegex(ValueError,'differs from this plan'):p.validate(plan)
            (units/'world-store.service').write_text(exact['world-store.service'])
            for change,message in (({'ActiveState':'active','MainPID':'77'},'already running'),
                                   ({'DropInPaths':'/etc/systemd/system/world-store.service.d/x.conf'},'exactly the published unit'),
                                   ({'NeedDaemonReload':'yes'},'exactly the published unit'),({'LoadState':'not-found'},'exactly the published unit')):
                saved=dict(shown);shown.update(change)
                with self.assertRaisesRegex(ValueError,message):p.validate(plan)
                shown.clear();shown.update(saved)
            p.validate(plan)
        with patch.object(p,'systemd_show',side_effect=show):
            with self.assertRaisesRegex(ValueError,'root-owned custody'):p.validate(plan)
        self.assertEqual(list(Path(plan['root']).iterdir()),[])
    def test_invalid_service_manager_declarations_refuse(self):
        plan,_=self.managed_plan()
        p.validate(plan,published=False)
        for mutate in (lambda m:m.update(type='systemd-user'),lambda m:m.update(systemctl=['systemctl']),
                       lambda m:m.update(systemctl=['/usr/bin/sudo','/bin/sh']),lambda m:m.update(systemctl=[]),
                       lambda m:m['units'].update(public=m['units']['operator']),lambda m:m['units'].pop('sshd'),
                       lambda m:m['units'].update(operator='../x.service'),lambda m:m.update(unitDirectory='etc/systemd/system'),
                       lambda m:m.update(extra=True)):
            changed=copy.deepcopy(plan);mutate(changed['serviceManager'])
            with self.assertRaises(ValueError):p.validate(changed,published=False)
    @unittest.skipUnless(Path('/proc').exists(),'Linux process identity')
    def test_managed_service_starts_and_stops_only_through_its_unit(self):
        run=self.root/'managed';run.mkdir();(run/'logs').mkdir()
        world=p.World(run)
        world.state['serviceManager']={'type':'systemd-system','systemctl':['/usr/bin/sudo','-n','/usr/bin/systemctl'],'unitDirectory':'/etc/systemd/system',
                                       'units':{'operator':'w-store.service','public':'w-ingress.service','sshd':'w-sshd.service'}}
        calls=[];unit={'ActiveState':'inactive','MainPID':'0','InvocationID':''};starts=True
        def control(label,argv,env=None):
            calls.append([str(word) for word in argv])
            if argv[-2]=='start' and starts:unit.update(ActiveState='active',MainPID=str(os.getpid()),InvocationID='first')
            if argv[-2]=='stop':unit.update(ActiveState='inactive',MainPID='0')
            return ''
        with patch.object(world,'run',side_effect=control),patch.object(p,'systemd_show',side_effect=lambda name:dict(unit)):
            world.spawn('operator',['mini','serve-operator'],lambda:True)
            retained=world.state['services']['operator']
            self.assertEqual((retained['unit'],retained['manager'],retained['pid'],retained['invocationId']),('w-store.service','systemd-system',os.getpid(),'first'))
            self.assertEqual(calls,[['/usr/bin/sudo','-n','/usr/bin/systemctl','start','w-store.service']])
            # No child of this constructor exists to be signalled later.
            self.assertEqual(world.children,{})
            self.assertEqual(json.loads((run/'runtime.json').read_text())['services']['operator']['unit'],'w-store.service')
            retained['unit']='other.service'
            with self.assertRaisesRegex(ValueError,'does not declare'):world.stop(['operator'])
            self.assertEqual(len(calls),1)
            retained['unit']='w-store.service'
            world.stop(['operator'])
            self.assertEqual(calls[-1],['/usr/bin/sudo','-n','/usr/bin/systemctl','stop','w-store.service'])
            self.assertNotIn('operator',world.state['services'])
            starts=False
            with self.assertRaisesRegex(ValueError,'did not stay active'):world.spawn('public',['mini','serve-public-proxy'],lambda:True)
            self.assertNotIn('public',world.state['services'])
    def test_managed_world_emits_no_owned_process_restart_hook(self):
        hooks=self.root/'retained-hooks';hooks.mkdir()
        for name in ('platform-provision.py','platform-native-hooks.py'):(hooks/name).write_text(name)
        self.assertEqual(set(p.journey_hooks(hooks,self.root,True)),{'group-boundary'})
        self.assertEqual(set(p.journey_hooks(hooks,self.root,False)),{'group-boundary','restart'})
    @unittest.skipUnless(Path('/proc').exists(),'Linux owned process groups')
    def test_owned_process_stop_and_pid_reuse_refusal(self):
        run=self.root/'runtime';run.mkdir();(run/'logs').mkdir()
        world=p.World(run)
        ready=run/'ready'
        world.spawn('fixture',[sys.executable,'-c',"from pathlib import Path; import time; Path("+repr(str(ready))+").touch(); time.sleep(60)"],ready.exists)
        pid=world.state['services']['fixture']['pid']
        retained=copy.deepcopy(world.state['services']['fixture'])
        world.state['services']['fixture']['startTicks']='impossible'
        with self.assertRaises(ValueError):world.stop(['fixture'])
        os.kill(pid,0)
        world.state['services']['fixture']=retained
        world.stop(['fixture'])
        self.assertNotIn('fixture',world.state['services'])

if __name__=='__main__':unittest.main()
