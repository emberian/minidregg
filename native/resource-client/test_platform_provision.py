"""Provisioning contract checks; these do not claim native enrollment evidence."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

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
        manifest={role:str(binary) for role in ('mini','host','store','verifier')}
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
    def test_selected_names_map_to_actual_subjects_and_keep_concurrency(self):
        self.plan['workload']={'members':['member-0','member-1'],'concurrency':8}
        p.validate(self.plan)
        allocated=p.allocated_workload(self.plan, {'member-'+str(i):str(9010+i*100) for i in range(5)})
        self.assertEqual(allocated, {'workload':{'members':['9010','9110'],'concurrency':8}})
        self.assertEqual(self.plan['workload']['members'],['member-0','member-1'])
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
