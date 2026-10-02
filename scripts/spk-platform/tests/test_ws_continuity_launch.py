#!/usr/bin/env python3
"""Root-driver staging logic only; no service, native candidate or root mutation."""
import importlib.util
import io
import json
import os
from pathlib import Path
import pwd
import stat
import tarfile
import tempfile
import unittest
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('launch',Path(__file__).resolve().parents[1]/'ws-continuity-launch.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class MaterializationTests(unittest.TestCase):
    def fixture(self,root,unsafe=False):
        revision='a'*40
        account=pwd.getpwuid(os.getuid())
        package=root/'ethercalc.spk';package.write_bytes(b'synthetic signed-package placeholder; not native qualification')
        plan={'root':str(root),'state':'dependencies-staged-no-candidate-no-services','fixtureRoot':str(root/'operator/new-run'),
              'grainsRoot':str(root/'grains'),'appPrefix':'47','app':'4701',
              'assets':{'ethercalc.spk':{'path':str(package),'sha256':m.sha(package)}},
              'operator':{'name':account.pw_name,'uid':account.pw_uid,'gid':account.pw_gid},
              'brokerConfigTemplate':{'grainsRoot':str(root/'grains'),'brokerSocket':str(root/'grains/broker.sock')}}
        plan_path=root/'plan.json';m.save(plan_path,plan)
        manifest={'sourceCommit':revision,'sourcePath':str(root/'source'),'spkHostFeatures':['integration-qualification'],'sha256':{}}
        for role,name in m.ROLES.items():
            file=root/name;file.write_bytes(('synthetic '+role).encode());file.chmod(0o700)
            manifest[role]=str(file);manifest['sha256'][role]=m.sha(file)
        manifest_path=root/'original.json';m.save(manifest_path,manifest)
        archive=io.BytesIO()
        with tarfile.open(fileobj=archive,mode='w') as tar:
            for directory in ['scripts','scripts/spk-platform']:
                info=tarfile.TarInfo(directory);info.type=tarfile.DIRTYPE;tar.addfile(info)
            for name in ['ws-continuity-fixture.py','ws-continuity-journey.py','ws-continuity-supervision.py','ws-continuity-regressions.py','ws-continuity-launch.py']:
                content=b'# synthetic source, never executed\n';info=tarfile.TarInfo('scripts/spk-platform/'+name);info.size=len(content);tar.addfile(info,io.BytesIO(content))
            if unsafe:
                info=tarfile.TarInfo('scripts/escape');info.type=tarfile.SYMTYPE;info.linkname='/outside';tar.addfile(info)
        return plan_path,manifest_path,revision,archive.getvalue()

    def test_exact_source_and_binary_pins_survive_staging(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);plan,manifest,revision,archive=self.fixture(root)
            original=manifest.read_bytes()
            with patch.object(m,'root_file',side_effect=Path),patch.object(m.subprocess,'check_output',side_effect=[revision+'\n',archive]):
                result=m.materialize(plan,manifest,revision)
            self.assertFalse(result['launched'])
            ready=m.load(result['ready']);staged=m.load(ready['manifest'])
            self.assertEqual(staged['sourceCommit'],revision)
            self.assertEqual(staged['sourcePath'],str(root/'source'))
            self.assertEqual(Path(staged['originalManifest']).read_bytes(),original)
            for role in m.ROLES:
                self.assertEqual(m.sha(staged[role]),staged['sha256'][role])
            self.assertEqual(m.load(ready['fixtureInput'])['delegateHosts'],{'a':'a.localhost:18447','b':'b.localhost:18448'})
            self.assertNotIn('sealSupervisor',m.load(ready['fixtureInput']))
            self.assertFalse((root/'operator/new-run').exists())

    def test_changed_binary_refuses_before_capsule_creation(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);plan,manifest,revision,_=self.fixture(root)
            Path(m.load(manifest)['spkHost']).write_bytes(b'changed')
            with patch.object(m,'root_file',side_effect=Path),self.assertRaisesRegex(RuntimeError,'artifact/hash'):
                m.materialize(plan,manifest,revision)
            self.assertFalse((root/('candidate-'+revision[:12])).exists())

    def test_source_archive_symlink_refused_and_partial_capsule_retained(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);plan,manifest,revision,archive=self.fixture(root,unsafe=True)
            with patch.object(m,'root_file',side_effect=Path),patch.object(m.subprocess,'check_output',side_effect=[revision+'\n',archive]),self.assertRaisesRegex(RuntimeError,'regular tracked scripts'):
                m.materialize(plan,manifest,revision)
            capsule=root/('candidate-'+revision[:12])
            self.assertTrue(capsule.exists());self.assertFalse((capsule/'ready.json').exists())
            self.assertFalse((capsule/'source/scripts/escape').exists())


class CustodyTests(unittest.TestCase):
    def test_wrong_fixture_root_or_state_refused(self):
        expected={'root':'/fixture/run','grainsRoot':'/fixture/grains','brokerSocket':'/fixture/grains/broker.sock'}
        f=dict(schema='spk-ws-continuity-fixture-v1',**expected,app='4701',generation='4',
               state='/fixture/grains/abcdef0123456789/host',profilePath='/fixture/grains/abcdef0123456789/host/grain-host.json')
        m.fixture_coordinates(f,expected,{'app':'4701'})
        for key,value in [('root','/other/run'),('state','/other/grains/abcdef0123456789/host'),('generation','04')]:
            with self.assertRaises(RuntimeError): m.fixture_coordinates(dict(f,**{key:value}),expected,{'app':'4701'})

    def test_route_symlink_and_outside_path_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);route=root/'route';route.mkdir(mode=0o700)
            token=route/'browser.token';token.write_text('synthetic');token.chmod(0o600)
            m.operator_custody(token,root,os.getuid(),'file')
            alias=root/'alias';alias.symlink_to(route)
            with self.assertRaisesRegex(RuntimeError,'custody differs'):
                m.operator_custody(alias/'browser.token',root,os.getuid(),'file')
            with self.assertRaisesRegex(RuntimeError,'escapes'):
                m.operator_custody(token,root/'other',os.getuid(),'file')

    def test_override_request_save_syncs_file_and_parent(self):
        with tempfile.TemporaryDirectory() as temp:
            kinds=[];original=os.fsync
            def synced(fd): kinds.append(stat.S_ISDIR(os.fstat(fd).st_mode));original(fd)
            with patch.object(m.os,'fsync',side_effect=synced):
                m.save(Path(temp)/'override-request.json',{'arguments':['exact','pins']})
            self.assertEqual(kinds,[False,True])


if __name__=='__main__': unittest.main()
