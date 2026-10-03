import importlib.util
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('stage',Path(__file__).resolve().parents[1]/'sandbox-launcher-stage.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class StageInputs(unittest.TestCase):
    def selected(self, frame=Path('/var/lib/mini-r2'), uid=64010, gid=64010):
        return m.selected(frame, {'bwrap':'/usr/local/libexec/mini-grain-bwrap'}, {'appUids':[64010,64011]}, uid,
                          SimpleNamespace(pw_uid=uid,pw_gid=gid))
    def test_only_exact_declared_app_identity(self):
        for uid,gid in [(64012,64012),(64010,1000),(0,0)]:
            with self.subTest(uid=uid,gid=gid), self.assertRaisesRegex(RuntimeError,'declared app'):
                self.selected(uid=uid,gid=gid)
    def test_policy_targets_only_frame_and_selected_app_launcher(self):
        source,launcher,policy,text=self.selected()
        self.assertEqual(source,Path('/usr/local/libexec/mini-grain-bwrap'))
        self.assertEqual(launcher,Path('/var/lib/mini-r2/usr/local/libexec/app-64010/mini-grain-bwrap'))
        self.assertIn(str(launcher).encode(),text)
        self.assertNotIn(str(source).encode(),text)
        self.assertNotIn(b'/**',text)
        self.assertNotEqual(self.selected(uid=64011,gid=64011)[2],policy)
    def test_frame_cannot_inject_apparmor_or_escape_staging(self):
        for frame in ['/var/lib/mini-r2*','/var/lib/mini-r2/../other','/tmp/mini-r2','/var/lib/mini-r2\nuserns,']:
            with self.subTest(frame=frame), self.assertRaisesRegex(RuntimeError,'isolated Mini frame'):
                self.selected(Path(frame))
    def test_changed_retained_launcher_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'mini-grain-bwrap';p.write_bytes(b'original');p.chmod(0o754)
            with patch.object(m,'root_path',return_value=p), self.assertRaisesRegex(RuntimeError,'retained launcher artifact differs'):
                m.publish(p,b'replacement',0o754,p.stat().st_gid)
            self.assertEqual(p.read_bytes(),b'original')

if __name__=='__main__':unittest.main()
