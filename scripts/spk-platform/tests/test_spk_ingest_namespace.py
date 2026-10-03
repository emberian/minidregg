import os
from pathlib import Path
import subprocess
import tempfile
import unittest
HELPER=Path(__file__).resolve().parents[3]/"deploy/spk-host/spk-ingest"
class IngestNamespace(unittest.TestCase):
    def invoke(self,root):
        return subprocess.run(["bash",str(HELPER),"--root",root,"/usr/bin/false","0"*64,
                               "/missing/inbox/package.spk","64010"],capture_output=True,text=True,timeout=5)
    def test_unsafe_root_arguments_refused_before_custody_or_effects(self):
        for root in ("/","relative","/../owned","/tmp/../owned","/tmp/owned/","/tmp/./owned"):
            with self.subTest(root=root):
                result=self.invoke(root)
                self.assertEqual(result.returncode,2)
                self.assertIn("usage:",result.stderr)
    def test_symlinked_root_refused_before_custody_or_effects(self):
        with tempfile.TemporaryDirectory() as raw:
            base=Path(raw);(base/"alias").symlink_to(base)
            result=self.invoke(str(base/"alias"/"spk"))
            self.assertNotEqual(result.returncode,0)
            self.assertIn("canonical and not symlinked",result.stderr)
            self.assertFalse((base/"spk").exists())
    @unittest.skipIf(os.geteuid()==0,"non-root guard requires ordinary test user")
    def test_valid_isolated_root_has_no_effect_for_nonroot_caller(self):
        with tempfile.TemporaryDirectory() as raw:
            selected=str(Path(raw)/"spk")
            result=self.invoke(selected)
            self.assertNotEqual(result.returncode,0)
            self.assertIn("requires root",result.stderr)
            self.assertFalse(Path(selected).exists())
