"""Refute first-namespace publication shadowing without invoking Lean."""
import importlib.util, hashlib, json, tempfile, unittest
from pathlib import Path
from types import SimpleNamespace
spec=importlib.util.spec_from_file_location("runner",Path(__file__).with_name("lean-scoped-dag.py"))
runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
class NamespaceTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
  self.cohort=self.root/"cohort";self.out=self.root/"out";self.tool=self.root/"lean";self.tool.write_bytes(b"pinned-tool")
  self.manifest=self.root/"manifest.json";self.manifest.write_text(json.dumps({"affected_topological":["Kernel.New"]}))
  self.records=[]
  for name,data in [("olean/Kernel/Old.olean",b"old"),("olean/Kernel/Old.olean.private",b"private"),("olean/Kernel/Old.ilean",b"ilean"),("olean/Kernel/Old.ir",b"ir"),("olean/Kernel/New.olean",b"stale-new"),("src/Kernel/Old.lean",b"source"),("c/Kernel/Old.c",b"c")]:
   p=self.cohort/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);self.records.append({"path":name,"sha256":runner.sha(p)})
  cat=self.cohort/"COHORT.json";cat.write_text(json.dumps({"state":"COMPLETE","toolchainSha256":runner.sha(self.tool),"artifacts":self.records}))
  self.args=SimpleNamespace(immutable_cohort=self.cohort,immutable_cohort_sha256=runner.sha(cat),lean=self.tool,manifest=self.manifest,output=self.out)
 def selected_namespace(self, roots, module):
  pieces=module.split(".")
  for root in roots:
   if (root/pieces[0]).is_dir():return root.joinpath(*pieces).with_suffix(".olean")
  raise ValueError("missing namespace")
 def test_publication_cannot_shadow_warm_old_or_private(self):
  # This exact root transition refuted the original empty-output preflight.
  self.assertTrue(self.selected_namespace([self.out,self.cohort/"olean"],"Kernel.Old").is_file())
  (self.out/"Kernel").mkdir(parents=True)
  self.assertFalse(self.selected_namespace([self.out,self.cohort/"olean"],"Kernel.Old").is_file())
  runner.project_immutable_namespace(self.args)
  (self.out/"Kernel/New.olean").write_bytes(b"new")
  self.assertEqual(self.selected_namespace([self.out,self.cohort/"olean"],"Kernel.Old").read_bytes(),b"old")
  self.assertEqual((self.out/"Kernel/Old.olean.private").read_bytes(),b"private")
  self.assertFalse((self.out/"Kernel/New.olean").is_symlink())
  runner.project_immutable_namespace(self.args) # idempotent; writable module untouched
  self.assertEqual((self.out/"Kernel/New.olean").read_bytes(),b"new")
 def test_companion_drift_refuses(self):
  (self.cohort/"olean/Kernel/Old.olean.private").write_bytes(b"substitute")
  with self.assertRaisesRegex(ValueError,"Immutable artifact drift"):runner.project_immutable_namespace(self.args)
 def test_existing_other_writer_is_never_overwritten(self):
  (self.out/"Kernel").mkdir(parents=True);p=self.out/"Kernel/Old.olean";p.write_bytes(b"other-owner")
  with self.assertRaisesRegex(ValueError,"Refusing namespace projection overwrite"):runner.project_immutable_namespace(self.args)
  self.assertEqual(p.read_bytes(),b"other-owner")
 def test_exact_catalogue_and_source_c_pins_required(self):
  (self.cohort/"src/Kernel/Old.lean").write_bytes(b"changed-source")
  with self.assertRaisesRegex(ValueError,"Immutable artifact drift"):runner.project_immutable_namespace(self.args)
if __name__=="__main__":unittest.main()
