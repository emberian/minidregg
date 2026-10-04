import os,pathlib,shutil,subprocess,sys,tempfile,unittest
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from lean_imports import header_imports
ROOT=pathlib.Path(__file__).resolve().parents[1]
class ColdStart(unittest.TestCase):
 def run_host(self,body=None,mode=0o755):
  with tempfile.TemporaryDirectory() as name:
   host=pathlib.Path(name)/'host'
   if body is not None:host.write_text('#!/bin/sh\n'+body);host.chmod(mode)
   return subprocess.run(['bash',str(ROOT/'scripts/check-host-cold-start.sh'),str(host)],capture_output=True,text=True)
 def test_missing_binary_is_not_a_measurement(self):self.assertEqual(self.run_host().returncode,2)
 def test_exec_error_is_not_cheap_startup(self):self.assertEqual(self.run_host('exit 127\n').returncode,2)
 def test_unrelated_error_is_not_usage(self):self.assertEqual(self.run_host('echo unrelated >&2; exit 1\n').returncode,2)
 def test_usage_completion_is_measured(self):
  out=self.run_host('echo "minidregg-host: minidregg-host CONFIG.json profile" >&2; exit 1\n');self.assertEqual(out.returncode,0,out.stderr)
 def test_non_executable_refused(self):self.assertEqual(self.run_host('exit 1\n',0o644).returncode,2)
class HeaderImports(unittest.TestCase):
 # Lean reads an indented import, several imports on a line, and the public/meta/private/all
 # forms; a gate that matches `^import\\s+(\\S+)` sees none of them (W20-GATE-MUTATION, 2026-10-05).
 def test_every_form_lean_reads(self):
  self.assertEqual(header_imports('import A\n'),['A'])
  self.assertEqual(header_imports('  import A\n'),['A'])
  self.assertEqual(header_imports('import A import B\n'),['A','B'])
  self.assertEqual(header_imports('module\npublic import A\nmeta import B\nprivate import C\n'),['A','B','C'])
  self.assertEqual(header_imports('import all A\n'),['A'])
  self.assertEqual(header_imports('/- a /- nested -/ b -/\n-- c\nimport A\n/-! doc -/\nimport B\n'),['A','B'])
 def test_only_the_header_is_read(self):
  self.assertEqual(header_imports('import A\n\n/-- import B -/\ntheorem t : True := trivial\nimport C\n'),['A'])
 def boundary(self,body):
  with tempfile.TemporaryDirectory() as t:
   root=pathlib.Path(t);(root/'scripts').mkdir();(root/'Theory').mkdir()
   for f in ('check-import-boundary.sh','lean_imports.py'):shutil.copy(ROOT/'scripts'/f,root/'scripts'/f)
   (root/'Theory/Probe.lean').write_text(body)
   subprocess.run(['git','init','-q',str(root)],check=True);subprocess.run(['git','add','.'],cwd=root,check=True)
   return subprocess.run(['bash','scripts/check-import-boundary.sh'],cwd=root,capture_output=True,text=True)
 def test_boundary_sees_the_forms_the_old_regex_missed(self):
  self.assertEqual(self.boundary('import Mathlib.Tactic.Basic\n').returncode,0)
  for body in ('import Host.Main\n','  import Host.Main\n','import Lean import Host.Main\n','module\npublic import Host.Main\n','meta import Host.Main\n','import all Host.Main\n'):
   run=self.boundary(body)
   self.assertEqual(run.returncode,1,body);self.assertIn('new edge Theory -> Host',run.stdout,body)
if __name__=='__main__':unittest.main()
