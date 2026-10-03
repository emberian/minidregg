import os,pathlib,subprocess,tempfile,unittest
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
if __name__=='__main__':unittest.main()
