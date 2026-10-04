import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

class CredentialLauncherTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix="credential-shell-")
        self.addCleanup(self.temp.cleanup)
        self.frame=Path(self.temp.name)/"frame"
        self.lib=self.frame/"usr/local/lib/mini";self.lib.mkdir(parents=True)
        source=Path(__file__).resolve().parents[2]/"deploy/shell"
        for name in ("mini-shell-ssh","mini-shell-ssh-credentials"):
            shutil.copyfile(source/name,self.lib/name);(self.lib/name).chmod(0o755)
        self.mini=self.frame/"mini"
        self.mini.write_text("#!/usr/bin/env python3\nimport json,sys\nprint(json.dumps(sys.argv[1:]))\n");self.mini.chmod(0o755)
        # The broker relay sits beside the pinned mini and records its argv the same way.
        self.keys=self.frame/"mini-keys"
        self.keys.write_text("#!/usr/bin/env python3\nimport json,sys\nprint(json.dumps(['mini-keys']+sys.argv[1:]))\n");self.keys.chmod(0o755)
        self.args=[str(self.mini),"/host","/config","/public/socket","/member/workspace","/member/home"]
    def run_launcher(self,command=None,args=None):
        env=os.environ.copy();env.pop("SSH_ORIGINAL_COMMAND",None)
        # An inherited frame variable must not select the root credential path.
        env["MINI_ROOT"]="/other-world"
        if command is not None:env["SSH_ORIGINAL_COMMAND"]=command
        return subprocess.run([str(self.lib/"mini-shell-ssh-credentials"),*(self.args if args is None else args)],env=env,capture_output=True,text=True)
    def test_signed_credential_protocol_uses_exact_installed_frame(self):
        result=self.run_launcher("mini-provider-credentials-v1")
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertEqual(json.loads(result.stdout),["mini-keys","relay","--client-config",str(self.frame/"etc/mini/keys-client.json")])
    def test_normal_shell_and_script_preserve_participant_binding(self):
        for command in (None,"whoami","mini-provider-credentials-v1 /foreign/config"):
            result=self.run_launcher(command)
            self.assertEqual(result.returncode,0,result.stderr)
            expected=["shell","--socket","/public/socket","--host","/host","--config","/config","--workspace","/member/workspace","--home","/member/home"]
            if command is not None:expected.extend(["--line",command])
            self.assertEqual(json.loads(result.stdout),expected)
    def test_missing_or_relative_arguments_refused_before_client(self):
        for args in (self.args[:5],[self.args[0],"relative",*self.args[2:]]):
            result=self.run_launcher("mini-provider-credentials-v1",args)
            self.assertEqual(result.returncode,64)
            self.assertEqual(result.stdout,"")
    def test_uninstalled_wrapper_refused(self):
        copied=self.frame/"uninstalled";shutil.copyfile(self.lib/"mini-shell-ssh-credentials",copied);copied.chmod(0o755)
        result=subprocess.run([str(copied),*self.args],env=dict(os.environ,SSH_ORIGINAL_COMMAND="mini-provider-credentials-v1"),capture_output=True,text=True)
        self.assertEqual(result.returncode,64)
        self.assertEqual(result.stdout,"")
if __name__=="__main__":unittest.main()
