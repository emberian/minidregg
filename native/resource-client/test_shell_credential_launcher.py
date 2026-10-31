import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

# The credential launcher's own job: the credential protocol to the key broker relay, everything
# else to mini-shell-ssh beside it with the same six arguments. mini-shell-ssh itself (bin/mini-line)
# is tested in tests/mini_shell_ssh.rs; here a stand-in beside the launcher records its argv.
class CredentialLauncherTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix="credential-shell-")
        self.addCleanup(self.temp.cleanup)
        self.frame=Path(self.temp.name)/"frame"
        self.lib=self.frame/"usr/local/lib/mini";self.lib.mkdir(parents=True)
        launcher=self.lib/"mini-shell-ssh-credentials"
        shutil.copyfile(Path(__file__).resolve().parents[2]/"deploy/shell/mini-shell-ssh-credentials",launcher);launcher.chmod(0o755)
        shell=self.lib/"mini-shell-ssh"
        shell.write_text("#!/usr/bin/env python3\nimport json,os,sys\nprint(json.dumps(['mini-shell-ssh']+sys.argv[1:]+[os.environ.get('SSH_ORIGINAL_COMMAND')]))\n");shell.chmod(0o755)
        self.mini=self.frame/"mini"
        self.mini.write_text("#!/bin/sh\nexit 0\n");self.mini.chmod(0o755)
        # The broker relay sits beside the pinned mini and records its argv the same way.
        self.keys=self.frame/"mini-keys"
        self.keys.write_text("#!/usr/bin/env python3\nimport json,sys\nprint(json.dumps(['mini-keys']+sys.argv[1:]))\n");self.keys.chmod(0o755)
        self.home=Path(self.temp.name)/"home";self.home.mkdir()
        self.args=[str(self.mini),"/host","/config","/public/socket","/member/workspace",str(self.home)]
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
            self.assertEqual(json.loads(result.stdout),["mini-shell-ssh",*self.args,command])
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
