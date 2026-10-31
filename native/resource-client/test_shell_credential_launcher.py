import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

# mini-shell-ssh holds a per-member call slot with flock (util-linux): Linux only.
@unittest.skipUnless(shutil.which("flock"), "mini-shell-ssh needs flock (util-linux)")
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
            expected=["shell","--socket","/public/socket","--host","/host","--config","/config","--workspace","/member/workspace","--home",str(self.home)]
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
class CallSlotTests(unittest.TestCase):
    """The wrapper execs the client with the member's call slots (`mini shell --call-slots`)."""
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix="call-slots-")
        self.addCleanup(self.temp.cleanup)
        root=Path(self.temp.name)
        self.wrapper=root/"mini-shell-ssh";shutil.copyfile(Path(__file__).resolve().parents[2]/"deploy/shell/mini-shell-ssh",self.wrapper);self.wrapper.chmod(0o755)
        self.home=root/"home";self.home.mkdir()
        # The fake client prints its arguments.
        self.mini=root/"mini"
        self.mini.write_text("#!/bin/sh\nprintf '%s\\n' \"$@\"\n")
        self.mini.chmod(0o755)
        self.env=dict(os.environ)
    def call(self,line):
        argv=[str(self.wrapper),str(self.mini),"/host","/config","/socket","/workspace",str(self.home)]
        return subprocess.run(argv,env=dict(self.env,SSH_ORIGINAL_COMMAND=line),capture_output=True,text=True,timeout=30)
    def test_the_line_and_the_call_slots_reach_the_client(self):
        result=self.call("read shared")
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertEqual(result.stdout.splitlines(),["shell","--socket","/socket","--host","/host","--config","/config",
            "--workspace","/workspace","--home",str(self.home),"--call-slots",f"{self.home}/.call-slots","--line","read shared"])
    def test_the_client_exit_code_passes_through(self):
        failing=Path(self.temp.name)/"mini-fail";failing.write_text("#!/bin/sh\nexit 3\n");failing.chmod(0o755)
        result=subprocess.run([str(self.wrapper),str(failing),"/h","/c","/s","/w",str(self.home)],env=dict(self.env,SSH_ORIGINAL_COMMAND="x"),capture_output=True,text=True)
        self.assertEqual(result.returncode,3)

if __name__=="__main__":unittest.main()
