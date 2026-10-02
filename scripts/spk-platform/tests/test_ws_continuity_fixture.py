#!/usr/bin/env python3
"""Adapter logic only; synthetic views do not qualify Mini or EtherCalc."""
import copy
import importlib.util
import json
import os
import signal
import sys
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock

MODULE = Path(__file__).resolve().parents[1]/"ws-continuity-fixture.py"
spec = importlib.util.spec_from_file_location("fixture",MODULE)
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)


def view(fields, height="30"):
    return {"view":{"cell":{"root":"99","entries":[{"key":{"field":k},"value":v} for k,v in fields.items()]},"balances":[["0","123"]]},
            "challenge":{"height":height,"worldRoot":"100","authorityRoot":"200"},"dir":Path("/unused")}


class CommandEvidenceTests(unittest.TestCase):
    def test_success_and_timeout_retain_elapsed_outcome(self):
        with tempfile.TemporaryDirectory() as temp:
            prefix=Path(temp)/'success'
            f.logged_run([sys.executable,'-c','print("ok")'],prefix,timeout=2)
            result=f.load(str(prefix)+'.exit.json')
            self.assertEqual(result['exit'],0);self.assertFalse(result['timedOut'])
            self.assertGreaterEqual(result['elapsedSeconds'],0)
            self.assertGreaterEqual(result['endedMonotonic'],result['startedMonotonic'])
            prefix=Path(temp)/'timeout'
            with self.assertRaises(subprocess.TimeoutExpired):
                f.logged_run([sys.executable,'-c','import time; time.sleep(1)'],prefix,timeout=.02)
            result=f.load(str(prefix)+'.exit.json')
            self.assertIsNone(result['exit']);self.assertTrue(result['timedOut'])
            self.assertEqual(result['errorType'],'TimeoutExpired')
            self.assertGreater(result['elapsedSeconds'],0)


class AdapterTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.x = f.Fixture.__new__(f.Fixture)
        self.x.root = Path(self.tmp.name)
        self.x.opdir = self.x.root/"hook"
        self.x.opdir.mkdir()
        self.x.state = self.x.root/"state"
        self.x.app = "4601"
        self.x.appcap = "3101"
        self.x.nonce = 100
        self.x.f = {"app":"4601","generation":"4","delegates":{
            "a":{"subject":"7","session":"4610","cap":"3211","ticket":"4620","ticketOwner":"3232","ticketControl":"3233","ticketObserve":"3234"},
            "b":{"subject":"9","session":"4612","cap":"3221","ticket":"4622","ticketOwner":"3242","ticketControl":"3243","ticketObserve":"3244"}}}
        self.x.submit = Mock(return_value=self.x.opdir/"native-attempt")
        self.x.write_state = Mock()
        self.x.query = Mock(return_value=view({"0":"4601","1":"4","2":"2","3":"1"}))

    def test_owner_revokes_only_a_ticket_child(self):
        b = copy.deepcopy(self.x.f["delegates"]["b"])
        result = self.x.action("revokeA")
        intent, signer = self.x.submit.call_args.args
        c = intent["purpose"]["draft"]["command"]
        self.assertEqual(signer,8)
        self.assertEqual((c["subject"],c["target"],c["capability"],c["controlCapability"]),
                         ("8","4620","3234","3233"))
        self.assertEqual(self.x.query.call_args_list[1].kwargs,{"denied":True})
        self.assertEqual(self.x.query.call_args_list[2].args,("9","4622","3244"))
        self.assertEqual(b,self.x.f["delegates"]["b"])
        self.assertTrue(self.x.f["delegates"]["a"]["revoked"])
        self.assertTrue(Path(result["artifact"]).is_file())

    def test_failed_confirmation_does_not_permit_second_mutation(self):
        self.x.query.side_effect = [view({}),RuntimeError("wrong refusal")]
        with self.assertRaisesRegex(RuntimeError,"wrong refusal"):
            self.x.action("revokeA")
        with self.assertRaisesRegex(RuntimeError,"already attempted"):
            self.x.action("revokeA")
        self.assertEqual(self.x.submit.call_count,1)
        self.x.write_state.assert_not_called()

    def test_regrant_without_hot_consumer_is_nonmutating(self):
        with self.assertRaisesRegex(RuntimeError,"regrant disabled"):
            self.x.action("regrantA")
        self.x.submit.assert_not_called()
        self.x.query.assert_not_called()
        self.assertFalse((self.x.root/"action-regrantA-started.json").exists())

    def snapshots(self, different_tip=False):
        app=view({"0":"4","1":"4"})
        a=view({"0":"4601","1":"4","2":"2","3":"1"})
        b=copy.deepcopy(a)
        payer=view({},height="31" if different_tip else "30")
        self.x.query.side_effect=[app,a,view({}),b,view({}),payer]

    def test_snapshot_does_not_fabricate_billing_counter(self):
        self.snapshots()
        result=self.x.snapshot()
        self.assertIsNone(result["billingCount"])
        self.assertEqual(result["payerBalances"],{"8:0":"123"})
        self.assertEqual(result["storeHeight"],30)
        self.assertIn("NOT a source history",result["provenance"]["dispatchCount"])
        self.assertTrue(result["delegates"]["a"]["active"])
        self.x.submit.assert_not_called()

    def test_snapshot_rejects_mixed_source_tips(self):
        self.snapshots(different_tip=True)
        with self.assertRaisesRegex(RuntimeError,"Store changed"):
            self.x.snapshot()

    def test_stale_session_generation_is_inactive(self):
        self.snapshots()
        values=list(self.x.query.side_effect)
        values[1]=view({"0":"4601","1":"3","2":"2","3":"1"})
        self.x.query.side_effect=values
        result=self.x.snapshot()
        self.assertFalse(result["delegates"]["a"]["active"])
        self.assertTrue(result["delegates"]["b"]["active"])


class RegistrationTests(unittest.TestCase):
    def setUp(self):
        self.request={"registrationNonceHex":"a"*64,"expectedApp":"4601","expectedAppGeneration":"4","expectedSessionGeneration":"4"}
        self.delegate={"session":"4610","subject":"7","ticket":"4641"}
        self.reply={"protocol":"mini-spk-route-register-v1","registrationNonceHex":"a"*64,"routeIndex":2,
            "app":"4601","appGeneration":"4","session":"4610","sessionGeneration":"4","subject":"7","ticketResource":"4641",
            "sessionFingerprintHex":"b"*64,"admittedHeight":"123","admittedWorldRoot":"456"}

    def test_exact_binding(self):
        f.check_registration(self.reply,self.request,self.delegate)

    def test_other_ticket_replay_refused(self):
        self.reply["ticketResource"]="4620"
        with self.assertRaisesRegex(RuntimeError,"identity differs"):
            f.check_registration(self.reply,self.request,self.delegate)

    def test_other_nonce_refused(self):
        self.reply["registrationNonceHex"]="c"*64
        with self.assertRaisesRegex(RuntimeError,"identity differs"):
            f.check_registration(self.reply,self.request,self.delegate)

    def test_unsupported_reply_field_refused(self):
        self.reply["accepted"]=True
        with self.assertRaisesRegex(RuntimeError,"shape differs"):
            f.check_registration(self.reply,self.request,self.delegate)


class ProfileDiscoveryTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name).resolve()
        self.grains=self.root/"grains"
        # Deliberately not sha(config)[:16]; deployment identity belongs to native code.
        self.state=self.grains/"deployment-blue"/"store-identity-42"/"host"
        self.state.mkdir(parents=True)
        (self.root/"evidence").mkdir()
        self.config=self.root/"config.json"
        self.config.write_text('{"deployment":"blue"}')
        self.artifacts={"host":{"path":"/candidate/Host","sha256":"a"*64},"spkHost":{"path":"/candidate/spk-host","sha256":"b"*64}}
        self.result={"protocol":"mini-spk-grain-profile-result-v1","stateRoot":str(self.state),
            "profilePath":str(self.state/"grain-host.json"),"grainsRoot":str(self.grains),
            "miniConfig":str(self.config),"miniConfigSha256":f.sha(self.config),
            "initStoreResult":str(self.root/"evidence/init-store.json")}
        self.profile={"stateRoot":str(self.state),"grainsRoot":str(self.grains),"miniConfig":str(self.config),
            "miniConfigSha256":f.sha(self.config),"miniHost":"/candidate/Host","miniHostSha256":"a"*64,
            "spkHost":"/candidate/spk-host","spkHostSha256":"b"*64}
        self.write(self.root/"evidence/profile-result.json",self.result)
        self.write(self.root/"evidence/init-store.json",{"protocol":"mini-spk-grain-init-store-v1","store":"deployment-owned-key","stateRoot":str(self.state)})
        self.write(self.state/"grain-host.json",self.profile)

    @staticmethod
    def write(path,value):
        path.write_text(json.dumps(value))

    def discover(self):
        return f.discover_profile(self.root,self.config,self.grains,self.artifacts)

    def test_native_deployment_identity_is_used_without_hash_guess(self):
        state,path,profile=self.discover()
        self.assertEqual(state,self.state)
        self.assertEqual(path,self.state/"grain-host.json")
        self.assertNotEqual(state,self.grains/f.sha(self.config)[:16]/"host")

    def test_isolated_broker_must_match_every_retained_native_layer(self):
        broker=str(self.grains/'broker.sock')
        paths=[self.root/'evidence/profile-result.json',self.root/'evidence/init-store.json',self.state/'grain-host.json']
        for path in paths:
            value=f.load(path);value['brokerSocket']=broker;self.write(path,value)
        f.discover_profile(self.root,self.config,self.grains,self.artifacts,broker)
        for path in paths:
            value=f.load(path);saved=value.copy();value.pop('brokerSocket');self.write(path,value)
            with self.assertRaisesRegex(RuntimeError,'broker endpoint differs'):
                f.discover_profile(self.root,self.config,self.grains,self.artifacts,broker)
            self.write(path,saved)

    def test_init_result_mismatch_is_refused(self):
        self.write(self.root/"evidence/init-store.json",{"protocol":"mini-spk-grain-init-store-v1","stateRoot":str(self.grains/"other")})
        with self.assertRaisesRegex(RuntimeError,"native Store initialization"):
            self.discover()

    def test_profile_cannot_point_to_another_config(self):
        self.profile["miniConfig"]="/another/config.json"
        self.write(self.state/"grain-host.json",self.profile)
        with self.assertRaisesRegex(RuntimeError,"fixture/config pins"):
            self.discover()

    def test_profile_cannot_select_another_binary(self):
        self.profile["miniHostSha256"]="c"*64
        self.write(self.state/"grain-host.json",self.profile)
        with self.assertRaisesRegex(RuntimeError,"candidate artifacts"):
            self.discover()

    def test_result_cannot_escape_pinned_grains_root(self):
        self.result["stateRoot"]=str(self.root/"outside")
        self.write(self.root/"evidence/profile-result.json",self.result)
        with self.assertRaisesRegex(RuntimeError,"outside the pinned grains root"):
            self.discover()


class NativeProfilePublicationTests(unittest.TestCase):
    def test_profile_phase_publishes_native_deployment_path(self):
        self.profile_case(False)

    def test_profile_phase_passes_explicit_broker_and_retains_pin(self):
        self.profile_case(True)

    def profile_case(self, isolated):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory).resolve()
            grains=root/"grains"
            state=grains/"deployment-green"/"independent-store-key"/"host"
            state.mkdir(parents=True)
            ev=root/"evidence";ev.mkdir()
            wr=root/"workroom";wr.mkdir()
            (wr/"operator-profile.json").write_text('{"semantics":"12"}')
            (wr/"tool.pub").write_bytes(bytes(32))
            config=root/"config.json";config.write_text('{"identity":"green"}')
            native=root/"fake-spk-host"
            native.write_text("""#!/usr/bin/env python3
import json, os, sys
assert sys.argv[1:3]==['grain','init-store']
value={'protocol':'mini-spk-grain-init-store-v1','store':'deployment-owned-key','stateRoot':os.environ['NATIVE_STATE']}
if os.environ.get('NATIVE_BROKER'):
    assert sys.argv[5:]==['--broker-socket',os.environ['NATIVE_BROKER']]
    value['brokerSocket']=os.environ['NATIVE_BROKER']
else: assert len(sys.argv)==5
print(json.dumps(value))
""")
            native.chmod(0o700)
            script=(MODULE.parent/"grain-journey.sh").read_text()
            paths=script[script.index('state_paths() {'):script.index('\nstate_paths\n')]
            writer=script[script.index('write_profile() {'):script.index('\n\n# Phases:')]
            runner=root/"profile.sh"
            runner.write_text('set -eu\numask 077\nSTATE= PROFILE=\nfail() { echo "$*" >&2; exit 1; }\nsha() { sha256sum "$1" | cut -d " " -f 1; }\n'+paths+'\n'+writer+'\nwrite_profile\nstate_paths\n')
            env=dict(os.environ,PROFILE_RESULT=str(ev/"profile-result.json"),CONFIG=str(config),GRAINS_ROOT=str(grains),EV=str(ev),
                SPK_HOST=str(native),HOST=str(native),WR=str(wr),OSOCK=str(root/"operator.sock"),STORE=str(root),BWRAP=str(native),NATIVE_STATE=str(state),BROKER_SOCKET=str(grains/"broker.sock") if isolated else "",NATIVE_BROKER=str(grains/"broker.sock") if isolated else "")
            subprocess.run(["/bin/sh",str(runner)],env=env,check=True,timeout=15,capture_output=True)
            result=json.loads((ev/"profile-result.json").read_text())
            self.assertEqual(result["profilePath"],str(state/"grain-host.json"))
            self.assertEqual(result["stateRoot"],str(state))
            self.assertEqual(json.loads((state/"grain-host.json").read_text())["stateRoot"],str(state))
            if isolated:
                self.assertEqual(result['brokerSocket'],str(grains/'broker.sock'))
                self.assertEqual(f.load(state/'grain-host.json')['brokerSocket'],str(grains/'broker.sock'))
            # A mismatching retained native result must stop future phase reuse.
            initialized=json.loads((ev/"init-store.json").read_text())
            initialized["stateRoot"]=str(grains/"other-deployment")
            (ev/"init-store.json").write_text(json.dumps(initialized))
            again=subprocess.run(["/bin/sh",str(runner)],env=env,timeout=15,capture_output=True)
            self.assertNotEqual(again.returncode,0)
            self.assertIn(b"differs from native Store initialization",again.stderr)


class ServiceTopologyTests(unittest.TestCase):
    def test_one_native_owner_and_config_pinned_public_proxy(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            (root/"sock").mkdir()
            mini=root/"fake-mini"
            mini.write_text("""#!/usr/bin/env python3
import json, os, signal, socket, sys, time
with open(os.environ['CALL_LOG'],'a') as f: f.write(json.dumps(sys.argv[1:])+'\\n')
p=sys.argv[sys.argv.index('--socket')+1]
s=socket.socket(socket.AF_UNIX);s.bind(p);s.listen()
signal.signal(signal.SIGTERM,lambda *_:sys.exit(0))
while True: time.sleep(1)
""")
            mini.chmod(0o700)
            script=(MODULE.parent/"grain-journey.sh").read_text()
            functions=script[script.index('service_up() {'):script.index('\nstop_services() {')]
            runner=root/"run.sh"
            runner.write_text('set -eu\nfail() { echo "$*" >&2; exit 1; }\n'+functions+'\nservices\n')
            env=dict(os.environ,RUN=str(root),MINI=str(mini),HOST="/candidate/Host",CONFIG="/candidate/pinned.json",
                OSOCK=str(root/"sock/operator/host.sock"),PSOCK=str(root/"sock/participant/host.sock"),CALL_LOG=str(root/"calls"))
            try:
                subprocess.run(["/bin/sh",str(runner)],env=env,check=True,timeout=15,capture_output=True)
                calls=[json.loads(line) for line in (root/"calls").read_text().splitlines()]
                self.assertEqual([args[0] for args in calls],["serve-operator","serve-public-proxy"])
                self.assertEqual(calls[1],["serve-public-proxy","--socket",env["PSOCK"],"--upstream",env["OSOCK"],"--config",env["CONFIG"]])
                self.assertNotIn("--host",calls[1])
                # A retained old independent public service is not silently accepted.
                (root/"sock/participant.pid.mode").write_text("serve\n")
                again=subprocess.run(["/bin/sh",str(runner)],env=env,timeout=15,capture_output=True)
                self.assertNotEqual(again.returncode,0)
                self.assertIn(b"service mode differs",again.stderr)
                self.assertEqual(len((root/"calls").read_text().splitlines()),2)
            finally:
                for name in ["participant","operator"]:
                    pidfile=root/f"sock/{name}.pid"
                    if pidfile.exists():
                        try: os.kill(int(pidfile.read_text()),signal.SIGTERM)
                        except ProcessLookupError: pass


if __name__ == "__main__":
    unittest.main()
