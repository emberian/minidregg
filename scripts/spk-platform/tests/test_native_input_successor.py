"""Adapter cases only; no native admission or app execution is simulated as success."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch
import sys
sys.path.insert(0,str(Path(__file__).parent))
import test_ws_continuity_fixture as original
s=importlib.util.spec_from_file_location("successor",Path(__file__).parents[1]/"native-input-successor.py")
n=importlib.util.module_from_spec(s);s.loader.exec_module(n)
s=importlib.util.spec_from_file_location("fixture_successor",Path(__file__).parents[1]/"ws-continuity-fixture.py")
f=importlib.util.module_from_spec(s);s.loader.exec_module(f)

class ReboundProfileTests(unittest.TestCase):
    write=staticmethod(original.ProfileDiscoveryTests.write)
    discover=original.ProfileDiscoveryTests.discover
    def setUp(self):
        original.ProfileDiscoveryTests.setUp(self)
        self.next=self.state/"upgrades/tx/grain-host.json"
        self.next.parent.mkdir(parents=True)
        self.write(self.next,self.profile)
        self.result={"protocol":"mini-spk-profile-rebind-v1","store":"deployment-owned-key",
            "previousProfile":str(self.state/"grain-host.json"),"profile":str(self.next),
            "profileSha256":f.sha(self.next),"admission":str(self.root/"root-admission.json"),
            "activeProfile":str(self.state/"active-profile.json")}
        self.write(self.root/"evidence/profile-result.json",self.result)
        self.current={"protocol":"mini-spk-current-profile-v1","store":"deployment-owned-key",
            "profile":str(self.next),"profileSha256":f.sha(self.next)}
    def test_rebind_uses_native_selection_and_retains_original_state(self):
        with patch.object(f.subprocess,"check_output",return_value=json.dumps(self.current)) as call:
            state,path,value=self.discover()
        self.assertEqual(state,self.state);self.assertEqual(path,self.next)
        self.assertEqual(call.call_args.args[0],["/candidate/spk-host","grain","current-profile",str(self.state/"grain-host.json")])
    def test_authored_rebind_does_not_override_native_selection(self):
        self.current["profile"]=str(self.state/"unselected.json")
        with patch.object(f.subprocess,"check_output",return_value=json.dumps(self.current)):
            with self.assertRaisesRegex(RuntimeError,"native current profile differs"):self.discover()
    def test_rebind_selected_bytes_mutation_refuses_before_native_call(self):
        self.next.write_text("{}")
        with patch.object(f.subprocess,"check_output") as call:
            with self.assertRaises((RuntimeError,KeyError)):self.discover()
        call.assert_not_called()

class SourceSuccessorTests(unittest.TestCase):
    def test_new_adapter_module_is_pinned_only_by_explicit_adoption(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            n.durable(root/"source-inputs.json",{f.__file__:n.sha(Path(f.__file__))})
            with patch.object(f,"protected_parent"):
                f.adopt_adapter(root,"native continuation source addition")
            pins=f.adapter_pins(root)[0]
            self.assertEqual(pins[str(Path(n.__file__).resolve())],n.sha(Path(n.__file__)))
            self.assertEqual(len(pins),2)
    def test_application_authority_keys_and_store_cannot_change(self):
        old={"manifest":"/old","expectedSourceCommit":"old","miniConfig":"/config-old",
             "miniConfigSha256":"a","profileResult":"/profile-old","initStoreResult":"/same",
             "application":{"app":"8502"},"keys":{"0":"existing"},"privateSocket":"/same.sock"}
        new=copy.deepcopy(old);new.update(manifest="/new",expectedSourceCommit="new",miniConfig="/config-new",
                                         miniConfigSha256="b",profileResult="/profile-new")
        n.source_change(old,new)
        for key,value in (("application",{"app":"9999"}),("keys",{"0":"other"}),("privateSocket","/other.sock")):
            changed=copy.deepcopy(new);changed[key]=value
            with self.assertRaisesRegex(RuntimeError,"application, authority, participant or Store"):n.source_change(old,changed)
    def test_committed_adoption_preserves_originals_and_uses_linked_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            old={"manifest":"/old","initStoreResult":"/same","profileResult":"/old-profile"}
            new={**old,"manifest":"/new","profileResult":"/new-profile"}
            n.durable(root/"input.json",old);n.durable(root/"manifest.json",{"source":"old"})
            request=root/"native-input-adoption-request-01.json"
            n.durable(request,{"oldInput":old,"oldManifest":{"source":"old"},
                              "targetInput":new,"targetManifest":{"source":"new"}})
            n.durable(root/"fixture.json",{"nativeInputSuccessor":{"request":str(request),"requestSha256":n.sha(request)}})
            receipt={"protocol":"mini-spk-native-input-successor-v1","previousSha256":n.sha(root/"input.json"),
                     "request":str(request),"requestSha256":n.sha(request)}
            n.durable(root/"native-input-successor-01.json",receipt)
            source,manifest,*_=n.current(root)
            self.assertEqual((source,manifest),(new,{"source":"new"}))
            self.assertEqual(n.load(root/"input.json"),old)
    def test_incomplete_adoption_never_silently_continues(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            n.durable(root/"input.json",{"initStoreResult":"/same"})
            n.durable(root/"manifest.json",{})
            n.durable(root/"fixture.json",{"nativeInputSuccessor":{"request":"pending"}})
            with self.assertRaisesRegex(RuntimeError,"adoption is incomplete"):n.current(root)

class AdoptionCrashTests(unittest.TestCase):
    def test_lost_adoption_receipt_resumes_exact_pointer_without_replaying_steps(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);state=root/"existing-state";state.mkdir()
            old={k:"/"+k for k in ("manifest","miniConfig","workspace","publicSocket","privateSocket","genesis","profileResult","initStoreResult","grainsRoot")}
            old.update(root=str(root),miniConfigSha256="old",expectedSourceCommit="old")
            new={**old,"manifest":"/new-manifest","miniConfig":"/new-config",
                 "miniConfigSha256":"new","expectedSourceCommit":"new","profileResult":str(root/"rebind.json")}
            n.durable(root/"admission.json",{"protocol":"mini-compatible-admission-v1","target":{
                "manifest":{"sourceCommit":"new"},"configPath":new["miniConfig"],"configSha256":new["miniConfigSha256"]}})
            n.durable(root/"rebind.json",{"protocol":"mini-spk-profile-rebind-v1","admission":str(root/"admission.json")})
            profile=state/"selected.json";n.durable(profile,{"selected":"native"})
            before={"state":str(state),"steps":{"done":["install","member:m0:ticket"],
                    "pending":{"name":"start"},"settled":[{"exact":"old-refusal"}]},
                    "app":"8502","keys":{"owner":"same"},"applicationSource":"same"}
            n.durable(root/"input.json",old);n.durable(root/"manifest.json",{"sourceCommit":"old"})
            n.durable(root/"fixture.json",before)
            oldpath=root/"old-input.json";newpath=root/"target-input.json"
            n.durable(oldpath,old);n.durable(newpath,new)
            api=SimpleNamespace(absolute=Path,protected_parent=lambda p:None,
                adapter_pins=lambda p:({str(Path(n.__file__).resolve()):n.sha(Path(n.__file__))},None,None),
                discover_profile=lambda *a:(state,profile,{"miniOperatorSocket":old["privateSocket"]}))
            adapter=SimpleNamespace(f=api,validate=lambda c:({"sourceCommit":"new"},{"host":{"path":"/new-host","sha256":"new"}}))
            with patch.object(adapter,"validate",return_value=({"sourceCommit":"unadmitted"},{"mini":"other"})):
                with self.assertRaisesRegex(RuntimeError,"native roles or configuration"):
                    n.adopt(adapter,oldpath,newpath,"native compatible rebind")
            self.assertEqual(n.load(root/"fixture.json"),before)
            self.assertFalse((root/"native-input-adoption-request-01.json").exists())
            real=n.durable
            def lose_receipt(path,value):
                if path.name=="native-input-successor-01.json":raise OSError("lost reply before receipt")
                return real(path,value)
            with patch.object(n,"durable",side_effect=lose_receipt):
                with self.assertRaises(OSError):n.adopt(adapter,oldpath,newpath,"native compatible rebind")
            with self.assertRaisesRegex(RuntimeError,"adoption is incomplete"):n.current(root)
            n.adopt(adapter,oldpath,newpath,"native compatible rebind")
            after=n.load(root/"fixture.json")
            self.assertEqual(after["steps"],before["steps"])
            self.assertEqual(after["keys"],before["keys"])
            self.assertEqual(after["app"],before["app"])
            self.assertEqual(n.load(root/"input.json"),old)
            self.assertEqual(n.current(root)[0],new)
            self.assertEqual(n.adopt(adapter,oldpath,newpath,"native compatible rebind")["status"],
                             "native profile lineage consumed; app admission remains current-law gated")
