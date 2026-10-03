import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

spec=importlib.util.spec_from_file_location("platform_stage",Path(__file__).with_name("platform-stage.py"))
stage=importlib.util.module_from_spec(spec);spec.loader.exec_module(stage)

class StageTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix="stage-")
        self.addCleanup(self.temp.cleanup)
        self.base=Path(self.temp.name)
        self.source=self.base/"source"
        recipes=("native/resource-client/paid-entry-adapter.py","deploy/shell/mini-shell-ssh","deploy/shell/mini-shell-ssh-credentials",
                 "testing/journeys/shared-resident-fixture-acp","testing/journeys/shared-resident-fixture-provider.py")
        for recipe in recipes:
            p=self.source/recipe;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(recipe)
        manifest={"sourceCommit":"e"*40,"sha256":{}}
        for role in ("mini","host","store","verifier","spkHost","spkBroker","browserProxy","bwrap","grainRuntime"):
            p=self.base/role;p.write_text(role);manifest[role]=str(p);manifest["sha256"][role]=stage.sha(p)
        self.manifest=self.base/"manifest.json";self.manifest.write_text(json.dumps(manifest))
        package=self.base/"sheet.spk";package.write_bytes(b"SPK fixture")
        self.options={"manifest":str(self.manifest),"manifestSha256":stage.sha(self.manifest),
            "source":str(self.source),"frame":"/var/lib/mini-test-r2","evidence":str(self.base/"evidence"),
            "prefix":"mini-test-r2","package":str(package),"packageSha256":stage.sha(package),
            "operator":"testoperator","appUids":[64010,64011],"ports":[22028,18444,18445,18446,18802]}
        self.uid=patch.object(stage.pwd,"getpwnam",return_value=SimpleNamespace(pw_uid=1000))
        self.uid.start();self.addCleanup(self.uid.stop)
    def planned(self):
        return stage.plan(self.options,probe=False)
    def test_names_and_sealed_pins_from_fresh_inputs(self):
        values=self.planned();p=values["provision-plan.json"]
        self.assertEqual(p["members"][-1]["name"],"connector-1")
        self.assertEqual(p["manifestSha256"],self.options["manifestSha256"])
        self.assertEqual(p["sshLauncher"]["renderer"],"mini-shell-ssh-credentials")
        self.assertTrue(p["sshLauncher"]["path"].endswith("/mini-shell-ssh-credentials"))
        self.assertEqual(p["sshLauncher"]["sha256"],stage.sha(self.source/"deploy/shell/mini-shell-ssh-credentials"))
        self.assertEqual(p["serviceManager"]["units"]["operator"],"mini-test-r2-store.service")
        self.assertTrue(all("r1" not in json.dumps(v) for v in values.values()))
        self.assertEqual(values["app-selection-template.json"]["app"]["owner"],"member-0")
    def test_manifest_tamper_refused_before_writes(self):
        self.manifest.write_text("{}")
        with self.assertRaisesRegex(RuntimeError,"manifest changed"):self.planned()
        self.assertFalse(Path(self.options["evidence"]).exists())
    def test_role_tamper_refused(self):
        (self.base/"host").write_text("other")
        with self.assertRaisesRegex(RuntimeError,"role changed: host"):self.planned()
    def test_package_tamper_refused(self):
        Path(self.options["package"]).write_text("other")
        with self.assertRaisesRegex(RuntimeError,"package bytes changed"):self.planned()
    def test_repeated_ports_refused(self):
        self.options["ports"]=[22028]*5
        with self.assertRaisesRegex(RuntimeError,"distinct nonprivileged"):self.planned()
    def test_gid_collision_refused_even_when_uid_free(self):
        with patch.object(stage.pwd,"getpwuid",side_effect=KeyError),patch.object(stage.grp,"getgrgid",return_value=object()):
            with self.assertRaisesRegex(RuntimeError,"UID or GID"):stage.collisions(Path("/var/lib/mini-test-r2"),"mini-test-r2",[22028],[64010,64011])
    def test_frame_symlink_refused(self):
        link=self.base/"link";link.symlink_to(self.base)
        self.options["frame"]=str(link/"new")
        with self.assertRaisesRegex(RuntimeError,"symlinks"):self.planned()
    def test_long_socket_refused(self):
        self.options["frame"]="/var/lib/"+("a"*72)
        with self.assertRaisesRegex(RuntimeError,"socket path too deep"):self.planned()
    def test_plan_publish_never_overwrites_receiving(self):
        directory=self.base/"out";stage.publish(directory,{"a.json":{"first":True}})
        with self.assertRaisesRegex(RuntimeError,"already exists"):
            stage.publish(directory,{"b.json":{},"a.json":{"second":True}})
        self.assertFalse((directory/"b.json").exists())
        self.assertEqual(stage.read(directory/"a.json"),{"first":True})
    def test_failed_binding_writes_no_invented_world(self):
        directory=self.base/"out";stage.publish(directory,self.planned())
        with self.assertRaises(FileNotFoundError):stage.bind(directory)
        self.assertFalse((directory/"WORLD-IDENTITY.json").exists())

    def completed_constructor(self):
        values=self.planned();directory=self.base/"out"
        root=self.base/"world-store";root.mkdir(mode=0o700)
        values["provision-plan.json"]["root"]=str(root)
        stage.publish(directory,values)
        config=root/"config.json";config.write_text("{}")
        names={m["name"]:str(17000+i) for i,m in enumerate(values["provision-plan.json"]["members"])}
        members={}
        for name,subject in names.items():
            home=root/name;workspace=home/"workspace";(workspace/"refs").mkdir(parents=True)
            pin={"subject":subject,"config":str(config),"socket":str(root/"public.sock")}
            (workspace/"workspace.json").write_text(json.dumps(pin))
            members[subject]={"subject":subject,"home":str(home),"workspace":str(workspace),
                "ssh":{"port":22028,"knownHostsFile":str(root/"known_hosts"),"identityFile":str(home/"key")}}
        context={"manifest":str(self.manifest),"config":str(config),"publicSocket":str(root/"public.sock"),
                 "identity":{"manifestSha256":stage.sha(self.manifest),"configSha256":stage.sha(config),"domain":"8501"},
                 "memberInventory":members,"privateSocket":str(root/"operator.sock"),"operatorWorkspace":str(root/"operator-workspace")}
        (root/"platform-inputs.json").write_text(json.dumps(context))
        (root/"runtime.json").write_text(json.dumps({"root":str(root),"allocationNames":names,"nodeRoot":str(root/"node")}))
        return directory,root,members,names
    def test_inventory_bootstraps_rooms_before_binding(self):
        directory,root,members,names=self.completed_constructor()
        values=stage.inventory(directory)
        self.assertEqual(values["bootstrap-world.json"]["members"]["member-0"]["subject"],names["member-0"])
        self.assertEqual(values["rooms-scenario.json"]["phases"],["rooms"])
        with self.assertRaises(FileNotFoundError):stage.bind(directory)
    def test_binding_uses_actual_held_reference_and_separate_receipt(self):
        directory,root,members,names=self.completed_constructor()
        references=Path(members[names["member-0"]]["workspace"])/"refs"
        original=references/"test-r2-r0.notes.json"
        original.write_text(json.dumps({"kind":"object","name":"test-r2-r0/notes","target":"772901","observeCapability":"210"}))
        reference=references/"r2-captured-source.json"
        reference.write_text(json.dumps({"kind":"object","name":"r2-captured-source","target":"772901","observeCapability":"210"}))
        values=stage.bind(directory);binding=values["resident-binding.json"]
        self.assertEqual(binding["sharedDocumentReference"],str(reference))
        self.assertEqual(binding["registration"],str(directory/"resident-registration-receipt.json"))
        self.assertIn(stage.sha(root/"config.json")[:16],values["app-selection.json"]["connector"]["ca"])
        self.assertIn("mini-grain-controller@8802.service",values["controller-unit-plan.json"])
        self.assertEqual(values["receiving-commands.json"]["providerCopy"]["argv"][-2],"8802")
    def test_binding_refuses_cross_store_member(self):
        directory,root,members,names=self.completed_constructor()
        workspace=Path(members[names["member-1"]]["workspace"])
        pin=stage.read(workspace/"workspace.json");pin["config"]="/different/config.json"
        (workspace/"workspace.json").write_text(json.dumps(pin))
        with self.assertRaisesRegex(RuntimeError,"another Store"):stage.inventory(directory)
