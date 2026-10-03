import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

HERE = Path(__file__).resolve().parents[1]


def module(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


inputs = module("same_store_inputs", "same-store-inputs.py")
app = module("same_store_app_consumer", "same-store-app.py")
f = inputs.f

# No number below is one the constructor's recipe happens to use: the builder
# must take every identity from the supplied inventory.
MANAGER, CUSTODIAN = "8123", "7123"
STORE = "c" * 64


class World:
    def __init__(self, root, members=3, grains=None):
        self.root = root
        self.grains = grains or root / "grains"
        self.manifest = {"sourceCommit": "d" * 40, "sha256": {}}
        for role in ["host", "mini", "store", "verifier", "spkHost", "bwrap"]:
            image = root / role
            image.write_bytes(role.encode()); image.chmod(0o700)
            self.manifest[role] = str(image); self.manifest["sha256"][role] = f.sha(image)
        (root / "manifest.json").write_text(json.dumps(self.manifest))
        config = {"lifecycleManagement": {"managementSubject": int(MANAGER), "managementKeyId": 90812}, "issuer": 51, "ownerBudget": 100000,
                  "lifetime": 10000, "grainBirthTariff": {"base": 4, "perBirth": 3}, "factoryId": 1010}
        (root / "config.json").write_text(json.dumps(config))
        genesis = {"domain": "9917", "expectedSemantics": "445566", "enrollments": [
            {"key": {"subject": CUSTODIAN}, "accountId": CUSTODIAN, "spendCapabilityId": "4101"},
            {"key": {"subject": MANAGER}, "accountId": MANAGER, "spendCapabilityId": "4202"}]}
        (root / "genesis.json").write_text(json.dumps(genesis))
        self.package = root / "app.spk"; self.package.write_bytes(b"signed package")
        self.status, inventory = {}, {}
        for index in range(members + 1):
            subject = str(9000000000000000000 + index * 7919)
            home = root / "members" / ("member-" + str(index)); workspace = home / "join" / "workspace"
            (workspace / "refs").mkdir(parents=True); (home / "keys").mkdir()
            seed = home / "keys" / "mini.key"; seed.write_bytes(bytes(32)); seed.chmod(0o600)
            Path(str(seed) + ".pub").write_bytes(bytes(32))
            (workspace / "workspace.json").write_text(json.dumps({"type": "minidregg-participant-workspace-v1", "subject": subject,
                "config": str(root / "config.json"), "socket": str(root / "public.sock"), "key": str(seed), "host": str(root / "host")}))
            self.status[str(workspace)] = {"type": "subject-key-status-v1", "subject": subject, "keyId": str(770000 + index), "keyEpoch": str(index + 1),
                "prerotated": True, "isCurrent": True, "isCommittedNext": False, "currentRevoked": False}
            inventory[subject] = {"subject": subject, "workspace": str(workspace), "home": str(home)}
        self.subjects = list(inventory)
        founder = Path(inventory[self.subjects[0]]["workspace"])
        (founder / "refs" / "lab.json").write_text(json.dumps({"kind": "object", "name": "lab", "target": "880001", "observeCapability": "880002",
            "operationCapability": "880002", "controlCapability": "880003"}))
        self.ctx = {"identity": {"manifestSha256": f.sha(root / "manifest.json"), "configSha256": f.sha(root / "config.json"), "domain": "9917"},
            "config": str(root / "config.json"), "genesis": str(root / "genesis.json"), "manifest": str(root / "manifest.json"),
            "publicSocket": str(root / "public.sock"), "privateSocket": str(root / "operator.sock"), "operatorWorkspace": str(root / "operator-workspace"),
            "memberInventory": inventory,
            "custody": {"completionSeed": str(root / "completion.seed"), "completionPublic": str(root / "completion.pub"),
                "owner": {"subject": CUSTODIAN, "keyId": "90711", "keyEpoch": "2", "seed": str(root / "controller.key"), "publicKey": str(root / "controller.pub")},
                "management": {"subject": MANAGER, "keyId": "90812", "keyEpoch": "2", "seed": str(root / "tool.key"), "publicKey": str(root / "tool.pub")}},
            "authority": {"factory": {"target": "1010", "ownerCapability": "5401", "managementCapability": "5502"},
                "parent": {"task": "79011", "ownerCapability": "7101", "managementCapability": "7303"},
                "tool": {"task": "79022", "managementCapability": "8101"}}}
        for name in ["controller", "tool"]:
            seed = root / (name + ".key"); seed.write_bytes(bytes(32)); seed.chmod(0o600); (root / (name + ".pub")).write_bytes(bytes(32))
        self.selection = {"protocol": inputs.SELECTION, "evidence": str(root / "evidence"), "grainsRoot": str(self.grains), "brokerSocket": str(self.grains / "broker.sock"),
            "package": {"path": str(self.package), "sha256": f.sha(self.package)},
            "app": {"owner": self.subjects[1], "room": "lab", "resources": "640001", "capabilities": "970001",
                "members": {"m" + str(i): {"subject": s, "expectedHost": f"m{i}.spk.localhost:18443"} for i, s in enumerate(self.subjects[:members])}}}
        (root / "evidence").mkdir()
        owner = Path(inventory[self.subjects[1]]["workspace"])
        (owner / "refs" / "lab.json").write_text((founder / "refs" / "lab.json").read_text())

    def build(self):
        (self.root / "platform-inputs.json").write_text(json.dumps(self.ctx))
        (self.root / "selection.json").write_text(json.dumps(self.selection))
        return inputs.World(self.root / "platform-inputs.json", self.root / "selection.json")

    def key_status(self, argv, **_):
        status = self.status[argv[argv.index("--workspace") + 1]]
        return Mock(returncode=0, stdout=json.dumps(status).encode(), stderr=b"")


class InputTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.w = World(Path(self.tmp.name))
        for target in (f, app.f):
            patcher = patch.object(target, "protected_parent"); patcher.start(); self.addCleanup(patcher.stop)
        patcher = patch.object(inputs.subprocess, "run", side_effect=lambda argv, **kw: self.w.key_status(argv, **kw)); self.run = patcher.start(); self.addCleanup(patcher.stop)

    def test_profile_takes_management_custody_and_namespace_from_the_supplied_world(self):
        value = inputs.profile(self.w.build())
        self.assertEqual(value["management"], {"subject": MANAGER, "keyId": "90812", "keyEpoch": "2",
            "seedPath": str(self.w.root / "tool.key"), "publicKeyPath": str(self.w.root / "tool.pub")})
        self.assertEqual((value["semantics"], value["bwrap"], value["expectedSourceCommit"]), ("445566", str(self.w.root / "bwrap"), "d" * 40))
        self.run.assert_not_called()

    def test_member_owned_attachment_satisfies_the_attach_adapter(self):
        value = inputs.attach(self.w.build())
        owner = self.w.subjects[1]
        self.assertEqual((value["authority"]["owner"], value["authority"]["creator"], value["authority"]["creatorAccountCapability"]), (owner, MANAGER, "4202"))
        self.assertEqual(value["authority"]["tool"], {"task": "79022", "capability": "8101", "observeCapability": "8101"})
        self.assertEqual(value["authority"]["parent"], {"task": "79011", "capability": "7303", "observeCapability": "7303"})
        self.assertEqual((value["authority"]["tariff"], value["authority"]["template"]["issuer"]), ({"base": "4", "perBirth": "3"}, "51"))
        self.assertEqual(value["lifecycleDelegation"], {"ownerWorkspace": self.w.ctx["memberInventory"][owner]["workspace"], "manager": MANAGER, "requestId": "hosting-640001"})
        self.assertEqual(value["keys"][owner]["keyId"], "770001")
        self.assertEqual(value["room"], {"target": "880001", "capability": "880002"})
        self.assertEqual(set(value["keys"]), {CUSTODIAN, MANAGER, *self.w.subjects[:3]})
        # The consumer's own validation accepts exactly what the builder emits.
        manifest, artifacts = app.validate(value)
        self.assertEqual(artifacts["spkHost"]["path"], str(self.w.root / "spkHost"))

    def test_population_is_a_parameter(self):
        for members in (1, 10):
            with tempfile.TemporaryDirectory() as temp:
                self.w = World(Path(temp), members=members)
                value = inputs.attach(self.w.build())
                self.assertEqual(len(value["delegates"]), members)
                numbers = [value["application"][k] for k in inputs.APP_RESOURCES + inputs.APP_CAPABILITIES]
                numbers += [d[k] for d in value["delegates"].values() for k in inputs.SESSION_RESOURCES + inputs.SESSION_CAPABILITIES]
                self.assertEqual(len(set(numbers)), 9 + 12 * members)
                app.validate(value)

    def test_stale_member_key_and_an_owner_outside_the_inventory_refuse(self):
        self.w.status[self.w.ctx["memberInventory"][self.w.subjects[2]]["workspace"]]["isCurrent"] = False
        with self.assertRaisesRegex(RuntimeError, "current signing key"):
            inputs.attach(self.w.build())
        # The host manager is not a member: an app is hosted for its owner.
        for owner in ("5555", MANAGER):
            self.w.selection["app"]["owner"] = owner
            with self.assertRaisesRegex(RuntimeError, "not in the world's member inventory"):
                inputs.attach(self.w.build())

    def test_foreign_workspace_changed_pins_and_overlapping_numbers_refuse(self):
        self.w.selection["app"]["capabilities"] = "640005"
        with self.assertRaisesRegex(RuntimeError, "overlap"):
            inputs.attach(self.w.build())
        self.w.selection["app"]["capabilities"] = "970001"
        workspace = Path(self.w.ctx["memberInventory"][self.w.subjects[2]]["workspace"]) / "workspace.json"
        pin = json.loads(workspace.read_text()); pin["socket"] = "/another/world.sock"; workspace.write_text(json.dumps(pin))
        with self.assertRaisesRegex(RuntimeError, "not bound to the supplied world"):
            inputs.attach(self.w.build())
        (self.w.root / "config.json").write_text("{}")
        with self.assertRaisesRegex(RuntimeError, "configuration pin differs"):
            self.w.build()

    def test_socket_bound_is_checked_on_the_actual_state_path(self):
        root = Path(self.tmp.name) / "framed"; root.mkdir()
        self.w = World(root, grains=Path("/var/lib/mini-bigstep-hbox-r1/grains"))
        world = self.w.build()
        world.socket_bound("530101", [inputs.route_name("member-0")])
        with self.assertRaisesRegex(RuntimeError, "exceeds 107 bytes"):
            world.socket_bound("5301010000000", [inputs.route_name("member-0")])
        with self.assertRaisesRegex(RuntimeError, "exceeds 107 bytes"):
            world.socket_bound("530101", ["connector-with-a-long-route-name"])
        self.assertEqual(inputs.route_name("A" * 64), app.route_name("A" * 64))

    def test_connector_and_journey_inputs_match_their_consumers(self):
        connector = self.w.subjects[3]
        self.w.selection["connector"] = {"subject": connector, "name": "csv", "expectedHost": "csv.spk.localhost:18443", "sheet": "lab-sheet", "role": "1",
            "task": "task", "document": "document", "resources": "650001", "capabilities": "980001",
            "reader": {"subject": self.w.subjects[0], "document": "shared-notes"}, "endpoint": "https://csv.spk.localhost:18443/", "ca": None, "operation": "export-1"}
        world = self.w.build()
        attach = inputs.attach(world)
        fixture = self.w.root / "fixture.json"
        fixture.write_text(json.dumps({"keys": attach["keys"], "application": attach["application"], "delegates": attach["delegates"]}))
        attached = self.w.root / "attached.json"
        attached.write_text(json.dumps({"protocol": "mini-spk-same-store-attached-v1", "miniConfigSha256": self.w.ctx["identity"]["configSha256"], "fixture": str(fixture), "appId": "640001"}))
        value = inputs.connector(world, attached)
        self.assertEqual(set(value), {"protocol", "root", "fixture", "fixtureSha256", "delegate", "key", "workspace", "task", "document", "roleBasis", "sheet"})
        self.assertEqual((value["roleBasis"], value["delegate"]["sessionKind"], value["key"]["keyId"]), ({"type": "role", "id": "1"}, "web", "770003"))
        self.w.selection["connector"]["resources"] = "640004"
        with self.assertRaisesRegex(RuntimeError, "overlaps the attached app"):
            inputs.connector(self.w.build(), attached)
        self.w.selection["connector"].update(resources="650001", subject=self.w.subjects[1])
        with self.assertRaisesRegex(RuntimeError, "independent"):
            inputs.connector(self.w.build(), attached)
        self.w.selection["connector"]["subject"] = connector
        provisioned = self.w.root / "result.json"
        provisioned.write_text(json.dumps({"protocol": "mini-app-document-provisioned-v1", "subject": connector, "fixture": str(self.w.root / "connector/fixture.json")}))
        value = inputs.journey(self.w.build(), provisioned)
        self.assertEqual(set(value), {"protocol", "root", "provisioned", "provisionedSha256", "mini", "endpoint", "ca", "operation", "taskReference", "documentReference", "reader"})
        self.assertEqual(value["reader"], {"workspace": self.w.ctx["memberInventory"][self.w.subjects[0]]["workspace"], "document": "shared-notes"})
        self.w.selection["connector"]["reader"]["subject"] = connector
        with self.assertRaisesRegex(RuntimeError, "independent participant"):
            inputs.journey(self.w.build(), provisioned)


if __name__ == "__main__":
    unittest.main()
