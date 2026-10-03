import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("same_world_resident", HERE / "same-world-resident.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)

class ResidentBindingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        # The existing source input fixture deliberately uses unrelated IDs.
        file = HERE.parent.parent / "scripts/spk-platform/tests/test_same_store_inputs.py"
        spec = importlib.util.spec_from_file_location("world_fixture", file)
        f = importlib.util.module_from_spec(spec); spec.loader.exec_module(f)
        self.world = f.World(self.root)
        (self.root / "platform-inputs.json").write_text(json.dumps(self.world.ctx))
        self.inventory = {"type": "mini-world-identity-v1", "members": {
            "person-" + str(i): row for i, row in enumerate(self.world.ctx["memberInventory"].values())}}
        founder = self.inventory["members"]["person-0"]
        (self.root / "provider.py").write_bytes(b"local scripted provider fixture")
        self.binding = {"protocol": r.PROTOCOL, "platformInputs": str(self.root / "platform-inputs.json"),
            "base": str(self.root / "frame"), "authors": ["person-0", "person-1"], "providerWitness": "person-2",
            "room": {"alias": "lab", "mode": "adopt"}, "sharedDocumentReference": str(Path(founder["workspace"]) / "refs/lab.json"),
            "fixtureAcp": {"path": str(self.root / "mini"), "sha256": r.sha(self.root / "mini")},
            "fixtureProvider": {"path": str(self.root / "provider.py"), "sha256": r.sha(self.root / "provider.py")},
            "registration": str(self.root / "registration.json"), "task": 7991, "requestCounts": [2, 1]}

    def test_named_binding_accepts_variable_authors_and_native_workroom_adoption(self):
        ctx, manifest, missing = r.validate(self.binding, self.inventory)
        self.assertFalse(missing)
        self.assertEqual(ctx["publicSocket"], self.world.ctx["publicSocket"])
        self.assertEqual(manifest["host"], str(self.root / "host"))

    def test_foreign_workspace_and_provider_author_collision_refuse(self):
        inventory = json.loads(json.dumps(self.inventory))
        inventory["members"]["person-1"]["workspace"] = "/other/store"
        with self.assertRaisesRegex(ValueError, "participant differ"):
            r.validate(self.binding, inventory)
        binding = dict(self.binding, providerWitness="person-0")
        with self.assertRaisesRegex(ValueError, "independent"):
            r.validate(binding, self.inventory)

    def test_fixture_pin_cannot_change_and_no_arbitrary_command_is_accepted(self):
        (self.root / "provider.py").write_bytes(b"changed fixture")
        with self.assertRaisesRegex(ValueError, "bytes changed"):
            r.validate(self.binding, self.inventory)
        with self.assertRaisesRegex(ValueError, "fields differ"):
            r.validate(dict(self.binding, argv=["danger"]), self.inventory)

    def test_restart_command_resumes_same_receiving_root_and_retains_world_binding(self):
        receiving = Path(self.binding["base"]) / "var/lib/mini/controllers/7991/receiving"
        receiving.mkdir(parents=True)
        words = r.command(self.binding, self.root / "WORLD.json", receiving / "capture.json", "retain")
        self.assertIn("--resume", words)
        self.assertIn("--preserve-on-success", words)
        self.assertEqual(words[words.index("--through") + 1], "retain")
        self.assertEqual(words[words.index("--member-names") + 1], str(self.root / "WORLD.json"))
        self.assertEqual(words[words.index("--request-counts") + 1], "2,1")
        self.assertNotIn("--settle", words)

    def capture(self):
        body = b"a,b\n1,2\n"
        receipt = {"bodyBytes": str(len(body)), "bodySha256": r.hashlib.sha256(body).hexdigest(), "operation": "export-1", "transaction": "7"}
        result = {"protocol": "mini-app-document-journey-result-v1", "status": "saved", "target": "880001",
                  "operation": "export-1", "receipt": receipt, "callSha256": "a" * 64}
        path = self.root / "connector-result.json"; path.write_text(json.dumps(result))
        marker = "Export " + receipt["bodySha256"] + " · operation export-1 · receipt 7"
        page = {"type": "document", "host": "880001", "lines": [{"kind": "atom", "text": line} for line in (marker, "a,b", "1,2")]}
        room = {"protocol": "mini-resident-room-capture-request-v1", "worldConfig": "/config", "socket": "/public",
                "founderSubject": "9", "founderWorkspace": "/member", "founderHome": "/home/member",
                "roomAlias": "lab", "roomTarget": "77", "documentAlias": "lab", "documentTarget": "880001"}
        return room, result, path, page

    def test_capture_bridge_requires_exact_export_bytes_and_keeps_native_receipt(self):
        room, result, path, page = self.capture()
        bridge = r.capture_context(room, result, path, page)
        self.assertEqual(bridge["protocol"], "mini-captured-document-room-context-v1")
        self.assertEqual(bridge["sourceExport"]["receipt"], result["receipt"])
        self.assertEqual(bridge["sourceExport"]["resultSha256"], r.sha(path))
        self.assertNotIn("founderHome", bridge)
        page["lines"][-1]["text"] = "another export"
        with self.assertRaisesRegex(RuntimeError, "bytes differ"):
            r.capture_context(room, result, path, page)

    def test_provision_only_uncertainty_or_another_document_cannot_feed_resident(self):
        room, result, path, page = self.capture()
        with self.assertRaisesRegex(ValueError, "saved"):
            r.capture_context(room, dict(result, status="uncertain"), path, page)
        with self.assertRaisesRegex(ValueError, "another"):
            r.capture_context(room, dict(result, target="other"), path, page)

if __name__ == "__main__":
    unittest.main()
