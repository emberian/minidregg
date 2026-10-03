import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("surfaces", Path(__file__).with_name("lean-build-surfaces.py"))
surfaces = importlib.util.module_from_spec(spec)
spec.loader.exec_module(surfaces)

class BuildSurfaces(unittest.TestCase):
    def fixture(self, root):
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        (root / "lakefile.toml").write_text("".join('[[lean_lib]]\nname = "' + n + '"\n' for n in ["Minidregg", *surfaces.GROUPS, "ResearchWip"]))
        (root / "Minidregg.lean").write_text("")
        for roots in surfaces.GROUPS.values():
            for name in roots:
                p = root / (name.replace(".", "/") + ".lean")
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("namespace Fixture\nend Fixture\n")
        (root / "docs/construction").mkdir(parents=True)
        (root / "docs/construction/source-intake-20261003.json").write_text('{"files": []}')
        (root / "protocol").mkdir()
        subprocess.run(["git", "add", "."], cwd=root, check=True)

    def test_authored_modules_and_programs_get_distinct_targets(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); self.fixture(root)
            (root / "Compiler/Unjoined.lean").write_text("def pending : Nat := 0\n")
            (root / "Host").mkdir()
            (root / "Host/Standalone.lean").write_text("def main : IO Unit := pure ()\n")
            data = surfaces.build(root)
            self.assertIn("Host.Standalone", data["programRoots"])
            self.assertIn("import Compiler.Unjoined", (root / "ResearchWip.lean").read_text())
            self.assertNotIn("Host.Standalone", (root / "ResearchWip.lean").read_text())
            self.assertNotIn("compilerPass", data)

    def test_missing_qualification_root_refuses_generation(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); self.fixture(root)
            name = next(iter(surfaces.GROUPS.values()))[0]
            (root / (name.replace(".", "/") + ".lean")).unlink()
            with self.assertRaisesRegex(ValueError, "Missing qualification"):
                surfaces.build(root)

    def test_check_refuses_changed_source_and_new_unclassified_module(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t); self.fixture(root)
            data = surfaces.build(root)
            (root / "protocol/lean-build-surfaces.json").write_text(json.dumps(data))
            script = str(Path(__file__).with_name("lean-build-surfaces.py"))
            subprocess.run(["python3", script, "check", "--root", str(root)], check=True)
            (root / "Compiler/New.lean").write_text("def newSource : Nat := 0\n")
            run = subprocess.run(["python3", script, "check", "--root", str(root)], capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0); self.assertIn("unclassified", run.stderr)
            (root / "Compiler/New.lean").unlink()
            (root / "Minidregg.lean").write_text("-- changed\n")
            run = subprocess.run(["python3", script, "check", "--root", str(root)], capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0); self.assertIn("source drift", run.stderr)

if __name__ == "__main__":
    unittest.main()
