import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

HELPER = Path(__file__).resolve().parents[3] / "deploy/spk-host/spk-ingest"
STORE = "0123456789abcdef"


class IngestNamespace(unittest.TestCase):
    def invoke(self, root, workspace):
        marker = workspace / "effect"
        host = workspace / "host"
        host.write_text(f'#!/bin/sh\ntouch "{marker}"\n')
        host.chmod(0o700)
        systemd = workspace / "systemd-run"
        systemd.write_text(f'#!/bin/sh\ntouch "{marker}"\nexit 99\n')
        systemd.chmod(0o700)
        env = dict(os.environ, PATH=str(workspace) + os.pathsep + os.environ["PATH"])
        return subprocess.run(
            ["bash", str(HELPER), "--root", root, str(host),
             hashlib.sha256(host.read_bytes()).hexdigest(), root.rstrip("/") + "/inbox/package.spk", "64010"],
            env=env, capture_output=True, text=True, timeout=5)

    def test_unsafe_root_arguments_refused_before_custody_or_effects(self):
        with tempfile.TemporaryDirectory() as raw:
            base = Path(raw)
            selected = base / STORE / "spk"
            for root in ("/", "relative", "/../owned", "/tmp/../owned", "/tmp/owned/", "/tmp/./owned",
                         str(selected) + "/", str(base / "global" / "spk"), str(base / STORE / "other")):
                with self.subTest(root=root):
                    result = self.invoke(root, base)
                    self.assertEqual(result.returncode, 2)
                    self.assertIn("SPK", result.stderr)
                    self.assertFalse(selected.exists())
                    self.assertFalse((base / "effect").exists())
                    self.assertFalse((base / "global").exists())
                    self.assertFalse((base / STORE).exists())

    def test_symlinked_root_refused_before_custody_or_effects(self):
        with tempfile.TemporaryDirectory() as raw:
            base = Path(raw)
            world = base / STORE
            selected = world / "spk"
            (base / "alias").symlink_to(base)
            # A valid store ID and package pin must not mask an ancestor alias.
            result = self.invoke(str(base / "alias" / STORE / "spk"), base)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("canonical and not symlinked", result.stderr)
            self.assertFalse(selected.exists())
            self.assertFalse(world.exists())
            self.assertFalse((base / "effect").exists())

    @unittest.skipIf(os.geteuid() == 0, "operator refusal requires ordinary test user")
    def test_valid_isolated_root_has_no_effect_for_nonroot_caller(self):
        with tempfile.TemporaryDirectory() as raw:
            base = Path(raw)
            selected = base / STORE / "spk"
            result = self.invoke(str(selected), base)
            self.assertNotEqual(result.returncode, 0)
            # New design permits the operator, but never bootstraps missing custody.
            self.assertIn("package.spk", result.stderr)
            self.assertFalse(selected.exists())
            self.assertFalse((base / STORE).exists())
            self.assertFalse((base / "effect").exists())
