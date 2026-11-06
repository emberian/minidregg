"""The source-binding header exception must not hide executable/import edits."""
import hashlib
import importlib.util
import io
from pathlib import Path
import tarfile
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    "jump_check", Path(__file__).with_name("check-simplex-jump.py"))
jump = importlib.util.module_from_spec(spec)
spec.loader.exec_module(jump)


class HeaderBinding(unittest.TestCase):
    def setUp(self):
        self.current = jump.SOURCE.read_text()
        marker = "namespace Minidregg.Kernel.GenericSimplex"
        self.legacy = "import Std\n" + self.current[self.current.index(marker):]

    def test_exact_module_port_preserves_whole_kernel(self):
        self.assertEqual(jump.kernel_code(self.current), jump.code(self.legacy))
        self.assertEqual(jump.kernel_code(self.legacy), jump.code(self.legacy))

    def test_different_or_extra_imports_are_not_erased(self):
        for changed in (
            self.current.replace("public import Std", "public import Lean", 1),
            self.current.replace("import all Init.Util", "import all Init.Util\nimport Lean", 1),
            self.current.replace("@[expose] public section", "public section", 1),
        ):
            with self.subTest(header=jump.code(changed).split("namespace", 1)[0]):
                self.assertNotEqual(jump.kernel_code(changed), jump.code(self.legacy))

    def test_adapter_preserves_exact_namespace_body(self):
        adapted = jump.adapt_oracle(self.legacy)
        jump.check_adapted_oracle(self.legacy, adapted)
        self.assertEqual(adapted.partition(jump.NAMESPACE)[2],
                         self.legacy.partition(jump.NAMESPACE)[2])
        self.assertEqual(jump.kernel_code(adapted), jump.code(self.legacy))

    def test_adapter_refuses_extra_imports_in_either_input(self):
        adapted = jump.adapt_oracle(self.legacy)
        for extra in ("import Lean\n", "import all Init.Prelude\n"):
            with self.subTest(extra=extra):
                with self.assertRaises(ValueError):
                    jump.adapt_oracle(self.legacy.replace(jump.NAMESPACE, extra + jump.NAMESPACE, 1))
                with self.assertRaises(ValueError):
                    jump.check_adapted_oracle(self.legacy,
                        adapted.replace(jump.NAMESPACE, extra + jump.NAMESPACE, 1))

    def test_adapter_refuses_successor_and_body_whitespace_changes(self):
        adapted = jump.adapt_oracle(self.legacy)
        for changed in (adapted.replace("preparedAbove s + 1", "preparedAbove s"),
                        adapted + "\n"):
            with self.subTest(changed=changed[-80:]):
                with self.assertRaises(ValueError):
                    jump.check_adapted_oracle(self.legacy, changed)

    def test_binding_restores_local_source_after_build_or_mutation_failure(self):
        # Simulate failures at both compiler and same-copy mutation boundaries.
        oracle = self.legacy.replace("s.offers.find?", "s.offers.reverse.find?").encode()
        native = b"pinned native fixture"
        with tempfile.TemporaryDirectory() as scratch:
            source = Path(scratch) / "GenericSimplex.lean"
            bundle = Path(scratch) / "source.tar"
            with tarfile.open(bundle, "w", format=tarfile.PAX_FORMAT,
                              pax_headers={"comment": "a" * 40}) as archive:
                for name, content in (("clockdag-simplex-oracle/Kernel/GenericSimplex.lean", oracle),
                                      ("crates/mesh-simplex/src/lib.rs", native)):
                    info = tarfile.TarInfo(name)
                    info.size = len(content)
                    archive.addfile(info, io.BytesIO(content))
            args = SimpleNamespace(bundle=str(bundle), clockdag_tip="a" * 40,
                native_sha256=hashlib.sha256(native).hexdigest(),
                oracle_sha256=hashlib.sha256(oracle).hexdigest(), kernel_check=True)
            for fail_build in (True, False):
                source.write_text(self.current)
                calls = []
                def build(argv):
                    calls.append(source.read_bytes())
                    return SimpleNamespace(returncode=int(fail_build and len(calls) == 1),
                                           stdout="injected build failure")
                def fail_mutation(_args, *, representation):
                    self.assertEqual(representation, "header-adapted-c5-oracle")
                    self.assertEqual(source.read_bytes(), jump.adapt_oracle(oracle.decode()).encode())
                    source.write_text("injected partial mutation")
                    raise ValueError("injected mutation failure")
                with self.subTest(fail_build=fail_build), patch.object(jump, "SOURCE", source), \
                        patch.dict(jump.os.environ, {"FAB_ID": "test-fixture"}), \
                        patch.object(jump, "run", side_effect=build), \
                        patch.object(jump, "claims"), \
                        patch.object(jump, "mutate", side_effect=fail_mutation):
                    with self.assertRaisesRegex(ValueError,
                            "proof closure failed" if fail_build else "injected mutation failure"):
                        jump.bind(args)
                    self.assertEqual(source.read_bytes(), self.current.encode())
                    self.assertEqual(len(calls), 2)
                    self.assertEqual(calls[0], jump.adapt_oracle(oracle.decode()).encode())
                    self.assertEqual(calls[-1], self.current.encode())

    def test_missing_or_wrong_jump_remains_visible(self):
        original = "s := enterView c s (preparedAbove s + 1)"
        self.assertEqual(self.current.count(original), 1)
        for replacement in ("s := s", "s := enterView c s (preparedAbove s)"):
            with self.subTest(replacement=replacement):
                changed = self.current.replace(original, replacement)
                self.assertNotEqual(jump.kernel_code(changed), jump.code(self.legacy))


if __name__ == "__main__":
    unittest.main()
