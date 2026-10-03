"""Source-pin rejection tests; no external tree mutation or compiler invocation."""
import hashlib
import importlib.util
import pathlib
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location("provision", pathlib.Path(__file__).parents[1] / "provision.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SourcePins(unittest.TestCase):
    def test_exact_missing_and_changed_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            file = root / "Cargo.toml"
            file.write_bytes(b"pinned source\n")
            pins = {"Cargo.toml": hashlib.sha256(file.read_bytes()).hexdigest()}
            MODULE.verify(root, pins)
            file.write_bytes(b"different source\n")
            with self.assertRaisesRegex(ValueError, "changed pinned source"):
                MODULE.verify(root, pins)
            file.unlink()
            with self.assertRaisesRegex(ValueError, "missing pinned source"):
                MODULE.verify(root, pins)


if __name__ == "__main__":
    unittest.main()
