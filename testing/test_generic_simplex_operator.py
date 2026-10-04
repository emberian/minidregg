import importlib.util
import io
from pathlib import Path
import struct
import sys
import tempfile
import unittest

path = Path(__file__).with_name("generic-simplex-operator.py")
spec = importlib.util.spec_from_file_location("agreement_operator", path)
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)


class NativeFrameBoundary(unittest.TestCase):
    def test_exact_all_operation_roundtrips(self):
        for operation in range(256):
            stream = io.BytesIO()
            bridge.write_frame(stream, operation, bytes((0, 255, operation)))
            stream.seek(0)
            self.assertEqual(bridge.read_frame(stream), (operation, bytes((0, 255, operation))))
            self.assertIsNone(bridge.read_frame(stream))

    def test_truncation_and_length_refusal(self):
        for raw in (b"\x01", struct.pack("<I", 0),
                    struct.pack("<I", bridge.MAX_FRAME + 1),
                    struct.pack("<I", 3) + b"\x02x"):
            with self.assertRaises(RuntimeError):
                bridge.read_frame(io.BytesIO(raw))

    def test_no_mutation_forwarding_set(self):
        self.assertEqual(bridge.READ_ONLY, frozenset((0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 91, 144)))
        self.assertNotIn(2, bridge.READ_ONLY)
        self.assertFalse((set(range(12, 256)) - {91, 144}) & bridge.READ_ONLY)

    def test_original_call_cannot_be_overwritten(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "call.bin"
            bridge.save_call(path, b"exact-original")
            with self.assertRaises(FileExistsError):
                bridge.save_call(path, b"replacement")
            self.assertEqual(path.read_bytes(), b"exact-original")
            self.assertEqual(path.stat().st_mode & 0o777, 0o600)

    def test_actual_child_reply_is_opaque_and_original_retained(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            code = ("import os,sys;from pathlib import Path;"
                    "p=Path(sys.argv[2]);p.write_bytes(b'opaque-native-frame');"
                    "os.chmod(p,0o600)")
            reply = bridge.run_submission([sys.executable, "-c", code],
                                          root, 12, 2, b"original-call")
            self.assertEqual(reply, b"opaque-native-frame")
            tickets = list(root.iterdir())
            self.assertEqual(len(tickets), 1)
            self.assertEqual((tickets[0] / "call.bin").read_bytes(), b"original-call")

    def test_child_timeout_has_no_automatic_redispatch(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            code = ("import sys,time;from pathlib import Path;"
                    "Path(sys.argv[1]).with_name('started').write_text('once');"
                    "time.sleep(5)")
            with self.assertRaisesRegex(RuntimeError, "completion uncertain"):
                bridge.run_submission([sys.executable, "-c", code],
                                      root, 12, 1, b"retained-after-timeout")
            tickets = list(root.iterdir())
            self.assertEqual(len(tickets), 1)
            self.assertEqual((tickets[0] / "started").read_text(), "once")
            self.assertEqual((tickets[0] / "call.bin").read_bytes(), b"retained-after-timeout")
            self.assertFalse((tickets[0] / "outcome.bin").exists())

    def test_persistent_session_two_calls_one_process_exact_originals(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            code = """import json,os,sys
from pathlib import Path
for line in sys.stdin:
    call,out,fuel=json.loads(line)
    p=Path(out);p.write_bytes(b'receipt:'+Path(call).read_bytes());os.chmod(p,0o600)
    print('done',flush=True)
"""
            session = bridge.SubmissionSession([sys.executable, "-c", code], root)
            pid = session.child.pid
            try:
                self.assertEqual(session.run(12, 2, b"first"), b"receipt:first")
                self.assertEqual(session.run(12, 2, b"second"), b"receipt:second")
                self.assertEqual(session.child.pid, pid)
                calls = sorted(p.read_bytes() for p in root.glob("*/call.bin"))
                self.assertEqual(calls, [b"first", b"second"])
            finally:
                session.close()
            self.assertIsNotNone(session.child.poll())

    def test_persistent_timeout_retains_once_and_refuses_redispatch(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            code = """import json,sys,time
from pathlib import Path
for line in sys.stdin:
    call,out,fuel=json.loads(line)
    Path(call).with_name('started').write_text('once')
    time.sleep(5)
"""
            session = bridge.SubmissionSession([sys.executable, "-c", code], root)
            with self.assertRaisesRegex(RuntimeError, "completion uncertain"):
                session.run(12, 1, b"held-original")
            with self.assertRaisesRegex(RuntimeError, "session stopped"):
                session.run(12, 1, b"must-not-dispatch")
            self.assertEqual(len(list(root.glob("*/call.bin"))), 1)
            self.assertEqual(next(root.glob("*/call.bin")).read_bytes(), b"held-original")
            self.assertIsNotNone(session.child.poll())

    def test_session_ack_is_not_a_receipt(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            code = "import sys;sys.stdin.readline();print('done',flush=True)"
            session = bridge.SubmissionSession([sys.executable, "-c", code], root)
            with self.assertRaises(FileNotFoundError):
                session.run(12, 2, b"original")
            self.assertIsNotNone(session.child.poll())

    def test_private_identical_client_config_copy(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            original, copy = root / "original.json", root / "socket.config"
            for path in (original, copy):
                path.write_bytes(b'{"exact":"profile"}')
                path.chmod(0o600)
            profile = {"clientArguments": [str(original), "stdio"]}
            bridge.check_client_arguments(profile, [str(copy), "stdio"])
            bridge.check_client_arguments(profile, [str(original), "stdio"])
            copy.write_bytes(b'{"other":"profile"}')
            with self.assertRaisesRegex(RuntimeError, "differs"):
                bridge.check_client_arguments(profile, [str(copy), "stdio"])
            for args in ([str(original)], [str(original), "stdio", "extra"],
                         [str(original), "serve"]):
                with self.assertRaises(RuntimeError):
                    bridge.check_client_arguments(profile, args)

    def test_client_config_copy_rejects_public_link_and_fifo(self):
        with tempfile.TemporaryDirectory() as name:
            import os
            root = Path(name)
            original, copy = root / "original.json", root / "copy"
            original.write_bytes(b"pinned")
            original.chmod(0o600)
            profile = {"clientArguments": [str(original), "stdio"]}
            copy.write_bytes(b"pinned")
            copy.chmod(0o644)
            with self.assertRaises(RuntimeError):
                bridge.check_client_arguments(profile, [str(copy), "stdio"])
            link = root / "link"
            link.symlink_to(original)
            with self.assertRaises(OSError):
                bridge.check_client_arguments(profile, [str(link), "stdio"])
            fifo = root / "fifo"
            os.mkfifo(fifo, 0o600)
            with self.assertRaises(RuntimeError):
                bridge.check_client_arguments(profile, [str(fifo), "stdio"])

    def test_outcome_rejects_public_and_linked_files(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            path = root / "outcome.bin"
            path.write_bytes(b"opaque-native-codec")
            path.chmod(0o644)
            with self.assertRaises(RuntimeError):
                bridge.read_outcome(path)
            path.chmod(0o600)
            self.assertEqual(bridge.read_outcome(path), b"opaque-native-codec")
            (root / "link").symlink_to(path)
            with self.assertRaises(OSError):
                bridge.read_outcome(root / "link")


if __name__ == "__main__":
    unittest.main()
