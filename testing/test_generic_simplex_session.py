import importlib.util
import json
import os
from pathlib import Path
import select
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import time
import unittest

path = Path(__file__).with_name("generic-simplex-session.py")
spec = importlib.util.spec_from_file_location("session_adapter", path)
adapter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adapter)


class SessionSocketBoundary(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.attempts = self.root / "attempts"
        self.attempts.mkdir(mode=0o700)
        self.path = self.root / "backend.sock"
        self.wrapper = self.root / "native"
        self.wrapper.write_text(r"""#!/usr/bin/env python3
import json,os,sys,time
from pathlib import Path
log=Path(__file__).with_name('dispatches')
for line in sys.stdin:
    call,out,fuel=json.loads(line)
    body=Path(call).read_bytes()
    with log.open('a') as f:f.write(json.dumps([os.getpid(),body.hex(),fuel])+'\n')
    if body==b'delay':time.sleep(10)
    p=Path(out);p.write_bytes(b'native:'+body);os.chmod(p,0o600)
    print('done',flush=True)
""")
        self.wrapper.chmod(0o700)
        self.server = subprocess.Popen(
            [sys.executable, str(path), "serve", str(self.path), str(self.wrapper),
             str(self.attempts), "12", "1", "owner-private"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        self.assertTrue(select.select([self.server.stdout], [], [], 3)[0])
        self.assertEqual(self.server.stdout.readline(), b"SESSION BACKEND READY\n")

    def tearDown(self):
        if self.server.poll() is None:
            self.server.terminate()
            try:self.server.wait(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(self.server.pid, signal.SIGKILL)
                self.server.wait()
        self.server.stdout.close()
        self.server.stderr.close()
        self.temp.cleanup()

    def call_file(self, name, data):
        path = self.root / name
        adapter.bridge.save_call(path, data)
        return path

    def dispatches(self):
        path = self.root / "dispatches"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def test_original_submission_seam_two_calls_one_native_process(self):
        outer = self.root / "outer"
        outer.mkdir(mode=0o700)
        prefix = [sys.executable, str(path), "submit", str(self.path)]
        for payload in [b"first", b"second"]:
            result = adapter.bridge.run_submission(prefix, outer, 12, 3, payload)
            self.assertEqual(result, b"native:" + payload)
        calls = self.dispatches()
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0][0], calls[1][0])
        self.assertEqual([bytes.fromhex(x[1]) for x in calls], [b"first", b"second"])
        self.assertEqual(sorted(p.read_bytes() for p in outer.glob("*/call.bin")),
                         [b"first", b"second"])

    def test_wrong_fuel_refused_before_dispatch(self):
        original = self.call_file("call", b"held")
        with self.assertRaises(RuntimeError):
            adapter.submit(self.path, original, self.root / "outcome", 13)
        self.assertEqual(self.dispatches(), [])
        self.assertFalse((self.root / "outcome").exists())

    def test_timeout_retains_once_no_automatic_dispatch(self):
        original = self.call_file("call", b"delay")
        with self.assertRaises(RuntimeError):
            adapter.submit(self.path, original, self.root / "outcome", 12)
        time.sleep(0.1)
        self.assertEqual(len(self.dispatches()), 1)
        self.assertEqual(original.read_bytes(), b"delay")
        self.assertFalse((self.root / "outcome").exists())
        pid = self.dispatches()[0][0]
        self.assertFalse(Path('/proc/'+str(pid)).exists())

    def test_oversized_request_does_not_dispatch(self):
        with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as connection:
            connection.connect(str(self.path))
            connection.sendall(struct.pack('<I', adapter.MAX_REQUEST + 1))
            self.assertEqual(connection.recv(1), b'')
        self.assertEqual(self.dispatches(), [])

    def test_client_refuses_public_call_file(self):
        original = self.call_file("call", b"held")
        original.chmod(0o644)
        with self.assertRaises(RuntimeError):
            adapter.submit(self.path, original, self.root / "outcome", 12)
        self.assertEqual(self.dispatches(), [])

    def test_socket_owner_permissions_and_shutdown(self):
        self.assertEqual(self.path.stat().st_mode & 0o777, 0o600)
        original = self.call_file("call", b"once")
        adapter.submit(self.path, original, self.root / "outcome", 12)
        pid = self.dispatches()[0][0]
        self.server.terminate();self.server.wait(timeout=3)
        self.assertFalse(self.path.exists())
        self.assertFalse(Path('/proc/'+str(pid)).exists())


if __name__ == '__main__':unittest.main()
