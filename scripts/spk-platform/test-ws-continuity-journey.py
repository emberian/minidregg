#!/usr/bin/env python3
"""Local Unix/RFC6455 fixture tests. This server is not Mini authority evidence."""
import base64
import hashlib
import importlib.util
import json
from pathlib import Path
import socket
import ssl
import struct
import sys
import tempfile
import threading
import time
import unittest

spec = importlib.util.spec_from_file_location("continuity_journey", Path(__file__).with_name("ws-continuity-journey.py"))
journey = importlib.util.module_from_spec(spec)
spec.loader.exec_module(journey)


def exact(sock, count):
    data = b""
    while len(data) < count:
        part = sock.recv(count-len(data))
        if not part:
            raise EOFError()
        data += part
    return data


def receive(sock):
    a, b = exact(sock, 2)
    count = b & 127
    if count == 126:
        count = struct.unpack("!H", exact(sock, 2))[0]
    elif count == 127:
        count = struct.unpack("!Q", exact(sock, 8))[0]
    mask = exact(sock, 4) if b & 128 else b"\0"*4
    data = exact(sock, count)
    return a & 15, bytes(v ^ mask[i % 4] for i, v in enumerate(data))


class FakeApp:
    def __init__(self, root, leak=False, charge=False, false_close=False, tls=False, rotate=False):
        self.root, self.leak, self.charge = root, leak, charge
        self.false_close = false_close
        self.rotate = rotate
        self.tokens = {}
        self.tls = None
        cert = Path(__file__).resolve().parents[2] / "native/spk-host/tests/fixtures/browser-proxy-test.crt"
        if tls:
            self.tls = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            self.tls.load_cert_chain(str(cert), str(cert.with_suffix(".key")))
        self.active = {"a": True, "b": True}
        self.count, self.billing, self.height = 0, 0, 10
        self.clients, self.listeners, self.headers = [], [], []
        self.log = []
        self.lock = threading.RLock()
        self.artifact = root / "fixture-action.json"
        self.artifact.write_text('{"testOnly":true}')
        self.config = {"room": "test", "roomSuffix": "localfixture", "leaseSeconds": .1,
                       "durationSeconds": .23, "trafficIntervalSeconds": .01, "responseTimeoutSeconds": .5,
                       "absenceObservationSeconds": .01, "cutoffToleranceSeconds": .08, "delegates": {},
                       "hooks": {"snapshot": ["unused"], "revokeA": ["unused"], "regrantA": ["unused"]}}
        for key in ("a", "b"):
            token = root / (key + ".token")
            self.tokens[key] = key + "-private-token"
            token.write_text(self.tokens[key])
            path = root / (key + ".sock")
            listener = socket.socket(socket.AF_INET if tls else socket.AF_UNIX)
            listener.bind(("127.0.0.1", 0) if tls else str(path)); listener.listen(8)
            self.listeners.append(listener)
            self.config["delegates"][key] = {"subject": "8" if key == "a" else "9",
                "session": "6208" if key == "a" else "6209",
                "endpoint": ({"token": str(token), "origin": "https://localhost:%d" % listener.getsockname()[1], "ca": str(cert)}
                             if tls else {"token": str(token), "unix_socket": str(path), "host": key + ".test"})}
            threading.Thread(target=self.accept, args=(listener, key), daemon=True).start()

    def accept(self, listener, key):
        while True:
            try:
                peer, _ = listener.accept()
            except OSError:
                return
            if self.tls:
                try:
                    peer = self.tls.wrap_socket(peer, server_side=True)
                except ssl.SSLError:
                    peer.close()
                    continue
            threading.Thread(target=self.serve, args=(peer, key), daemon=True).start()

    def send(self, peer, value):
        data = value.encode()
        head = bytes([129, len(data)]) if len(data) < 126 else bytes([129, 126])+struct.pack("!H", len(data))
        with self.lock:
            peer.sendall(head+data)

    def serve(self, peer, key):
        try:
            header = b""
            while b"\r\n\r\n" not in header:
                header += exact(peer, 1)
            headers = {k.lower(): v.strip() for k, v in [line.split(":", 1) for line in header.decode().split("\r\n")[1:] if ":" in line]}
            with self.lock:
                self.headers.append(headers)
                if not self.active[key]:
                    peer.sendall(b"HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\n\r\n")
                    return
                if headers["cookie"] != "__Host-mini_spk_session="+self.tokens[key]:
                    return
                accept = base64.b64encode(hashlib.sha1(headers["sec-websocket-key"].encode()+journey.wsmod.GUID).digest()).decode()
                peer.sendall(("HTTP/1.1 101 Switching Protocols\r\nSec-WebSocket-Accept: "+accept+"\r\n\r\n").encode())
                self.clients.append((key, peer)); self.count += 1; self.height += 1
            self.send(peer, '0{"pingInterval":25000}')
            self.send(peer, "40")
            while True:
                op, data = receive(peer)
                if op == 8:
                    return
                if data == b"2":
                    self.send(peer, "3"); continue
                if not data.startswith(b"42"):
                    continue
                command = json.loads(data[2:])[1]
                with self.lock:
                    if command["type"] == "ask.log":
                        self.send(peer, "42"+json.dumps(["data", {"type": "log", "log": self.log}]))
                    elif command["type"] == "execute":
                        self.log.append(command["cmdstr"])
                        if self.charge:
                            self.count += 1; self.billing += 1; self.height += 1
                        for _, target in self.clients:
                            try:
                                self.send(target, "42"+json.dumps(["data", command]))
                            except OSError:
                                pass
        except (OSError, EOFError, ValueError):
            pass
        finally:
            with self.lock:
                self.clients = [(k, s) for k, s in self.clients if s is not peer]
            peer.close()

    def hook(self, name):
        with self.lock:
            if name == "snapshot":
                return {"schema": "spk-ws-continuity-snapshot-v1", "app": "4501", "generation": "4",
                        "dispatchCount": self.count, "billingCount": self.billing, "storeHeight": self.height,
                        "delegates": {k: {"subject": self.config["delegates"][k]["subject"],
                                           "session": self.config["delegates"][k]["session"], "active": self.active[k]} for k in ("a", "b")}}
            self.height += 1
            if name == "revokeA":
                self.active["a"] = False
                if not self.leak:
                    for key, peer in list(self.clients):
                        if key == "a":
                            if self.false_close:
                                peer.sendall(b"\x88\x02\x03\xe8")
                            else:
                                peer.shutdown(socket.SHUT_RDWR)
            elif name == "regrantA":
                self.active["a"] = True
            elif name == "generationStop":
                for _, peer in list(self.clients):
                    peer.shutdown(socket.SHUT_RDWR)
            result = {"schema": "spk-ws-continuity-action-v1", "action": name, "confirmed": True, "artifact": str(self.artifact)}
            if name == "regrantA" and self.rotate:
                self.tokens["a"] = "a-regranted-private-token"
                token = self.root / "a-regrant.token"
                token.write_text(self.tokens["a"])
                result["endpoint"] = dict(self.config["delegates"]["a"]["endpoint"], token=str(token))
            return result

    def close(self):
        for listener in self.listeners:
            listener.close()
        for _, peer in list(self.clients):
            try:
                peer.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass


class Tests(unittest.TestCase):
    def run_fixture(self, **options):
        temp = tempfile.TemporaryDirectory(prefix="ws-continuity-")
        self.addCleanup(temp.cleanup)
        app = FakeApp(Path(temp.name), **options)
        self.addCleanup(app.close)
        run = journey.Journey(app.config)
        self.addCleanup(run.close)
        run.hook = app.hook
        return app, run

    def test_two_authenticated_endpoints_sustain_revoke_and_regrant(self):
        app, run = self.run_fixture()
        result = run.run()
        self.assertEqual(result["status"], "passed")
        self.assertGreater(result["traffic"]["seconds"], 2*app.config["leaseSeconds"])
        self.assertEqual(result["newAOpen"], {"status": "403", "refused": True})
        self.assertTrue(result["regrant"]["freshOpenAndEdit"])
        self.assertEqual({h["host"] for h in app.headers}, {"a.test", "b.test"})
        self.assertEqual({h["cookie"] for h in app.headers}, {"__Host-mini_spk_session=a-private-token", "__Host-mini_spk_session=b-private-token"})
        self.assertNotIn("private-token", json.dumps(result))

    def test_regrant_can_replace_only_a_endpoint_credentials(self):
        app, run = self.run_fixture(rotate=True)
        result = run.run()
        self.assertTrue(result["regrant"]["endpointReplaced"])
        self.assertIn("__Host-mini_spk_session=a-regranted-private-token", {h["cookie"] for h in app.headers})
        self.assertNotIn("private-token", json.dumps(result))

    def test_verified_tls_origins_keep_credentials_separate(self):
        cert = Path(__file__).resolve().parents[2] / "native/spk-host/tests/fixtures/browser-proxy-test.crt"
        if not cert.exists():
            self.skipTest("run from source tree for public localhost TLS fixture")
        app, run = self.run_fixture(tls=True)
        self.assertEqual(run.run()["status"], "passed")
        self.assertEqual(len({h["host"] for h in app.headers}), 2)
        self.assertEqual(len({h["cookie"] for h in app.headers}), 2)

    def test_explicit_missing_billing_counter_uses_verified_height(self):
        app, run = self.run_fixture()
        def hook(name):
            result = app.hook(name)
            if name == "snapshot":
                result.update(billingCount=None, billingEvidence="fixture verified height; no classified billing counter")
            return result
        run.hook = hook
        report = run.run()
        self.assertTrue(report["directBillingCounter"].startswith("unqualified"))
        self.assertEqual(report["status"], "passed")

    def test_missing_cutoff_is_a_failure_not_a_successful_tcp_write(self):
        _, run = self.run_fixture(leak=True)
        with self.assertRaisesRegex(AssertionError, "A did not end"):
            run.run()

    def test_close_frame_with_fresh_app_writes_is_rejected(self):
        _, run = self.run_fixture(false_close=True)
        with self.assertRaisesRegex(AssertionError, "fresh A write observed"):
            run.run()

    def test_optional_generation_stop_records_stream_closure(self):
        _, run = self.run_fixture()
        run.c["hooks"]["generationStop"] = ["unused"]
        self.assertTrue(run.run()["generationStop"]["allStreamsEnded"])

    def test_renewal_only_billing_or_dispatch_delta_fails(self):
        _, run = self.run_fixture(charge=True)
        with self.assertRaisesRegex(AssertionError, "renewal-only counters changed"):
            run.run()

    def test_hook_is_argv_json_and_tokens_are_not_shared(self):
        app, run = self.run_fixture()
        run.c["hooks"]["snapshot"] = [sys.executable, "-c", 'import os,json; print(json.dumps({"room":os.environ["SPK_CONTINUITY_ROOM"],"action":os.environ["SPK_CONTINUITY_ACTION"]}))']
        self.assertEqual(journey.Journey.hook(run, "snapshot"), {"room": run.room, "action": "snapshot"})
        bpath = Path(app.config["delegates"]["b"]["endpoint"]["token"])
        bpath.write_text("a-private-token")
        with self.assertRaisesRegex(AssertionError, "different authentication tokens"):
            journey.Journey(app.config)


if __name__ == "__main__":
    unittest.main()
