#!/usr/bin/env python3
"""Private submission backend behind the unchanged pinned native Host.

The socket transports original SignedCall bytes and the actual native Outcome.
It introduces no source authority, automatic retry, or new client transport pin.
"""
import importlib.util
import os
from pathlib import Path
import signal
import socket
import stat
import struct
import sys

spec = importlib.util.spec_from_file_location(
    "agreement_operator", Path(__file__).with_name("generic-simplex-operator.py"))
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)
MAX_REQUEST = bridge.MAX_FRAME + 8


def peer_is_owner(connection):
    if not hasattr(socket, "SO_PEERCRED"):
        raise RuntimeError("local peer credentials unavailable")
    _pid, uid, _gid = struct.unpack("3i", connection.getsockopt(
        socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i")))
    if uid != os.getuid():
        raise RuntimeError("submission peer is not this owner")


def receive_request(stream, required_fuel):
    header = bridge.exact(stream, 4)
    count = struct.unpack("<I", header)[0]
    if not 8 < count <= MAX_REQUEST:
        raise RuntimeError("submission request exceeds fixed bound")
    body = bridge.exact(stream, count)
    fuel = struct.unpack("<Q", body[:8])[0]
    if fuel != required_fuel:
        raise RuntimeError("submission fuel differs from pinned service")
    return body[8:]


def serve(path, prefix, attempts, fuel, seconds):
    path, attempts = Path(path), Path(attempts)
    bridge.private_dir(path.parent)
    bridge.private_dir(attempts)
    if path.exists() or path.is_symlink():
        raise RuntimeError("refuse to replace an existing session endpoint")
    listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    session = None
    identity = None
    try:
        listener.bind(str(path))
        os.chmod(path, 0o600)
        identity = path.lstat().st_ino
        listener.listen(4)
        # Prewarm once without a source request. Restart occurs only when a
        # later explicit request arrives after the old session stopped.
        session = bridge.SubmissionSession(prefix, attempts)
        print("SESSION BACKEND READY", flush=True)
        while True:
            connection, _ = listener.accept()
            with connection:
                try:
                    peer_is_owner(connection)
                    connection.settimeout(seconds)
                    with connection.makefile("rwb", buffering=0) as stream:
                        call = receive_request(stream, fuel)
                        if session.closed or session.child.poll() is not None:
                            session.close()
                            session = bridge.SubmissionSession(prefix, attempts)
                        outcome = session.run(fuel, seconds, call)
                        connection.sendall(struct.pack("<I", len(outcome)) + outcome)
                except Exception as error:
                    # The caller keeps its exact original attempt. A closed
                    # response is uncertainty, never permission to redispatch.
                    print("submission session: " + str(error), file=sys.stderr, flush=True)
    finally:
        if session is not None:
            session.close()
        listener.close()
        if identity is not None:
            try:
                info = path.lstat()
                if stat.S_ISSOCK(info.st_mode) and info.st_ino == identity:
                    path.unlink()
            except FileNotFoundError:
                pass


def submit(path, original, outcome, fuel):
    if not 0 < fuel < 2**64:
        raise RuntimeError("invalid finite service fuel")
    # This is the original operator's already fsynced owner-private call.bin.
    # It is copied byte-for-byte; only Lean interprets the signed call.
    call = bridge.read_outcome(Path(original))
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as connection:
        connection.connect(str(path))
        peer_is_owner(connection)
        with connection.makefile("rwb", buffering=0) as stream:
            body = struct.pack("<Q", fuel) + call
            connection.sendall(struct.pack("<I", len(body)) + body)
            count = struct.unpack("<I", bridge.exact(stream, 4))[0]
            if not 0 < count < bridge.MAX_FRAME:
                raise RuntimeError("native outcome exceeds fixed bound")
            reply = bridge.exact(stream, count)
    # Never turn an acknowledgement or process success into confirmation.
    # The bytes are the exact native Outcome; exclusive write preserves custody.
    bridge.save_call(Path(outcome), reply)


def main(args):
    if len(args) == 7 and args[0] == "serve":
        _, path, wrapper, attempts, fuel, seconds, marker = args
        if marker != "owner-private":
            raise RuntimeError("explicit owner-private service required")
        serve(path, [wrapper], attempts, int(fuel), int(seconds))
    elif len(args) == 5 and args[0] == "submit":
        _, path, original, outcome, fuel = args
        submit(path, original, outcome, int(fuel))
    else:
        raise RuntimeError("usage: session serve SOCKET WRAPPER ATTEMPTS FUEL SECONDS owner-private | submit SOCKET CALL OUTCOME FUEL")


if __name__ == "__main__":
    def stopped(_signal, _frame):
        raise SystemExit(0)
    signal.signal(signal.SIGTERM, stopped)
    try:
        main(sys.argv[1:])
    except Exception as error:
        print("agreement session adapter: " + str(error), file=sys.stderr)
        sys.exit(1)
