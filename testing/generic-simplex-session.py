#!/usr/bin/env python3
"""Private submission backend behind the unchanged pinned native Host.

The socket transports original SignedCall bytes and the actual native Outcome.
Each request runs one Lean await client against the standing replicas. It
introduces no source authority, automatic retry, engine lifetime, or new pin.
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
MAX_REQUEST = bridge.MAX_FRAME


def peer_is_owner(connection):
    if not hasattr(socket, "SO_PEERCRED"):
        raise RuntimeError("local peer credentials unavailable")
    _pid, uid, _gid = struct.unpack("3i", connection.getsockopt(
        socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i")))
    if uid != os.getuid():
        raise RuntimeError("submission peer is not this owner")


def receive_request(stream):
    header = bridge.exact(stream, 4)
    count = struct.unpack("<I", header)[0]
    if not 0 < count <= MAX_REQUEST:
        raise RuntimeError("submission request exceeds fixed bound")
    return bridge.exact(stream, count)


def serve(path, prefix, attempts, seconds):
    """Owner-private submission socket. Each request runs one await client;
    there is no warm engine child to keep, restart or signal."""
    path, attempts = Path(path), Path(attempts)
    bridge.private_dir(path.parent)
    bridge.private_dir(attempts)
    if path.exists() or path.is_symlink():
        raise RuntimeError("refuse to replace an existing session endpoint")
    listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    identity = None
    try:
        listener.bind(str(path))
        os.chmod(path, 0o600)
        identity = path.lstat().st_ino
        listener.listen(4)
        print("SESSION BACKEND READY", flush=True)
        while True:
            connection, _ = listener.accept()
            with connection:
                try:
                    peer_is_owner(connection)
                    connection.settimeout(seconds + bridge.CLIENT_GRACE_SECONDS + 5)
                    with connection.makefile("rwb", buffering=0) as stream:
                        call = receive_request(stream)
                        outcome = bridge.run_submission(prefix, attempts, seconds, call)
                        connection.sendall(struct.pack("<I", len(outcome)) + outcome)
                except Exception as error:
                    # The caller keeps its exact original attempt. A closed
                    # response is uncertainty, never permission to redispatch.
                    print("submission session: " + str(error), file=sys.stderr, flush=True)
    finally:
        listener.close()
        if identity is not None:
            try:
                info = path.lstat()
                if stat.S_ISSOCK(info.st_mode) and info.st_ino == identity:
                    path.unlink()
            except FileNotFoundError:
                pass


def submit(path, original, outcome):
    # This is the original operator's already fsynced owner-private call.bin.
    # It is copied byte-for-byte; only Lean interprets the signed call.
    call = bridge.read_outcome(Path(original))
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as connection:
        connection.connect(str(path))
        peer_is_owner(connection)
        with connection.makefile("rwb", buffering=0) as stream:
            connection.sendall(struct.pack("<I", len(call)) + call)
            count = struct.unpack("<I", bridge.exact(stream, 4))[0]
            if not 0 < count < bridge.MAX_FRAME:
                raise RuntimeError("native outcome exceeds fixed bound")
            reply = bridge.exact(stream, count)
    # Never turn an acknowledgement or process success into confirmation.
    # The bytes are the exact native Outcome; exclusive write preserves custody.
    bridge.save_call(Path(outcome), reply)


def main(args):
    if len(args) == 6 and args[0] == "serve":
        _, path, wrapper, attempts, seconds, marker = args
        if marker != "owner-private":
            raise RuntimeError("explicit owner-private service required")
        serve(path, [wrapper], attempts, int(seconds))
    elif len(args) == 6 and args[0] == "submit":
        # Invoked as a bridge submitCommand: SOCKET CALL OUTCOME SECONDS ID.
        # The backend applies its own pinned deadline and its own ticket.
        _, path, original, outcome, _seconds, _ticket = args
        submit(path, original, outcome)
    else:
        raise RuntimeError("usage: session serve SOCKET WRAPPER ATTEMPTS SECONDS owner-private | submit SOCKET CALL OUTCOME SECONDS ID")


if __name__ == "__main__":
    def stopped(_signal, _frame):
        raise SystemExit(0)
    signal.signal(signal.SIGTERM, stopped)
    try:
        main(sys.argv[1:])
    except Exception as error:
        print("agreement session adapter: " + str(error), file=sys.stderr)
        sys.exit(1)
