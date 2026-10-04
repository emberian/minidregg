#!/usr/bin/env python3
"""Owner-configured local four-participant bridge for the native Host frame API.

Only op2 may mutate, via the actual Lean source-agreement fixture. Other allowed
operations go to the same-profile Host's existing read/prepare/author handlers.
This is a local multi-participant operator, not four independent deployed nodes.
"""
import json
import os
from pathlib import Path
import signal
import select
import time
import stat
import struct
import subprocess
import sys
import uuid

# Compiler.FnEvidenceCodec.maxHostFrameBytes, proved by selected_poll_envelope_exact.
# This differs from the agreement crypto helper's separate 16MiB wire bound.
MAX_FRAME = 12_102_760
READ_ONLY = frozenset((0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 91, 144))


def exact(stream, count, eof=False):
    result = bytearray()
    while len(result) < count:
        chunk = stream.read(count - len(result))
        if not chunk:
            if eof and not result:
                return None
            raise RuntimeError("truncated native frame")
        result.extend(chunk)
    return bytes(result)


def read_frame(stream):
    header = exact(stream, 4, eof=True)
    if header is None:
        return None
    length = struct.unpack("<I", header)[0]
    if not 1 <= length <= MAX_FRAME:
        raise RuntimeError("native frame exceeds fixed bound")
    body = exact(stream, length)
    return body[0], body[1:]


def write_frame(stream, operation, payload):
    if not 0 <= operation <= 255 or len(payload) + 1 > MAX_FRAME:
        raise RuntimeError("response exceeds native frame bound")
    stream.write(struct.pack("<I", len(payload) + 1) + bytes((operation,)) + payload)
    stream.flush()


def command(value, label):
    if not isinstance(value, list) or not value or not all(
        isinstance(part, str) and part and "\x00" not in part for part in value
    ):
        raise RuntimeError(label + " must be an explicit nonempty argv array")
    return value


def private_dir(path):
    info = path.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or info.st_mode & 0o077:
        raise RuntimeError("bridge attempts directory must be owner-private")


def save_call(path, payload):
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(descriptor, "wb") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def read_outcome(path):
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(descriptor, "rb") as stream:
        info = os.fstat(stream.fileno())
        if (not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid()
                or info.st_nlink != 1 or info.st_mode & 0o077
                or not 0 < info.st_size < MAX_FRAME):
            raise RuntimeError("source outcome is not a bounded owner-private regular file")
        result = stream.read(MAX_FRAME)
        if len(result) != info.st_size:
            raise RuntimeError("source outcome changed during read")
        return result


def retained_attempt(attempts, payload):
    ticket = attempts / uuid.uuid4().hex
    ticket.mkdir(mode=0o700)
    parent = os.open(attempts, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(parent)
    finally:
        os.close(parent)
    original = ticket / "call.bin"
    outcome = ticket / "outcome.bin"
    save_call(original, payload)
    return ticket, original, outcome


def run_submission(prefix, attempts, fuel, seconds, payload):
    ticket, original, outcome = retained_attempt(attempts, payload)
    # Retain original bytes after success, timeout, or lost response. An
    # uncertain process result never causes a second invocation here.
    with (ticket / "operator.log").open("xb") as log:
        os.chmod(log.name, 0o600)
        child = subprocess.Popen(
            prefix + [str(original), str(outcome), str(fuel)],
            stdin=subprocess.DEVNULL, stdout=log, stderr=log, start_new_session=True,
        )
        try:
            result = child.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
            raise RuntimeError("agreement completion uncertain; use exact original-call lookup")
        log.flush()
        os.fsync(log.fileno())
    if result:
        raise RuntimeError("agreement process failed; original call retained for lookup")
    # Only the actual Lean codec producer writes this result; the bridge never
    # translates JSON or a process exit into a confirmation receipt.
    return read_outcome(outcome)


class SubmissionSession:
    """One supervised native participant process; uncertain calls never retry."""

    def __init__(self, prefix, attempts):
        self.attempts = attempts
        self.closed = False
        log_path = attempts / ("session-" + uuid.uuid4().hex + ".log")
        descriptor = os.open(log_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        self.log = os.fdopen(descriptor, "wb")
        try:
            self.child = subprocess.Popen(prefix, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                          stderr=self.log, start_new_session=True)
        except BaseException:
            self.log.close()
            raise

    def close(self):
        if self.closed:
            return
        self.closed = True
        if self.child.poll() is None:
            os.killpg(self.child.pid, signal.SIGTERM)
            try:
                self.child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(self.child.pid, signal.SIGKILL)
                self.child.wait()
        self.child.stdin.close()
        self.child.stdout.close()
        self.log.flush()
        os.fsync(self.log.fileno())
        self.log.close()

    def run(self, fuel, seconds, payload):
        if self.closed or self.child.poll() is not None:
            raise RuntimeError("native agreement session stopped; use exact original-call lookup")
        ticket, original, outcome = retained_attempt(self.attempts, payload)
        try:
            request = json.dumps([str(original), str(outcome), str(fuel)]).encode() + b"\n"
            self.child.stdin.write(request)
            self.child.stdin.flush()
            deadline = time.monotonic() + seconds
            reply = bytearray()
            while b"\n" not in reply:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([self.child.stdout], [], [], remaining)[0]:
                    raise RuntimeError("agreement completion uncertain; use exact original-call lookup")
                part = os.read(self.child.stdout.fileno(), 256)
                if not part:
                    raise RuntimeError("agreement session closed; original call retained for lookup")
                reply.extend(part)
                if len(reply) > 256:
                    raise RuntimeError("invalid native session acknowledgement")
            if reply != b"done\n":
                raise RuntimeError("invalid native session acknowledgement")
            # The acknowledgement is supervision only. Confirmation bytes come
            # exclusively from the native Outcome file for this exact ticket.
            return read_outcome(outcome)
        except BaseException:
            self.close()
            raise


def serve(profile, source, destination):
    reader_args = command(profile["readerCommand"], "readerCommand")
    submit_args = command(profile["submitCommand"], "submitCommand")
    session_args = (command(profile["submitSessionCommand"], "submitSessionCommand")
                    if "submitSessionCommand" in profile else None)
    attempts = Path(profile["attempts"]).resolve(strict=True)
    private_dir(attempts)
    fuel, seconds = profile["fuel"], profile["timeoutSeconds"]
    if type(fuel) is not int or type(seconds) is not int or fuel <= 0 or seconds <= 0:
        raise RuntimeError("finite positive service fuel and timeout are required")
    reader = subprocess.Popen(reader_args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              stderr=sys.stderr, start_new_session=True)
    session = None
    try:
        if session_args is not None:
            session = SubmissionSession(session_args, attempts)
        while (request := read_frame(source)) is not None:
            operation, payload = request
            if operation == 2:
                answer = (session.run(fuel, seconds, payload) if session is not None else
                          run_submission(submit_args, attempts, fuel, seconds, payload))
                write_frame(destination, 2, answer)
            elif operation in READ_ONLY:
                write_frame(reader.stdin, operation, payload)
                response = read_frame(reader.stdout)
                if response is None or response[0] not in (operation, 255):
                    raise RuntimeError("read-only Host returned an invalid response operation")
                write_frame(destination, *response)
            else:
                # Never forward an unrecognized opcode to a Host that also
                # implements non-agreed mutation families. Closing is fail-closed;
                # it makes no semantic rejection/rollback claim.
                raise RuntimeError("operation is outside the agreed ordinary-call profile")
    finally:
        if session is not None:
            session.close()
        if reader.poll() is None:
            os.killpg(reader.pid, signal.SIGTERM)
            try:
                reader.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(reader.pid, signal.SIGKILL)
                reader.wait()


def private_config_bytes(path):
    # The native client pins configuration to a private socket-adjacent copy.
    # Read by descriptor; never follow a substituted link or block on a FIFO.
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as stream:
        info = os.fstat(stream.fileno())
        if (not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid()
                or info.st_nlink != 1 or info.st_mode & 0o077
                or not 0 < info.st_size <= 1024 * 1024):
            raise RuntimeError("client configuration must be a bounded owner-private regular file")
        value = stream.read(1024 * 1024 + 1)
        after = os.fstat(stream.fileno())
        if (len(value) != info.st_size or info.st_size != after.st_size
                or info.st_mtime_ns != after.st_mtime_ns
                or info.st_ctime_ns != after.st_ctime_ns):
            raise RuntimeError("client configuration changed during verification")
        return value


def check_client_arguments(profile, arguments):
    pinned = command(profile["clientArguments"], "clientArguments")
    if len(pinned) != 2 or pinned[1] != "stdio":
        raise RuntimeError("bridge requires the pinned CONFIG stdio client profile")
    if len(arguments) != 2 or arguments[1] != "stdio":
        raise RuntimeError("client launch arguments differ from the pinned bridge profile")
    if private_config_bytes(arguments[0]) != private_config_bytes(pinned[0]):
        raise RuntimeError("client configuration differs from the pinned bridge profile")
    # Supplied path is never passed to the reader: readerCommand stays pinned.


def main():
    path = os.environ.get("MINI_AGREEMENT_BRIDGE_CONFIG")
    if not path:
        raise RuntimeError("MINI_AGREEMENT_BRIDGE_CONFIG is required")
    with open(path, encoding="utf-8") as stream:
        profile = json.load(stream)
    check_client_arguments(profile, sys.argv[1:])
    serve(profile, sys.stdin.buffer, sys.stdout.buffer)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print("agreement bridge: " + str(error), file=sys.stderr)
        sys.exit(1)
