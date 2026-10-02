#!/usr/bin/env python3
"""Real CLI/Unix/stdio receiving checks. Host here is only a framed echo fixture;
these checks qualify transport, not Lean admission or a deployed service.
Usage: python3 public-ingress-process.py /absolute/path/to/mini
"""
import hashlib
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

mini = str(Path(sys.argv[1]).resolve())
root = Path(tempfile.mkdtemp(prefix="mini-public-process-"))
rows = []
children = []
logs = []
def checked(name, condition):
    assert condition, name
    rows.append(name)
def receive(stream):
    def exact(n):
        value = b""
        while len(value) < n:
            ready, _, _ = select.select([stream], [], [], 3)
            if not ready:
                raise TimeoutError("framed response timed out")
            part = stream.recv(n - len(value)) if isinstance(stream, socket.socket) else os.read(stream.fileno(), n - len(value))
            if not part:
                if not value:
                    return None
                raise EOFError("truncated frame")
            value += part
        return value
    prefix = exact(4)
    if prefix is None:
        return None
    return exact(struct.unpack("<I", prefix)[0])
def send(stream, data):
    wire = struct.pack("<I", len(data)) + data
    if isinstance(stream, socket.socket):
        stream.sendall(wire)
    else:
        stream.write(wire)
        stream.flush()
def connect(path):
    stream = socket.socket(socket.AF_UNIX)
    stream.settimeout(3)
    stream.connect(str(path))
    return stream
def exchange(path, data):
    with connect(path) as stream:
        send(stream, data)
        return receive(stream)
def start(label, args, stdin=False):
    log = open(root / (label + ".log"), "wb")
    logs.append(log)
    proc = subprocess.Popen([mini] + args, stdin=subprocess.PIPE if stdin else subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=log, start_new_session=True)
    children.append(proc)
    return proc
def wait_listener(proc, path):
    until = time.monotonic() + 5
    while time.monotonic() < until:
        if proc.poll() is not None:
            raise RuntimeError("listener exited: " + str(proc.returncode))
        try:
            connect(path).close()
            return
        except OSError:
            time.sleep(.02)
    raise TimeoutError(str(path))
try:
    private_dir = root / "operator"
    public_dir = root / "public"
    private_dir.mkdir(mode=0o700)
    public_dir.mkdir(mode=0o700)
    private = private_dir / "mini.sock"
    public = public_dir / "mini.sock"
    config = root / "config.json"
    config.write_bytes(b'{"domain":"7"}')
    config.chmod(0o600)
    host = root / "host.py"
    host.write_text('''#!/usr/bin/env python3
import os, struct, sys
from pathlib import Path
root=Path(sys.argv[1]).parent.parent
(root/"host.pid").write_text(str(os.getpid()))
def exact(n):
 b=b""
 while len(b)<n:
  p=sys.stdin.buffer.read(n-len(b))
  if not p: return None
  b+=p
 return b
while True:
 p=exact(4)
 if p is None: break
 r=exact(struct.unpack("<I",p)[0])
 if r is None: break
 with open(root/"received.hex","a") as f: f.write(r.hex()+"\\n")
 if r==b"\\x00stall":
  while not (root/"release").exists():
   import time; time.sleep(.01)
 sys.stdout.buffer.write(struct.pack("<I",len(r))+r); sys.stdout.buffer.flush()
''')
    host.chmod(0o700)
    pin = hashlib.sha256(host.read_bytes()).digest()
    def envelope(request, cfg=None, image=None):
        cfg = config.read_bytes() if cfg is None else cfg
        return b"\x02" + struct.pack("<I", len(cfg)) + cfg + (pin if image is None else image) + request
    backend = start("private", ["serve-operator", "--host", str(host), "--config", str(config), "--socket", str(private)])
    wait_listener(backend, private)
    # Existing public-v1 pins represent an explicit stop/start migration from
    # monolithic mini serve. The relay accepts these without erasing custody.
    public.with_suffix(".mode").write_bytes(b"public-v1")
    public.with_suffix(".config").write_bytes(config.read_bytes())
    public.with_suffix(".mode").chmod(0o600)
    public.with_suffix(".config").chmod(0o600)
    args = ["serve-public-proxy", "--socket", str(public), "--upstream", str(private), "--config", str(config)]
    relay = start("public", args)
    wait_listener(relay, public)
    checked("private listener receives ordinary public operation", exchange(private, envelope(b"\x00direct")) == b"\x00direct")
    checked("public listener preserves exact request and image pin", exchange(public, envelope(b"\x00public")) == b"\x00public")
    checked("private listener retains operator operation", exchange(private, envelope(b"\x16private")) == b"\x16private")
    before = (root / "received.hex").read_bytes()
    for name, data in [
        ("operator request", envelope(b"\x16private")),
        ("SPK stream operator request", envelope(b"\x98private")),
        ("config substitution", envelope(b"\x00bad", b"{}")),
        ("Host image substitution", envelope(b"\x00bad", image=b"x" * 32)),
    ]:
        checked(name + " refused", exchange(public, data)[0] == 254)
    checked("refused requests never reach Host", (root / "received.hex").read_bytes() == before)
    # Idle forced-command process survives between requests. Its next exchange
    # must not bypass a stopped ingress by reconnecting directly to the Host.
    old = start("ssh-stdio", ["socket-proxy", "--socket", str(public)], stdin=True)
    send(old.stdin, envelope(b"\x00ssh"))
    checked("existing stdio client reaches public ingress", receive(old.stdout) == b"\x00ssh")
    idle = connect(public)
    active = connect(public)
    send(active, envelope(b"\x00stall"))
    until = time.monotonic() + 3
    while b"007374616c6c" not in (root / "received.hex").read_bytes():
        assert time.monotonic() < until
        time.sleep(.01)
    start_stop = time.monotonic()
    relay.send_signal(signal.SIGTERM)
    checked("SIGTERM exits successfully within one second", relay.wait(timeout=2) == 0 and time.monotonic() - start_stop < 1)
    checked("stop closes idle accepted connection", receive(idle) is None)
    checked("stop closes in-flight connection without false refusal", receive(active) is None)
    idle.close()
    active.close()
    checked("stop removes owned public socket", not public.exists())
    try:
        connect(public)
        raise AssertionError("new connection succeeded after stop")
    except OSError:
        rows.append("stop blocks new connections")
    send(old.stdin, envelope(b"\x00reconnect"))
    checked("existing stdio client cannot reconnect around stopped ingress", receive(old.stdout) is None and old.wait(timeout=2) != 0)
    checked("private process remains alive", backend.poll() is None)
    (root / "release").touch()
    checked("private operator remains available after ingress stop", exchange(private, envelope(b"\x16after")) == b"\x16after")
    relay2 = start("public-restart", args)
    wait_listener(relay2, public)
    checked("explicit relay restart restores public service", exchange(public, envelope(b"\x00resumed")) == b"\x00resumed")
    duplicate = start("public-duplicate", args)
    checked("second owner refuses without disrupting listener", duplicate.wait(timeout=3) != 0 and exchange(public, envelope(b"\x00still")) == b"\x00still")
    relay2.terminate()
    relay2.wait(timeout=2)
    public.with_suffix(".mode").write_bytes(b"operator-v1")
    refused = start("wrong-mode", args)
    checked("retained operator path cannot become public relay", refused.wait(timeout=3) != 0 and not public.exists())
    def control(command, extra=(), expected=0):
        result = subprocess.run([mini, command, "--socket", str(private), "--host", str(host), "--config", str(config)] + list(extra), capture_output=True, timeout=8)
        assert result.returncode == expected, (result.returncode, result.stderr)
        return json.loads(result.stdout) if result.stdout else None
    state = control("operator-status")
    checked("control status binds current private process", state["format"] == "mini-operator-drain-v1" and state["processId"] == backend.pid and state["phase"] == "serving")
    instance = state["instanceId"]
    original_host_pid = state["hostProcessId"]
    drain_args = ["--instance", instance, "--pid", str(backend.pid), "--timeout-seconds", "1"]
    control("drain-operator", ["--instance", "0" * 64, "--pid", str(backend.pid), "--timeout-seconds", "1"], expected=1)
    checked("wrong instance cannot close admission", control("operator-status")["phase"] == "serving")
    (root / "release").unlink()
    busy = connect(private)
    queued = connect(private)
    accepted_idle = connect(private)
    send(busy, envelope(b"\x00stall"))
    send(queued, envelope(b"\x00queued-after-cancel"))
    until = time.monotonic() + 3
    while control("operator-status")["unresolvedConnections"] < 3:
        assert time.monotonic() < until
        time.sleep(.01)
    timed_out = control("drain-operator", drain_args, expected=1)
    checked("drain timeout closes admission but preserves unresolved work", timed_out["admissionClosed"] and not timed_out["drained"] and timed_out["unresolvedConnections"] >= 2)
    try:
        connect(private)
        raise AssertionError("private listener remained open after close")
    except OSError:
        rows.append("drain closes actual private listener")
    busy.close()
    queued.close()
    accepted_idle.close()
    still_busy = control("operator-status")
    checked("cancelled clients do not imply Host drain", not still_busy["drained"] and still_busy["unresolvedConnections"] >= 2)
    checked("Host survives admission close and timeout", backend.poll() is None and still_busy["hostProcessId"] == original_host_pid)
    os.kill(original_host_pid, 0)
    (root / "release").touch()
    drained = control("drain-operator", drain_args[:-1] + ["3"])
    checked("exact-instance retry certifies all accepted and queued work drained", drained["admissionClosed"] and drained["drained"] and all(drained[k] == 0 for k in ["unresolvedConnections", "acceptedConnections", "queuedRequests", "activeRequests"]))
    checked("queued request completes despite disconnected client", b"007175657565642d61667465722d63616e63656c" in (root / "received.hex").read_bytes())
    checked("drain keeps same Host process alive", drained["hostProcessId"] == original_host_pid)
    os.kill(original_host_pid, 0)
    again = control("drain-operator", drain_args)
    checked("drain remains idempotently closed", again["instanceId"] == instance and again["phase"] == "drained")
    # Restart, rather than a control command, is the only reopening operation.
    os.killpg(backend.pid, signal.SIGTERM)
    backend.wait(timeout=3)
    backend2 = start("private-restart", ["serve-operator", "--host", str(host), "--config", str(config), "--socket", str(private)])
    wait_listener(backend2, private)
    new_state = control("operator-status")
    checked("service restart creates fresh instance and reopens admission", new_state["instanceId"] != instance and new_state["processId"] == backend2.pid and new_state["phase"] == "serving")
    control("drain-operator", drain_args, expected=1)
    checked("old drain receipt cannot close restarted process", control("operator-status")["phase"] == "serving" and exchange(private, envelope(b"\x00new-instance")) == b"\x00new-instance")
    result = {"format": "mini-public-ingress-process-v1", "mini": mini, "miniSha256": hashlib.sha256(Path(mini).read_bytes()).hexdigest(), "scope": "real mini processes and Unix sockets; framed echo Host fixture, not Lean admission", "passed": len(rows), "checks": rows, "evidence": str(root)}
    (root / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
finally:
    # Only our isolated process groups. The existing serve-operator lacks a
    # signal handler; terminate its fixture child together with its wrapper.
    for child in reversed(children):
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
    for log in logs:
        log.close()
