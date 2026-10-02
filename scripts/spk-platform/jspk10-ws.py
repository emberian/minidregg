#!/usr/bin/env python3
"""J-SPK-10 WebSocket client: RFC 6455 over a grain route's Unix socket.

Standard library only. Every verdict is printed as one JSON object (the
artifact); the process exits nonzero when the scenario's expectation fails.

  jspk10-ws.py ntfy ROUTE JOURNAL TOPIC          (a) subscribe, publish, deliver; records
  jspk10-ws.py flood ROUTE JOURNAL TOPIC K UNIT  (e) one flooder cut at the byte cap, K bystanders; burst numbers
  jspk10-ws.py caps ROUTE JOURNAL ROOM N UNIT    (d) N EtherCalc opens alive + the N+1th refused; memory
  jspk10-ws.py hold ROUTE TOPIC MARKER           (f) hold a socket until the grain closes it
  jspk10-ws.py ethercalc ROUTE JOURNAL ROOM      (b) two sockets co-edit one sheet
  jspk10-ws.py meteor ROUTE JOURNAL              (c) DDP over /websocket, a todo lands

ROUTE is the owner route directory (http.sock + api.token or browser.token);
JOURNAL is the running generation's journal directory, whose dispatch-op-N
attempt directories are the resident's per-dispatch records.
"""
import base64, hashlib, json, os, queue, random, socket, struct, sys, threading, time

HOST = "grain.test"
GUID = b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11"


def creds(route):
    if os.path.exists(os.path.join(route, "api.token")) and route.rstrip("/").endswith("owner-api"):
        return [("Authorization", "Bearer " + open(os.path.join(route, "api.token")).read().strip())]
    return [("Cookie", "__Host-mini_spk_session=" + open(os.path.join(route, "browser.token")).read().strip()),
            ("Origin", "https://" + HOST)]


def records(journal):
    """The generation's committed Mini dispatch records: each dispatch-op-N
    attempt directory holding Mini's committed inspection."""
    out = []
    for name in os.listdir(journal):
        suffix = name[len("dispatch-op-"):]
        if name.startswith("dispatch-op-") and suffix.isdigit() and \
                os.path.exists(os.path.join(journal, name, "inspection.json")):
            out.append(int(suffix))
    return sorted(out)


def record(journal, n):
    """One committed record as an audit reads it: method, streamed mark, receipt."""
    obj = json.load(open(os.path.join(journal, "dispatch-op-%d" % n, "inspection.json")))
    req = obj["request"]
    return {"op": n, "type": obj.get("type"), "method": bytes.fromhex(req["methodHex"]).decode(),
            "streamed": req.get("streamed"), "path": bytes.fromhex(req["pathHex"]).decode(),
            "acceptedCount": obj["receipt"]["acceptedCount"]}


def rss_kib(unit_pid):
    for line in open("/proc/%d/status" % unit_pid):
        if line.startswith("VmRSS:"):
            return int(line.split()[1])
    return None


class Refused(Exception):
    def __init__(self, status, head):
        super().__init__("refused %s" % status)
        self.status, self.head = status, head


class WS:
    def __init__(self, route, path, protocols=None, timeout=900):
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.sock.settimeout(timeout)
        self.sock.connect(os.path.join(route, "http.sock"))
        key = base64.b64encode(os.urandom(16)).decode()
        lines = ["GET %s HTTP/1.1" % path, "Host: " + HOST, "Connection: Upgrade", "Upgrade: websocket",
                 "Sec-WebSocket-Key: " + key, "Sec-WebSocket-Version: 13", "Sec-Fetch-Site: same-origin",
                 "Sec-Fetch-Mode: websocket"]
        if protocols:
            lines.append("Sec-WebSocket-Protocol: " + ", ".join(protocols))
        lines += ["%s: %s" % kv for kv in creds(route)]
        t0 = time.monotonic()
        self.sock.sendall(("\r\n".join(lines) + "\r\n\r\n").encode())
        head = b""
        while b"\r\n\r\n" not in head:
            chunk = self.sock.recv(1)
            if not chunk:
                raise Refused("closed", head.decode(errors="replace"))
            head += chunk
        self.open_seconds = time.monotonic() - t0
        text = head.decode(errors="replace")
        status = text.split(" ", 2)[1] if " " in text else "?"
        if status != "101":
            rest = b""
            try:
                self.sock.settimeout(2)
                rest = self.sock.recv(4096)
            except OSError:
                pass
            raise Refused(status, text + rest.decode(errors="replace"))
        want = base64.b64encode(hashlib.sha1(key.encode() + GUID).digest()).decode()
        headers = {l.split(":", 1)[0].lower(): l.split(":", 1)[1].strip() for l in text.split("\r\n")[1:] if ":" in l}
        if headers.get("sec-websocket-accept") != want:
            raise RuntimeError("Sec-WebSocket-Accept mismatch: %r" % headers)
        self.head = text
        self.buf = b""
        self.lock = threading.Lock()
        self.queue = None
        self.ended = None
        self.pongs = 0

    def start(self, keepalive=None, every=20.0):
        """Read in the background: answer pings, count pongs, queue data
        messages; `keepalive` (a text message) is sent every `every` s."""
        self.queue = queue.Queue()
        self.sock.settimeout(None)
        def run():
            try:
                while True:
                    op, payload = self.recv_frame()
                    if op == 9:
                        self.send(payload, 10)
                    elif op == 10:
                        self.pongs += 1
                    elif op == 8:
                        code = struct.unpack("!H", payload[:2])[0] if len(payload) >= 2 else None
                        self.ended = "close frame %s" % code
                        break
                    elif op in (1, 2):
                        self.queue.put(payload.decode(errors="replace") if op == 1 else payload)
            except Exception as e:
                self.ended = "eof" if isinstance(e, EOFError) else "error: %s" % e
            self.queue.put(None)
        threading.Thread(target=run, daemon=True).start()
        if keepalive is not None:
            def beat():
                while self.ended is None:
                    time.sleep(every)
                    try:
                        self.send(keepalive)
                    except OSError:
                        return
            threading.Thread(target=beat, daemon=True).start()
        return self

    def get(self, deadline):
        left = deadline - time.monotonic()
        if left <= 0:
            raise TimeoutError("deadline")
        item = self.queue.get(timeout=left)
        if item is None:
            self.queue.put(None)
            raise EOFError(self.ended)
        return item

    def send(self, payload, opcode=1):
        if isinstance(payload, str):
            payload = payload.encode()
        mask = os.urandom(4)
        n = len(payload)
        if n < 126:
            hdr = struct.pack("!BB", 0x80 | opcode, 0x80 | n)
        elif n < 65536:
            hdr = struct.pack("!BBH", 0x80 | opcode, 0x80 | 126, n)
        else:
            hdr = struct.pack("!BBQ", 0x80 | opcode, 0x80 | 127, n)
        masked = bytes(b ^ mask[i % 4] for i, b in enumerate(payload))
        with self.lock:
            self.sock.sendall(hdr + mask + masked)

    def _need(self, n):
        while len(self.buf) < n:
            chunk = self.sock.recv(65536)
            if not chunk:
                raise EOFError("socket closed")
            self.buf += chunk

    def recv_frame(self):
        self._need(2)
        b0, b1 = self.buf[0], self.buf[1]
        n, off = b1 & 0x7F, 2
        if n == 126:
            self._need(4); n = struct.unpack("!H", self.buf[2:4])[0]; off = 4
        elif n == 127:
            self._need(10); n = struct.unpack("!Q", self.buf[2:10])[0]; off = 10
        self._need(off + n)
        payload, self.buf = self.buf[off:off + n], self.buf[off + n:]
        return b0 & 0x0F, payload

    def recv(self):
        """Next data message; answers pings, raises EOFError on close."""
        while True:
            op, payload = self.recv_frame()
            if op == 9:
                self.send(payload, 10)
            elif op == 8:
                code = struct.unpack("!H", payload[:2])[0] if len(payload) >= 2 else None
                raise EOFError("close frame %s" % code)
            elif op in (1, 2):
                return payload.decode(errors="replace") if op == 1 else payload
            # pongs and continuation frames are not data messages here

    def close(self):
        try:
            self.send(struct.pack("!H", 1000), 8)
        except OSError:
            pass
        self.sock.close()


def http(route, method, path, body=b"", ctype="text/plain"):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(900)
    s.connect(os.path.join(route, "http.sock"))
    lines = ["%s %s HTTP/1.1" % (method, path), "Host: " + HOST, "Content-Length: %d" % len(body)]
    if body:
        lines.append("Content-Type: " + ctype)
    lines += ["%s: %s" % kv for kv in creds(route)]
    s.sendall(("\r\n".join(lines) + "\r\n\r\n").encode() + body)
    data = b""
    while True:
        chunk = s.recv(65536)
        if not chunk:
            break
        data += chunk
    s.close()
    head = data.split(b"\r\n", 1)[0].decode(errors="replace")
    return head.split(" ")[1] if " " in head else "?", data


def wait_for(ws, pred, deadline):
    seen = []
    while time.monotonic() < deadline:
        msg = ws.get(deadline) if ws.queue is not None else ws.recv()
        seen.append(msg if isinstance(msg, str) else repr(msg))
        if pred(msg):
            return msg, seen
    raise TimeoutError("expected message not seen: %r" % seen[-5:])


def ntfy_event(msg, event, text=None):
    try:
        obj = json.loads(msg)
    except (ValueError, TypeError):
        return False
    return obj.get("event") == event and (text is None or obj.get("message") == text)


def cmd_ntfy(route, journal, topic):
    r0 = records(journal)
    ws = WS(route, "/%s/ws" % topic)
    wait_for(ws, lambda m: ntfy_event(m, "open"), time.monotonic() + 60)
    r1 = records(journal)
    text = "published over POST %d" % random.randrange(1 << 30)
    status, _ = http(route, "POST", "/" + topic, text.encode())
    r2 = records(journal)
    t0 = time.monotonic()
    msg, _ = wait_for(ws, lambda m: ntfy_event(m, "message", text), time.monotonic() + 120)
    delivered = time.monotonic() - t0
    pings = 200
    for i in range(pings):
        ws.send(b"p%03d" % i, 9)
    pongs = 0
    while pongs < pings:
        op, _ = ws.recv_frame()
        if op == 10:
            pongs += 1
    r3 = records(journal)
    ws.close()
    time.sleep(2)
    r4 = records(journal)
    out = {"row": "ntfy-deliver", "openSeconds": round(ws.open_seconds, 3), "postStatus": status,
           "deliveredAfterPostSeconds": round(delivered, 3), "message": json.loads(msg)["message"],
           "recordsBefore": len(r0), "afterOpen": len(r1), "afterPost": len(r2),
           "afterFrames": len(r3), "afterClose": len(r4), "framesExchanged": pings * 2,
           "openRecord": record(journal, r1[-1]) if len(r1) > len(r0) else None,
           "postRecord": record(journal, r2[-1]) if len(r2) > len(r1) else None}
    print(json.dumps(out))
    ok = (status == "200" and len(r1) - len(r0) == 1 and len(r2) - len(r1) == 1
          and len(r3) == len(r2) and len(r4) == len(r3))
    return 0 if ok else 1


def resident_pid(unit):
    import subprocess
    return int(subprocess.check_output(["systemctl", "show", unit, "--property=MainPID", "--value"]).strip())


def refusal_of(route, path):
    try:
        WS(route, path).close()
        return None
    except Refused as e:
        return {"status": e.status, "refusal": [l.split(":", 1)[1].strip() for l in e.head.split("\r\n")
                                                if l.lower().startswith("x-mini-refusal:")]}


def cmd_flood(route, journal, topic, bystanders, unit):
    """(e) and the per-socket numbers, on ntfy: a burst through one socket,
    then one flooder past the class byte cap while bystanders keep receiving."""
    bystanders = int(bystanders)
    pid = resident_pid(unit)
    socks = []
    for _ in range(bystanders):
        ws = WS(route, "/%s/ws" % topic).start()
        wait_for(ws, lambda m: ntfy_event(m, "open"), time.monotonic() + 60)
        socks.append(ws)
    # Frames/s and bytes/s through one socket: a ping burst within the class
    # budget, timed until every pong is back (both directions carried).
    probe = WS(route, "/%s/ws" % topic).start()
    wait_for(probe, lambda m: ntfy_event(m, "open"), time.monotonic() + 60)
    burst, size = 2000, 125
    t0 = time.monotonic()
    for _ in range(burst):
        probe.send(os.urandom(size), 9)
    while probe.pongs < burst and time.monotonic() - t0 < 120:
        time.sleep(0.005)
    burst_s = time.monotonic() - t0
    burst_pongs = probe.pongs
    probe.close()
    time.sleep(2)
    r0 = records(journal)
    flooder = WS(route, "/%s/ws" % topic).start()
    wait_for(flooder, lambda m: ntfy_event(m, "open"), time.monotonic() + 60)
    r1 = records(journal)
    sent, cut = 0, None
    t0 = time.monotonic()
    try:
        while time.monotonic() - t0 < 300 and flooder.ended is None:
            flooder.send(os.urandom(size), 9)
            sent += size + 6
        time.sleep(1)
    except OSError as e:
        pass
    deadline = time.monotonic() + 30
    while flooder.ended is None and time.monotonic() < deadline:
        time.sleep(0.1)
    if flooder.ended is not None:
        cut = {"afterSeconds": round(time.monotonic() - t0, 3), "clientBytesSent": sent,
               "pongsReceived": flooder.pongs, "end": flooder.ended}
    r2 = records(journal)
    text = "after flood %d" % random.randrange(1 << 30)
    status, _ = http(route, "POST", "/" + topic, text.encode())
    got = 0
    for ws in socks:
        try:
            wait_for(ws, lambda m: ntfy_event(m, "message", text), time.monotonic() + 120)
            got += 1
        except Exception:
            pass
    for ws in socks:
        ws.close()
    frame = size + 6
    out = {"row": "flood", "burst": {"pings": burst, "pongs": burst_pongs, "seconds": round(burst_s, 3),
                                     "framesPerSecond": round(2 * burst_pongs / burst_s, 1),
                                     "bytesPerSecond": round(2 * burst_pongs * frame / burst_s, 1)},
           "flood": {"openRecordAdded": len(r1) - len(r0), "recordsDuringFlood": len(r2) - len(r1), "cut": cut},
           "bystanders": bystanders, "afterFloodPostStatus": status, "afterFloodDelivered": got,
           "residentRssKiB": rss_kib(pid)}
    print(json.dumps(out))
    ok = (cut is not None and len(r1) - len(r0) == 1 and len(r2) == len(r1) and status == "200"
          and got == bystanders and burst_pongs == burst)
    return 0 if ok else 1


def eio_socket(route):
    ws = WS(route, "/socket.io/?EIO=3&transport=websocket").start(keepalive="2", every=20.0)
    opened = ws.get(time.monotonic() + 60)
    assert opened.startswith("0"), opened
    info = json.loads(opened[1:])
    wait_for(ws, lambda m: m.startswith("40"), time.monotonic() + 60)
    return ws, info


def sio_data(m):
    if isinstance(m, str) and m.startswith("42"):
        try:
            event = json.loads(m[2:])
            return event[1] if event[0] == "data" else None
        except (ValueError, IndexError):
            return None
    return None


def ec_join(ws, room, user):
    ws.send("42" + json.dumps(["data", {"type": "ask.log", "room": room, "user": user}]))
    wait_for(ws, lambda m: (sio_data(m) or {}).get("type") == "log", time.monotonic() + 120)


def cmd_caps(route, journal, room, n, unit):
    """(d) on EtherCalc: n sockets open and joined, the n+1th refused by the
    class cap before Mini, every one of the n still receives a broadcast."""
    n = int(n)
    pid = resident_pid(unit)
    cg = open("/proc/%d/cgroup" % pid).read().strip().split("::")[-1]
    def cg_mem():
        try:
            return int(open("/sys/fs/cgroup%s/memory.current" % cg).read())
        except OSError:
            return None
    rss0, mem0 = rss_kib(pid), cg_mem()
    r0 = records(journal)
    socks, lat = [], []
    for i in range(n):
        ws, _ = eio_socket(route)
        ec_join(ws, room, "u%02d" % i)
        socks.append(ws)
        lat.append(ws.open_seconds)
    r1 = records(journal)
    rss1, mem1 = rss_kib(pid), cg_mem()
    refused = refusal_of(route, "/socket.io/?EIO=3&transport=websocket")
    r2 = records(journal)
    cmd = "set B2 text t fan-out-%d" % random.randrange(1 << 30)
    socks[0].send("42" + json.dumps(["data", {"type": "execute", "room": room, "user": "u00", "cmdstr": cmd,
                                               "saveundo": False}]))
    got = 0
    for ws in socks[1:]:
        try:
            wait_for(ws, lambda m: (sio_data(m) or {}).get("cmdstr") == cmd, time.monotonic() + 120)
            got += 1
        except Exception:
            pass
    alive = sum(1 for ws in socks if ws.ended is None)
    for ws in socks:
        ws.close()
    time.sleep(3)
    after_close = refusal_of(route, "/socket.io/?EIO=3&transport=websocket")
    r3 = records(journal)
    out = {"row": "caps", "class": "S", "opened": n, "openSeconds": [round(x, 3) for x in lat],
           "openSecondsMin": round(min(lat), 3), "openSecondsMedian": round(sorted(lat)[n // 2], 3),
           "openSecondsMax": round(max(lat), 3),
           "recordsBefore": len(r0), "afterOpens": len(r1), "afterRefusal": len(r2),
           "refused": refused, "broadcastReceivedBy": got, "aliveAtBroadcast": alive,
           "residentRssKiB": {"before": rss0, "with": rss1, "perSocket": round((rss1 - rss0) / n, 1)},
           "unitMemoryCurrent": {"before": mem0, "with": mem1},
           "openAfterClose": after_close, "recordsAfterReopen": len(r3)}
    print(json.dumps(out))
    ok = (len(r1) - len(r0) == n and refused == {"status": "429", "refusal": ["wsConcurrencyCap"]}
          and len(r2) == len(r1) and got == n - 1 and alive == n and after_close is None
          and len(r3) == len(r2) + 1)
    return 0 if ok else 1


def cmd_hold(route, topic, marker):
    ws = WS(route, "/%s/ws" % topic)
    wait_for(ws, lambda m: ntfy_event(m, "open"), time.monotonic() + 60)
    open(marker, "w").write(json.dumps({"openSeconds": ws.open_seconds, "at": time.time()}) + "\n")
    ws.sock.settimeout(7200)
    t0 = time.time()
    end = None
    try:
        while True:
            ws.recv()
    except EOFError as e:
        end = str(e)
    except OSError as e:
        end = "error: %s" % e
    print(json.dumps({"row": "hold", "heldSeconds": round(time.time() - t0, 1), "end": end, "closedAt": time.time()}))
    return 0 if end is not None and not end.startswith("error") else 1


def cmd_ethercalc(route, journal, room):
    r0 = records(journal)
    (a, ia), (b, _) = eio_socket(route), eio_socket(route)
    r1 = records(journal)
    ec_join(a, room, "alice")
    ec_join(b, room, "bob")
    value = "co-edit-%d" % random.randrange(1 << 30)
    cmd = "set A1 text t %s" % value
    a.send("42" + json.dumps(["data", {"type": "execute", "room": room, "user": "alice", "cmdstr": cmd,
                                       "saveundo": False}]))
    t0 = time.monotonic()
    msg, _ = wait_for(b, lambda m: (sio_data(m) or {}).get("cmdstr") == cmd, time.monotonic() + 120)
    seen = time.monotonic() - t0
    r2 = records(journal)
    a.close(); b.close()
    time.sleep(2)
    status, body = http(route, "GET", "/_/%s/csv" % room)
    r3 = records(journal)
    out = {"row": "ethercalc-coedit", "openSeconds": [round(a.open_seconds, 3), round(b.open_seconds, 3)],
           "engineIo": {"pingInterval": ia.get("pingInterval"), "upgrades": ia.get("upgrades")},
           "recordsBefore": len(r0), "afterOpens": len(r1), "afterEdit": len(r2), "afterCsvGet": len(r3),
           "editSeenOnOtherSocketSeconds": round(seen, 3), "broadcast": sio_data(msg),
           "csvStatus": status, "csvHasValue": value in body.decode(errors="replace")}
    print(json.dumps(out))
    return 0 if (len(r1) - len(r0) == 2 and len(r2) == len(r1) and out["csvHasValue"]) else 1


def ddp(ws):
    ws.send(json.dumps({"msg": "connect", "version": "1", "support": ["1", "pre2", "pre1"]}))
    msg, seen = wait_for(ws, lambda m: json.loads(m).get("msg") == "connected", time.monotonic() + 120)
    return json.loads(msg), seen


def cmd_meteor(route, journal):
    r0 = records(journal)
    a = WS(route, "/websocket")
    connected, seen = ddp(a)
    r1 = records(journal)
    a.send(json.dumps({"msg": "sub", "id": "l", "name": "publicLists", "params": []}))
    lists = {}
    def collect(m):
        o = json.loads(m)
        if o.get("msg") == "added" and o.get("collection") == "lists":
            lists[o["id"]] = o.get("fields", {})
        return o.get("msg") == "ready" and "l" in o.get("subs", [])
    wait_for(a, collect, time.monotonic() + 120)
    list_id = sorted(lists)[0]
    a.send(json.dumps({"msg": "sub", "id": "t", "name": "todos", "params": [list_id]}))
    wait_for(a, lambda m: json.loads(m).get("msg") == "ready" and "t" in json.loads(m).get("subs", []),
             time.monotonic() + 120)
    text = "todo over the socket %d" % random.randrange(1 << 30)
    todo_id = "".join(random.choice("23456789ABCDEFGHJKLMNPQRSTWXYZabcdefghijkmnopqrstuvwxyz") for _ in range(17))
    a.send(json.dumps({"msg": "method", "method": "/todos/insert", "id": "1",
                       "params": [{"_id": todo_id, "listId": list_id, "text": text, "checked": False,
                                   "createdAt": {"$date": int(time.time() * 1000)}}]}))
    result, _ = wait_for(a, lambda m: json.loads(m).get("msg") == "result" and json.loads(m).get("id") == "1",
                         time.monotonic() + 120)
    r2 = records(journal)
    # A second socket's subscription sees the todo: it landed server-side.
    b = WS(route, "/websocket")
    ddp(b)
    b.send(json.dumps({"msg": "sub", "id": "t", "name": "todos", "params": [list_id]}))
    added, _ = wait_for(b, lambda m: json.loads(m).get("msg") == "added" and json.loads(m).get("id") == todo_id,
                        time.monotonic() + 120)
    r3 = records(journal)
    a.close(); b.close()
    out = {"row": "meteor-ddp", "openSeconds": [round(a.open_seconds, 3), round(b.open_seconds, 3)],
           "firstMessages": seen[:2], "connected": connected, "lists": len(lists),
           "methodResult": json.loads(result), "secondSocketAdded": json.loads(added),
           "recordsBefore": len(r0), "afterOpen": len(r1), "afterMethod": len(r2), "afterSecondOpen": len(r3)}
    print(json.dumps(out))
    ok = ("error" not in json.loads(result) and json.loads(added)["fields"]["text"] == text
          and len(r1) - len(r0) == 1 and len(r2) == len(r1) and len(r3) - len(r2) == 1)
    return 0 if ok else 1


if __name__ == "__main__":
    cmd, args = sys.argv[1], sys.argv[2:]
    sys.exit({"ntfy": cmd_ntfy, "flood": cmd_flood, "caps": cmd_caps, "hold": cmd_hold,
              "ethercalc": cmd_ethercalc, "meteor": cmd_meteor}[cmd](*args))
