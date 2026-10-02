#!/usr/bin/env python3
"""Two actual EtherCalc delegates: continuity, revoke, fresh-open refusal.

See ws-continuity-journey.md for the private argv-hook and snapshot contract.
This file runs no Mini command by itself. Configured hooks supply checked
lifecycle actions and source-backed counters; no hook is retried automatically.
"""
import argparse
import concurrent.futures
import importlib.util
import json
import math
import os
from pathlib import Path
import queue
import re
import subprocess
import tempfile
import time
import uuid

spec = importlib.util.spec_from_file_location("jspk10_ws", Path(__file__).with_name("jspk10-ws.py"))
wsmod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wsmod)
PATH = "/socket.io/?EIO=3&transport=websocket"
COUNTERS = ("dispatchCount", "storeHeight")


def require(condition, reason):
    if not condition:
        raise AssertionError(reason)


def no_delta(before, after, label):
    require(all(before[k] == after[k] for k in (*COUNTERS, "billingCount")), label + ": renewal-only counters changed")


class Journey:
    def __init__(self, config, output=None):
        self.c, self.output = config, output
        self.lease = float(config["leaseSeconds"])
        self.duration = float(config.get("durationSeconds", 2.2 * self.lease))
        self.interval = float(config.get("trafficIntervalSeconds", 2))
        self.timeout = float(config.get("responseTimeoutSeconds", 10))
        self.tolerance = float(config.get("cutoffToleranceSeconds", 2))
        require(all(math.isfinite(v) for v in (self.lease, self.duration, self.interval, self.timeout, self.tolerance)), "timings must be finite")
        require(self.lease > 0 and self.duration > 2 * self.lease, "duration must exceed two lease intervals")
        require(0 < self.interval < self.lease / 2 and self.timeout > 0 and self.tolerance >= 0, "invalid timing")
        base, suffix = config["room"], config["roomSuffix"]
        require(all(isinstance(v, str) and re.fullmatch(r"[A-Za-z0-9_-]+", v) for v in [base, suffix])
                and len(suffix) >= 8, "supply a unique roomSuffix of at least eight safe characters")
        self.room = base + "-" + suffix + "-" + uuid.uuid4().hex[:8]
        self.endpoint = {k: wsmod.Endpoint(**config["delegates"][k]["endpoint"]) for k in ("a", "b")}
        for field in ("subject", "session"):
            require(config["delegates"]["a"][field] != config["delegates"]["b"][field], "delegates must have distinct " + field)
        tokens = [Path(self.endpoint[k].token).read_text().strip() for k in ("a", "b")]
        require(tokens[0] and tokens[1] and tokens[0] != tokens[1], "delegates require different authentication tokens")
        self.sockets = []
        self.seq = 0
        self.forbidden = set()
        self.report = {"schema": "spk-ws-continuity-journey-v1", "status": "running", "room": self.room,
                       "leaseSeconds": self.lease, "durationSeconds": self.duration,
                       "cutoffToleranceSeconds": self.tolerance, "snapshots": [], "traffic": {},
                       "regrant": "unqualified: hook omitted", "generationStop": "unqualified: hook omitted"}

    def save(self):
        if self.output:
            parent = Path(self.output).resolve().parent
            parent.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile(mode="w", dir=parent, prefix=".ws-continuity-", delete=False) as out:
                json.dump(self.report, out, indent=2)
                out.write("\n")
                name = out.name
            os.replace(name, self.output)

    def hook(self, name):
        argv = self.c["hooks"][name]
        require(isinstance(argv, list) and argv and all(isinstance(v, str) for v in argv), "hook must be an argv array")
        env = dict(os.environ, SPK_CONTINUITY_ROOM=self.room, SPK_CONTINUITY_ACTION=name)
        result = subprocess.run(argv, capture_output=True, timeout=float(self.c.get("hookTimeoutSeconds", 600)), env=env)
        require(result.returncode == 0, name + ": hook failed; inspect its own evidence, no automatic retry")
        require(len(result.stdout) <= 1024 * 1024, name + ": hook output too large")
        value = json.loads(result.stdout)
        require(isinstance(value, dict), name + ": hook must return one JSON object")
        return value

    def snapshot(self, label):
        raw = self.hook("snapshot")
        require(raw.get("schema") == "spk-ws-continuity-snapshot-v1", "snapshot schema mismatch")
        require(all(type(raw.get(k)) is int and raw[k] >= 0 for k in COUNTERS), "snapshot counters must be nonnegative integers")
        require(isinstance(raw.get("app"), str) and isinstance(raw.get("generation"), str), "snapshot app/generation required")
        billing = raw.get("billingCount")
        require(billing is None or type(billing) is int and billing >= 0, "billing count must be nonnegative or explicitly unavailable")
        require(billing is not None or isinstance(raw.get("billingEvidence"), str) and raw["billingEvidence"], "unavailable billing count needs billingEvidence")
        safe = {k: raw[k] for k in (*COUNTERS, "app", "generation")}
        safe["billingCount"] = billing
        safe["billingEvidence"] = raw.get("billingEvidence", "direct source-backed cumulative event count")
        self.report["directBillingCounter"] = "available" if billing is not None else "unqualified: using verified Store height for no-write evidence"
        if "evidence" in raw:
            require(isinstance(raw["evidence"], list) and all(isinstance(p, str) and Path(p).is_file() for p in raw["evidence"]), "snapshot evidence files missing")
            safe["evidence"] = raw["evidence"]
        safe["label"] = label
        safe["delegates"] = {}
        for key in ("a", "b"):
            got, expected = raw["delegates"][key], self.c["delegates"][key]
            require(all(got.get(k) == expected[k] for k in ("subject", "session")), "snapshot delegate identity mismatch")
            require(type(got.get("active")) is bool, "snapshot active state required")
            safe["delegates"][key] = {k: got[k] for k in ("subject", "session", "active")}
        if self.report["snapshots"]:
            prior = self.report["snapshots"][-1]
            require(safe["app"] == prior["app"] and safe["generation"] == prior["generation"], "fixture app/generation changed")
            require(all(safe[k] >= prior[k] for k in COUNTERS), "snapshot counters regressed")
            require((billing is None) == (prior["billingCount"] is None), "billing evidence availability changed")
            if billing is not None:
                require(billing >= prior["billingCount"], "billing counter regressed")
        self.report["snapshots"].append(safe)
        self.save()
        return safe

    def open(self, key):
        ws = wsmod.WS(None, PATH, timeout=float(self.c.get("openTimeoutSeconds", 120)), endpoint=self.endpoint[key])
        self.sockets.append(ws)
        ws.start(keepalive="2", every=20)
        opened = ws.get(time.monotonic() + self.timeout)
        require(isinstance(opened, str) and opened.startswith("0"), "Engine.IO open absent")
        self.wait(ws, lambda m: isinstance(m, str) and m.startswith("40"), time.monotonic() + self.timeout)
        self.log(ws, key)
        return ws

    def wait(self, ws, predicate, deadline):
        def checked(message):
            text = message if isinstance(message, str) else repr(message)
            require(not any(marker in text for marker in self.forbidden), "fresh A write observed after cutoff")
            return predicate(message)
        return wsmod.wait_for(ws, checked, deadline)

    def log(self, ws, key):
        ws.send("42" + json.dumps(["data", {"type": "ask.log", "room": self.room, "user": key}]))
        msg, _ = self.wait(ws, lambda m: (wsmod.sio_data(m) or {}).get("type") == "log", time.monotonic() + self.timeout)
        return json.dumps(wsmod.sio_data(msg), sort_keys=True)

    def command(self, key, tag):
        self.seq += 1
        marker = "%s-%s-%d-%s" % (key, tag, self.seq, uuid.uuid4().hex)
        return marker, {"type": "execute", "room": self.room, "user": key,
                        "cmdstr": "set %s1 text t %s" % ("A" if key == "a" else "B", marker), "saveundo": False}

    def edit(self, source, observer, key, tag):
        marker, command = self.command(key, tag)
        source.send("42" + json.dumps(["data", command]))
        if source is observer:
            require(marker in self.log(source, key), "fresh B write absent from app log")
        else:
            self.wait(observer, lambda m: (wsmod.sio_data(m) or {}).get("cmdstr") == command["cmdstr"],
                           time.monotonic() + self.timeout)
        return marker

    def action_while_b_writes(self, name, b):
        start = time.monotonic()
        edits = 0
        # Only the main thread consumes B's WS queue; hook subprocess IO is off-thread.
        def invoke():
            result = self.hook(name)
            return result, time.monotonic()
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:
            future = pool.submit(invoke)
            while not future.done():
                self.edit(b, b, "b", name)
                edits += 1
                time.sleep(self.interval)
            result, end = future.result()
        require(result.get("schema") == "spk-ws-continuity-action-v1" and result.get("action") == name
                and result.get("confirmed") is True, name + ": checked action not confirmed")
        require(isinstance(result.get("artifact"), str) and Path(result["artifact"]).is_file(), name + ": checked action evidence absent")
        self.report[name] = {"seconds": round(end-start, 3), "bConfirmedWrites": edits, "artifact": result["artifact"]}
        self.save()
        return start, end, result

    def run(self):
        before = self.snapshot("before-opens")
        require(all(before["delegates"][k]["active"] for k in ("a", "b")), "both delegates must start active")
        a, b = self.open("a"), self.open("b")
        opened = self.snapshot("after-two-opens")
        require(opened["dispatchCount"] == before["dispatchCount"]+2, "expected exactly two admitted opens")
        start, rounds = time.monotonic(), 0
        while time.monotonic()-start < self.duration:
            self.edit(a, b, "a", "renewal")
            self.edit(b, a, "b", "renewal")
            rounds += 1
            time.sleep(self.interval)
        renewed = self.snapshot("after-renewal-only-traffic")
        no_delta(opened, renewed, "initial sustained traffic")
        self.report["traffic"] = {"seconds": round(time.monotonic()-start, 3), "crossObservedEdits": 2*rounds}
        require(a.ended is None and b.ended is None, "stream ended before revoke")
        action_start, confirmed, _ = self.action_while_b_writes("revokeA", b)
        revoked = self.snapshot("after-revoke")
        require(not revoked["delegates"]["a"]["active"] and revoked["delegates"]["b"]["active"], "revoke changed wrong delegate")
        bound = confirmed + self.lease + self.tolerance
        while a.ended_at is None and time.monotonic() < bound:
            self.edit(b, b, "b", "await-a-cutoff")
            time.sleep(min(self.interval, max(0, bound-time.monotonic())))
        require(a.ended_at is not None and action_start <= a.ended_at <= bound, "A did not end within stated revoke bound")
        marker, command = self.command("a", "forbidden-after-cutoff")
        self.forbidden.add(marker)
        sent = True
        try:
            a.send("42" + json.dumps(["data", command]))
        except OSError:
            sent = False
        # Socket send success says nothing about admission. Ask the live app via B.
        self.edit(b, b, "b", "after-a-cutoff")
        time.sleep(float(self.c.get("absenceObservationSeconds", 2)))
        require(marker not in self.log(b, "b"), "fresh A write reached app after cutoff")
        no_delta(revoked, self.snapshot("after-revocation-traffic-only"), "post-revoke traffic")
        self.report["aCutoff"] = {"secondsAfterHookConfirmed": round(a.ended_at-confirmed, 3), "end": a.ended,
                                  "postCutoffSendReturnedSuccess": sent, "freshMarkerAbsentFromAppLog": True}
        try:
            self.open("a")
        except wsmod.Refused as refusal:
            require(refusal.status in self.c.get("newOpenRefusalStatuses", ["401", "403", "503"]), "unexpected fresh-open refusal")
            self.report["newAOpen"] = {"status": refusal.status, "refused": True}
        else:
            raise AssertionError("new A open admitted after revoke")
        no_delta(self.report["snapshots"][-1], self.snapshot("after-refused-open"), "refused open")
        self.edit(b, b, "b", "after-refused-a-open")
        if "regrantA" in self.c["hooks"]:
            _, _, regrant = self.action_while_b_writes("regrantA", b)
            if "endpoint" in regrant:
                replacement = wsmod.Endpoint(**regrant["endpoint"])
                require(Path(replacement.token).read_text().strip() != Path(self.endpoint["b"].token).read_text().strip(), "regrant reused B authentication")
                self.endpoint["a"] = replacement
            granted = self.snapshot("after-regrant")
            require(all(granted["delegates"][k]["active"] for k in ("a", "b")), "regrant did not restore A")
            require(a.ended is not None, "regrant revived original A stream")
            fresh = self.open("a")
            self.edit(fresh, b, "a", "regranted")
            after = self.snapshot("after-regranted-open-and-edit")
            require(after["dispatchCount"] == granted["dispatchCount"]+1, "regrant reconnect needs exactly one admitted open")
            self.report["regrant"] = {"freshOpenAndEdit": True, "oldStreamRemainedEnded": True, "endpointReplaced": "endpoint" in regrant}
        if "generationStop" in self.c["hooks"]:
            # STOP intentionally ends B, so do not require continuing traffic during this hook.
            result = self.hook("generationStop")
            require(result.get("schema") == "spk-ws-continuity-action-v1" and result.get("action") == "generationStop"
                    and result.get("confirmed") is True and Path(result.get("artifact", "")).is_file(), "generation STOP unconfirmed")
            deadline = time.monotonic()+self.lease+self.tolerance
            while any(s.ended is None for s in self.sockets) and time.monotonic() < deadline:
                time.sleep(min(self.interval, .1))
            require(all(s.ended is not None for s in self.sockets), "generation STOP left streams open")
            self.report["generationStop"] = {"allStreamsEnded": True, "artifact": result["artifact"]}
        self.report["status"] = "passed"
        self.save()
        return self.report

    def close(self):
        for ws in self.sockets:
            ws.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("config")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    journey = None
    try:
        journey = Journey(json.loads(Path(args.config).read_text()), args.output)
        result = journey.run()
        code = 0
    except Exception as error:
        result = journey.report if journey else {"schema": "spk-ws-continuity-journey-v1"}
        result.update(status="failed", error=type(error).__name__ + ": " + str(error))
        if journey:
            journey.save()
        else:
            Path(args.output).write_text(json.dumps(result, indent=2)+"\n")
        code = 1
    finally:
        if journey:
            journey.close()
    print(json.dumps(result))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
