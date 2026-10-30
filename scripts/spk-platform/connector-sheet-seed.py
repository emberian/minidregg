#!/usr/bin/env python3
"""Create the connector's EtherCalc sheet before its capture.

The connector's route is confined to one `_/SHEET/csv` GET (app-document.md), and EtherCalc answers that GET with an
empty 404 until the sheet exists, so a capture of a never-written sheet fails as "export requires a successful
representation". The owner's delegate is the participant who edits: it writes one cell over the Socket.IO entrance
(the same entrance and commands the joined-member hook uses) and reads the room log back.

  connector-sheet-seed.py FIXTURE SHEET     FIXTURE = the apps phase's fixture.json (delegates.owner.endpoint)
Prints one JSON object; exit 0 only when the cell is observed in the room log. Idempotent: an existing marker file
beside FIXTURE records the write and is only re-read, never re-sent.
"""
import importlib.util, json, pathlib, re, sys, time, uuid

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("jspk10_ws", HERE / "jspk10-ws.py")
ws = importlib.util.module_from_spec(spec); sys.modules["jspk10_ws"] = ws; spec.loader.exec_module(ws)


def main(fixture_path, sheet):
    if not re.fullmatch(r"[A-Za-z0-9_-]{1,128}", sheet):
        raise ValueError("exact simple EtherCalc sheet required")
    fixture = pathlib.Path(fixture_path)
    delegate = json.loads(fixture.read_text())["delegates"]["owner"]
    retained = fixture.parent / ("connector-sheet-" + sheet + ".json")
    if retained.exists():
        marker = json.loads(retained.read_text())["marker"]; write = False
    else:
        marker = "connector-" + uuid.uuid4().hex; write = True
        retained.write_text(json.dumps({"sheet": sheet, "marker": marker})); retained.chmod(0o600)
    sock = ws.WS(None, "/socket.io/?EIO=3&transport=websocket", timeout=60, endpoint=ws.Endpoint(**delegate["endpoint"]))
    sock.start(keepalive="2", every=20)
    try:
        opened = sock.get(time.monotonic() + 10)
        if not (isinstance(opened, str) and opened.startswith("0")):
            raise RuntimeError("Engine.IO opening absent")
        ws.wait_for(sock, lambda m: isinstance(m, str) and m.startswith("40"), time.monotonic() + 10)
        if write:
            sock.send("42" + json.dumps(["data", {"type": "execute", "room": sheet, "user": "connector-seed",
                                                  "cmdstr": "set A1 text t " + marker, "saveundo": False}]))
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline:
            sock.send("42" + json.dumps(["data", {"type": "ask.log", "room": sheet, "user": "connector-seed"}]))
            got, _ = ws.wait_for(sock, lambda m: (ws.sio_data(m) or {}).get("type") == "log", time.monotonic() + 10)
            if marker in json.dumps(ws.sio_data(got)):
                return {"protocol": "mini-connector-sheet-seed-v1", "sheet": sheet, "marker": marker, "written": write}
            time.sleep(1)
        raise RuntimeError("seeded cell not observed in the room log")
    finally:
        sock.close()


if __name__ == "__main__":
    try:
        print(json.dumps(main(*sys.argv[1:3])))
    except (RuntimeError, ValueError, KeyError, OSError, TypeError) as error:
        print("connector sheet seed: " + str(error), file=sys.stderr); sys.exit(1)
