"""Bounded Mini side of the isolated fn A↔B E1/E2 handoff.

The fn fixture owns both native Stores and publishes an atomic ready.json.
This driver uses the clean B3 baseline Mini executable; it never decides fn
article or consumer semantics in Python. See README.md for the exact contract.
"""

import base64
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import time


HERE = Path(__file__).resolve().parent
OUT = Path(os.environ["FN_E1E2_OUTPUT"])
HANDOFF = os.environ["FN_E1E2_HANDOFF"]
HOST = Path(os.environ["FN_E1E2_MINI_HOST"])
CONFIG = Path(os.environ["FN_E1E2_MINI_CONFIG"])
MINI = Path(os.environ["FN_E1E2_MINI_CLIENT"])
EXPECTED_FN_IMAGE = os.environ["FN_E1E2_EXPECTED_FN_IMAGE"]
EXPECTED_FN_LAUNCHER_SHA256 = os.environ["FN_E1E2_EXPECTED_FN_LAUNCHER_SHA256"]
EXPECTED_FN_CORE_SHA256 = os.environ["FN_E1E2_EXPECTED_FN_CORE_SHA256"]
BRIDGE = HERE / "fn_bridge.sh"
OUT.mkdir(exist_ok=False)
TIMINGS = {}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(label, argv, expected=0, env=None):
    print(label, flush=True)
    started = time.monotonic()
    with (OUT / (label + ".stdout")).open("wb") as stdout, \
            (OUT / (label + ".stderr")).open("wb") as stderr:
        result = subprocess.run([str(arg) for arg in argv], stdout=stdout,
                                stderr=stderr, env=env, timeout=240, check=False)
    TIMINGS[label] = {"seconds": round(time.monotonic() - started, 3),
                      "exit_code": result.returncode}
    (OUT / "timings.json").write_text(json.dumps(TIMINGS, sort_keys=True,
                                                   indent=2) + "\n")
    if result.returncode != expected:
        tail = (OUT / (label + ".stderr")).read_text(errors="replace")[-500:]
        raise RuntimeError(f"{label}: exit {result.returncode}, expected {expected}: {tail}")
    return result


def remote_path(value):
    if not (isinstance(value, str) and value.startswith("/") and
            re.fullmatch(r"/[A-Za-z0-9_./-]+", value)):
        raise ValueError("invalid absolute remote path")
    return value


def remote(*args):
    return ["ssh", "hbox", " ".join(shlex.quote(str(arg)) for arg in args)]


def fetch(field, name):
    source = remote_path(READY[field])
    target = OUT / name
    run("fetch-" + name, ["scp", "-q", "hbox:" + source, target])
    return target


def native_source(label, carrier, public_pem):
    run(label, [BRIDGE, "--fn", "hybrid-verify-source", carrier, public_pem])
    fields = (OUT / (label + ".stdout")).read_text("ascii").strip().split()
    if len(fields) != 6 or fields[0] != "fn-portable-v1":
        raise AssertionError("native verifier returned unexpected tuple")
    return fields


def pin(principal, ed_public, ml_raw, ml_pem):
    p, e, m = (Path(value).read_bytes() for value in
               (principal, ed_public, ml_raw))
    if len(p) != 32 or len(e) != 32 or len(m) != 1952:
        raise AssertionError("unexpected fn signer public key width")
    return {"fnBinary": str(BRIDGE), "mlPublicKey": str(ml_pem),
            "principal": p.hex(), "edPublicKey": e.hex(),
            "mlPublicKeyHex": m.hex()}


if not re.fullmatch(r"/tank/fn/gates/[A-Za-z0-9_./-]+", HANDOFF):
    raise ValueError("handoff must be an isolated fn gate path")

started = time.monotonic()
for _ in range(240):
    if subprocess.run(remote("test", "-f", HANDOFF + "/ready.json"),
                      stdout=subprocess.DEVNULL,
                      stderr=subprocess.DEVNULL).returncode == 0:
        break
    time.sleep(1)
else:
    raise RuntimeError("native A/B fixture never published ready.json")
TIMINGS["wait-ready"] = {"seconds": round(time.monotonic() - started, 3),
                          "exit_code": 0}
run("ready", ["scp", "-q", "hbox:" + HANDOFF + "/ready.json", OUT / "ready.json"])
READY = json.loads((OUT / "ready.json").read_text("ascii"))
assert READY["version"] == 1 and READY["consumer_b"] == "worker"
assert READY["image"] == remote_path(EXPECTED_FN_IMAGE)
assert READY["image"].startswith("/tank/fn/gates/")
assert READY["q_generation"] == 2
for digest in (EXPECTED_FN_LAUNCHER_SHA256, EXPECTED_FN_CORE_SHA256):
    assert re.fullmatch(r"[0-9a-f]{64}", digest)
run("hash-fn-image", remote("sha256sum", READY["image"], READY["image"] + ".core"))
image_hashes = (OUT / "hash-fn-image.stdout").read_text("ascii").strip().splitlines()
assert len(image_hashes) == 2
assert image_hashes[0].split() == [EXPECTED_FN_LAUNCHER_SHA256, READY["image"]]
assert image_hashes[1].split() == [EXPECTED_FN_CORE_SHA256, READY["image"] + ".core"]
os.environ["FN_B3_IMAGE"] = READY["image"]

# R's exact source is old experimental content, but the fn publication and
# authenticated B admission are fresh in this pair of Stores.
r_source = fetch("r_source", "r.source")
r_carrier = fetch("r_carrier_b", "r-at-b.eml")
r_principal = fetch("r_principal", "r-principal.bin")
r_ed = fetch("r_ed_public", "r-ed-public.bin")
r_ml = fetch("r_ml_public", "r-ml-public.pem")
r_ml_raw = fetch("r_ml_public_raw", "r-ml-public.raw")
registered = fetch("b_registered_cursor", "b-registered.fncu")
preview_cursor = fetch("b_preview_cursor", "b-preview.fncu")
preview_report = fetch("b_preview_report", "b-preview.fn-e")
assert sha(r_source) == "fca9c81e8cd02281b3703df4e931ae82c55a0bda63b3cf3447c8e32e13199000"
r_verified = native_source("verify-r-at-b", r_carrier, r_ml)
assert r_verified[1] == r_principal.read_bytes().hex()
assert r_verified[3] == r_ed.read_bytes().hex()
assert r_verified[4] == r_ml_raw.read_bytes().hex()
assert bytes.fromhex(r_verified[5]) == r_source.read_bytes()
assert READY["r_message_id"].encode("ascii") in r_source.read_bytes()

r_pin = pin(r_principal, r_ed, r_ml_raw, r_ml)
(OUT / "r-fn-pin.json").write_text(json.dumps(r_pin, sort_keys=True) + "\n")
run("project-preview", [BRIDGE, "--fn", "consumer-project",
                        preview_cursor, preview_report])
projected = (OUT / "project-preview.stdout").read_text("ascii").strip().split(" ")
assert len(projected) == 18 and projected[0] == "fn-consumer-project-v1"
assert bytes.fromhex(projected[14]) == r_source.read_bytes()
assert bytes.fromhex(projected[15]) == r_carrier.read_bytes()
assert projected[12] == r_verified[2]
assert bytes.fromhex(projected[13]).decode("ascii") == READY["r_message_id"]
assert registered.read_bytes() != preview_cursor.read_bytes()
scope = {"history": projected[1], "incarnation": projected[2],
         "consumer": projected[3], "principal": projected[4],
         "query": projected[5], "queryVersion": int(projected[6]),
         "viewVersion": int(projected[7]), "registrationEpoch": int(projected[8])}
(OUT / "b-scope-pin.json").write_text(json.dumps(scope, sort_keys=True) + "\n")

run("b-mini-decide", [HOST, CONFIG, "consumer-poll-decide",
                      os.environ["FN_E1E2_ORIGIN_PIN"], OUT / "r-fn-pin.json",
                      OUT / "b-scope-pin.json", os.environ["FN_E1E2_CLAIM"],
                      os.environ["FN_E1E2_POLICY"], READY["b_control"],
                      OUT / "b-live.fncu", OUT / "b-live.fn-e",
                      OUT / "b-live.eml", OUT / "intent.bin",
                      OUT / "decision.json"])
decision = json.loads((OUT / "decision.json").read_text())
assert decision["storeAdmission"] == "observed-control-poll"
assert decision["decision"]["type"] == "proposed-fresh"
assert (OUT / "b-live.fncu").read_bytes() == preview_cursor.read_bytes()
assert (OUT / "b-live.fn-e").read_bytes() == preview_report.read_bytes()
assert (OUT / "b-live.eml").read_bytes() == r_carrier.read_bytes()

run("mini-submit", [MINI, "submit", "--host", HOST, "--config", CONFIG,
                    "--intent", OUT / "intent.bin", "--intent-kind", "binary",
                    "--key", os.environ["FN_E1E2_CUSTODY_KEY"],
                    "--dir", OUT / "mini-attempt"])
outcome = json.loads((OUT / "mini-attempt/outcome.json").read_text())
assert outcome["type"] == "confirmed" and outcome["confirmation"] == "installed"
assert outcome["acceptedCount"] == "2"
tx = outcome["transactionId"]
run("mini-export-poll", [HOST, CONFIG, "consumer-export-poll", tx,
                         OUT / "export.fncu", OUT / "export.fn-e",
                         OUT / "export.json"])
assert (OUT / "export.fncu").read_bytes() == (OUT / "b-live.fncu").read_bytes()
assert (OUT / "export.fn-e").read_bytes() == (OUT / "b-live.fn-e").read_bytes()
assert json.loads((OUT / "export.json").read_text())["pollCallObserved"] is True
run("mini-export-q", [HOST, CONFIG, "consumer-export-reply", tx, OUT / "reply.bin"])
assert (OUT / "reply.bin").read_bytes() == bytes.fromhex(decision["decision"]["reply"])

# The bridge lets fn finish an advancing ACK, then loses only its response.
# Mini must report transport-fault; read-only position settles the true state.
drop_ack = dict(os.environ, FN_E1E2_DROP_ACK_REPLY="1")
run("b-ack-lost-response", [HOST, CONFIG, "consumer-ack-poll",
     OUT / "r-fn-pin.json", OUT / "b-scope-pin.json", READY["b_control"],
     tx, OUT / "b-live.fncu", OUT / "b-live.fn-e", OUT / "ack-lost.json"],
    expected=4, env=drop_ack)
assert json.loads((OUT / "ack-lost.json").read_text())["fnAck"] == "transport-fault"
run("b-position-after-loss", [BRIDGE, "--fn", "consumer", "position",
                              READY["b_control"], "worker", OUT / "b-position.fncu"])
assert (OUT / "b-position.fncu").read_bytes() == (OUT / "b-live.fncu").read_bytes()
run("b-ack-idempotent", [HOST, CONFIG, "consumer-ack-poll",
     OUT / "r-fn-pin.json", OUT / "b-scope-pin.json", READY["b_control"],
     tx, OUT / "b-live.fncu", OUT / "b-live.fn-e", OUT / "ack-repeat.json"])
assert json.loads((OUT / "ack-repeat.json").read_text())["fnAck"] == "durable-accepted"

q_principal = fetch("q_principal", "q-principal.bin")
q_ed = fetch("q_ed_public", "q-ed-public.bin")
q_ml = fetch("q_ml_public", "q-ml-public.pem")
q_ml_raw = fetch("q_ml_public_raw", "q-ml-public.raw")
assert q_principal.read_bytes() != r_principal.read_bytes()
assert q_ed.read_bytes() != r_ed.read_bytes()
assert q_ml_raw.read_bytes() != r_ml_raw.read_bytes()
q_pin = pin(q_principal, q_ed, q_ml_raw, q_ml)
(OUT / "q-signer.json").write_text(json.dumps({k: q_pin[k] for k in
    ("principal", "edPublicKey", "mlPublicKeyHex")}, sort_keys=True) + "\n")
(OUT / "q-fn-pin.json").write_text(json.dumps(q_pin, sort_keys=True) + "\n")

run("q-prepare", [HOST, CONFIG, "consumer-stage-reply-plan",
                  OUT / "q-signer.json", tx, OUT / "q-prepared-store",
                  OUT / "q-prepared-candidate.bin", OUT / "q-prepared-readback.bin",
                  OUT / "q-prepared.source", OUT / "q-prepared.json"])
prepared = json.loads((OUT / "q-prepared.json").read_text())
assert prepared["stage"] == "durable-accepted"
assert (OUT / "q-prepared-candidate.bin").read_bytes() == \
       (OUT / "q-prepared-readback.bin").read_bytes()
run("q-sign-stage", [HOST, CONFIG, "consumer-stage-reply-sign",
     OUT / "q-fn-pin.json", q_principal, q_ed, READY["q_ed_secret"],
     READY["q_ml_private"], tx, OUT / "q-prepared-store",
     OUT / "q-signed-store", OUT / "q-plan-readback.bin",
     OUT / "q.source", OUT / "q-preflight-carrier.eml",
     OUT / "q-signed-candidate.bin", OUT / "q-signed-readback.bin",
     OUT / "q-ed.sig", OUT / "q-ml.sig", OUT / "q-signed.json"])
signed = json.loads((OUT / "q-signed.json").read_text())
assert signed["stage"] == "durable-accepted"
assert signed["messageId"] == prepared["messageId"]
assert (OUT / "q.source").read_bytes() == (OUT / "q-prepared.source").read_bytes()
assert (OUT / "q-signed-candidate.bin").read_bytes() == \
       (OUT / "q-signed-readback.bin").read_bytes()

# A fresh Mini process cannot access the synthetic private keys here.
run("q-signed-slot-reopen", [HOST, CONFIG, "consumer-stage-reply-sign",
     OUT / "q-fn-pin.json", q_principal, q_ed,
     "/no-retry-ed-secret", "/no-retry-ml-secret", tx,
     OUT / "q-prepared-store", OUT / "q-signed-store",
     OUT / "q-repeat-plan.bin", OUT / "q-repeat.source",
     OUT / "q-repeat-carrier.eml", OUT / "q-repeat-signed-candidate.bin",
     OUT / "q-repeat-signed-readback.bin", OUT / "q-repeat-ed.sig",
     OUT / "q-repeat-ml.sig", OUT / "q-repeat-signed.json"])
repeat = json.loads((OUT / "q-repeat-signed.json").read_text())
assert repeat["stage"] == "durable-accepted"
assert repeat["messageId"] == signed["messageId"]
assert repeat["sourceIdentity"] == signed["sourceIdentity"]
assert not (OUT / "q-repeat-carrier.eml").exists()
for repeat_name, first_name in (("q-repeat.source", "q.source"),
                                ("q-repeat-ed.sig", "q-ed.sig"),
                                ("q-repeat-ml.sig", "q-ml.sig")):
    assert (OUT / repeat_name).read_bytes() == (OUT / first_name).read_bytes()
assert (OUT / "q-repeat-signed-readback.bin").read_bytes() == \
       (OUT / "q-signed-readback.bin").read_bytes()

# The native post succeeds, but the shell transport loses its response.
# A protected read-only lookup and native verifier settle this ambiguity.
drop_post = dict(os.environ, FN_E1E2_DROP_POST_REPLY="1")
run("q-post-lost-response", [BRIDGE, "--fn", "hybrid-author",
     READY["b_control"], READY["q_generation"], OUT / "q.source",
     OUT / "q-ed.sig", OUT / "q-ml.sig", q_ml], expected=75, env=drop_post)
run("stage-probe", ["scp", "-q", HERE / "protected_article.py",
                    "hbox:" + HANDOFF + "/protected_article.py"])
probe_path = HANDOFF + "/protected_article.py"
settled_path = HANDOFF + "/q-settled-at-b.eml"
run("q-protected-lookup", remote("python3", probe_path,
    HANDOFF + "/ready.json", signed["messageId"], settled_path))
run("fetch-q-settled", ["scp", "-q", "hbox:" + settled_path,
                        OUT / "q-settled-at-b.eml"])
q_verified = native_source("verify-q-settled", OUT / "q-settled-at-b.eml", q_ml)
assert q_verified[1] == q_principal.read_bytes().hex()
assert q_verified[2] == signed["sourceIdentity"]
assert q_verified[3] == q_ed.read_bytes().hex()
assert q_verified[4] == q_ml_raw.read_bytes().hex()
assert bytes.fromhex(q_verified[5]) == (OUT / "q.source").read_bytes()

run("post-q-source", ["scp", "-q", OUT / "q.source",
                      "hbox:" + HANDOFF + "/posted.source"])
run("post-q-reply", ["scp", "-q", OUT / "reply.bin",
                     "hbox:" + HANDOFF + "/posted.reply.bin"])
marker = {"result": "accepted", "message_id": signed["messageId"],
          "source_identity": signed["sourceIdentity"],
          "mini_transaction": tx, "r_message_id": READY["r_message_id"],
          "r_source_identity": r_verified[2],
          "source_sha256": sha(OUT / "q.source"),
          "reply_sha256": sha(OUT / "reply.bin")}
(OUT / "mini-finished.json").write_text(json.dumps(marker, sort_keys=True) + "\n")
run("post-marker-temp", ["scp", "-q", OUT / "mini-finished.json",
                         "hbox:" + HANDOFF + "/mini-finished.json.tmp"])
run("post-marker-atomic", remote("mv", HANDOFF + "/mini-finished.json.tmp",
                                  HANDOFF + "/mini-finished.json"))
(OUT / "summary.json").write_text(json.dumps({"marker": marker,
    "r_source_sha256": sha(r_source), "r_carrier_b_sha256": sha(r_carrier),
    "b_poll_sha256": sha(OUT / "b-live.fn-e"),
    "b_cursor_sha256": sha(OUT / "b-live.fncu"),
    "q_reply_sha256": sha(OUT / "reply.bin"),
    "q_signed_slot_sha256": sha(OUT / "q-signed-readback.bin"),
    "q_carrier_b_sha256": sha(OUT / "q-settled-at-b.eml")},
    sort_keys=True, indent=2) + "\n")
print("MINI A/B HANDOFF ACCEPTED", tx, flush=True)

# The fn owner now cold-reopens both Stores and observes protected B→A Q.
# Keep its result separate from the already settled B post above.
started = time.monotonic()
for _ in range(240):
    if subprocess.run(remote("test", "-f", HANDOFF + "/owner-finished.json"),
                      stdout=subprocess.DEVNULL,
                      stderr=subprocess.DEVNULL).returncode == 0:
        break
    time.sleep(1)
else:
    raise RuntimeError("B post settled, but A owner did not finish")
TIMINGS["wait-a-owner"] = {"seconds": round(time.monotonic() - started, 3),
                            "exit_code": 0}
run("fetch-owner-finished", ["scp", "-q", "hbox:" + HANDOFF + "/owner-finished.json",
                             OUT / "owner-finished.json"])
owner = json.loads((OUT / "owner-finished.json").read_text("ascii"))
assert owner["result"] == "accepted"
assert owner["message_id"] == signed["messageId"]
assert owner["source_identity"] == signed["sourceIdentity"]
assert owner["a_q_position_unchanged"] is True
for remote_name, local_name in (("a-q-carrier.eml", "q-at-a.eml"),
                                ("a-q-verified-source.bin", "q-verified-at-a.source"),
                                ("a-q-verifier.txt", "a-q-verifier.txt"),
                                ("a-q-poll.fncu", "a-q-poll.fncu"),
                                ("a-q-poll.fn-e", "a-q-poll.fn-e")):
    run("fetch-" + local_name, ["scp", "-q", "hbox:" + HANDOFF + "/" + remote_name,
                                OUT / local_name])
a_verified = native_source("verify-q-at-a", OUT / "q-at-a.eml", q_ml)
assert a_verified[1:5] == q_verified[1:5]
assert bytes.fromhex(a_verified[5]) == (OUT / "q.source").read_bytes()
assert (OUT / "q-verified-at-a.source").read_bytes() == bytes.fromhex(a_verified[5])
assert (OUT / "a-q-verifier.txt").read_text("ascii").strip().split() == a_verified
run("project-a-q", [BRIDGE, "--fn", "consumer-project",
                    OUT / "a-q-poll.fncu", OUT / "a-q-poll.fn-e"])
a_projected = (OUT / "project-a-q.stdout").read_text("ascii").strip().split(" ")
assert len(a_projected) == 18 and a_projected[0] == "fn-consumer-project-v1"
assert a_projected[12] == signed["sourceIdentity"]
assert bytes.fromhex(a_projected[13]).decode("ascii") == signed["messageId"]
assert bytes.fromhex(a_projected[14]) == (OUT / "q.source").read_bytes()
assert bytes.fromhex(a_projected[15]) == (OUT / "q-at-a.eml").read_bytes()

(OUT / "r-source-identity.bin").write_bytes(bytes.fromhex(r_verified[2]))
run("build-a-check", ["lake", "build", "Kernel.FnReplyPublication"])
run("check-a-correlation", ["lake", "env", "lean", "--run",
    HERE / "check_a_reply.lean", OUT / "q-prepared-readback.bin",
    OUT / "q-signed-readback.bin", OUT / "reply.bin", r_source,
    OUT / "r-source-identity.bin", OUT / "q-verified-at-a.source"])
summary = json.loads((OUT / "summary.json").read_text())
summary["a_owner"] = owner
summary["a_q_carrier_sha256"] = sha(OUT / "q-at-a.eml")
summary["a_q_poll_sha256"] = sha(OUT / "a-q-poll.fn-e")
summary["a_q_source_sha256"] = sha(OUT / "q-verified-at-a.source")
(OUT / "summary.json").write_text(json.dumps(summary, sort_keys=True,
                                             indent=2) + "\n")
print("TWO-STORE A/B/A TRACE PASS", tx, flush=True)
