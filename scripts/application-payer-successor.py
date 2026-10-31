#!/usr/bin/env python3
"""Operator repair of derived payer pins; native code owns admission and custody.

After a completed native STOP and a stopped, settled controller, reinspect the
same accepted grant and register an immutable successor route. No grant/session
is issued, and no journal or prior registration is rewritten. The caller then
uses ordinary native START, session enrollment and controller enrollment.

Input protocol mini-application-payer-successor-v1 names attachmentRoot,
allocation, profile, host, hostConfig, spkHost, correctedRepo, controllerStatus,
controllerJournal, controllerEvidence, stopReceipt, outputDir, successorName,
inspectionMode (explicitly "detached" for these retained old cohorts). Optional contract
selects a generic attachment whose two source pins are explicitly adopted.
Optional miniUpgrade {binary,receipt} adopts an already installed controller
Mini image only when the fixed installer receipt links its old and new hashes.
Every path is absolute. outputDir must be attachmentRoot/repair-payer-custody.
Reentry resumes only the identical retained request and publication transaction;
an interrupted native invocation is never automatically submitted again.
"""
import copy
import base64
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def raw(path):
    path = Path(path)
    for parent in (path, *path.parents):
        require(not parent.is_symlink(), f"linked input refused: {parent}")
    m = path.stat()
    require(stat.S_ISREG(m.st_mode) and m.st_nlink == 1 and m.st_uid in (0, os.getuid())
            and not m.st_mode & 0o022, f"input custody refused: {path}")
    return path.read_bytes()


def read(path):
    return json.loads(raw(path))


def encode(value):
    return (json.dumps(value, indent=2) + "\n").encode()


def write(path, data):
    data = data if isinstance(data, bytes) else encode(data)
    with Path(path).open("xb") as out:
        os.chmod(path, 0o600)
        out.write(data)
        out.flush()




def narrowed(value):
    """The only permitted metadata change removes the obsolete observation slot."""
    pins = value.get("payerPins")
    require(isinstance(pins, list) and [p.get("role") for p in pins] == ["4", "8", "1"],
            "original payer slots must be exactly target/observation/authority")
    require(all(set(p) == {"role", "index", "keyId", "keyEpoch", "publicKeyHex"} for p in pins),
            "payer pin fields differ")
    identity = {k: v for k, v in pins[0].items() if k != "role"}
    require(identity["index"] == "0" and all({k: v for k, v in p.items() if k != "role"} == identity for p in pins),
            "payer witness identity differs across roles")
    result = copy.deepcopy(value)
    result["payerPins"] = [result["payerPins"][0], result["payerPins"][2]]
    return result


def check_settled(status, journal, registration, evidence=None):
    layout = registration["layout"]
    require(status.get("stopped") is True and status.get("store") == layout["store"]
            and type(status.get("controllerUid")) is int
            and status["controllerUid"] == layout["controllerUid"] not in (0, os.getuid()),
            "fixed stopped controller identity differs")
    fields = ("applicationApiAttempt", "dispatchAttempt", "dispatchHold", "dispatchPending",
              "foregroundAttempt", "parentHold", "toolHold", "toolPending", "pending", "settlementDue",
              "providerAttempt", "providerHold", "providerPending", "child", "roomAttempt", "workspaceAttempt",
              "birthPending", "birthOperation", "workspaceBirth", "residentDelivery", "residentCompletion", "promptWitness",
              "providerSettlement", "providerRetryGate", "hermesSession")
    require(all(journal.get(k) is None for k in fields) and journal.get("unresolvedExternal") == []
            and not journal.get("hardReconnectPending") and journal.get("connection") not in ("fenced", "hard"),
            "controller retains unsettled custody")
    for family, field in (("workspaceResolutions", "resolution"), ("foregroundHistory", "phase"),
                          ("applicationApiHistory", "phase")):
        seen = set()
        for entry in reversed(journal.get(family, [])):
            operation = entry["operationId"]
            if operation not in seen:
                require(entry[field] != "uncertain", "controller retains unresolved historical work: " + family)
                seen.add(operation)
    if evidence is not None:
        require(evidence.get("protocol") == "mini-spk-controller-evidence-v1" and evidence.get("store") == layout["store"],
                "controller evidence belongs to another Store")
        def decoded(name):
            file = evidence["files"][name]
            data = base64.b64decode(file["base64"], validate=True)
            require(digest(data) == file["sha256"], "controller evidence digest differs")
            return json.loads(data)
        require(decoded("journal.json") == journal, "stopped journal and exported journal differ")
        config = journal["binding"]["config"]
        require(journal["binding"]["configPath"] == str(Path(layout["controllerHome"]) / "controller.json"),
                "controller journal installation root differs")
        if config.get("toolTask", {}).get("room") is not None:
            state, requests = decoded("resident/resident.json"), decoded("resident/requests.json")
            require(state.get("pending") is None and not state.get("returnPending") and requests.get("selected") is None
                    and requests.get("maintenancePending") is None
                    and not requests.get("pending") and not requests.get("queue") and not requests.get("queued"),
                    "room resident has pending work")


def check_stopped(value, stop, app):
    require(stop.get("protocol") == "mini-spk-grain-stop-v1" and stop.get("app") == app
            and stop.get("activeState") in ("inactive", "failed"), "native STOP receipt differs")
    require(value.get("protocol") == "mini-spk-grain-status-v2" and value.get("app") == app,
            "native application status differs")
    runs = value["runs"]
    require(runs and all(r["state"] in ("stopped", "never-begun") for r in runs),
            "application is not stopped")
    latest = max(runs, key=lambda r: int(r["generation"]))
    require(latest["state"] == "stopped" and all(latest.get(k) == stop.get(k) for k in ("generation", "unit")),
            "STOP receipt is not the latest native generation")


def publish(path, before, after):
    current = raw(path)
    if current == after:
        return
    require(current == before, f"publication changed outside retained transition: {path}")
    temporary = Path(str(path) + ".payer-next")
    if temporary.exists():
        require(raw(temporary) == after, "interrupted temporary publication differs")
    else:
        write(temporary, after)
    os.replace(temporary, path)


def adopt_mini(previous, upgrade, journal, status):
    require(isinstance(upgrade, dict) and set(upgrade) == {"binary", "receipt"}, "Mini upgrade input differs")
    for path in upgrade.values():
        require(isinstance(path, str) and Path(path).is_absolute() and ".." not in Path(path).parts,
                "absolute Mini upgrade paths required")
    receipt = read(upgrade["receipt"])
    new_sha = digest(raw(upgrade["binary"]))
    installed = journal["binding"]["config"]["mini"]
    require(receipt.get("store") == status["store"]
            and receipt.get("previousMiniSha256") == previous["sha256"]["mini"]
            and receipt.get("miniSha256") == new_sha == digest(raw(installed))
            and receipt.get("miniUpgrade") == f"/var/lib/mini-spk-worlds/{status['store']}/controller/mini-upgrade-{new_sha}.json",
            "Mini upgrade receipt does not bind the old attachment and installed image")
    updated = copy.deepcopy(previous)
    updated["contract"]["paths"]["mini"] = upgrade["binary"]
    updated["files"]["mini"] = upgrade["binary"]
    updated["sha256"]["mini"] = new_sha
    return updated


class Repair:
    def __init__(self, request):
        self.input = Path(request)
        self.c = read(request)
        c = self.c
        fields = {"protocol", "attachmentRoot", "allocation", "profile", "host", "hostConfig", "spkHost",
                  "correctedRepo", "controllerStatus", "controllerJournal", "controllerEvidence", "stopReceipt", "outputDir", "successorName", "inspectionMode"}
        require(set(c) in (fields, fields | {"contract"}, fields | {"contract", "miniUpgrade"})
                and c["protocol"] == "mini-application-payer-successor-v1",
                "payer successor request shape differs")
        require(c["inspectionMode"] == "detached", "retained-cohort repair requires explicit detached inspection")
        for k in set(c) - {"protocol", "successorName", "inspectionMode", "miniUpgrade"}:
            require(isinstance(c[k], str) and Path(c[k]).is_absolute() and ".." not in Path(c[k]).parts,
                    "absolute input paths required")
        require(re.fullmatch(r"[A-Za-z0-9_-]{1,48}", c["successorName"]), "successor name refused")
        self.root = Path(c["attachmentRoot"])
        self.out = Path(c["outputDir"])
        require(self.out == self.root / "repair-payer-custody", "repair must be directly under attachment root")
        m = self.root.stat()
        require(m.st_uid == os.getuid() and stat.S_IMODE(m.st_mode) == 0o700 and not self.root.is_symlink(),
                "private attachment root required")
        self.lock = os.open(self.root / ".payer-successor.lock", os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        require(os.fstat(self.lock).st_nlink == 1 and os.fstat(self.lock).st_uid == os.getuid(), "repair lock custody differs")
        fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.renderer = Path(c["correctedRepo"]) / "scripts/spk-platform/prepare-lifetime-route.sh"
        self.orchestrator = Path(c["correctedRepo"]) / ("scripts/application-attachment.py" if "contract" in c
                                                    else "deploy/oracle/acceptance/agent.py")
        if not self.out.exists():
            self.out.mkdir(mode=0o700)
            write(self.out / "input.json", raw(request))
            for name in ("registered-agent-route.json", "attachment.json"):
                if (self.root / name).exists():
                    write(self.out / ("before-" + name), raw(self.root / name))
            if "contract" in c:
                write(self.out / "before-contract.json", raw(c["contract"]))
            self.prepare()
        require(raw(self.out / "input.json") == raw(request), "retained successor request differs")
        self.plan = read(self.out / "plan.json")
        for path, expected in self.plan["pins"].items():
            require(digest(raw(path)) == expected, f"successor input changed: {path}")

    def prepare(self):
        c = self.c
        old = read(self.out / "before-registered-agent-route.json")
        journal = read(c["controllerJournal"])
        check_settled(read(c["controllerStatus"]), journal, old, read(c["controllerEvidence"]))
        allocation = read(c["allocation"])
        old_request = read(old["request"])
        require(old_request["name"] != c["successorName"], "successor must have a new registration name")
        custody = read(Path(old["sourceRoute"]) / "resident-custody-v3.json")
        require(custody["lineage"]["appResource"] == allocation["app"], "custody names another app")
        require(journal["binding"]["config"]["task"] == custody["lineage"]["parentTask"], "journal names another controller task")
        native = read(old["registration"]["registration"])
        require(native["registration"] == old_request
                and bytes.fromhex(native["custodyHex"]) == raw(Path(old["sourceRoute"]) / "resident-custody-v3.json"),
                "old native registration differs from retained attachment")
        pins = narrowed(read(old["pins"]))
        require(pins["hostUnit"] is None, "initial registration must not select a running unit")
        write(self.out / "operator-pins.json", pins)
        write(self.out / "expected-custody.json", narrowed(custody))
        paths = [self.input, self.renderer, self.orchestrator, Path(__file__).resolve(),
                 *[Path(c[k]) for k in ("allocation", "profile", "host", "hostConfig", "spkHost", "controllerStatus", "controllerJournal", "controllerEvidence", "stopReceipt")],
                 Path(old["pins"]), Path(old["request"]), Path(old["registration"]["registration"]),
                 Path(old["sourceRoute"]) / "resident-custody-v3.json"]
        grant = Path(old["grantAttempt"])
        paths.extend(p for p in grant.iterdir() if p.is_file())
        if "contract" in c:
            previous = read(self.out / "before-attachment.json")
            require(previous["contract"] == read(c["contract"]), "generic attachment contract changed")
            for key, path in previous["files"].items():
                require(digest(raw(path)) == previous["sha256"][key], "original generic attachment pin changed: " + key)
                paths.append(Path(path))
            for key in ("orchestrator", "routeRenderer"):
                write(self.out / ("previous-" + key), raw(previous["files"][key]))
            updated = copy.deepcopy(previous)
            if "miniUpgrade" in c:
                updated = adopt_mini(previous, c["miniUpgrade"], journal, read(c["controllerStatus"]))
                paths.extend(Path(p) for p in c["miniUpgrade"].values())
                paths.append(Path(journal["binding"]["config"]["mini"]))
                write(self.out / "mini-upgrade-receipt.json", raw(c["miniUpgrade"]["receipt"]))
            updated["contract"]["paths"]["repo"] = c["correctedRepo"]
            updated["contract"]["inspectionMode"] = c["inspectionMode"]
            for key, path in (("orchestrator", self.orchestrator), ("routeRenderer", self.renderer)):
                updated["files"][key] = str(path)
                updated["sha256"][key] = digest(raw(path))
            write(self.out / "after-attachment.json", updated)
            write(self.out / "after-contract.json", updated["contract"])
        write(self.out / "plan.json", {"pins": {str(p): digest(raw(p)) for p in paths}, "app": allocation["app"]})

    def command(self, label, args):
        marker = self.out / (label + ".command.json")
        if marker.exists():
            require(read(marker) == list(map(str, args)), "retained native argv differs")
            require((self.out / (label + ".exit.json")).exists(), "native invocation interrupted; inspect retained evidence, do not resend")
        else:
            write(marker, list(map(str, args)))
            with (self.out / (label + ".stdout")).open("xb") as stdout, (self.out / (label + ".stderr")).open("xb") as stderr:
                result = subprocess.run(list(map(str, args)), stdout=stdout, stderr=stderr, timeout=2400)
            write(self.out / (label + ".exit.json"), {"exitCode": result.returncode})
        require(read(self.out / (label + ".exit.json"))["exitCode"] == 0, "native invocation failed: " + label)
        return self.out / (label + ".stdout")

    def run(self):
        c = self.c
        old = read(self.out / "before-registered-agent-route.json")
        # Always inspect current lifecycle, even when resuming metadata publication.
        with (self.out / "status-latest.stdout").open("wb") as stdout:
            subprocess.run([c["spkHost"], "grain", "status", c["profile"], self.plan["app"]], stdout=stdout, check=True, timeout=1800)
        check_stopped(read(self.out / "status-latest.stdout"), read(c["stopReceipt"]), self.plan["app"])
        routes = self.out / "source-route"
        self.command("render", ["sh", self.renderer, "--custody-only", c["host"], c["hostConfig"],
            old["grantAttempt"], old["lookup"], self.out / "operator-pins.json", routes,
            digest(raw(c["host"])), c["allocation"], read(c["allocation"])["agents"][0]["route"]])
        require(read(routes / "resident-custody-v3.json") == read(self.out / "expected-custody.json"),
                "native reinspection changed more than payer signing witnesses")
        request = read(old["request"])
        request.update(name=c["successorName"], replaces=request["name"], custody=str(routes / "resident-custody-v3.json"))
        request_path = self.out / "route-request.json"
        if not request_path.exists(): write(request_path, request)
        require(read(request_path) == request, "successor registration request changed")
        result = read(self.command("register", [c["spkHost"], "grain", "agent-route", c["profile"], self.plan["app"], request_path]))
        require(result.get("protocol") == "mini-spk-grain-agent-route-registered-v1"
                and result.get("app") == self.plan["app"] and result.get("name") == c["successorName"]
                and result.get("grantIssued") is False and result.get("activation") == "next-resident-generation",
                "native registration response differs")
        native = read(result["registration"])
        require(native["registration"] == request and bytes.fromhex(native["custodyHex"]) == raw(routes / "resident-custody-v3.json"),
                "native successor registration bytes differ")
        after = copy.deepcopy(old)
        after.update(pins=str(self.out / "operator-pins.json"), sourceRoute=str(routes), request=str(request_path), registration=result)
        target = self.out / "after-registered-agent-route.json"
        if not target.exists(): write(target, after)
        require(read(target) == after, "retained successor publication changed")
        publish(self.root / "registered-agent-route.json", raw(self.out / "before-registered-agent-route.json"), raw(target))
        if "contract" in c:
            publish(Path(c["contract"]), raw(self.out / "before-contract.json"), raw(self.out / "after-contract.json"))
            publish(self.root / "attachment.json", raw(self.out / "before-attachment.json"), raw(self.out / "after-attachment.json"))
        complete = self.out / "complete.json"
        if not complete.exists():
            write(complete, {"protocol": "mini-application-payer-successor-complete-v1", "app": self.plan["app"],
                "previous": old["registration"]["name"], "successor": c["successorName"],
                "grantChanged": False, "sessionChanged": False, "next": "native START then session/controller enrollment"})
        return complete


if __name__ == "__main__":
    os.umask(0o077)
    require(len(sys.argv) == 2, "usage: application-payer-successor.py INPUT.json")
    print(Repair(sys.argv[1]).run())
