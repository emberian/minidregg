#!/usr/bin/env python3
"""Compose existing member/service APIs on one deployment; never bootstrap a world.

`check` is read-only and launches no processes. `run` uses existing forced Mini SSH
sessions and explicitly configured owner adapters. It never certifies human use.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def read(path):
    return json.loads(Path(path).read_text())


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def absolute(value):
    path = Path(value)
    require(path.is_absolute(), f"absolute path required: {value}")
    return path.resolve(strict=True)


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def validate(spec):
    require(spec["type"] == "mini-joined-member-journey-v1", "unknown journey type")
    manifest_path = absolute(spec["manifest"])
    manifest = read(manifest_path)
    require(digest(manifest_path) == spec["manifestSha256"], "manifest changed")
    for role in ("mini", "host", "store", "verifier"):
        require(digest(absolute(manifest[role])) == manifest["sha256"][role],
                f"manifest {role} binary changed")
    config_path = absolute(spec["deployment"]["config"])
    config = read(config_path)
    require(digest(config_path) == spec["deployment"]["configSha256"], "configuration changed")
    require(absolute(config["storageBinary"]) == absolute(manifest["store"]), "different Store binary")
    require(absolute(config["signatureBinary"]) == absolute(manifest["verifier"]), "different verifier")
    identity = {
        "manifestSha256": spec["manifestSha256"], "configSha256": digest(config_path),
        "storageRoot": str(absolute(config["storageRoot"])),
        "domain": str(config["domain"]), "genesisSeed": str(config["expectedSeed"]),
        "socket": spec["deployment"]["socket"],
    }
    require(Path(identity["socket"]).is_absolute(), "deployment socket must be absolute")
    identity["id"] = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    require(re.fullmatch(r"[A-Za-z][A-Za-z0-9-]{0,23}", spec["prefix"]) is not None,
            "prefix must be a fresh 1..24 character Mini name")
    require(set(spec["members"]) == {"alice", "bob"}, "provide exactly alice and bob")
    subjects = []
    for name, member in spec["members"].items():
        workspace = absolute(member["workspace"])
        pin = read(workspace / "workspace.json")
        require(str(pin["subject"]) == member["subject"], f"{name} subject differs")
        require(absolute(pin["config"]) == config_path, f"{name} config differs")
        require(absolute(pin["host"]) == absolute(manifest["host"]), f"{name} Host differs")
        require(pin["socket"] == identity["socket"], f"{name} socket differs")
        absolute(member["home"])
        ssh = member["ssh"]
        absolute(ssh["identityFile"])
        absolute(ssh["knownHostsFile"])
        require(re.fullmatch(r"[A-Za-z0-9_.@:-]+", ssh["destination"]) is not None
                and not ssh["destination"].startswith("-"), "invalid SSH destination")
        require(isinstance(ssh["port"], int) and 0 < ssh["port"] < 65536, "invalid SSH port")
        subjects.append(member["subject"])
    require(subjects[0] != subjects[1], "members must be distinct participants")
    for role, hook in spec.get("hooks", {}).items():
        executable = absolute(hook["executable"])
        require(os.access(executable, os.X_OK), f"{role} hook is not executable")
        require(digest(executable) == hook["sha256"], f"{role} hook changed")
        require(all(isinstance(x, str) for x in hook.get("args", [])), "hook args must be strings")
    return identity


class Journey:
    def __init__(self, spec, output):
        self.spec, self.identity = spec, validate(spec)
        self.output = Path(output).absolute()
        self.output.mkdir(mode=0o700, parents=False, exist_ok=False)
        self.rows, self.serial = [], 0
        self.context = {"type": "mini-joined-member-hook-request-v1", "identity": self.identity,
                        "manifest": spec["manifest"], "deployment": spec["deployment"],
                        "members": {k: {f: v[f] for f in ("subject", "workspace", "home")}
                                    for k, v in spec["members"].items()},
                        "room": spec["prefix"], "roomTarget": None}
        save(self.output / "identity.json", self.identity)
        (self.output / "manifest.json").write_bytes(Path(spec["manifest"]).read_bytes())
        # Paths/configuration only; neither member keys nor provider credentials copied.
        save(self.output / "spec.json", spec)

    def record(self, row):
        self.rows.append(row)
        save(self.output / "result.json", {
            "type": "mini-joined-member-journey-result-v1", "identity": self.identity,
            "execution": "automated; not human transcripts", "barComplete": False,
            "automatedComplete": bool(self.rows) and all(r["status"] in ("pass", "pending-human") for r in self.rows),
            "requiredOutstanding": [r["id"] for r in self.rows if r["status"] != "pass"],
            "rows": self.rows, "slowRows": [r["id"] for r in self.rows if r.get("seconds", 0) > 5],
        })

    def execute(self, label, argv, expected=0, refusal=None):
        # Recheck local deployment and executable pins before every operation.
        require(validate(self.spec) == self.identity, "deployment identity changed")
        self.serial += 1
        stem = self.output / f"{self.serial:03d}-{label}"
        save(stem.with_suffix(".command.json"), argv)
        start = time.monotonic()
        try:
            process = subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True,
                                     timeout=self.spec.get("timeoutSeconds", 300), check=False)
            rc, out, err = process.returncode, process.stdout, process.stderr
        except subprocess.TimeoutExpired as exc:
            rc, out, err = 124, exc.stdout or b"", exc.stderr or b""
        seconds = time.monotonic() - start
        stem.with_suffix(".out").write_bytes(out)
        stem.with_suffix(".err").write_bytes(err)
        stem.with_suffix(".rc").write_text(str(rc) + "\n")
        allowed = expected if isinstance(expected, tuple) else (expected,)
        good = rc in allowed and (refusal is None or (rc == 0 and 0 in allowed)
                                   or re.search(refusal, err.decode(errors="replace")))
        self.last_rc = rc
        self.record({"id": label, "status": "pass" if good else "fail", "rc": rc,
                     "expectedRc": expected, "seconds": seconds, "evidence": str(stem)})
        require(good, f"{label}: expected rc {expected} / {refusal}, got {rc}; see {stem}")
        return out.decode()

    def shell(self, who, label, line, expected=0, refusal=None):
        ssh = self.spec["members"][who]["ssh"]
        return self.execute(label, ["/usr/bin/ssh", "-F", "/dev/null", "-T",
            "-o", "BatchMode=yes", "-o", "IdentitiesOnly=yes", "-o", "StrictHostKeyChecking=yes",
            "-o", "ClearAllForwardings=yes", "-o", "ConnectTimeout=15",
            "-o", "UserKnownHostsFile=" + ssh["knownHostsFile"], "-i", ssh["identityFile"],
            "-p", str(ssh["port"]), ssh["destination"], line], expected, refusal)

    def json_shell(self, who, label, line):
        return json.loads(self.shell(who, label, line))

    def proposal_refused(self, who, label, line, operation, reason):
        # Existing client proposals may fail at signed preparation or submission.
        # A successful proposal is never itself recorded as the desired refusal.
        self.shell(who, label + "-prepare", line, (0, 3), reason)
        if self.last_rc == 0:
            self.shell(who, label + "-submit", "submit " + operation, 3, reason)
        self.check(label, self.last_rc == 3, "native refusal at prepare or submit")

    def check(self, label, condition, detail):
        self.record({"id": label, "status": "pass" if condition else "fail", "detail": detail})
        require(condition, label + ": " + detail)

    def hook(self, role, phase="run"):
        label = role + "-" + phase
        hook = self.spec.get("hooks", {}).get(role)
        if not hook:
            self.record({"id": label, "status": "blocked", "detail": f"owner adapter required: {role}"})
            return None
        request, result = self.output / (label + "-request.json"), self.output / (label + "-result.json")
        save(request, dict(self.context, role=role, phase=phase, evidenceDirectory=str(self.output)))
        self.execute(label, [hook["executable"], *hook.get("args", []),
                             "--request", str(request), "--result", str(result)])
        value = read(result)
        require(value["type"] == "mini-joined-member-hook-result-v1", "unknown hook result")
        require(value["identity"] == self.identity, f"{label}: other deployment/Store")
        require(value["role"] == role and value["phase"] == phase, "wrong hook role/phase")
        require(value["status"] == "pass", f"{label}: owner did not report pass")
        require(value.get("artifacts"), f"{label}: no retained evidence")
        for item in value["artifacts"]:
            require(digest(absolute(item["path"])) == item["sha256"], "hook evidence changed")
        if role in ("hermes", "spk"):
            require(value["roomTarget"] == self.context["roomTarget"], "hook operated another room")
            require(value["subjects"] == [self.spec["members"][n]["subject"] for n in ("alice", "bob")],
                    "hook operated other members")
        self.record({"id": label + "-evidence", "status": "pass", "result": str(result)})
        return value

    def run(self):
        p = self.spec["prefix"]
        a, b = self.spec["members"]["alice"], self.spec["members"]["bob"]
        # Paid entry is owner-managed and must preserve the supplied identities.
        paid = self.hook("paid-entry")
        if paid:
            self.check("paid-mainnet", paid.get("rail") == "solana-mainnet" and
                       paid.get("creditedSubjects") == [a["subject"], b["subject"]],
                       "real mainnet receipts and credited member identities required")
        for who, member in (("alice", a), ("bob", b)):
            me = self.json_shell(who, who + "-session", "whoami")
            self.check(who + "-binding", all(me.get(k) == member[k] for k in ("subject", "workspace", "home"))
                       and me.get("socket") == self.identity["socket"], "forced SSH binding matches pinned workspace")
        self.shell("alice", "room-create", f"room new {p} --template workroom")
        refs = self.json_shell("alice", "room-reference", "refs")
        self.context["roomTarget"] = next(r["target"] for r in refs["references"] if r["name"] == p)
        self.shell("alice", "invite-plan", f"room invite {p}-invite {p} {b['subject']} --verbs observe,mutate")
        self.shell("alice", "invite-submit", f"submit {p}-invite")
        self.shell("alice", "invite-publish", f"publish {p}-invite")
        invite = self.json_shell("alice", "invite-export", f"export {p}-invite")
        self.check("invite-recipient", invite.get("recipient") == b["subject"], "invitation addressed to Bob")
        self.shell("bob", "invite-import", f"import {p} " + json.dumps(invite, separators=(",", ":")))
        for who in ("alice", "bob"):
            target = self.json_shell(who, who + "-shared-name", f"room resolve {p}/notes")["target"]
            if who == "alice":
                self.context["documentTarget"] = target
            else:
                self.check("same-shared-document", target == self.context["documentTarget"], "both names open one object")
        marker = p + " joined member text"
        self.shell("bob", "member-append", f"doc append {p}-write {p}/notes " + json.dumps(marker))
        receipt = self.json_shell("bob", "member-submit", f"submit {p}-write")
        for who in ("alice", "bob"):
            text = self.shell(who, who + "-document-read", f"doc show {p}/notes")
            self.check(who + "-document-content", marker in text, "shared text is visible")
        self.shell("bob", "no-local-control-authority", f'law {p}-unauthorized {p}/notes {{"type":"all","predicates":[]}}',
                   1, r"controlCapability")
        self.shell("alice", "shared-transclusion", f"doc transclude {p}/tasks {p}/notes 1 1 snapshot")
        self.shell("alice", "law-inspection", f"inspect law {p}/notes")
        # Both owner adapters get this exact room/object/member/deployment context.
        hermes = self.hook("hermes")
        if hermes:
            self.check("hermes-real-delivery", hermes.get("providerMode") == "real" and hermes.get("delivered") is True,
                       "real resident task and retained paid delivery evidence required")
        spk = self.hook("spk", "before-restart")
        if spk:
            self.check("app-write-share", spk.get("writeRead") is True and spk.get("shared") is True,
                       "both members use same hosted app and retained data")
            self.context["appId"] = spk["appId"]
        restart = self.hook("restart")
        if restart:
            recovered = self.json_shell("bob", "exact-retry", f"lookup {p}-write")
            self.check("same-receipt", recovered.get("transactionId") == receipt.get("transactionId")
                       and receipt.get("transactionId") is not None, "retry returns same admitted transaction")
            text = self.shell("alice", "after-restart-read", f"doc show {p}/notes")
            self.check("one-effect", text.count(marker) == 1, "same retained document after restart; no duplicate write")
            if spk:
                after = self.hook("spk", "after-restart")
                self.check("app-retained", after and after.get("appId") == self.context["appId"]
                           and after.get("retainedData") is True, "same app and stored data survived restart")
        else:
            self.record({"id": "exact-retry-after-restart", "status": "blocked", "detail": "restart adapter missing"})
        # Separate sacrificial object: lockout must not destroy the shared work.
        self.shell("alice", "law-object", f"doc new {p}-law draft --in {p}")
        self.shell("alice", "lock-plan", f'law {p}-lock {p}-law {{"type":"any","predicates":[]}} --allow-unsatisfiable')
        self.shell("alice", "lock-submit", f"submit {p}-lock")
        self.proposal_refused("alice", "owner-bypass-refusal", f'doc append {p}-blocked {p}-law "blocked"',
                              p + "-blocked", r"law-denied")
        self.proposal_refused("alice", "owner-repair-refusal", f'law {p}-repair {p}-law {{"type":"all","predicates":[]}}',
                              p + "-repair", r"law-denied")
        self.shell("alice", "revoke-plan", f"room kick {p}-revoke {p} {b['subject']}")
        self.shell("alice", "revoke-submit", f"submit {p}-revoke")
        self.shell("bob", "revoked-read-refusal", f"doc show {p}/notes", 3, r"no-grant|revoked|grant")
        growth = self.hook("growth")
        if growth:
            self.check("growth-bar", growth.get("acceptedRecords", 0) >= 1000 and
                       0 <= growth.get("writeSeconds", -1) <= 5 and
                       0 <= growth.get("coldReopenSeconds", -1) <= 60,
                       "1000 actual accepted records; write <=5s; cold reopen <=60s on this deployment")
        self.record({"id": "two-human-transcripts", "status": "pending-human",
                     "detail": "automated SSH is not two real friends; retain and review their actual sessions separately"})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("check", "run"))
    parser.add_argument("spec")
    parser.add_argument("--output")
    args = parser.parse_args()
    os.umask(0o077)
    spec = read(args.spec)
    if args.mode == "check":
        print(json.dumps({"identity": validate(spec), "missingAdapters":
                          sorted(set(("paid-entry", "hermes", "spk", "restart", "growth")) - set(spec.get("hooks", {}))),
                          "launches": False, "humanTranscripts": "still required"}, indent=2))
        return 0
    require(args.output is not None, "run requires fresh --output directory")
    journey = Journey(spec, args.output)
    try:
        journey.run()
    except (ValueError, KeyError, OSError, StopIteration, json.JSONDecodeError) as exc:
        journey.record({"id": "stopped", "status": "fail", "detail": str(exc)})
        print(str(exc), file=__import__("sys").stderr)
        return 1
    print(journey.output / "result.json")
    return 2 if any(r["status"] != "pass" for r in journey.rows) else 0


if __name__ == "__main__":
    raise SystemExit(main())
