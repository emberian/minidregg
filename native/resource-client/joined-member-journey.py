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
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from copy import deepcopy


def read(path):
    return json.loads(Path(path).read_text())


_digest_cache = {}
_digest_lock = threading.RLock()


def digest(path):
    # Rehash if inode/content metadata changes; repeated operations on a pinned
    # 100-member inventory must not hash the same native binaries thousands of times.
    path = Path(path)
    stat = path.stat()
    key = (str(path.resolve()), stat.st_dev, stat.st_ino, stat.st_size,
           stat.st_mtime_ns, stat.st_ctime_ns)
    with _digest_lock:
        if key not in _digest_cache:
            _digest_cache[key] = hashlib.sha256(path.read_bytes()).hexdigest()
        return _digest_cache[key]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def absolute(value):
    path = Path(value)
    require(path.is_absolute(), f"absolute path required: {value}")
    return path.resolve(strict=True)


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")



# Mirrors room_schema.rs's declared historical roster bound. This is a schema
# boundary, not a platform population limit: disjoint rooms can exceed it.
ROOM_NONFOUNDER_CAPACITY = 499


def workload(spec):
    members = spec["members"]
    require(isinstance(members, dict) and len(members) >= 2,
            "a shared journey requires at least two provisioned members")
    require(all(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,63}", key) for key in members),
            "invalid member inventory key")
    selected = spec.get("workload", {}).get("members", list(members))
    require(len(selected) >= 2 and len(set(selected)) == len(selected)
            and all(key in members for key in selected), "invalid selected member population")
    concurrency = spec.get("workload", {}).get("concurrency", 1)
    require(type(concurrency) is int and 1 <= concurrency <= 64,
            "declared concurrency must be 1..64")
    require(concurrency <= spec.get("maxConcurrency", 16), "concurrency exceeds operator resource limit")
    groups = spec.get("rooms") or {"shared": {"owner": selected[0], "members": selected}}
    rooms = {}
    for key, group in groups.items():
        require(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,63}", key) is not None,
                "invalid room inventory key")
        owner, peers = group["owner"], group["members"]
        require(owner in members and owner in peers and len(peers) == len(set(peers))
                and all(peer in members for peer in peers), "invalid room membership/owner")
        require(len(peers) - 1 <= ROOM_NONFOUNDER_CAPACITY,
                "room historical roster exceeds declared 499 non-founder slots")
        if owner not in selected:
            continue
        peers = [peer for peer in peers if peer in selected]
        if len(peers) < 2:
            continue
        name = group.get("name", spec["prefix"] + "-r" + str(len(rooms)))
        require(re.fullmatch(r"[A-Za-z][A-Za-z0-9-]{0,63}", name) is not None, "invalid room name")
        rooms[key] = dict(group, name=name, owner=owner, members=peers)
    require(rooms, "selected population has no shared room")
    require(set(selected) == {key for room in rooms.values() for key in room["members"]},
            "selected member has no workload group")
    # Aliases can repeat for different owners. They cannot collide within one
    # owner's local workspace. Room cell IDs, not aliases, key hook inventories.
    aliases = [(room["owner"], room["name"]) for room in rooms.values()]
    require(len(set(aliases)) == len(aliases), "one owner has duplicate room aliases")
    for role in ("residents", "apps"):
        for key, instance in spec.get(role, {}).items():
            require(instance["room"] in groups, f"{role}/{key} references missing room")
            require(instance.get("owner", groups[instance["room"]]["owner"]) in members,
                    f"{role}/{key} references missing owner")
    return {"members": selected, "concurrency": concurrency, "rooms": rooms}


def hook_inventory(spec):
    hooks = dict(spec.get("hooks", {}))
    for role in ("residents", "apps"):
        for key, instance in spec.get(role, {}).items():
            if "hook" in instance:
                hooks[role + "/" + key] = instance["hook"]
    return hooks


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
    workload(spec)
    subjects = []
    for name, member in spec["members"].items():
        require(isinstance(member["subject"], str) and re.fullmatch(r"0|[1-9][0-9]*", member["subject"]),
                f"{name} must use an actual natural subject ID")
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
    require(len(set(subjects)) == len(subjects), "members must have distinct actual subject IDs")
    for role, hook in hook_inventory(spec).items():
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
        self.lock = threading.RLock()
        self.plan = workload(spec)
        self.context = {"type": "mini-joined-member-hook-request-v1", "identity": self.identity,
                        "manifest": spec["manifest"], "deployment": spec["deployment"],
                        "members": {k: {f: v[f] for f in ("subject", "workspace", "home")}
                                    for k, v in spec["members"].items() if k in self.plan["members"]},
                        "memberInventory": {v["subject"]: {"key": k, "workspace": v["workspace"],
                                                          "home": v["home"], "budget": v.get("budget")}
                                            for k, v in spec["members"].items() if k in self.plan["members"]},
                        "workload": self.plan, "rooms": {},
                        "residents": spec.get("residents", {}), "apps": spec.get("apps", {}),
                        "room": None, "roomTarget": None}
        save(self.output / "identity.json", self.identity)
        (self.output / "manifest.json").write_bytes(Path(spec["manifest"]).read_bytes())
        # Paths/configuration only; neither member keys nor provider credentials copied.
        save(self.output / "spec.json", spec)

    def record(self, row):
        lock = getattr(self, "lock", _digest_lock)
        with lock:
            self.rows.append(row)
            save(self.output / "result.json", {
                "type": "mini-joined-member-journey-result-v1", "identity": self.identity,
                "execution": "automated fixtures; not human transcripts", "barComplete": False,
                "population": len(getattr(self, "plan", {}).get("members", [])),
                "concurrency": getattr(self, "plan", {}).get("concurrency", 1),
                "automatedComplete": bool(self.rows) and all(r["status"] == "pass" or r.get("environmental") for r in self.rows),
                "requiredOutstanding": [r["id"] for r in self.rows if r["status"] != "pass"],
                "rows": self.rows, "slowRows": [r["id"] for r in self.rows if r.get("seconds", 0) > 5],
            })

    def execute(self, label, argv, expected=0, refusal=None):
        # Recheck local deployment and executable pins before every operation.
        require(validate(self.spec) == self.identity, "deployment identity changed")
        with getattr(self, "lock", _digest_lock):
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

    def hook(self, role, phase="run", instance=None):
        suffix = "" if instance is None else "-" + instance
        scope = self.context.get("roomKey")
        label = role + suffix + "-" + phase + ("-" + scope if scope else "")
        inventory_role = {"hermes": "residents", "spk": "apps"}.get(role)
        configured = self.spec.get(inventory_role, {}).get(instance, {}) if instance else {}
        hook = configured.get("hook", self.spec.get("hooks", {}).get(role))
        if not hook:
            self.record({"id": label, "status": "blocked", "detail": f"owner adapter required: {role}"})
            return None
        request, result = self.output / (label + "-request.json"), self.output / (label + "-result.json")
        subjects = {key: self.spec["members"][key]["subject"] for key in self.context.get("memberKeys", getattr(self, "plan", {"members": []})["members"])}
        save(request, dict(self.context, role=role, phase=phase, instanceId=instance,
                           instance=configured, subjects=subjects, evidenceDirectory=str(self.output)))
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
            require(value["subjects"] == subjects, "hook operated other member IDs")
            if instance:
                require(value.get("instanceId") == instance, "hook operated another resident/app instance")
        self.record({"id": label + "-evidence", "status": "pass", "result": str(result)})
        return value

    def scope(self, key, room):
        self.context.update(roomKey=key, room=room["name"], roomTarget=room["target"],
                            documentTarget=room["documentTarget"], owner=room["owner"],
                            memberKeys=room["members"], memberRoomNames=room["memberNames"])

    def invite(self, owner, member, name, operation, label):
        subject = self.spec["members"][member]["subject"]
        self.shell(owner, label + "-plan", f"room invite {operation} {name} {subject} --verbs observe,mutate")
        self.shell(owner, label + "-submit", "submit " + operation)
        self.shell(owner, label + "-publish", "publish " + operation)
        value = self.json_shell(owner, label + "-export", "export " + operation)
        self.check(label + "-recipient", value.get("recipient") == subject, "invitation binds actual recipient subject")
        imported_name = getattr(self, "import_name", name)
        self.shell(member, label + "-import", "import " + imported_name + " " + json.dumps(value, separators=(",", ":")))

    def member_write(self, room_index, room, member_index, member):
        prefix = self.spec["prefix"] + "-r" + str(room_index) + "-w" + str(member_index)
        marker = prefix + " joined member text"
        alias = room["memberNames"][member]
        self.shell(member, prefix + "-append", f"doc append {prefix} {alias}/notes " + json.dumps(marker))
        receipt = self.json_shell(member, prefix + "-submit", "submit " + prefix)
        return {"member": member, "operation": prefix, "marker": marker, "receipt": receipt}

    def run(self):
        p = self.spec["prefix"]
        paid = self.hook("paid-entry")
        if paid:
            subjects = {key: self.spec["members"][key]["subject"] for key in self.plan["members"]}
            real = paid.get("rail") == "solana-mainnet" and paid.get("creditedSubjects") == subjects
            self.record({"id": "paid-mainnet", "status": "pass" if real else "pending-environment",
                         "environmental": not real, "detail": "actual mainnet receipts and the selected subject IDs required"})
        for who in self.plan["members"]:
            member = self.spec["members"][who]
            me = self.json_shell(who, who + "-session", "whoami")
            self.check(who + "-binding", all(me.get(k) == member[k] for k in ("subject", "workspace", "home"))
                       and me.get("socket") == self.identity["socket"], "forced SSH matches the supplied workspace and Store")
        for index, (key, room) in enumerate(self.plan["rooms"].items()):
            name, owner = room["name"], room["owner"]
            room["memberNames"] = {member: name if member == owner else f"{p}-r{index}" for member in room["members"]}
            self.shell(owner, key + "-create", f"room new {name} --template workroom")
            refs = self.json_shell(owner, key + "-reference", "refs")
            room["target"] = next(r["target"] for r in refs["references"] if r["name"] == name)
            for member_index, member in enumerate(room["members"]):
                if member != owner:
                    self.import_name = room["memberNames"][member]
                    self.invite(owner, member, name, f"{p}-r{index}-i{member_index}", key + "-invite-" + str(member_index))
                target = self.json_shell(member, key + "-resolve-" + str(member_index), f"room resolve {room['memberNames'][member]}/notes")["target"]
                if member == owner:
                    room["documentTarget"] = target
            # Resolve all again after founder to avoid dependence on member order.
            for member_index, member in enumerate(room["members"]):
                target = self.json_shell(member, key + "-shared-" + str(member_index), f"room resolve {room['memberNames'][member]}/notes")["target"]
                self.check(key + "-same-object-" + str(member_index), target == room["documentTarget"], "group opens one actual document cell")
            self.context["rooms"][room["target"]] = dict(room, inventoryKey=key)
            self.scope(key, room)
            # One operation per member: a workspace's signer is never raced with itself.
            writes, errors = [], []
            with ThreadPoolExecutor(max_workers=self.plan["concurrency"]) as workers:
                futures = [workers.submit(self.member_write, index, room, member_index, member)
                           for member_index, member in enumerate(room["members"])]
                for future in as_completed(futures):
                    try:
                        writes.append(future.result())
                    except Exception as exc:
                        errors.append(str(exc))
            self.check(key + "-concurrent-writes", not errors, "; ".join(errors) or "all concurrent member writes completed")
            room["writes"] = writes
            for member_index, member in enumerate(room["members"]):
                text = self.shell(member, key + "-read-" + str(member_index), f"doc show {room['memberNames'][member]}/notes")
                self.check(key + "-all-writes-" + str(member_index), all(text.count(w["marker"]) == 1 for w in writes), "each group member sees one effect for every writer")
            outsiders = [member for member in self.plan["members"] if member not in room["members"]]
            if outsiders:
                # A room reference itself is not authority. Use one native-source
                # observer hook to test the exact object without importing a grant.
                self.context["boundaryActor"] = outsiders[0]
                boundary = self.hook("group-boundary")
                if boundary:
                    self.check(key + "-disjoint-refusal", boundary.get("refusedSubject") == self.spec["members"][outsiders[0]]["subject"] and boundary.get("refused") is True, "uninvited subject refused on the exact document")
                self.context.pop("boundaryActor", None)
            nonowner = next(member for member in room["members"] if member != owner)
            self.shell(nonowner, key + "-no-control", f'law {p}-r{index}-unauthorized {room['memberNames'][nonowner]}/notes {{"type":"all","predicates":[]}}', 1, r"controlCapability")
            self.shell(owner, key + "-transclusion", f"doc transclude {name}/tasks {name}/notes 1 1 snapshot")
            self.shell(owner, key + "-law", f"inspect law {name}/notes")
            residents = [(iid, instance) for iid, instance in self.spec.get("residents", {}).items() if instance["room"] == key]
            for iid, instance in residents or [(None, {})]:
                hermes = self.hook("hermes", instance=iid)
                if hermes:
                    self.check(key + "-hermes-delivered-" + str(iid), hermes.get("delivered") is True, "resident delivered on this room and actual subjects")
                    real = hermes.get("providerMode") == "real"
                    self.record({"id": key + "-hermes-real-" + str(iid), "status": "pass" if real else "pending-environment", "environmental": not real, "detail": "synthetic provider evidence does not complete the real-provider row"})
            room["appResults"] = {}
            apps = [(iid, instance) for iid, instance in self.spec.get("apps", {}).items() if instance["room"] == key]
            for iid, instance in apps or [(None, {})]:
                spk = self.hook("spk", "before-restart", iid)
                if spk:
                    self.check(key + "-app-shared-" + str(iid), spk.get("writeRead") is True and spk.get("shared") is True, "group shares the same hosted app and retained data")
                    room["appResults"][iid] = spk
        self.context.update(room=None, roomTarget=None, documentTarget=None, owner=None,
                            memberKeys=self.plan["members"], memberRoomNames={})
        self.context.pop("roomKey", None)
        restart = self.hook("restart")
        for index, (key, room) in enumerate(self.plan["rooms"].items()):
            self.scope(key, room)
            name, owner = room["name"], room["owner"]
            if restart:
                for wi, write in enumerate(room["writes"]):
                    recovered = self.json_shell(write["member"], key + "-retry-" + str(wi), "lookup " + write["operation"])
                    receipt = write["receipt"]
                    self.check(key + "-exact-receipt-" + str(wi), recovered.get("transactionId") == receipt.get("transactionId") and receipt.get("transactionId") is not None, "restart keeps the admitted transaction identity")
                text = self.shell(owner, key + "-reopened", f"doc show {name}/notes")
                self.check(key + "-one-effect", all(text.count(write["marker"]) == 1 for write in room["writes"]), "cold restart retains every write exactly once")
                for iid, before in room["appResults"].items():
                    self.context["appId"] = before["appId"]
                    after = self.hook("spk", "after-restart", iid)
                    self.check(key + "-app-retained-" + str(iid), after and after.get("appId") == before["appId"] and after.get("retainedData") is True, "same app data survives controlled restart")
            nonowner = next(member for member in room["members"] if member != owner)
            op = f"{p}-r{index}-revoke"
            self.shell(owner, key + "-kick-plan", f"room kick {op} {name} {self.spec['members'][nonowner]['subject']}")
            self.shell(owner, key + "-kick-submit", "submit " + op)
            self.shell(nonowner, key + "-revoked-read", f"doc show {room['memberNames'][nonowner]}/notes", 3, r"no-grant|revoked|grant")
            text = self.shell(owner, key + "-unblocked-owner", f"doc show {name}/notes")
            self.check(key + "-other-progress", all(write["marker"] in text for write in room["writes"]), "revoked actor does not block remaining member")
            self.import_name = room["memberNames"][nonowner]
            self.invite(owner, nonowner, name, f"{p}-r{index}-rejoin", key + "-rejoin")
            text = self.shell(nonowner, key + "-rejoined-read", f"doc show {room['memberNames'][nonowner]}/notes")
            self.check(key + "-rejoin-same-data", all(write["marker"] in text for write in room["writes"]), "rejoining actual subject reuses roster history and document")
        # Source-law owner lockout is isolated from all shared group data.
        key, room = next(iter(self.plan["rooms"].items()))
        self.scope(key, room)
        owner, name = room["owner"], room["name"]
        self.shell(owner, "law-object", f"doc new {p}-law draft --in {name}")
        self.shell(owner, "lock-plan", f'law {p}-lock {p}-law {{"type":"any","predicates":[]}} --allow-unsatisfiable')
        self.shell(owner, "lock-submit", "submit " + p + "-lock")
        self.proposal_refused(owner, "owner-bypass-refusal", f'doc append {p}-blocked {p}-law "blocked"', p + "-blocked", r"law-denied")
        self.proposal_refused(owner, "owner-repair-refusal", f'law {p}-repair {p}-law {{"type":"all","predicates":[]}}', p + "-repair", r"law-denied")
        growth = self.hook("growth")
        if growth:
            self.check("growth-bar", growth.get("acceptedRecords", 0) >= 1000 and 0 <= growth.get("writeSeconds", -1) <= 5 and 0 <= growth.get("coldReopenSeconds", -1) <= 60, "1000 accepted records; write <=5s and cold reopen <=60s on this deployment")
        self.record({"id": "human-transcripts", "status": "pending-human", "environmental": True,
                     "detail": "scripted fixture sessions do not certify human onboarding"})


def selected_spec(spec, row, index):
    value = deepcopy(spec)
    population = row["population"]
    require(type(population) is int and 2 <= population <= len(spec["members"]), "sweep population lacks provisioned members")
    value["workload"] = dict(members=list(spec["members"])[:population], concurrency=row["concurrency"])
    value["prefix"] = spec["prefix"] + "-s" + str(index)
    require(len(value["prefix"]) <= 24, "sweep prefix exceeds Mini name bound")
    # Workloads are selected pairs, not a Cartesian product. With no supplied
    # groups, create overlapping and disjoint groups once population permits.
    if not spec.get("rooms") and population >= 5:
        keys = value["workload"]["members"]
        value["rooms"] = {
            "shared": {"owner": keys[0], "members": keys},
            "overlap": {"owner": keys[1], "members": keys[:3]},
            "disjoint": {"owner": keys[3], "members": keys[3:]},
        }
    workload(value)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("check", "run", "sweep"))
    parser.add_argument("spec")
    parser.add_argument("--output")
    args = parser.parse_args()
    os.umask(0o077)
    spec = read(args.spec)
    if args.mode == "check":
        print(json.dumps({"identity": validate(spec), "missingAdapters":
                          sorted(set(("paid-entry", "hermes", "spk", "restart", "growth")) - set(spec.get("hooks", {}))),
                          "workload": workload(spec), "declaredRosterNonfounderLimit": ROOM_NONFOUNDER_CAPACITY,
                          "launches": False, "humanTranscripts": "still required"}, indent=2))
        return 0
    require(args.output is not None, "run requires fresh --output directory")
    if args.mode == "sweep":
        output = Path(args.output).absolute()
        output.mkdir(mode=0o700, parents=False, exist_ok=False)
        rows = spec.get("sweeps", [])
        require(rows, "sweep requires selected population/concurrency pairs")
        results = []
        for index, row in enumerate(rows):
            selected = selected_spec(spec, row, index)
            journey = Journey(selected, output / str(index))
            try:
                journey.run()
            except (ValueError, KeyError, OSError, StopIteration, json.JSONDecodeError) as exc:
                journey.record({"id": "stopped", "status": "fail", "detail": str(exc)})
            results.append(read(journey.output / "result.json"))
            save(output / "sweep-result.json", {"type": "mini-joined-sweep-result-v1", "identity": journey.identity,
                                             "selectedPairs": rows, "barComplete": False, "results": results})
        return 2 if any(result["requiredOutstanding"] for result in results) else 0
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
