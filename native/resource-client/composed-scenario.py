#!/usr/bin/env python3
"""Composed scenario on one supplied, already-running Mini world.

  composed-scenario.py check SPEC           validate the spec and world inventory; no effects
  composed-scenario.py run SPEC             run, or resume, the scenario's retained ledger
  composed-scenario.py status SPEC          retained ledger and phase report; no native call
  composed-scenario.py settle SPEC STEP absent|confirmed EVIDENCE REASON
  composed-scenario.py spec WORLD.json STATE N OP [--residents-binding B]
                            [--app-world-inputs PLATFORM SELECTION]
                                            print a spec over the first N inventory members:
                                            one shared room of all N, churn on the last,
                                            documents in the room, every phase declared
  composed-scenario.py gate SPEC RESULT.json  run (or resume), then the DEPLOY verdict:
                                            PASS only when every one of the seven phases
                                            is declared and reports exactly "pass"

The population comes from the world's inventory file (WORLD-IDENTITY.json):
rooms name their owner and members by inventory name or by an inventory
selector, never by position, and no member count is assumed. Room/document
scenario phases use forced Mini SSH sessions. App and resident adapters use
checked native workspaces; outside entrance authorization is qualified separately.

Phases run in order: rooms, churn, documents, apps, connector, residents,
restart. A phase whose adapter is absent from source is reported UNBUILT; one
whose input or prerequisite phase is absent is BLOCKED with the reason. No
phase is faked. `run` exits 0 with blocked or unbuilt phases (a development
report); `gate` does not: for the deploy gate an undeclared, blocked, unbuilt
or partly blocked phase is a FAIL, named.

Restart has two forms. {"binding": B} retains the typed resident's own
crash/restart (residents' binding). {"world": "restart"} restarts the world's
Store through the inventory's own "restart": {"argv": [...]} and then requires
that every member resolves every room's notes to the SAME cell as before, reads
every documents-phase marker exactly once, and sees an owner write admitted
after the restart.

Connector binding: {"input": "/provision-input.json", "journeyInput": "/journey-input.json"}.
An app can instead bind {"worldInputs":{"platformInputs":"/platform-inputs.json",
"selection":"/selection.json"}}; selection participants are WORLD inventory names.
Then connector {"app":"APP-KEY"} derives attach, connector, and journey inputs
through same-store-inputs.py after each retained predecessor result.
The journey input comes from same-store-inputs.py journey after provisioning;
a connector passes only after exact publication and independent byte readback.

Every native effect is one retained ledger step (step_ledger.py). A completed
step never repeats. An interrupted effect is decided on resume by the member's
own exact `lookup` of each attempt it created (or, for client-local steps, the
retained proposal or reference). An undecided outcome fences the scenario
until it is settled from retained evidence. Nothing is re-authored blindly.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("step_ledger", HERE / "step_ledger.py")
step_ledger = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(step_ledger)

PHASES = ("rooms", "churn", "documents", "apps", "connector", "residents", "restart")
REQUIRES = {"rooms": (), "churn": ("rooms",), "documents": ("rooms",), "apps": ("rooms",),
            "connector": ("apps",), "residents": ("rooms",), "restart": ()}
# The deploy gate's definition of "reaches the end" (G-product-journey §1 rows
# 6-13): every phase, each exactly "pass". Changing this set weakens the gate.
GATE_PHASES = PHASES
SPK = HERE.parent.parent / "scripts" / "spk-platform"
SCRIPTS = HERE.parent.parent / "scripts"
# In-source adapters each phase composes with. The typed resident adapter
# consumes native public-relay workspaces and source-owned service custody.
ADAPTERS = {"apps": SPK / "same-store-app.py", "connector": SPK / "app-document-provision.py",
            "protected": SCRIPTS / "protected-document-same-store.py",
            "ordinary": SCRIPTS / "docuverse-same-store.py",
            "connectorJourney": SPK / "app-document-journey.py",
            "worldInputs": SPK / "same-store-inputs.py",
            "resident": HERE.parent.parent / "testing/journeys/same-world-resident.py"}
NAME = re.compile(r"[A-Za-z][A-Za-z0-9-]{0,63}")
KEY = re.compile(r"[A-Za-z0-9][A-Za-z0-9_-]{0,63}")
# Exit codes the forced shell reports (shell.rs): 3 is a definite Host refusal.
REFUSED, UNDECIDED = 3, 4


class Undecided(RuntimeError):
    """An effect's outcome is not known; its step stays pending."""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text())


def save(path, value):
    path = Path(path)
    temporary = path.with_name("." + path.name + ".tmp")
    with open(temporary, "w") as stream:
        stream.write(json.dumps(value, indent=2) + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def loadavg():
    try:
        return Path("/proc/loadavg").read_text().split()[:3]
    except OSError:
        return [str(round(x, 2)) for x in os.getloadavg()]


def inventory(world):
    """Members by inventory name, with the forced-SSH coordinates."""
    require(world.get("type") == "mini-world-identity-v1", "unknown world inventory type")
    ssh = world["ssh"]
    require(isinstance(ssh.get("port"), int) and 0 < ssh["port"] < 65536, "invalid world SSH port")
    members = {}
    for name, row in world["members"].items():
        require(KEY.fullmatch(name) is not None, f"invalid inventory member name {name}")
        require(re.fullmatch(r"0|[1-9][0-9]*", str(row.get("subject", ""))) is not None, f"{name} lacks a subject")
        members[name] = {"subject": row["subject"], "workspace": row["workspace"], "home": row["home"],
                         "key": row["sshKeyFile"], "entry": row.get("entry")}
    require(len({m["subject"] for m in members.values()}) == len(members), "inventory subjects are not distinct")
    return members, ssh


def inventory_sha(world):
    projection = {"members": world["members"], "ssh": world["ssh"], "unitUser": world.get("unitUser")}
    return hashlib.sha256(json.dumps(projection, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def select(selector, members, population):
    """An explicit list of inventory names, "population", or {"entry": E}."""
    if selector == "population":
        return list(population)
    if isinstance(selector, dict):
        require(set(selector) == {"entry"}, "selector supports only entry")
        return [name for name in population if members[name]["entry"] == selector["entry"]]
    require(isinstance(selector, list) and all(isinstance(n, str) for n in selector), "members must be names or a selector")
    require(len(set(selector)) == len(selector), "duplicate member in selection")
    for name in selector:
        require(name in members, f"{name} is not in the world inventory")
    return list(selector)


def plan(spec):
    """Validate the spec against the world inventory; no process, no SSH."""
    require(spec.get("type") == "mini-composed-scenario-v1", "unknown scenario type")
    world_path = Path(spec["world"])
    require(world_path.is_absolute(), "world inventory path must be absolute")
    world = read(world_path)
    if "worldSha256" in spec:
        require(sha(world_path) == spec["worldSha256"], "world inventory changed")
    members, ssh = inventory(world)
    if "inventorySha256" in spec:
        # Pins only who acts and how (members, forced-SSH coordinates), so
        # recording new rooms in the same inventory file does not move it.
        require(inventory_sha(world) == spec["inventorySha256"], "world member inventory changed")
    population = select(spec.get("population", list(members)), members, list(members))
    require(len(population) >= 2, "a composed scenario needs at least two members")
    op = spec["operationPrefix"]
    require(re.fullmatch(r"[a-z][a-z0-9-]{0,23}", op) is not None, "operationPrefix must be 1..24 lowercase characters")
    phases = spec.get("phases", list(PHASES))
    require(all(p in PHASES for p in phases) and len(set(phases)) == len(phases), "unknown or repeated phase")
    rooms = {}
    for key, room in spec.get("rooms", {}).items():
        require(KEY.fullmatch(key) is not None, f"invalid room key {key}")
        require(NAME.fullmatch(room["name"]) is not None, f"invalid room name {room['name']}")
        peers = select(room.get("members", "population"), members, population)
        require(all(p in population for p in peers), f"room {key} selects members outside the population")
        owner = room["owner"]
        require(owner in peers, f"room {key} owner must be one of its members")
        require(len(peers) >= 2, f"room {key} needs another member besides its owner")
        alias = room.get("alias", room["name"])
        require(NAME.fullmatch(alias) is not None, f"invalid alias for room {key}")
        rooms[key] = {"name": room["name"], "owner": owner, "members": peers, "alias": alias,
                      "existing": bool(room.get("existing", False))}
    owned = [(r["owner"], r["name"]) for r in rooms.values()]
    require(len(set(owned)) == len(owned), "one owner has two rooms with one name")
    churn = spec.get("churn", {})
    for key, row in churn.get("rooms", {}).items():
        require(key in rooms, f"churn names unknown room {key}")
        require(row["member"] in rooms[key]["members"] and row["member"] != rooms[key]["owner"],
                f"churn member for {key} must be a non-owner member of that room")
    if "lockout" in churn:
        require(churn["lockout"]["room"] in rooms, "lockout names unknown room")
    docs = spec.get("documents", {})
    for key in docs.get("rooms", []):
        require(key in rooms, f"documents names unknown room {key}")
    for key, binding in spec.get("apps", {}).items():
        require(KEY.fullmatch(key) is not None, "invalid app binding key")
        if "worldInputs" in binding:
            inputs = binding["worldInputs"]
            require(isinstance(inputs, dict) and set(inputs) == {"platformInputs", "selection"},
                    "app worldInputs names platformInputs and selection")
            require(all(isinstance(v, str) and Path(v).is_absolute() for v in inputs.values()),
                    "app worldInputs paths must be absolute")
        else:
            require(isinstance(binding.get("input"), str) and Path(binding["input"]).is_absolute(), "app input must be absolute")
    if "connector" in spec and "app" in spec["connector"]:
        require(set(spec["connector"]) == {"app"}, "derived connector names only its app")
        require(spec["connector"]["app"] in spec.get("apps", {})
                and "worldInputs" in spec["apps"][spec["connector"]["app"]],
                "derived connector requires an app with worldInputs")
    restart = spec.get("restart", {})
    if "world" in restart:
        require(restart == {"world": "restart"}, "world restart is spelled {\"world\": \"restart\"}")
        argv = world.get("restart", {}).get("argv")
        require(isinstance(argv, list) and argv and all(isinstance(a, str) for a in argv)
                and Path(argv[0]).is_absolute(), "world restart needs the inventory's absolute restart argv")
    for phase in ("residents", "restart"):
        value = spec.get(phase, {})
        if "binding" in value:
            require(set(value) == {"binding"} and isinstance(value["binding"], str) and Path(value["binding"]).is_absolute(),
                    "typed " + phase + " names one absolute binding")
    if "binding" in spec.get("residents", {}) and "binding" in spec.get("restart", {}):
        require(spec["residents"]["binding"] == spec["restart"]["binding"], "restart must retain the same resident binding")
    concurrency = spec.get("concurrency", 1)
    require(type(concurrency) is int and 1 <= concurrency <= spec.get("maxConcurrency", 16),
            "concurrency must be 1..maxConcurrency")
    user = world.get("unitUser")
    require(isinstance(user, str) and re.fullmatch(r"[a-z_][a-z0-9_-]{0,31}", user) is not None,
            "world inventory lacks the forced-command account")
    require(re.fullmatch(r"[A-Za-z0-9_.:-]+", str(ssh["host"])) is not None and not str(ssh["host"]).startswith("-"),
            "invalid world SSH host")
    return {"world": world, "worldPath": str(world_path), "members": members, "ssh": ssh,
            "destination": f"{user}@{ssh['host']}",
            "population": population, "op": op, "phases": phases, "rooms": rooms,
            "churn": churn, "documents": docs, "concurrency": concurrency,
            "restartArgv": world.get("restart", {}).get("argv"),
            "timeout": spec.get("timeoutSeconds", 3600)}


def readiness(spec, p):
    """What each phase would do, decided from the spec and source alone."""
    report = {}
    for phase in p["phases"]:
        if phase == "rooms":
            report[phase] = "ready" if p["rooms"] else "blocked: no rooms declared"
        elif phase == "churn":
            report[phase] = "ready" if p["churn"].get("rooms") or "lockout" in p["churn"] else "blocked: no churn rows declared"
        elif phase == "documents":
            parts = []
            if p["documents"].get("rooms"):
                parts.append("rooms ready")
            for kind in ("protected", "ordinary"):
                if kind in p["documents"]:
                    parts.append(f"{kind} adapter " + ("ready" if ADAPTERS[kind].is_file() else "unbuilt"))
                else:
                    parts.append(f"{kind}: blocked: no {kind} supplied-world binding (its adapter drives member CLIs directly, not forced SSH)")
            report[phase] = "; ".join(parts)
        elif phase in ("apps", "connector"):
            if not ADAPTERS[phase].is_file():
                report[phase] = f"unbuilt: {ADAPTERS[phase]} absent"
            elif not spec.get(phase):
                report[phase] = f"blocked: no {phase} input supplied"
            elif phase == "connector" and not spec[phase].get("journeyInput") and "app" not in spec[phase]:
                report[phase] = "blocked: no connector journeyInput supplied; provisioning alone does not capture or publish"
            elif phase == "connector" and not ADAPTERS["connectorJourney"].is_file():
                report[phase] = "unbuilt: connector capture/publication journey absent"
            else:
                report[phase] = "ready"
        elif phase == "restart" and "world" in spec.get(phase, {}):
            report[phase] = "ready" if p["rooms"] else "blocked: world restart verifies rooms; none declared"
        elif "binding" in spec.get(phase, {}):
            report[phase] = "ready" if ADAPTERS["resident"].is_file() else "unbuilt: typed resident adapter absent"
        else:
            report[phase] = "ready" if spec.get(phase, {}).get("argv") else \
                f"blocked: no typed {phase}.binding supplied"
    return report


def input_builder():
    spec = importlib.util.spec_from_file_location("same_store_inputs", ADAPTERS["worldInputs"])
    builder = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(builder)
    return builder


class Scenario:
    def __init__(self, spec, spec_path):
        self.spec, self.p = spec, plan(spec)
        self.root = Path(spec["state"])
        require(self.root.is_absolute(), "state directory must be absolute")
        self.root.mkdir(mode=0o700, parents=False, exist_ok=True)
        self.root = self.root.resolve(strict=True)
        require(self.root.stat().st_mode & 0o077 == 0, "state directory must be private")
        self.lockfile = open(self.root / "scenario.lock", "a")
        fcntl.flock(self.lockfile, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.state_path = self.root / "state.json"
        self.lock = threading.RLock()
        try:
            if self.state_path.exists():
                self.state = read(self.state_path)
                require(self.state["spec"] == spec, "retained scenario spec differs; a changed scenario needs a fresh state directory")
            else:
                self.state = {"type": "mini-composed-scenario-state-v1", "spec": spec, "serial": 0,
                              "rows": [], "phases": {}}
                self.persist()
            (self.root / "evidence").mkdir(mode=0o700, exist_ok=True)
            self.ledger = step_ledger.StepLedger(self.state, self.persist, lock=self.lock)
            for pin in self.state.get("derivedInputPins", {}).values():
                require(sha(pin["path"]) == pin["sha256"], "retained world-derived input bytes changed")
            for pin in self.state.get("worldInputSourcePins", {}).values():
                require(sha(pin["path"]) == pin["sha256"], "world-derived source input bytes changed")
        except Exception:
            self.lockfile.close()
            raise

    def persist(self):
        with self.lock:
            save(self.state_path, self.state)

    def row(self, row):
        with self.lock:
            self.state["rows"].append(row)
            self.persist()

    def evidence(self, label):
        with self.lock:
            self.state["serial"] += 1
            return self.root / "evidence" / f"{self.state['serial']:04d}-{label}"

    def attempt(self, label):
        directory = self.evidence(label.replace(":", "-"))
        directory.mkdir(mode=0o700)
        return directory

    def lane(self, name):
        return step_ledger.StepLedger(self.state, self.persist, key="lane:" + name, lock=self.lock)

    # -- forced SSH ----------------------------------------------------------
    def ssh(self, who, label, line, into):
        member, ssh = self.p["members"][who], self.p["ssh"]
        with self.lock:
            self.state["serial"] += 1
            stem = Path(into) / f"{self.state['serial']:04d}-{label.replace(':', '-')}"
        argv = ["/usr/bin/ssh", "-F", "/dev/null", "-T", "-o", "BatchMode=yes", "-o", "IdentitiesOnly=yes",
                "-o", "StrictHostKeyChecking=yes", "-o", "ClearAllForwardings=yes", "-o", "ConnectTimeout=15",
                "-o", "UserKnownHostsFile=" + ssh["knownHosts"], "-i", member["key"],
                "-p", str(ssh["port"]), self.p["destination"], line]
        save(stem.with_suffix(".command.json"), {"member": who, "line": line, "argv": argv})
        before, start = loadavg(), time.monotonic()
        try:
            done = subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True,
                                  timeout=self.p["timeout"], check=False)
            rc, out, err = done.returncode, done.stdout, done.stderr
        except subprocess.TimeoutExpired as exc:
            rc, out, err = 124, exc.stdout or b"", exc.stderr or b""
        seconds = round(time.monotonic() - start, 3)
        stem.with_suffix(".out").write_bytes(out)
        stem.with_suffix(".err").write_bytes(err)
        timing = {"rc": rc, "seconds": seconds, "loadBefore": before, "loadAfter": loadavg()}
        save(stem.with_suffix(".rc.json"), timing)
        return rc, out.decode(errors="replace"), err.decode(errors="replace"), stem, timing

    def attempts(self, who):
        directory = Path(self.p["members"][who]["workspace"]) / "attempts"
        return sorted(p.name for p in directory.iterdir()) if directory.is_dir() else []

    def proposal_exists(self, who, operation):
        return (Path(self.p["members"][who]["workspace"]) / "proposals" / operation / "proposal.json").is_file()

    # -- step kinds ----------------------------------------------------------
    def _outcome(self, label, who, line, rc, err, stem, timing, expect, refusal):
        allowed = expect if isinstance(expect, tuple) else (expect,)
        good = rc in allowed and (refusal is None or rc == 0 or re.search(refusal, err) is not None)
        self.row({"id": label, "member": who, "line": line, "status": "pass" if good else "fail",
                  "expect": list(allowed), **timing, "evidence": str(stem)})
        return good

    def read(self, ledger, label, who, line, expect=0, refusal=None, check=None, fatal=True):
        """A signed or local read: no effect, so entering it again is safe.

        A non-fatal read is a probe: its failure is reported as a failed row
        and the scenario continues."""
        if ledger.done(label):
            return ledger.result(label)
        into = self.attempt(label)

        def action():
            rc, out, err, stem, timing = self.ssh(who, label, line, into)
            good = self._outcome(label, who, line, rc, err, stem, timing, expect, refusal)
            if good and check is not None:
                good, detail = check(out)
                self.row({"id": label + "-check", "status": "pass" if good else "fail", "detail": detail})
            require(good or not fatal, f"{label}: unexpected result; see {stem}")
            return out
        ledger.step(label, action, into, reentrant=True, keep=True)
        return ledger.result(label)

    def local(self, ledger, label, who, line, operation=None, reference=None, expect=0, refusal=None):
        """A client-local step (a proposal or an import): no native effect.

        On resume an interrupted proposal is complete when its retained
        proposal exists, an import when the member's reference exists, and is
        otherwise authored again; it never admitted anything natively.
        """
        if ledger.done(label):
            return ledger.result(label)
        into = self.attempt(label)

        def recover(pending):
            if expect != 0:
                # An expected refusal admits nothing natively; ask again.
                return ("absent", {"expectedRefusal": True})
            if operation is not None and self.proposal_exists(who, operation):
                return ("done", {"proposal": operation}, None)
            if reference is not None:
                rc, out, _, stem, _ = self.ssh(who, label + "-recover-refs", "refs", pending["evidence"][-1])
                if rc == 0 and any(r.get("name") == reference for r in json.loads(out).get("references", [])):
                    return ("done", {"reference": reference, "evidence": str(stem)}, None)
            return ("absent", {"proposal": operation, "reference": reference})

        def action():
            rc, out, err, stem, timing = self.ssh(who, label, line, into)
            require(self._outcome(label, who, line, rc, err, stem, timing, expect, refusal),
                    f"{label}: unexpected result; see {stem}")
            return out
        ledger.step(label, action, into, recover=recover, keep=True)
        return ledger.result(label)

    def effect(self, ledger, label, who, line, expect=0, refusal=None):
        """One native effect through the member's shell.

        Before running, the member's existing attempts are retained with the
        pending step. On resume each attempt created since is decided by the
        member's exact `lookup`: a confirmed receipt completes the step, a
        definite refusal (or no new attempt at all) means nothing was
        admitted, and anything else keeps the step fenced.
        """
        if ledger.done(label):
            return ledger.result(label)
        into = self.attempt(label)

        def recover(pending):
            fresh = [a for a in self.attempts(who) if a not in set(pending.get("before", []))]
            if not fresh:
                return ("absent", {"newAttempts": []})
            decided, receipt = {}, None
            for name in fresh:
                rc, out, err, stem, _ = self.ssh(who, label + "-lookup", "lookup " + name, pending["evidence"][-1])
                decided[name] = {"rc": rc, "evidence": str(stem)}
                if rc == 0:
                    try:
                        value = json.loads(out)
                    except json.JSONDecodeError:
                        return None
                    if value.get("type") != "confirmed":
                        return None
                    receipt = value
                elif rc != REFUSED:
                    return None
            if receipt is not None:
                return ("done", decided, receipt)
            return ("absent", decided)

        def action():
            rc, out, err, stem, timing = self.ssh(who, label, line, into)
            good = self._outcome(label, who, line, rc, err, stem, timing, expect, refusal)
            if not good:
                raise Undecided(f"{label}: rc {rc}, outcome retained at {stem}; resume decides it by exact lookup")
            try:
                return json.loads(out) if out.strip().startswith("{") else out
            except json.JSONDecodeError:
                return out
        ledger.step(label, action, into, recover=recover, keep=True, before=self.attempts(who))
        return ledger.result(label)

    # -- phases --------------------------------------------------------------
    def refs_target(self, out, name):
        matches = [r for r in json.loads(out).get("references", []) if r.get("name") == name]
        return (bool(matches), f"reference {name} " + ("present" if matches else "absent")), matches

    def join(self, ledger, key, room, who, tag, alias=None):
        alias = alias or room["alias"]
        op = f"{self.p['op']}-{key}-{tag}-{who}"
        owner, subject = room["owner"], self.p["members"][who]["subject"]
        self.local(ledger, f"room:{key}:{tag}:{who}:plan", owner,
                   f"room invite {op} {room['name']} {subject} --verbs observe,mutate", operation=op)
        self.effect(ledger, f"room:{key}:{tag}:{who}:submit", owner, "submit " + op)
        self.effect(ledger, f"room:{key}:{tag}:{who}:publish", owner, "publish " + op)
        exported = self.read(ledger, f"room:{key}:{tag}:{who}:export", owner, "export " + op,
                             check=lambda out: (json.loads(out).get("recipient") == subject,
                                                "invitation binds the actual recipient subject"))
        invitation = json.dumps(json.loads(exported), separators=(",", ":"))
        self.local(ledger, f"room:{key}:{tag}:{who}:import", who, f"import {alias} {invitation}",
                   reference=alias)

    def rooms(self):
        for key, room in self.p["rooms"].items():
            owner = room["owner"]
            if not room["existing"]:
                self.effect(self.ledger, f"room:{key}:create", owner, f"room new {room['name']} --template workroom")
            self.read(self.ledger, f"room:{key}:reference", owner, "refs",
                      check=lambda out, n=room["name"]: self.refs_target(out, n)[0])
            for who in room["members"]:
                if who == owner or room["existing"]:
                    continue
                self.join(self.ledger, key, room, who, "invite")
            targets = {}
            for who in room["members"]:
                name = room["name"] if who == owner else room["alias"]
                out = self.read(self.ledger, f"room:{key}:resolve:{who}", who, f"room resolve {name}/notes")
                targets[who] = json.loads(out)["target"]
            same = len(set(targets.values())) == 1
            self.row({"id": f"room:{key}:one-document", "status": "pass" if same else "fail",
                      "detail": "every member opens the same notes cell", "targets": targets})
            require(same, f"room {key}: members resolve different notes cells")

    def churn(self):
        for key, row in self.p["churn"].get("rooms", {}).items():
            room = self.p["rooms"][key]
            owner, who = room["owner"], row["member"]
            op = f"{self.p['op']}-{key}"
            subject = self.p["members"][who]["subject"]
            self.local(self.ledger, f"churn:{key}:no-control", who,
                       f'law {op}-unauth {room["alias"]}/notes {{"type":"all","predicates":[]}}',
                       operation=f"{op}-unauth", expect=1, refusal=r"controlCapability")
            self.local(self.ledger, f"churn:{key}:kick-plan", owner,
                       f"room kick {op}-kick {room['name']} {subject}", operation=f"{op}-kick")
            self.effect(self.ledger, f"churn:{key}:kick-submit", owner, f"submit {op}-kick")
            self.read(self.ledger, f"churn:{key}:revoked-read", who, f"doc show {room['alias']}/notes",
                      expect=REFUSED, refusal=r"no-grant|revoked|grant")
            self.read(self.ledger, f"churn:{key}:owner-progress", owner, f"doc show {room['name']}/notes")
            # The kicked member's old reference still names the revoked grant;
            # the new invitation is imported beside it, never over it.
            rejoined = room["alias"][:58] + "-again"
            self.join(self.ledger, key, room, who, "rejoin", alias=rejoined)
            # Probe, not a gate: the sealed 2a075e68 client resolves a shared
            # name through the member's first reference to the room (the
            # revoked one), fixed on main by the shared-names authority change.
            self.read(self.ledger, f"churn:{key}:rejoined-read", who, f"doc show {rejoined}/notes", fatal=False)
            self.read(self.ledger, f"churn:{key}:old-reference-still-revoked", who,
                      f"doc show {room['alias']}/notes", expect=REFUSED, refusal=r"no-grant|revoked|grant",
                      fatal=False)
        lockout = self.p["churn"].get("lockout")
        if lockout:
            room = self.p["rooms"][lockout["room"]]
            owner, doc = room["owner"], f"{self.p['op']}-law"
            self.effect(self.ledger, "lockout:doc", owner, f"doc new {doc} draft --in {room['name']}")
            self.local(self.ledger, "lockout:lock-plan", owner,
                       f'law {doc}-lock {doc} {{"type":"any","predicates":[]}} --allow-unsatisfiable',
                       operation=f"{doc}-lock")
            self.effect(self.ledger, "lockout:lock-submit", owner, f"submit {doc}-lock")
            for tag, line in (("bypass", f'doc append {doc}-blocked {doc} "blocked"'),
                              ("repair", f'law {doc}-repair {doc} {{"type":"all","predicates":[]}}')):
                operation = f"{doc}-{tag}" if tag == "repair" else f"{doc}-blocked"
                prepared = self.local(self.ledger, f"lockout:{tag}-prepare", owner, line, operation=operation,
                                      expect=(0, REFUSED), refusal=r"law-denied")
                if self.proposal_exists(owner, operation):
                    self.effect(self.ledger, f"lockout:{tag}-submit", owner, "submit " + operation,
                                expect=REFUSED, refusal=r"law-denied")
                elif prepared is not None:
                    self.row({"id": f"lockout:{tag}-refused-at-prepare", "status": "pass"})

    def alias(self, key, who):
        """The name this member reads the room by now: its rejoined reference
        after churn, else the room's alias (the owner uses the room name)."""
        room = self.p["rooms"][key]
        if who == room["owner"]:
            return room["name"]
        if self.ledger.done(f"room:{key}:rejoin:{who}:import"):
            return room["alias"][:58] + "-again"
        return room["alias"]

    def documents(self):
        for key in self.p["documents"].get("rooms", []):
            room = self.p["rooms"][key]
            markers = {who: f"{self.p['op']}-{key}-{who} composed member text" for who in room["members"]}

            # Every lane's ledger exists before any thread runs, so persisting
            # the state never races a new lane's creation.
            lanes = {who: self.lane(f"documents:{key}:{who}") for who in room["members"]}

            def write(who):
                lane = lanes[who]
                op = f"{self.p['op']}-{key}-w-{who}"
                name = self.alias(key, who)
                self.local(lane, f"documents:{key}:{who}:append", who,
                           f"doc append {op} {name}/notes {json.dumps(markers[who])}", operation=op)
                return self.effect(lane, f"documents:{key}:{who}:submit", who, "submit " + op)

            with ThreadPoolExecutor(max_workers=min(self.p["concurrency"], len(room["members"]))) as pool:
                results = list(pool.map(lambda who: _capture(write, who), room["members"]))
            failures = [str(r) for r in results if isinstance(r, Exception)]
            self.row({"id": f"documents:{key}:concurrent-writes", "status": "fail" if failures else "pass",
                      "detail": "; ".join(failures) or "every member write confirmed"})
            if failures:
                raise RuntimeError(f"documents {key}: " + "; ".join(failures))
            for who in room["members"]:
                name = self.alias(key, who)
                self.read(self.ledger, f"documents:{key}:read:{who}", who, f"doc show {name}/notes",
                          check=lambda out: (all(out.count(m) == 1 for m in markers.values()),
                                             "each member sees exactly one effect of every writer"))
            owner = room["owner"]
            shown = self.read(self.ledger, f"documents:{key}:source-read", owner, f"doc show {room['name']}/notes")
            line = first_line(shown)
            # A transclusion is cut from a published run (K-TRANSCLUDE); the
            # source's writer publishes line 1, then the host transcludes it.
            self.effect(self.ledger, f"documents:{key}:range", owner, f"doc range {room['name']}/notes 1 1")
            self.effect(self.ledger, f"documents:{key}:transclude", owner,
                        f"doc transclude {room['name']}/tasks {room['name']}/notes 1 1 snapshot")
            self.read(self.ledger, f"documents:{key}:transcluded-read", owner, f"doc show {room['name']}/tasks",
                      check=lambda out: (line in out, "host shows the source's line 1 through the snapshot"))
        for kind in ("protected", "ordinary"):
            binding = self.p["documents"].get(kind)
            if binding is None:
                self.row({"id": f"documents:{kind}", "status": "blocked",
                          "detail": f"no {kind} supplied-world binding; that adapter drives member CLIs directly"})
                continue
            self.adapter(f"documents:{kind}", [sys.executable, str(ADAPTERS[kind]),
                                                "--binding", binding["binding"], "--output", binding["output"]],
                         reentrant=False)

    def world_restart(self):
        """Restart the world's Store; every member's view must survive it."""
        before = {}
        for key, room in self.p["rooms"].items():
            for who in room["members"]:
                label = f"room:{key}:resolve:{who}"
                if self.ledger.done(label):
                    before[(key, who)] = json.loads(self.ledger.result(label))["target"]
        require(before, "world restart needs the rooms phase's resolved targets")
        self.adapter("restart:world", list(self.p["restartArgv"]), reentrant=False)
        for (key, who), target in sorted(before.items()):
            room = self.p["rooms"][key]
            name = self.alias(key, who)
            self.read(self.ledger, f"restart:{key}:resolve:{who}", who, f"room resolve {name}/notes",
                      check=lambda out, t=target: (json.loads(out)["target"] == t,
                                                   "the same notes cell as before the restart"))
        for key in self.p["documents"].get("rooms", []):
            room = self.p["rooms"][key]
            markers = [f"{self.p['op']}-{key}-{who} composed member text" for who in room["members"]
                       if self.lane(f"documents:{key}:{who}").done(f"documents:{key}:{who}:submit")]
            for who in room["members"]:
                self.read(self.ledger, f"restart:{key}:read:{who}", who, f"doc show {self.alias(key, who)}/notes",
                          check=lambda out, ms=markers: (all(out.count(m) == 1 for m in ms),
                                                         f"each of {len(ms)} pre-restart writes exactly once"))
        for key, room in self.p["rooms"].items():
            owner, op = room["owner"], f"{self.p['op']}-{key}-after-restart"
            marker = f"{op} owner text after restart"
            self.local(self.ledger, f"restart:{key}:append", owner,
                       f"doc append {op} {room['name']}/notes {json.dumps(marker)}", operation=op)
            self.effect(self.ledger, f"restart:{key}:submit", owner, "submit " + op)
            for who in room["members"]:
                self.read(self.ledger, f"restart:{key}:after:{who}", who, f"doc show {self.alias(key, who)}/notes",
                          check=lambda out, m=marker: (out.count(m) == 1, "the post-restart write, once"))

    def adapter(self, label, argv, reentrant, check=None):
        if self.ledger.done(label):
            return
        into = self.attempt(label)

        def action():
            stem = into / "adapter"
            before, start = loadavg(), time.monotonic()
            done = subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True, check=False)
            stem.with_suffix(".out").write_bytes(done.stdout)
            stem.with_suffix(".err").write_bytes(done.stderr)
            good, detail = done.returncode == 0, ""
            if good and check is not None:
                try:
                    check(done.stdout)
                except (ValueError, RuntimeError, KeyError, OSError) as error:
                    good, detail = False, str(error)
            self.row({"id": label, "status": "pass" if good else "fail", "rc": done.returncode,
                      "seconds": round(time.monotonic() - start, 3), "loadBefore": before,
                      "loadAfter": loadavg(), "argv": argv, "evidence": str(stem), "detail": detail})
            require(good, f"{label}: adapter failed: {detail}; see {stem}")
        self.ledger.step(label, action, into, reentrant=reentrant)

    def derived_input(self, command, app, dependency=None):
        """Compose the existing constructor input builder; retain exact files once."""
        binding = self.spec["apps"][app]["worldInputs"]
        sources = {key: {"path": path, "sha256": sha(path)} for key, path in binding.items()}
        # Recording rooms may edit WORLD-IDENTITY; identities and SSH entrance
        # are pinned separately. Every generation matches its constructor rows.
        source_pins = self.state.setdefault("worldInputSourcePins", {})
        for key, pin in sources.items():
            name = app + ":" + key
            require(name not in source_pins or source_pins[name] == pin, "world input source changed: " + name)
            source_pins[name] = pin
        projection = inventory_sha(read(self.p["worldPath"]))
        prior = self.state.setdefault("worldInputInventorySha256", projection)
        require(prior == projection, "world input participant inventory changed")
        self.persist()
        inputs = self.root / "inputs"
        inputs.mkdir(mode=0o700, exist_ok=True)
        path = inputs / (app + "-" + command + ".json")
        pins = self.state.setdefault("derivedInputPins", {})
        key = app + ":" + command
        if key in pins:
            require(pins[key] == {"path": str(path), "sha256": sha(path)}, "derived input bytes changed")
            return str(path)
        # Module and native builder own source-pin, signing-key and authority
        # validation. key-status is read-only; this method submits no effect.
        builder = input_builder()
        world = builder.World(binding["platformInputs"], binding["selection"], self.p["worldPath"])
        if command == "attach":
            value = builder.attach(world)
        elif command == "connector":
            value = builder.connector(world, dependency)
        elif command == "journey":
            value = builder.journey(world, dependency)
        else:
            raise ValueError("unsupported derived input command")
        if path.exists():
            require(read(path) == value, "unrecorded derived input differs; retain original source operation")
        else:
            save(path, value)
        pins[key] = {"path": str(path), "sha256": sha(path)}
        self.persist()
        return str(path)

    def connector_saved(self, output):
        """Require the source journey's publication and independent byte readback.

        Its rc=0 can also report a retained uncertain outcome. Such an outcome
        fences this phase and is re-entered through the same retained operation.
        """
        result = json.loads(output)
        binding = read(self.state["connectorJourneyInputPin"]["path"])
        require(result.get("protocol") == "mini-app-document-journey-result-v1"
                and result.get("status") == "saved",
                "connector capture/publication is not saved; retain the operation and resume exact recovery")
        require(result.get("operation") == binding["operation"], "connector journey returned another operation")
        require(re.fullmatch(r"[0-9a-f]{64}", str(result.get("callSha256", ""))) is not None,
                "connector saved result lacks the exact publication call digest")
        receipt = result.get("receipt", {})
        require(re.fullmatch(r"[0-9a-f]{64}", str(receipt.get("bodySha256", ""))) is not None
                and re.fullmatch(r"0|[1-9][0-9]*", str(receipt.get("bodyBytes", ""))) is not None,
                "connector saved result lacks independently verified export bytes")
        result_path = self.root / "connector-result.json"
        if result_path.exists():
            prior = read(result_path)
            require(all(prior.get(k) == result.get(k) for k in ("protocol", "status", "operation", "target", "receipt", "callSha256")),
                    "connector retained saved operation changed")
        else:
            save(result_path, result)
        self.state["connectorResultPin"] = {"path": str(result_path), "sha256": sha(result_path)}
        self.persist()

    def typed_resident(self, phase, binding):
        require("connectorResultPin" in self.state, "typed resident requires retained actual connector capture/readback result")
        captured = self.state["connectorResultPin"]
        require(sha(captured["path"]) == captured["sha256"], "connector result changed before resident consumption")
        pin = {"path": binding, "sha256": sha(binding)}
        pins = self.state.setdefault("derivedInputPins", {})
        key = "resident:binding"
        require(key not in pins or pins[key] == pin, "resident/restart binding changed")
        pins[key] = pin
        self.persist()
        through = "verify" if phase == "residents" else "retain"
        output = self.root / (phase + "-result.json")
        def checked(raw):
            result = json.loads(raw)
            require(result.get("protocol") == "mini-same-world-resident-result-v1" and result.get("passed") is True
                    and result.get("through") == through and result.get("bindingSha256") == pin["sha256"],
                    "typed resident did not return this binding's native acceptance result")
        self.adapter(phase, [sys.executable, str(ADAPTERS["resident"]), "run", "--binding", binding,
            "--world", self.p["worldPath"], "--connector-result", captured["path"], "--through", through,
            "--output", str(output)], reentrant=True, check=checked)

    def generic(self, phase):
        if phase == "connector":
            value = self.spec[phase]
            if "app" in value:
                app = value["app"]
                app_input = read(self.derived_input("attach", app))
                attached = str(Path(app_input["root"]) / "attachment-result.json")
                provision_input = self.derived_input("connector", app, attached)
            else:
                provision_input = value["input"]
            self.adapter("connector", [sys.executable, str(ADAPTERS[phase]), provision_input], reentrant=True)
            if "app" in value:
                provisioned = str(Path(read(provision_input)["root"]) / "result.json")
                journey_input = self.derived_input("journey", app, provisioned)
            else:
                journey_input = value["journeyInput"]
            pin = {"path": journey_input, "sha256": sha(journey_input)}
            retained = self.state.setdefault("connectorJourneyInputPin", pin)
            require(retained == pin, "connector journey input changed; retain the original operation for exact recovery")
            self.persist()
            self.adapter("connector:journey", [sys.executable, str(ADAPTERS["connectorJourney"]), journey_input],
                         reentrant=True, check=self.connector_saved)
            return
        for key, value in sorted(self.spec[phase].items()) if phase == "apps" else [(None, self.spec[phase])]:
            label = phase if key is None else f"{phase}:{key}"
            if phase == "apps":
                path = self.derived_input("attach", key) if "worldInputs" in value else value["input"]
                self.adapter(label, [sys.executable, str(ADAPTERS[phase]), path], reentrant=True)
            elif "binding" in value:
                self.typed_resident(phase, value["binding"])
            else:
                self.adapter(label, list(value["argv"]), reentrant=False)

    def close(self):
        self.lockfile.close()

    def run(self):
        try:
            return self._run()
        finally:
            self.close()

    def _run(self):
        ready = readiness(self.spec, self.p)
        statuses = self.state["phases"]
        for phase in self.p["phases"]:
            required = REQUIRES[phase]
            if "binding" in self.spec.get(phase, {}):
                required = (*required, "connector" if phase == "residents" else "residents")
            if phase == "restart" and "world" in self.spec.get(phase, {}):
                required = (*required, "rooms", *(("documents",) if self.p["documents"].get("rooms") else ()))
            missing = [r for r in required
                       if r in self.p["phases"] and not str(statuses.get(r, "")).startswith("pass")]
            if str(statuses.get(phase, "")).startswith(("pass", "fail (probes)")) and (
                    phase != "connector" or self.ledger.done("connector:journey")):
                continue
            if missing:
                statuses[phase] = f"blocked: prerequisite {', '.join(missing)} has not passed"
            elif phase == "documents" and not self.p["documents"].get("rooms") and not any(
                    k in self.p["documents"] for k in ("protected", "ordinary")):
                statuses[phase] = "blocked: no document rooms or supplied-world bindings declared"
            elif ready[phase].startswith(("blocked", "unbuilt")) and phase != "documents":
                statuses[phase] = ready[phase]
            else:
                statuses[phase] = "running"
                self.persist()
                try:
                    if phase in ("rooms", "churn", "documents"):
                        getattr(self, phase)()
                    elif phase == "restart" and "world" in self.spec.get(phase, {}):
                        self.world_restart()
                    else:
                        self.generic(phase)
                except (step_ledger.LedgerFenced, Undecided, ValueError, RuntimeError, KeyError, OSError,
                        json.JSONDecodeError) as error:
                    statuses[phase] = "stopped: " + str(error)
                    for later in self.p["phases"][self.p["phases"].index(phase) + 1:]:
                        if not str(statuses.get(later, "")).startswith(("pass", "fail (probes)")):
                            statuses[later] = f"not reached: stopped at {phase}; would be {ready[later]}"
                    self.persist()
                    return self.report()
                mine = [r for r in self.state["rows"] if r["id"].startswith(phase + ":")
                        or (phase == "churn" and (r["id"].startswith("lockout:") or ":rejoin:" in r["id"]))]
                latest = {r["id"]: r.get("status") for r in mine}  # a retried row's last outcome
                blocked = [i for i, status in latest.items() if status == "blocked"]
                failed = sorted(i for i, status in latest.items() if status == "fail")
                if failed:
                    statuses[phase] = "fail (probes): " + ", ".join(failed)
                else:
                    statuses[phase] = "pass" + (f"; blocked rows: {', '.join(blocked)}" if blocked else "")
            self.persist()
        return self.report()

    def report(self):
        rows = self.state["rows"]
        return {"type": "mini-composed-scenario-result-v1", "state": str(self.root),
                "phases": self.state["phases"], "pending": self.ledger.pending(),
                "lanesPending": {k: v["pending"] for k, v in self.state.items()
                                 if k.startswith("lane:") and v.get("pending")},
                "failed": [r["id"] for r in rows if r.get("status") == "fail"],
                "slow": [{"id": r["id"], "seconds": r["seconds"], "load": r.get("loadBefore")}
                         for r in rows if r.get("seconds", 0) > 5]}


def _capture(function, argument):
    try:
        return function(argument)
    except Exception as error:  # reported per lane; the lane ledger keeps the pending step
        return error


def first_line(shown):
    """Text of line 1 in `doc show` output (`  N  TEXT`)."""
    for line in shown.splitlines():
        match = re.fullmatch(r"\s*1\s{2}(.*)", line)
        if match:
            return match.group(1)
    raise ValueError("source document has no line 1")


def status(spec):
    root = Path(spec["state"])
    state = read(root / "state.json")
    require(state["spec"] == spec, "retained scenario spec differs")
    ledger = state.get("steps", {"done": [], "pending": None, "settled": []})
    return {"type": "mini-composed-scenario-status-v1", "phases": state["phases"], "done": ledger["done"],
            "pending": ledger["pending"], "settled": ledger.get("settled", []),
            "lanesPending": {k: v["pending"] for k, v in state.items() if k.startswith("lane:") and v.get("pending")}}


def generate(world_path, state, count, op, residents=None, app_inputs=None):
    """A spec over the first COUNT inventory members, every phase declared."""
    world = read(world_path)
    members, _ = inventory(world)
    names = list(members)
    require(2 <= count <= len(names), f"N must be 2..{len(names)} (the inventory's member count)")
    population = names[:count]
    spec = {"type": "mini-composed-scenario-v1", "world": str(Path(world_path).resolve()),
            "inventorySha256": inventory_sha(world), "state": str(Path(state).resolve()),
            "operationPrefix": op, "population": population, "phases": list(PHASES),
            "concurrency": min(count, 4),
            "rooms": {"shared": {"name": f"{op}-room", "owner": population[0], "members": "population"}},
            "churn": {"rooms": {"shared": {"member": population[-1]}}},
            "documents": {"rooms": ["shared"]},
            "restart": {"world": "restart"} if residents is None else {"binding": residents}}
    if residents is not None:
        spec["residents"] = {"binding": residents}
    if app_inputs is not None:
        spec["apps"] = {"sheet": {"worldInputs": {"platformInputs": app_inputs[0], "selection": app_inputs[1]}}}
        spec["connector"] = {"app": "sheet"}
    plan(spec)
    return spec


def gate(spec, spec_path, result_path):
    report = Scenario(spec, spec_path).run()
    phases, reasons = report["phases"], []
    for phase in GATE_PHASES:
        status = phases.get(phase)
        if phase not in spec.get("phases", PHASES):
            reasons.append(f"{phase}: not declared in the spec")
        elif status != "pass":
            reasons.append(f"{phase}: {status or 'never ran'}")
    population = plan(spec)["population"]
    result = {"type": "mini-composed-gate-v1", "verdict": "FAIL" if reasons else "PASS",
              "members": len(population), "population": population, "phases": phases,
              "reasons": reasons, "failedRows": report["failed"], "pending": report["pending"],
              "spec": str(Path(spec_path).resolve()), "specSha256": sha(spec_path),
              "world": spec["world"], "worldSha256": sha(spec["world"]), "state": report["state"]}
    save(result_path, result)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("words", nargs="+")
    parser.add_argument("--residents-binding")
    parser.add_argument("--app-world-inputs", nargs=2)
    parsed = parser.parse_args(argv)
    words = parsed.words
    os.umask(0o077)
    if len(words) < 2:
        parser.error("command and SPEC required")
    if words[0] == "spec":
        if len(words) != 5 or not re.fullmatch(r"[0-9]+", words[3]):
            parser.error("spec WORLD.json STATE N OP")
        print(json.dumps(generate(words[1], words[2], int(words[3]), words[4], parsed.residents_binding,
                                  parsed.app_world_inputs), indent=2))
        return 0
    spec = read(words[1])
    if words[0] == "gate":
        if len(words) != 3:
            parser.error("gate SPEC RESULT.json")
        result = gate(spec, words[1], words[2])
        print(json.dumps(result, indent=2))
        return 0 if result["verdict"] == "PASS" else 1
    if words[0] == "check" and len(words) == 2:
        p = plan(spec)
        result = {"type": "mini-composed-scenario-check-v1", "effects": False,
                  "inventorySha256": inventory_sha(p["world"]),
                  "population": p["population"], "rooms": p["rooms"], "phases": readiness(spec, p)}
    elif words[0] == "status" and len(words) == 2:
        result = status(spec)
    elif words[0] == "run" and len(words) == 2:
        result = Scenario(spec, words[1]).run()
    elif words[0] == "settle" and len(words) == 6:
        scenario = Scenario(spec, words[1])
        lane = scenario.ledger
        if scenario.ledger.pending() is None or scenario.ledger.pending()["name"] != words[2]:
            for key, value in scenario.state.items():
                if key.startswith("lane:") and (value.get("pending") or {}).get("name") == words[2]:
                    lane = scenario.lane(key[len("lane:"):])

        def write_record(record):
            path = scenario.evidence("settlement").with_suffix(".json")
            save(path, record)
            return path

        def confirmed(path):
            try:
                value = read(path)
            except (ValueError, OSError):
                return False
            return value.get("type") == "confirmed" and value.get("confirmation") in ("installed", "replayed")
        try:
            result = lane.settle(words[2], words[3], Path(words[4]).resolve(), words[5], scenario.root,
                                 write_record, confirmed=confirmed, sha=sha)
        finally:
            scenario.close()
    else:
        parser.error("unknown command")
    print(json.dumps(result, indent=2))
    if words[0] == "run":
        return 0 if all(v.startswith(("pass", "blocked", "unbuilt")) for v in result["phases"].values()) else 1  # probes count as failure
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError, step_ledger.LedgerFenced) as error:
        print("composed scenario: " + str(error), file=sys.stderr)
        raise SystemExit(1)
