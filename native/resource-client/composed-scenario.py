#!/usr/bin/env python3
"""Composed scenario on one supplied, already-running Mini world.

  composed-scenario.py check SPEC           validate the spec and world inventory; no effects
  composed-scenario.py run SPEC             run, or resume, the scenario's retained ledger
  composed-scenario.py status SPEC          retained ledger and phase report; no native call
  composed-scenario.py settle SPEC STEP absent|confirmed EVIDENCE REASON

The population comes from the world's inventory file (WORLD-IDENTITY.json):
rooms name their owner and members by inventory name or by an inventory
selector, never by position, and no member count is assumed. Members act only
through their forced Mini SSH sessions.

Phases run in order: rooms, churn, documents, apps, connector, residents,
restart. A phase whose adapter is absent from source is reported UNBUILT; one
whose input or prerequisite phase is absent is BLOCKED with the reason. No
phase is faked.

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
SPK = HERE.parent.parent / "scripts" / "spk-platform"
SCRIPTS = HERE.parent.parent / "scripts"
# In-source adapters each phase composes with. Residents and restart have no
# adapter that drives forced-SSH members on a supplied world yet.
ADAPTERS = {"apps": SPK / "same-store-app.py", "connector": SPK / "app-document-provision.py",
            "protected": SCRIPTS / "protected-document-same-store.py",
            "ordinary": SCRIPTS / "docuverse-same-store.py"}
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
            else:
                report[phase] = "ready"
        else:
            report[phase] = "ready" if spec.get(phase, {}).get("argv") else \
                f"unbuilt: no in-source {phase} adapter for forced-SSH members; supply {phase}.argv"
    return report


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
        if self.state_path.exists():
            self.state = read(self.state_path)
            require(self.state["spec"] == spec, "retained scenario spec differs; a changed scenario needs a fresh state directory")
        else:
            self.state = {"type": "mini-composed-scenario-state-v1", "spec": spec, "serial": 0,
                          "rows": [], "phases": {}}
            self.persist()
        (self.root / "evidence").mkdir(mode=0o700, exist_ok=True)
        self.ledger = step_ledger.StepLedger(self.state, self.persist, lock=self.lock)

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
            self.read(self.ledger, f"churn:{key}:rejoined-read", who, f"doc show {rejoined}/notes")
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

            def write(who):
                lane = self.lane(f"documents:{key}:{who}")
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

    def adapter(self, label, argv, reentrant):
        if self.ledger.done(label):
            return
        into = self.attempt(label)

        def action():
            stem = into / "adapter"
            before, start = loadavg(), time.monotonic()
            done = subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True, check=False)
            stem.with_suffix(".out").write_bytes(done.stdout)
            stem.with_suffix(".err").write_bytes(done.stderr)
            good = done.returncode == 0
            self.row({"id": label, "status": "pass" if good else "fail", "rc": done.returncode,
                      "seconds": round(time.monotonic() - start, 3), "loadBefore": before,
                      "loadAfter": loadavg(), "argv": argv, "evidence": str(stem)})
            require(good, f"{label}: adapter failed; see {stem}")
        self.ledger.step(label, action, into, reentrant=reentrant)

    def generic(self, phase):
        for key, value in sorted(self.spec[phase].items()) if phase in ("apps",) else [(None, self.spec[phase])]:
            label = phase if key is None else f"{phase}:{key}"
            if phase in ("apps", "connector"):
                # Both adapters re-enter their own retained ledgers.
                self.adapter(label, [sys.executable, str(ADAPTERS[phase]), value["input"]], reentrant=True)
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
            missing = [r for r in REQUIRES[phase]
                       if r in self.p["phases"] and not str(statuses.get(r, "")).startswith("pass")]
            if str(statuses.get(phase, "")).startswith("pass"):
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
                    else:
                        self.generic(phase)
                except (step_ledger.LedgerFenced, Undecided, ValueError, RuntimeError, KeyError,
                        json.JSONDecodeError) as error:
                    statuses[phase] = "stopped: " + str(error)
                    self.persist()
                    return self.report()
                blocked = [r["id"] for r in self.state["rows"]
                           if r.get("status") == "blocked" and r["id"].startswith(phase + ":")]
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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("words", nargs="+")
    words = parser.parse_args(argv).words
    os.umask(0o077)
    if len(words) < 2:
        parser.error("command and SPEC required")
    spec = read(words[1])
    if words[0] == "check" and len(words) == 2:
        p = plan(spec)
        result = {"type": "mini-composed-scenario-check-v1", "effects": False,
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
        return 0 if all(v.startswith(("pass", "blocked", "unbuilt")) for v in result["phases"].values()) else 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError, step_ledger.LedgerFenced) as error:
        print("composed scenario: " + str(error), file=sys.stderr)
        raise SystemExit(1)
