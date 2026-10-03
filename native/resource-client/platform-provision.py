#!/usr/bin/env python3
"""Provision one fresh private Mini world and arbitrary synthetic SSH members.

The source workroom provisioner owns the single genesis and initial native grain
birth. This glue enrolls independent member keys on that same Store; hooks cannot
bootstrap another one. check launches nothing. Services and prior evidence stay
under a fresh dedicated root; stop/restart signal only pinned owned process groups.
With a declared serviceManager the private operator, its public relay and the member
SSH entrance are root-published SYSTEM units from birth: units renders them from the
plan, check/start refuse any published unit that differs, and no process is owned here.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import pwd
import re
import signal
import shutil
import socket
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
module = importlib.util.spec_from_file_location("joined", HERE / "joined-member-journey.py")
joined = importlib.util.module_from_spec(module)
module.loader.exec_module(joined)
load, save, digest, require = joined.read, joined.save, joined.digest, joined.require


def simple(path, exists=True):
    value = str(Path(path).absolute())
    require(re.fullmatch(r"/[A-Za-z0-9_./-]+", value) and "/../" not in value, "simple absolute path required")
    return Path(value).resolve(strict=exists)


SERVICES = ("operator", "public", "sshd")
DESCRIPTIONS = {"operator": "Mini supplied Store operator", "public": "Mini supplied Store public ingress",
                "sshd": "Mini supplied Store member SSH entrance"}


def unit(argv, user, description, cwd):
    require(re.fullmatch(r"/[A-Za-z0-9_./-]+", cwd), "unit working directory requires a simple absolute path")
    # systemd parses quoted words independently of the shell. Percent is an
    # expansion character even inside quotes; literal arguments escape it.
    words = [json.dumps(str(word).replace("%", "%%")) for word in argv]
    return ("[Unit]\nDescription=" + description + "\n[Service]\nType=exec\nUser=" + user
            + "\nUMask=0077\nWorkingDirectory=" + cwd
            + "\nExecStart=" + " ".join(words)
            + "\nKillMode=control-group\nTimeoutStopSec=30\nRestart=no\n")


def service_argv(mini, host, config, public, private):
    """The one definition of the private operator and its public relay."""
    return {"operator": [mini, "serve-operator", "--host", host, "--config", config, "--socket", private],
            "public": [mini, "serve-public-proxy", "--socket", public, "--upstream", private, "--config", config]}


def service_manager(plan):
    """Optional: the world's long-lived services are root-published SYSTEM units from birth."""
    manager = plan.get("serviceManager")
    if manager is None:
        return None
    require(type(manager) is dict and set(manager) == {"type", "systemctl", "unitDirectory", "units"}
            and manager["type"] == "systemd-system", "unknown service manager")
    control = manager["systemctl"]
    require(type(control) is list and 1 <= len(control) <= 4
            and all(type(word) is str and re.fullmatch(r"/[A-Za-z0-9_./-]+|-[a-z]", word) for word in control)
            and control[0].startswith("/") and control[-1].startswith("/") and Path(control[-1]).name == "systemctl",
            "service manager control must be an absolute systemctl invocation")
    units = manager["units"]
    require(type(units) is dict and set(units) == set(SERVICES)
            and all(type(name) is str and re.fullmatch(r"[A-Za-z0-9_.@-]+\.service", name) and len(name.encode()) <= 255
                    for name in units.values())
            and len(set(units.values())) == len(SERVICES), "service manager requires distinct operator, public and sshd units")
    directory = manager["unitDirectory"]
    require(type(directory) is str and directory.startswith("/") and Path(directory).is_dir()
            and simple(directory) == Path(directory), "unit directory must be a canonical existing directory")
    return manager


def rendered_units(plan, manifest):
    """Unit text is a function of the plan alone, so root can publish it before genesis."""
    manager = service_manager(plan)
    require(manager is not None, "plan declares no service manager")
    require(os.getuid() != 0, "units name the unprivileged Store operator; render them as that user")
    root, node = root_layout(plan)
    commands = service_argv(manifest["mini"], manifest["host"], node / "deployment/pinned-config.json",
                            root / "sock/public.sock", root / "sock/operator.sock")
    commands["sshd"] = [simple(plan.get("sshd", "/usr/sbin/sshd")), "-D", "-e", "-f", root / "ssh/sshd_config"]
    user = pwd.getpwuid(os.getuid()).pw_name
    return {manager["units"][name]: unit(commands[name], user, DESCRIPTIONS[name], str(root)) for name in SERVICES}


def root_custody(path):
    for entry in (path, *path.parents):
        metadata = entry.stat()
        require(metadata.st_uid == 0 and not metadata.st_mode & 0o022,
                "service unit requires immutable root-owned custody: " + str(entry))


def systemd_show(name):
    reply = subprocess.run(["/usr/bin/systemctl", "show", name,
                            "--property=LoadState,ActiveState,MainPID,FragmentPath,DropInPaths,NeedDaemonReload,InvocationID"],
                           stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=30)
    require(reply.returncode == 0, "service manager cannot describe " + name)
    return dict(line.split("=", 1) for line in reply.stdout.splitlines() if "=" in line)


def published_units(plan, manifest, birth):
    """A unit that differs from this plan is the public-`serve`-behind-a-private-descriptor failure."""
    manager = service_manager(plan)
    for name, text in rendered_units(plan, manifest).items():
        path = Path(manager["unitDirectory"]) / name
        require(path.is_file() and not path.is_symlink(), "service unit is not published: " + name)
        root_custody(path)
        require(path.read_text() == text, "published service unit differs from this plan: " + name)
        shown = systemd_show(name)
        require(shown.get("LoadState") == "loaded" and shown.get("FragmentPath") == str(path)
                and not shown.get("DropInPaths") and shown.get("NeedDaemonReload") == "no",
                "service manager has not loaded exactly the published unit: " + name)
        if birth:
            require(shown.get("ActiveState") == "inactive" and shown.get("MainPID") == "0",
                    "service unit is already running before genesis: " + name)


def observer_allocation(plan):
    observer=plan.get('payObserver')
    if observer is None:
        return None
    fields={'subject','keyId','account','spendCapability','controlCapability','factoryObserveCapability','capability','payControlCapability','enrolCapability'}
    reserved={'5','7','8','9','10','11','12','41','42','51','52','53','54','55','71','72','73','81','82','89','90','91','92','93','94','7003','8001','7007','8008',str(plan.get('parentTask',7901)),str(plan.get('toolTask',7902))}
    require(type(observer) is dict and set(observer)==fields,'invalid pay observer allocation fields')
    values=list(observer.values())
    require(all(type(value) is str and re.fullmatch(r'[1-9][0-9]*',value) and int(value)<2**256 for value in values), 'pay observer allocations must be positive canonical Nat256 strings')
    require(len(set(values))==len(values) and not reserved.intersection(values), 'pay observer allocations collide')
    return observer


def root_layout(plan):
    declared = Path(plan["root"]).absolute()
    root = simple(declared, False)
    require(declared == root, "provisioning root must be canonical")
    prepared = plan.get("preparedEmptyRoot", False)
    require(type(prepared) is bool, "preparedEmptyRoot must be boolean")
    if prepared:
        require(root.is_dir() and not root.is_symlink(), "prepared root must be a real directory")
        metadata = root.stat()
        require(metadata.st_uid == os.getuid() and metadata.st_mode & 0o777 == 0o700,
                "prepared root must be private and owned by the Store operator")
        require(not any(root.iterdir()), "prepared root must be empty")
    else:
        require(not root.exists() and not root.is_symlink(), "fresh provisioning root required")
    require(root.parent.is_dir(), "provisioning root parent must already exist")
    name = plan.get("nodeDirectory", "world")
    require(type(name) is str and re.fullmatch(r"[a-z][a-z0-9-]{0,31}", name)
            and name not in {"logs", "custody", "sock", "members", "ssh", "namespace", "operator-home", "hooks", "paid-entry", "operator-workspace", "pay-observer-workspace"},
            "nodeDirectory must be a distinct simple directory name")
    require(len(os.fsencode(root / name / "session/host.sock")) <= 100, "root is too deep for native Unix sockets")
    return root, root / name


def validate(plan, published=True):
    require(plan["type"] == "mini-platform-provision-v1", "unknown provisioning plan")
    root, _ = root_layout(plan)
    source = simple(plan["sourceRepo"])
    manifest_path = simple(plan["manifest"])
    require(digest(manifest_path) == plan["manifestSha256"], "manifest changed")
    manifest = load(manifest_path)
    for role in ("mini", "host", "store", "verifier"):
        executable = simple(manifest[role])
        require(os.access(executable, os.X_OK) and digest(executable) == manifest["sha256"][role], "candidate binary changed: " + role)
    for path in (source / "scripts/workroom/provision.sh", source / "deploy/shell/mini-shell-ssh", source / "deploy/shell/render-shell-key"):
        require(path.is_file(), "missing source recipe: " + str(path))
    if "sshLauncher" in plan:
        launcher = plan["sshLauncher"]
        require(type(launcher) is dict and set(launcher) in ({"path", "sha256"}, {"path", "sha256", "renderer"}), "invalid SSH launcher pin")
        renderer = launcher.get("renderer", "mini-shell-ssh")
        require(renderer in ("mini-shell-ssh", "mini-shell-ssh-credentials"), "unknown SSH source renderer")
        path = simple(launcher["path"])
        require(Path(launcher["path"]).absolute() == path, "SSH launcher must be canonical")
        require(path.is_file() and os.access(path, os.X_OK)
                and digest(path) == launcher["sha256"] == digest(source / "deploy/shell" / renderer),
                "SSH launcher differs from the pinned source renderer")
        for parent in (path, *path.parents):
            metadata = parent.stat()
            require(metadata.st_uid == 0 and not metadata.st_mode & 0o022,
                    "SSH launcher requires immutable root-owned custody")
    members = plan["members"]
    require(type(members) is list and 2 <= len(members) <= plan.get("maxMembers", 100), "member population outside operator receiving bound")
    names = [row["name"] for row in members]
    require(len(set(names)) == len(names) and all(re.fullmatch(r"[a-z][a-z0-9-]{0,31}", name) for name in names), "member names must be distinct Mini names")
    require(all(type(row.get("funding", 1000)) is int and 0 < row.get("funding", 1000) < 2**53 for row in members), "invalid independent member funding")
    require(all(row.get('entry','sponsored') in ('sponsored','paid') for row in members), 'unknown member entry mode')
    observer=observer_allocation(plan)
    if any(row.get('entry')=='paid' for row in members):
        require(observer is not None, 'paid members require a separate genesis pay observer')
        adapter=plan['paidEntryAdapter'];path=simple(adapter['path'])
        require(path.is_file() and digest(path)==adapter['sha256'],'paid entry adapter changed')
        require(all(type(row.get('weeks',2)) is int and 0 < row.get('weeks',2) < 2**32 for row in members if row.get('entry')=='paid'),'invalid paid membership duration')
        require('payWatcher' in manifest and digest(simple(manifest['payWatcher']))==manifest['sha256']['payWatcher'],'paid candidate watcher missing or changed')
        require('WORKROOM_PAY_OBSERVER' in (source/'scripts/workroom/provision.sh').read_text(),'source recipe lacks genesis pay observer contract')
    port = plan["sshPort"]
    require(type(port) is int and 1024 < port < 65536, "private SSH port must be 1025..65535")
    budget = plan.get("sponsorBalance", 10000000)
    require(type(budget) is int and sum(row.get("funding", 1000) for row in members) + 1000 <= budget < 2**53, "sponsor balance does not cover declared member funding and source fees")
    for key in ("toolBalance", "parentBudget", "toolBudget"):
        require(type(plan.get(key, 1000000)) is int and 100 <= plan.get(key, 1000000) < 2**53, "invalid source allocation: " + key)
    for role in ("parentTask", "toolTask"):
        value = str(plan.get(role, 7901 if role == "parentTask" else 7902))
        require(re.fullmatch(r"[1-9][0-9]*", value) and value not in {"7", "8", "10", "11", "12", "7003", "8001"}, "invalid source task allocation")
    require(str(plan.get("parentTask", 7901)) != str(plan.get("toolTask", 7902)), "parent/tool allocations overlap")
    policy = plan.get("operatorPolicy", {})
    require(type(policy) is dict and set(policy) <= {"grainBirthTariff", "providerServices", "disabledEvaluators"}, "operator policy may not replace lifecycle custody or Store identity")
    require(type(plan.get("timeoutSeconds", 600)) is int and 1 <= plan.get("timeoutSeconds", 600) <= 3600, "invalid native command timeout")
    joined.workload(dict(plan, members={name: {} for name in names}, prefix=plan.get("prefix", "platform")))
    require(re.fullmatch(r"[A-Za-z][A-Za-z0-9-]{0,23}", plan.get("prefix", "platform")), "invalid journey prefix")
    require("WORKROOM_OPERATOR_POLICY" in (source / "scripts/workroom/provision.sh").read_text(), "source recipe lacks pre-genesis operator policy contract")
    if service_manager(plan) is not None:
        rendered_units(plan, manifest)
        if published:
            published_units(plan, manifest, birth=True)
    return root, source, manifest


def retain_hooks(root):
    retained = root / "hooks"
    retained.mkdir(mode=0o700)
    for name in ("platform-provision.py", "joined-member-journey.py", "platform-native-hooks.py"):
        source = HERE / name
        require(source.is_file(), "missing native hook source: " + name)
        shutil.copyfile(source, retained / name)
        (retained / name).chmod(0o700)
    return retained


def journey_hooks(hooks_root, root, managed):
    hooks = {"group-boundary": {"executable": str(hooks_root / "platform-native-hooks.py"), "sha256": digest(hooks_root / "platform-native-hooks.py"),
                                "args": ["--state", str(root / "runtime.json")]}}
    if not managed:
        # This hook signals processes this constructor owns. A service-managed
        # world leaves the adapter missing until its manager supplies a drained one.
        hooks["restart"] = {"executable": str(hooks_root / "platform-provision.py"), "sha256": digest(hooks_root / "platform-provision.py"),
                            "args": ["hook", "--state", str(root / "runtime.json")]}
    return hooks


def allocated_workload(plan, names):
    if "workload" not in plan:
        return {}
    selected = plan["workload"].get("members", list(names))
    return {"workload": dict(plan["workload"], members=[names[name] for name in selected])}


def proc_identity(pid):
    process = Path("/proc") / str(pid)
    # Field22 follows '(comm)' which can contain spaces and parentheses.
    stat = (process / "stat").read_text().rsplit(")", 1)[1].split()
    executable = (process / "exe").stat()
    # sshd changes argv/process title after startup. Kernel start time plus
    # credential and executable identity remain stable for this owned process.
    return {"pid": pid, "startTicks": stat[19], "uid": process.stat().st_uid,
            "executableDevice": executable.st_dev, "executableInode": executable.st_ino}


class World:
    def __init__(self, root, state=None):
        self.root = Path(root)
        self.state = state or {"type": "mini-platform-runtime-v1", "root": str(root), "services": {}}
        self.serial = self.state.get("serial", 0)
        self.children = {}

    def persist(self):
        self.state["serial"] = self.serial
        with tempfile.NamedTemporaryFile(mode="w", prefix=".runtime-", dir=self.root, delete=False) as retained:
            json.dump(self.state, retained, indent=2)
            retained.write("\n"); retained.flush(); os.fsync(retained.fileno())
        os.replace(retained.name, self.root / "runtime.json")
        directory = os.open(self.root, os.O_RDONLY | os.O_DIRECTORY)
        try: os.fsync(directory)
        finally: os.close(directory)

    def run(self, label, argv, env=None):
        argv = [str(value) for value in argv]
        self.serial += 1
        base = self.root / "logs" / f"{self.serial:04d}-{label}"
        save(base.with_suffix(".command.json"), argv)
        process = subprocess.run([str(value) for value in argv], stdin=subprocess.DEVNULL, capture_output=True,
                                 timeout=self.state.get("timeoutSeconds", 600), env=env)
        base.with_suffix(".out").write_bytes(process.stdout)
        base.with_suffix(".err").write_bytes(process.stderr)
        base.with_suffix(".rc").write_text(str(process.returncode) + "\n")
        self.persist()
        require(process.returncode == 0, f"{label}: native command refused; see {base}")
        return process.stdout.decode()

    def managed(self, name):
        manager = self.state.get("serviceManager")
        return manager["units"][name] if manager else None

    def spawn(self, name, argv, ready):
        require(name not in self.state["services"], "service already tracked: " + name)
        managed = self.managed(name)
        if managed:
            # The published unit, not this process, owns the service. Its text was
            # checked against the plan; the manager's main PID is what is retained.
            self.run(name + "-unit-start", [*self.state["serviceManager"]["systemctl"], "start", managed])
            shown = systemd_show(managed)
            require(shown.get("ActiveState") == "active" and shown.get("MainPID", "0") != "0",
                    f"{name} unit did not stay active; see journalctl -u {managed}")
            self.state["services"][name] = dict(proc_identity(int(shown["MainPID"])), argv=[str(value) for value in argv],
                                                manager="systemd-system", unit=managed, invocationId=shown["InvocationID"])
            self.persist()
            deadline = time.monotonic() + 60
            while not ready():
                current = systemd_show(managed)
                require(current.get("ActiveState") == "active" and current.get("MainPID") == shown["MainPID"],
                        f"{name} unit exited; see journalctl -u {managed}")
                require(time.monotonic() < deadline, name + " readiness timeout")
                time.sleep(0.2)
            return
        output = open(self.root / "logs" / (name + ".log"), "ab", buffering=0)
        process = subprocess.Popen([str(value) for value in argv], stdin=subprocess.DEVNULL, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        self.children[name] = process
        self.state["services"][name] = dict(proc_identity(process.pid), argv=[str(value) for value in argv])
        self.persist()
        deadline = time.monotonic() + 60
        while not ready():
            require(process.poll() is None, f"{name} exited; see {self.root}/logs/{name}.log")
            require(time.monotonic() < deadline, name + " readiness timeout")
            time.sleep(0.05)
        output.close()

    def stop(self, names):
        for name in names:
            retained = self.state["services"].get(name)
            if not retained:
                continue
            if "unit" in retained:
                managed = retained["unit"]
                require(retained.get("manager") == "systemd-system" and managed == self.managed(name),
                        "refusing to stop a unit this world does not declare: " + name)
                self.run(name + "-unit-stop", [*self.state["serviceManager"]["systemctl"], "stop", managed])
                shown = systemd_show(managed)
                require(shown.get("ActiveState") in ("inactive", "failed") and shown.get("MainPID") == "0",
                        "service unit did not stop: " + name)
                self.state["services"].pop(name)
                self.persist()
                continue
            pid = retained["pid"]
            try:
                current = proc_identity(pid)
            except FileNotFoundError:
                self.state["services"].pop(name)
                self.persist()
                continue
            require(all(current[key] == retained[key] for key in ("pid", "startTicks", "uid", "executableDevice", "executableInode"))
                    and os.getpgid(pid) == pid, "refusing to signal unowned/reused process: " + name)
            os.killpg(pid, signal.SIGTERM)
            deadline = time.monotonic() + 30
            while Path("/proc", str(pid)).exists():
                try:
                    os.waitpid(pid, os.WNOHANG)
                except ChildProcessError:
                    pass
                if not Path("/proc", str(pid)).exists():
                    break
                stat = Path("/proc", str(pid), "stat").read_text().rsplit(")", 1)[1].split()
                if stat[0] == "Z":
                    break
                require(time.monotonic() < deadline, "owned process did not stop: " + name)
                time.sleep(0.05)
            if name in self.children:
                self.children.pop(name).poll()
            self.state["services"].pop(name)
            self.persist()

    def start_store(self):
        m, config, public, private = (self.state[key] for key in ("manifest", "config", "publicSocket", "privateSocket"))
        for path in (public, private):
            path = Path(path)
            if path.exists():
                require(path.is_socket() and path.stat().st_uid == os.getuid(), "foreign socket path")
                try:
                    probe = socket.socket(socket.AF_UNIX); probe.connect(str(path))
                    raise ValueError("socket is already served: " + str(path))
                except ConnectionRefusedError:
                    path.unlink()
                finally:
                    probe.close()
        commands = service_argv(m["mini"], m["host"], config, public, private)
        self.spawn("operator", commands["operator"], lambda: Path(private).is_socket())
        self.spawn("public", commands["public"], lambda: Path(public).is_socket())

    def shell(self, workspace, home, line, label):
        m = self.state["manifest"]
        return self.run(label, [m["mini"], "shell", "--host", m["host"], "--config", self.state["config"],
                               "--socket", self.state["publicSocket"], "--workspace", workspace, "--home", home, "--line", line])


def start(plan):
    require(os.getuid() != 0, "run as the isolated Store operator, not root")
    root, source, manifest = validate(plan)
    _, node = root_layout(plan)
    # Refuse a used port before creating any Store or output directory.
    probe = socket.socket()
    try:
        probe.bind(("127.0.0.1", plan["sshPort"]))
    finally:
        probe.close()
    if plan.get("preparedEmptyRoot", False):
        # Recheck after the port probe before publishing the first artifact.
        root_layout(plan)
    else:
        root.mkdir(mode=0o700)
    for name in ("logs", "custody", "sock", "members", "ssh", "namespace", "operator-home"):
        (root / name).mkdir(mode=0o700)
    hooks_root = retain_hooks(root)
    save(root / "plan.json", plan)
    world = World(root)
    world.state.update(manifest=manifest, manifestPath=plan["manifest"], manifestSha256=plan["manifestSha256"], timeoutSeconds=plan.get("timeoutSeconds", 600), nodeRoot=str(node))
    manager = service_manager(plan)
    if manager:
        world.state["serviceManager"] = manager
    world.persist()
    world.run("completion-key", [manifest["mini"], "keygen", "--secret", root / "custody/completion.seed", "--public", root / "custody/completion.pub"])
    policy = dict({"grainBirthTariff": {"base": 2, "perBirth": 1}}, **plan.get("operatorPolicy", {}))
    policy.update(completionCustodianKey=(root / "custody/completion.pub").read_bytes().hex(),
                  lifecycleManagement={"managementSubject": 8, "managementKeyId": 8008})
    save(root / "operator-policy.json", policy)
    recipe = source / "scripts/workroom/provision.sh"
    source_pins = {str(path): digest(path) for path in (recipe, source / "deploy/shell/render-shell-key", source / "deploy/shell/mini-shell-ssh", Path(__file__))}
    ssh_launcher = simple(plan["sshLauncher"]["path"]) if "sshLauncher" in plan else source / "deploy/shell/mini-shell-ssh"
    source_pins[str(ssh_launcher)] = digest(ssh_launcher)
    save(root / "source-pins.json", source_pins)
    env = dict(os.environ, MINI=manifest["mini"], STORE_BINARY=manifest["store"], SIGNATURE_BINARY=manifest["verifier"],
               WORKROOM_OPERATOR_POLICY=str(root / "operator-policy.json"), WORKROOM_SPONSOR_BALANCE=str(plan.get("sponsorBalance", 10000000)),
               WORKROOM_TOOL_BALANCE=str(plan.get("toolBalance", 1000000)), WORKROOM_PARENT_BUDGET=str(plan.get("parentBudget", 1000000)),
               WORKROOM_TOOL_BUDGET=str(plan.get("toolBudget", 1000000)), WORKROOM_PARENT_TASK=str(plan.get("parentTask", 7901)),
               WORKROOM_TOOL_TASK=str(plan.get("toolTask", 7902)))
    observer=observer_allocation(plan)
    if observer:
        save(root/'pay-observer-allocation.json',observer)
        env['WORKROOM_PAY_OBSERVER']=str(root/'pay-observer-allocation.json')
    world.run("single-native-world", ["/bin/sh", recipe, manifest["host"], node], env)
    config = node / "deployment/pinned-config.json"
    configured = load(config)
    require(configured["lifecycleManagement"] == policy["lifecycleManagement"] and configured["completionCustodianKey"] == policy["completionCustodianKey"], "lifecycle policy missing from genesis-pinned configuration")
    world.state.update(config=str(config), publicSocket=str(root / "sock/public.sock"), privateSocket=str(root / "sock/operator.sock"))
    world.persist(); world.start_store()
    genesis = load(node / "genesis.json")
    birth = {"type": "minidregg-participant-birth-context-v1", "genesis": genesis,
             "template": {"issuer": str(configured["issuer"]), "ownerBudget": str(configured["ownerBudget"]), "lifetime": str(configured["lifetime"])},
             "sourceCapabilities": ["41"], "funding": [], "feePayer": "7",
             "grants": [{"kind": "object", "target": str(configured["factoryId"]), "capability": "54"},
                        {"kind": "account", "target": "7", "capability": "41"}]}
    save(root / "operator-birth-context.json", birth)
    sponsor = root / "operator-workspace"
    world.run("sponsor-init", [manifest["mini"], "workspace", "--action", "init", "--host", manifest["host"], "--config", config,
                               "--socket", world.state["publicSocket"], "--key", node / "controller.key", "--subject", "7",
                               "--birth-context", root / "operator-birth-context.json", "--namespace-root", root / "namespace", "--dir", sponsor, "--no-prerotation"])
    world.run("sponsor-factory", [manifest["mini"], "workspace", "--action", "import", "--dir", sponsor, "--name", "factory", "--kind", "object",
                                  "--target", str(configured["factoryId"]), "--observe-capability", "54", "--control-capability", "53"])
    paid_members={};paid_state=None
    if any(row.get('entry')=='paid' for row in plan['members']):
        observer_workspace=root/'pay-observer-workspace'
        world.run('pay-observer-init',[manifest['mini'],'workspace','--action','init','--host',manifest['host'],'--config',config,
                  '--socket',world.state['publicSocket'],'--key',node/'pay-observer.key','--subject',observer['subject'],
                  '--dir',observer_workspace,'--no-prerotation'])
        world.run('pay-observer-account',[manifest['mini'],'workspace','--action','import','--dir',observer_workspace,'--name','account',
                  '--kind','account','--target',observer['account'],'--operation-capability',observer['spendCapability'],'--observe-capability',observer['spendCapability']])
        paid_root=root/'paid-entry'
        paid_rows=[row for row in plan['members'] if row.get('entry')=='paid']
        for row in paid_rows:
            (root/'members'/row['name']).mkdir(mode=0o700)
        adapter=hooks_root/'paid-entry-adapter.py'
        adapter.write_bytes(simple(plan['paidEntryAdapter']['path']).read_bytes());adapter.chmod(0o700)
        require(digest(adapter)==plan['paidEntryAdapter']['sha256'],'paid entry adapter changed before retention')
        paid_request=root/'paid-entry-request.json';paid_state=root/'paid-entry-result.json'
        # The adapter's population bound and native timeout are the plan's, not its own defaults.
        save(paid_request,{'type':'mini-paid-entry-provision-v1','manifest':plan['manifest'],'manifestSha256':plan['manifestSha256'],'sourceRepo':str(source),
          'maxMembers':plan.get('maxMembers',100),'timeoutSeconds':plan.get('timeoutSeconds',600),
          'deployment':{'config':str(config),'configSha256':digest(config),'socket':world.state['publicSocket'],'operatorSocket':world.state['privateSocket'],'genesis':str(node/'genesis.json')},
          'operatorWorkspace':str(sponsor),'observerWorkspace':str(observer_workspace),'observer':{'capability':observer['capability'],'enrolCapability':observer['enrolCapability']},
          'factoryControl':'53','evidenceDirectory':str(paid_root),
          'members':[{'name':row['name'],'joinDir':str(root/'members'/row['name']/'join'),'weeks':row.get('weeks',2),'starterCredit':str(row.get('funding',1000))} for row in paid_rows]})
        world.run('native-paid-member-entry',[adapter,'--mode','provision','--request',paid_request,'--result',paid_state])
        received=load(paid_state)
        require(received['type']=='mini-paid-entry-provision-result-v1' and received['status']=='pass' and received['rail']=='synthetic-rpc','native paid entry incomplete')
        paid_members={row['name']:row for row in received['members']}
        require(len(paid_members)==len(paid_rows) and set(paid_members)=={row['name'] for row in paid_rows},'paid member inventory differs')
    save(root / "permit-all.json", {"type": "all", "predicates": []})
    world.run("ssh-host-key", ["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", root / "ssh/host"])
    host_public = (root / "ssh/host.pub").read_text().split()
    known = root / "ssh/known_hosts"
    known.write_text(f"[127.0.0.1]:{plan['sshPort']} {host_public[0]} {host_public[1]}\n")
    inventory, names, authorized = {}, {}, []
    for row in plan["members"]:
        name = row["name"]
        home = root / "members" / name
        if row.get('entry')=='paid':
            received=paid_members[name];subject=str(received['subject']);workspace=simple(received['workspace']);key=simple(received['sshKeyFile'])
            require(workspace==home/'join/workspace' and simple(received['joinDir'])==home/'join','paid entry returned another workspace')
            pin=load(workspace/'workspace.json')
            require(str(pin['subject'])==subject and simple(pin['config'])==config.resolve() and simple(pin['host'])==simple(manifest['host']) and pin['socket']==world.state['publicSocket'],'paid workspace is not bound to the supplied world')
            simple(received['miniKeyFile']);simple(received['nextPublicFile']);simple(str(key)+'.pub')
        else:
            home.mkdir(mode=0o700)
            workspace = home / "workspace"
            world.shell(workspace, home, "keygen mini.key", name + "-keygen")
            enrollment = home / "enrollment"
            world.run(name + "-enroll-plan", [manifest["mini"], "enroll", "--action", "plan", "--sponsor-workspace", sponsor, "--factory-ref", "factory", "--name", name,
                                        "--new-key", home / "keys/mini.key", "--next-public-key", home / "keys/mini.key.next.pub", "--operator-socket", world.state["privateSocket"], "--dir", enrollment])
            for action in ("seal", "submit"):
                world.run(name + "-enroll-" + action, [manifest["mini"], "enroll", "--action", action, "--dir", enrollment])
            admitted = json.loads(world.run(name + "-enroll-lookup", [manifest["mini"], "enroll", "--action", "lookup", "--dir", enrollment]))
            subject = str(admitted["subject"])
            world.run(name + "-provision", [manifest["mini"], "workspace", "--action", "provision", "--dir", sponsor, "--name", name, "--holder", subject,
                                           "--funding", str(row.get("funding", 1000)), "--account-predicate", root / "permit-all.json", "--factory-ref", "factory"])
            (home / "provision").mkdir(mode=0o700)
            (home / "provision/birth-context.json").write_bytes((sponsor / "provisions" / name / "birth-context.json").read_bytes())
            world.shell(workspace, home, "init mini.key " + subject, name + "-init")
            key = root / "ssh" / name
            world.run(name + "-ssh-key", ["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", key])
        require(re.fullmatch(r"0|[1-9][0-9]*", subject) and subject not in inventory, "enrollment returned duplicate/invalid subject")
        authorized.append(world.run(name + "-force-command", [source / "deploy/shell/render-shell-key", ssh_launcher,
                                                             manifest["mini"], manifest["host"], config, world.state["publicSocket"], workspace, home, str(key) + ".pub"]))
        inventory[subject] = {"subject": subject, "workspace": str(workspace), "home": str(home), "budget": row.get("funding", 1000),
                              "ssh": {"identityFile": str(key), "knownHostsFile": str(known), "destination": pwd.getpwuid(os.getuid()).pw_name + "@127.0.0.1", "port": plan["sshPort"]}}
        names[name] = subject
        if row.get('entry')=='paid':
            inventory[subject]['paidEntry']=paid_members[name]
    (root / "ssh/authorized_keys").write_text("".join(authorized))
    ssh_config = root / "ssh/sshd_config"
    ssh_config.write_text(f"""Port {plan['sshPort']}
ListenAddress 127.0.0.1
HostKey {root}/ssh/host
AuthorizedKeysFile {root}/ssh/authorized_keys
PidFile {root}/ssh/sshd.pid
AllowUsers {pwd.getpwuid(os.getuid()).pw_name}
PubkeyAuthentication yes
PasswordAuthentication no
KbdInteractiveAuthentication no
UsePAM no
StrictModes yes
PermitRootLogin no
PermitTTY yes
X11Forwarding no
AllowTcpForwarding no
AllowAgentForwarding no
PermitUserEnvironment no
LogLevel VERBOSE
""")
    sshd = simple(plan.get("sshd", "/usr/sbin/sshd"))
    world.run("sshd-configuration", [sshd, "-t", "-f", ssh_config])
    def ssh_ready():
        try:
            with socket.create_connection(("127.0.0.1", plan["sshPort"]), timeout=0.1): return True
        except OSError:
            return False
    world.spawn("sshd", [sshd, "-D", "-e", "-f", ssh_config], ssh_ready)
    rooms = {key: dict(room, owner=names[room["owner"]], members=[names[name] for name in room["members"]]) for key, room in plan.get("rooms", {}).items()}
    spec = {"type": "mini-joined-member-journey-v1", "manifest": plan["manifest"], "manifestSha256": plan["manifestSha256"], "prefix": plan.get("prefix", "platform"),
            "deployment": {"config": str(config), "configSha256": digest(config), "socket": world.state["publicSocket"], "publicSocket": world.state["publicSocket"], "privateSocket": world.state["privateSocket"]},
            "members": inventory, "maxConcurrency": plan.get("maxConcurrency", 16), "sweeps": plan.get("sweeps", []),
            "hooks": journey_hooks(hooks_root, root, manager is not None)}
    if "timeoutSeconds" in plan:
        # Member operations are native effects too; an earlier client timeout
        # would abandon one whose outcome is still unknown.
        spec["timeoutSeconds"] = plan["timeoutSeconds"]
    if paid_state:
        spec['hooks']['paid-entry']={'executable':str(adapter),'sha256':digest(adapter),'args':['--state',str(paid_state)],
                                    'paidSubjects':[member['subject'] for member in paid_members.values()]}
    spec.update(allocated_workload(plan, names))
    if rooms: spec["rooms"] = rooms
    save(root / "journey.json", spec)
    identity = joined.validate(spec)
    if paid_state:
        require(load(paid_state)['identity']==identity,'paid entry artifact belongs to another supplied Store')
    world.state.update(journey=str(root / "journey.json"), identity=identity, allocationNames=names)
    world.persist()
    save(root / "platform-inputs.json", {"identity": identity, "config": str(config), "genesis": str(node / "genesis.json"), "manifest": plan["manifest"],
         "publicSocket": world.state["publicSocket"], "privateSocket": world.state["privateSocket"], "operatorWorkspace": str(sponsor), "memberInventory": inventory,
         "custody": {"completionSeed": str(root / "custody/completion.seed"), "completionPublic": str(root / "custody/completion.pub"),
                    "owner": {"subject": "7", "keyId": "7007", "keyEpoch": "2", "seed": str(node / "controller.key"), "publicKey": str(node / "controller.pub")},
                    "management": {"subject": "8", "keyId": "8008", "keyEpoch": "2", "seed": str(node / "tool.key"), "publicKey": str(node / "tool.pub")}},
         "authority": {"factory": {"target": str(configured["factoryId"]), "ownerCapability": "54", "managementCapability": "55"},
                       "parent": {"task": str(plan.get("parentTask", 7901)), "ownerCapability": "71", "managementCapability": "73"},
                       "tool": {"task": str(plan.get("toolTask", 7902)), "managementCapability": "81"}}})
    require(all(digest(path) == pin for path, pin in source_pins.items()), "source recipe changed during provisioning")
    for subject, member in inventory.items():
        ssh = member["ssh"]
        actual = json.loads(world.run(subject + "-forced-ssh", ["/usr/bin/ssh", "-F", "/dev/null", "-T", "-o", "BatchMode=yes", "-o", "IdentitiesOnly=yes", "-o", "StrictHostKeyChecking=yes",
                                                            "-o", "ClearAllForwardings=yes", "-o", "UserKnownHostsFile=" + str(known), "-i", ssh["identityFile"], "-p", str(plan["sshPort"]), ssh["destination"], "whoami"]))
        require(all(actual.get(key) == member[key] for key in ("subject", "workspace", "home")) and actual.get("socket") == world.state["publicSocket"], "forced SSH binding differs")
    return root / "journey.json"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("check", "units", "start", "restart", "stop", "hook"))
    parser.add_argument("plan", nargs="?")
    parser.add_argument("--state")
    parser.add_argument("--request")
    parser.add_argument("--result")
    parser.add_argument("--output")
    args = parser.parse_args()
    os.umask(0o077)
    if args.mode in ("check", "units", "start"):
        require(args.plan, "plan required")
        plan = load(args.plan)
        if args.mode == "check":
            root, source, manifest = validate(plan)
            print(json.dumps({"launches": False, "root": str(root), "population": len(plan["members"]), "manifest": plan["manifest"], "oneStore": True,
                              "serviceUnits": sorted(plan["serviceManager"]["units"].values()) if "serviceManager" in plan else None}))
        elif args.mode == "units":
            # Publishes nothing: root installs these exact bytes, then check/start verify them.
            require(args.output, "units requires a fresh --output directory")
            _, _, manifest = validate(plan, published=False)
            output = Path(args.output).absolute()
            output.mkdir(mode=0o700)
            units = rendered_units(plan, manifest)
            for name, text in units.items():
                (output / name).write_text(text)
            print(json.dumps({"launches": False, "unitDirectory": plan["serviceManager"]["unitDirectory"],
                              "units": {name: digest(output / name) for name in units}}))
        else:
            print(start(plan))
        return
    require(args.state, "runtime --state required")
    state = load(simple(args.state)); world = World(state["root"], state)
    require(state["type"] == "mini-platform-runtime-v1", "unknown runtime state")
    if args.mode == "stop":
        world.stop(["sshd", "public", "operator"])
        return
    require("serviceManager" not in state,
            "service-managed world: restart belongs to its manager's drained stop/start, not this owned-process hook")
    request = None
    if args.mode == "hook":
        require(args.request and args.result, "hook request/result required")
        request = load(simple(args.request))
        require(request["role"] == "restart" and request["phase"] == "run" and request["identity"] == state["identity"], "restart request belongs to another Store")
    spec = load(state["journey"])
    require(joined.validate(spec) == state["identity"], "deployment identity changed before restart")
    world.stop(["public", "operator"]); world.start_store()
    # Source signed observation verifies the new owner has opened the same world.
    world.shell(Path(state["root"]) / "operator-workspace", Path(state["root"]) / "operator-home", "read factory", "restart-signed-read")
    require(joined.validate(spec) == state["identity"], "deployment identity changed on restart")
    if request:
        evidence_dir = simple(request["evidenceDirectory"])
        evidence = evidence_dir / "restart-runtime.json"
        require(not evidence.exists(), "restart evidence already exists")
        save(evidence, world.state)
        save(Path(args.result), {"type": "mini-joined-member-hook-result-v1", "identity": state["identity"], "role": "restart", "phase": "run", "status": "pass",
                               "artifacts": [{"path": str(evidence), "sha256": digest(evidence)}]})


if __name__ == "__main__":
    main()
