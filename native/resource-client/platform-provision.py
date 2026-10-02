#!/usr/bin/env python3
"""Provision one fresh private Mini world and arbitrary synthetic SSH members.

The source workroom provisioner owns the single genesis and initial native grain
birth. This glue enrolls independent member keys on that same Store; hooks cannot
bootstrap another one. check launches nothing. Services and prior evidence stay
under a fresh dedicated root; stop/restart signal only pinned owned process groups.
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


def validate(plan):
    require(plan["type"] == "mini-platform-provision-v1", "unknown provisioning plan")
    root = simple(plan["root"], False)
    require(not root.exists() and not root.is_symlink(), "fresh provisioning root required")
    require(root.parent.is_dir(), "provisioning root parent must already exist")
    require(len(os.fsencode(root / "world/session/host.sock")) <= 100, "root is too deep for native Unix sockets")
    source = simple(plan["sourceRepo"])
    manifest_path = simple(plan["manifest"])
    require(digest(manifest_path) == plan["manifestSha256"], "manifest changed")
    manifest = load(manifest_path)
    for role in ("mini", "host", "store", "verifier"):
        executable = simple(manifest[role])
        require(os.access(executable, os.X_OK) and digest(executable) == manifest["sha256"][role], "candidate binary changed: " + role)
    for path in (source / "scripts/workroom/provision.sh", source / "deploy/shell/mini-shell-ssh", source / "deploy/shell/render-shell-key"):
        require(path.is_file(), "missing source recipe: " + str(path))
    members = plan["members"]
    require(type(members) is list and 2 <= len(members) <= plan.get("maxMembers", 100), "member population outside operator receiving bound")
    names = [row["name"] for row in members]
    require(len(set(names)) == len(names) and all(re.fullmatch(r"[a-z][a-z0-9-]{0,31}", name) for name in names), "member names must be distinct Mini names")
    require(all(type(row.get("funding", 1000)) is int and 0 < row.get("funding", 1000) < 2**53 for row in members), "invalid independent member funding")
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
    return root, source, manifest


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

    def spawn(self, name, argv, ready):
        require(name not in self.state["services"], "service already tracked: " + name)
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
        self.spawn("operator", [m["mini"], "serve-operator", "--host", m["host"], "--config", config, "--socket", private], lambda: Path(private).is_socket())
        self.spawn("public", [m["mini"], "serve-public-proxy", "--socket", public, "--upstream", private, "--config", config], lambda: Path(public).is_socket())

    def shell(self, workspace, home, line, label):
        m = self.state["manifest"]
        return self.run(label, [m["mini"], "shell", "--host", m["host"], "--config", self.state["config"],
                               "--socket", self.state["publicSocket"], "--workspace", workspace, "--home", home, "--line", line])


def start(plan):
    require(os.getuid() != 0, "run as the isolated Store operator, not root")
    root, source, manifest = validate(plan)
    # Refuse a used port before creating any Store or output directory.
    probe = socket.socket()
    try:
        probe.bind(("127.0.0.1", plan["sshPort"]))
    finally:
        probe.close()
    root.mkdir(mode=0o700)
    for name in ("logs", "custody", "sock", "members", "ssh", "namespace", "operator-home"):
        (root / name).mkdir(mode=0o700)
    save(root / "plan.json", plan)
    world = World(root)
    world.state.update(manifest=manifest, manifestPath=plan["manifest"], manifestSha256=plan["manifestSha256"], timeoutSeconds=plan.get("timeoutSeconds", 600))
    world.persist()
    world.run("completion-key", [manifest["mini"], "keygen", "--secret", root / "custody/completion.seed", "--public", root / "custody/completion.pub"])
    policy = dict({"grainBirthTariff": {"base": 2, "perBirth": 1}}, **plan.get("operatorPolicy", {}))
    policy.update(completionCustodianKey=(root / "custody/completion.pub").read_bytes().hex(),
                  lifecycleManagement={"managementSubject": 8, "managementKeyId": 8008})
    save(root / "operator-policy.json", policy)
    recipe = source / "scripts/workroom/provision.sh"
    source_pins = {str(path): digest(path) for path in (recipe, source / "deploy/shell/render-shell-key", source / "deploy/shell/mini-shell-ssh", Path(__file__))}
    save(root / "source-pins.json", source_pins)
    env = dict(os.environ, MINI=manifest["mini"], STORE_BINARY=manifest["store"], SIGNATURE_BINARY=manifest["verifier"],
               WORKROOM_OPERATOR_POLICY=str(root / "operator-policy.json"), WORKROOM_SPONSOR_BALANCE=str(plan.get("sponsorBalance", 10000000)),
               WORKROOM_TOOL_BALANCE=str(plan.get("toolBalance", 1000000)), WORKROOM_PARENT_BUDGET=str(plan.get("parentBudget", 1000000)),
               WORKROOM_TOOL_BUDGET=str(plan.get("toolBudget", 1000000)), WORKROOM_PARENT_TASK=str(plan.get("parentTask", 7901)),
               WORKROOM_TOOL_TASK=str(plan.get("toolTask", 7902)))
    world.run("single-native-world", ["/bin/sh", recipe, manifest["host"], root / "world"], env)
    config = root / "world/deployment/pinned-config.json"
    configured = load(config)
    require(configured["lifecycleManagement"] == policy["lifecycleManagement"] and configured["completionCustodianKey"] == policy["completionCustodianKey"], "lifecycle policy missing from genesis-pinned configuration")
    world.state.update(config=str(config), publicSocket=str(root / "sock/public.sock"), privateSocket=str(root / "sock/operator.sock"))
    world.persist(); world.start_store()
    genesis = load(root / "world/genesis.json")
    birth = {"type": "minidregg-participant-birth-context-v1", "genesis": genesis,
             "template": {"issuer": str(configured["issuer"]), "ownerBudget": str(configured["ownerBudget"]), "lifetime": str(configured["lifetime"])},
             "sourceCapabilities": ["41"], "funding": [], "feePayer": "7",
             "grants": [{"kind": "object", "target": str(configured["factoryId"]), "capability": "54"},
                        {"kind": "account", "target": "7", "capability": "41"}]}
    save(root / "operator-birth-context.json", birth)
    sponsor = root / "operator-workspace"
    world.run("sponsor-init", [manifest["mini"], "workspace", "--action", "init", "--host", manifest["host"], "--config", config,
                               "--socket", world.state["publicSocket"], "--key", root / "world/controller.key", "--subject", "7",
                               "--birth-context", root / "operator-birth-context.json", "--namespace-root", root / "namespace", "--dir", sponsor, "--no-prerotation"])
    world.run("sponsor-factory", [manifest["mini"], "workspace", "--action", "import", "--dir", sponsor, "--name", "factory", "--kind", "object",
                                  "--target", str(configured["factoryId"]), "--observe-capability", "54", "--control-capability", "53"])
    save(root / "permit-all.json", {"type": "all", "predicates": []})
    world.run("ssh-host-key", ["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", root / "ssh/host"])
    host_public = (root / "ssh/host.pub").read_text().split()
    known = root / "ssh/known_hosts"
    known.write_text(f"[127.0.0.1]:{plan['sshPort']} {host_public[0]} {host_public[1]}\n")
    inventory, names, authorized = {}, {}, []
    for row in plan["members"]:
        name = row["name"]
        home = root / "members" / name
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
        require(re.fullmatch(r"0|[1-9][0-9]*", subject) and subject not in inventory, "enrollment returned duplicate/invalid subject")
        world.run(name + "-provision", [manifest["mini"], "workspace", "--action", "provision", "--dir", sponsor, "--name", name, "--holder", subject,
                                       "--funding", str(row.get("funding", 1000)), "--account-predicate", root / "permit-all.json", "--factory-ref", "factory"])
        (home / "provision").mkdir(mode=0o700)
        (home / "provision/birth-context.json").write_bytes((sponsor / "provisions" / name / "birth-context.json").read_bytes())
        world.shell(workspace, home, "init mini.key " + subject, name + "-init")
        key = root / "ssh" / name
        world.run(name + "-ssh-key", ["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", key])
        authorized.append(world.run(name + "-force-command", [source / "deploy/shell/render-shell-key", source / "deploy/shell/mini-shell-ssh",
                                                             manifest["mini"], manifest["host"], config, world.state["publicSocket"], workspace, home, str(key) + ".pub"]))
        inventory[subject] = {"subject": subject, "workspace": str(workspace), "home": str(home), "budget": row.get("funding", 1000),
                              "ssh": {"identityFile": str(key), "knownHostsFile": str(known), "destination": pwd.getpwuid(os.getuid()).pw_name + "@127.0.0.1", "port": plan["sshPort"]}}
        names[name] = subject
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
            "hooks": {"restart": {"executable": str(Path(__file__).resolve()), "sha256": digest(Path(__file__)), "args": ["hook", "--state", str(root / "runtime.json")]}}}
    spec.update(allocated_workload(plan, names))
    if rooms: spec["rooms"] = rooms
    save(root / "journey.json", spec)
    identity = joined.validate(spec)
    world.state.update(journey=str(root / "journey.json"), identity=identity, allocationNames=names)
    world.persist()
    save(root / "platform-inputs.json", {"identity": identity, "config": str(config), "genesis": str(root / "world/genesis.json"), "manifest": plan["manifest"],
         "publicSocket": world.state["publicSocket"], "privateSocket": world.state["privateSocket"], "operatorWorkspace": str(sponsor), "memberInventory": inventory,
         "custody": {"completionSeed": str(root / "custody/completion.seed"), "completionPublic": str(root / "custody/completion.pub"),
                    "owner": {"subject": "7", "keyId": "7007", "keyEpoch": "2", "seed": str(root / "world/controller.key"), "publicKey": str(root / "world/controller.pub")},
                    "management": {"subject": "8", "keyId": "8008", "keyEpoch": "2", "seed": str(root / "world/tool.key"), "publicKey": str(root / "world/tool.pub")}},
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
    parser.add_argument("mode", choices=("check", "start", "restart", "stop", "hook"))
    parser.add_argument("plan", nargs="?")
    parser.add_argument("--state")
    parser.add_argument("--request")
    parser.add_argument("--result")
    args = parser.parse_args()
    os.umask(0o077)
    if args.mode in ("check", "start"):
        require(args.plan, "plan required")
        plan = load(args.plan)
        if args.mode == "check":
            root, source, manifest = validate(plan)
            print(json.dumps({"launches": False, "root": str(root), "population": len(plan["members"]), "manifest": plan["manifest"], "oneStore": True}))
        else:
            print(start(plan))
        return
    require(args.state, "runtime --state required")
    state = load(simple(args.state)); world = World(state["root"], state)
    require(state["type"] == "mini-platform-runtime-v1", "unknown runtime state")
    if args.mode == "stop":
        world.stop(["sshd", "public", "operator"])
        return
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
