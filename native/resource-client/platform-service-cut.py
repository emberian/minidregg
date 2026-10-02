#!/usr/bin/env python3
"""Prepare a same-Store SYSTEM cut; drain/stop only retained owned processes.

prepare writes a reviewable proposal and never publishes a roster or unit.
stop is an explicit coordinated operation: public ingress stops first, the
native operator confirms an instance-bound drained boundary, then its owned
process group stops. A timeout retains its exact journal for another stop.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import pwd
import re
import shlex
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
loader = importlib.util.spec_from_file_location("provision", HERE / "platform-provision.py")
provision = importlib.util.module_from_spec(loader)
loader.loader.exec_module(provision)
read, digest, require = provision.load, provision.digest, provision.require


def write(path, value):
    data = value if isinstance(value, str) else json.dumps(value, indent=2) + "\n"
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as file:
        file.write(data); file.flush(); os.fsync(file.fileno())
    os.replace(file.name, path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try: os.fsync(fd)
    finally: os.close(fd)


def canonical(value):
    path = Path(value)
    require(path.is_absolute() and path.resolve(strict=True) == path, "noncanonical path")
    return path


def pin(value, expected=None):
    path = canonical(value)
    require(path.is_file(), "pin must be a regular file")
    sha = digest(path)
    require(expected is None or expected == sha, "file differs from selected manifest")
    return {"path": str(path), "sha256": sha}


def protected(value):
    path = canonical(value)
    for parent in (path, *path.parents):
        stat = parent.stat()
        require(stat.st_uid == 0 and not stat.st_mode & 0o022,
                "candidate executable custody requires immutable root-owned ancestors")
    return path


def unit(argv, user, description, cwd):
    # systemd parses quoted words independently of the shell. Percent is an
    # expansion character even inside quotes; literal arguments escape it.
    words = [json.dumps(str(word).replace("%", "%%")) for word in argv]
    return ("[Unit]\nDescription=" + description + "\n[Service]\nType=exec\nUser=" + user
            + "\nUMask=0077\nWorkingDirectory=" + json.dumps(cwd.replace("%", "%%"))
            + "\nExecStart=" + " ".join(words)
            + "\nKillMode=control-group\nTimeoutStopSec=30\nRestart=no\n")


def prepare(request, output):
    require(request["protocol"] == "mini-platform-service-cut-input-v1", "unknown cut input")
    runtime_path = canonical(request["runtime"])
    state = read(runtime_path); root = canonical(state["root"])
    require(state["type"] == "mini-platform-runtime-v1", "unknown runtime")
    journey = read(canonical(state["journey"]))
    provision.joined.validate(journey)
    selected = canonical(request["manifest"])
    protected(selected)
    require(digest(selected) == request["manifestSha256"], "candidate manifest changed")
    manifest = read(selected)
    cli = pin(protected(request["cli"]), manifest["sha256"]["mini"])
    launcher = pin(protected(request["launcher"]))
    # A manifest identifies bytes; deployed paths are observed separately.
    config = pin(state["config"])
    cfg = read(config["path"])
    roles = {"host": state["manifest"]["host"], "store": cfg["storageBinary"],
             "verifier": cfg["signatureBinary"]}
    for name, path in roles.items(): pin(path, manifest["sha256"][name])
    uid = os.stat(root).st_uid
    require(uid != 0, "member deployment must use a non-root service owner")
    user = pwd.getpwuid(uid).pw_name
    require(os.getuid() in (uid, 0), "cut preparer differs from runtime owner")
    cwds = {}
    for name in ("operator", "public"):
        retained = state["services"][name]
        current = provision.proc_identity(retained["pid"])
        require(all(current[key] == retained[key] for key in current), "retained process identity changed")
        cwds[name] = str(canonical(Path("/proc", str(retained["pid"]), "cwd").resolve(strict=True)))
    roster = canonical(request["authorizedKeys"])
    require(roster.is_relative_to(root), "roster outside deployment")
    commands, lines, key_inventory = [], [], set()
    require(len(journey["members"]) <= 4096, "member command inventory exceeds service bound")
    for key, member in journey["members"].items():
        workspace = canonical(member["workspace"]); ws = read(workspace / "workspace.json")
        require(ws["host"] == roles["host"], "workspace Host path differs")
        public = pin(member["ssh"]["identityFile"] + ".pub")
        tokens = Path(public["path"]).read_text().split()
        require(len(tokens) >= 2 and tokens[0] == "ssh-ed25519"
                and re.fullmatch(r"[A-Za-z0-9+/=]+", tokens[1]), "unsupported member SSH key")
        require(tokens[1] not in key_inventory, "duplicate member SSH key")
        key_inventory.add(tokens[1])
        argv = [launcher["path"], cli["path"], roles["host"], config["path"],
                state["publicSocket"], str(workspace), member["home"]]
        require(all(re.fullmatch(r"/[A-Za-z0-9_./-]+", word) and "/../" not in word
                    for word in argv), "forced command requires source renderer's simple paths")
        forced = shlex.join(argv)
        require("\n" not in forced, "invalid forced command")
        lines.append('restrict,pty,command="' + forced.replace('\\', '\\\\').replace('"', '\\"')
                     + '" ' + " ".join(tokens[:2]) + "\n")
        commands.append({"subject": member["subject"], "launcher": launcher, "mini": cli,
                         "host": roles["host"], "authorizedKeys": None, "publicKey": public})
    current_keys = []
    for line in roster.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"): continue
        words = shlex.split(line)
        require(len(words) >= 3 and words[1] == "ssh-ed25519", "roster contains unbound SSH format")
        current_keys.append(words[2])
    require(len(current_keys) == len(key_inventory) and set(current_keys) == key_inventory,
            "roster contains members absent from authoritative journey; expand inventory before cut")
    write(output / "authorized_keys", "".join(lines))
    observed = {"path": str(roster), "sha256": digest(output / "authorized_keys")}
    for command in commands: command["authorizedKeys"] = observed
    store_unit, public_unit = request["storeUnit"], request["ingressUnit"]
    require(all(re.fullmatch(r"[A-Za-z0-9_.@-]+\.service", name)
                for name in (store_unit, public_unit)) and store_unit != public_unit, "invalid units")
    store = [cli["path"], "serve-operator", "--host", roles["host"], "--config", config["path"],
             "--socket", state["privateSocket"]]
    ingress = [cli["path"], "serve-public-proxy", "--socket", state["publicSocket"],
               "--upstream", state["privateSocket"], "--config", config["path"]]
    write(output / store_unit, unit(store, user, "Mini supplied Store operator", cwds["operator"]))
    write(output / public_unit, unit(ingress, user, "Mini supplied Store public ingress", cwds["public"]))
    descriptor = {"protocol": "mini-service-deployment-binding-v1", "dataRoot": str(root),
        "nodeRoot": str(root / "world"), "operatorSocket": state["privateSocket"],
        "publicSocket": state["publicSocket"], "storeUnit": store_unit, "ingressUnit": public_unit,
        "unitManager": "system", "authorizedKeys": str(roster), "memberHomes":
        [row["home"] for row in journey["members"].values()], "serviceUid": uid,
        "operatorWorkspace": str(root / "operator-workspace"), "deployment": {
            "config": config, "manifest": pin(selected), "rolePaths": roles, "cli": cli,
            "memberCommands": commands}}
    write(output / "deployment-binding.json", descriptor)
    # The reviewed stop implementation and its ownership checks travel with
    # the proposal; later source edits cannot change an already prepared cut.
    for name in ("platform-service-cut.py", "platform-provision.py", "joined-member-journey.py"):
        (output / name).write_bytes((HERE / name).read_bytes())
    write(output / "proposal.json", {"protocol": "mini-platform-service-cut-proposal-v1",
        "runtime": pin(runtime_path), "input": request, "sourceIdentity": state["identity"],
        "ownedServices": state["services"], "ownedCwds": cwds, "descriptor": descriptor,
        "artifacts": {file.name: digest(file) for file in output.iterdir() if file.is_file()},
        "published": False})


def stop(output):
    proposal = read(output / "proposal.json")
    require(digest(__file__) == proposal["artifacts"]["platform-service-cut.py"],
            "stop implementation differs from prepared cut")
    for name, sha in proposal["artifacts"].items():
        require(Path(name).name == name and digest(output / name) == sha, "cut proposal artifact changed")
    state = read(proposal["runtime"]["path"])
    require(state["identity"] == proposal["sourceIdentity"], "runtime source identity changed")
    require(state["root"] == proposal["descriptor"]["dataRoot"], "runtime root changed")
    journal_path = output / "stop-journal.json"
    journal = read(journal_path) if journal_path.exists() else {"protocol": "mini-platform-owned-stop-v1"}
    deployment = proposal["descriptor"]["deployment"]
    for name in ("config", "manifest", "cli"):
        pin(deployment[name]["path"], deployment[name]["sha256"])
    protected(deployment["manifest"]["path"]); protected(deployment["cli"]["path"])
    for command in deployment["memberCommands"]:
        protected(command["launcher"]["path"])
        pin(command["launcher"]["path"], command["launcher"]["sha256"])
    for name in ("public", "operator"):
        if name in state["services"]:
            require(state["services"][name] == proposal["ownedServices"][name], "owned process binding changed")
            cwd = Path("/proc", str(state["services"][name]["pid"]), "cwd").resolve(strict=True)
            require(str(cwd) == proposal["ownedCwds"][name], "owned process working directory changed")
    world = provision.World(Path(state["root"]), state)
    world.stop(["public"])
    journal["publicStopped"] = True; write(journal_path, journal)
    if "operator" in state["services"]:
        common = ["--socket", state["privateSocket"], "--host", deployment["rolePaths"]["host"],
                  "--config", deployment["config"]["path"]]
        def native(label, args):
            argv = [deployment["cli"]["path"], *args, *common]
            journal["serial"] = journal.get("serial", 0) + 1
            write(journal_path, journal)
            label = f'{journal["serial"]:04d}-' + label
            write(output / (label + ".command.json"), argv)
            result = subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True, timeout=620)
            (output / (label + ".out")).write_bytes(result.stdout)
            (output / (label + ".err")).write_bytes(result.stderr)
            require(result.returncode == 0, "native drain refused; exact evidence retained")
            return json.loads(result.stdout)
        status = native("operator-status", ["operator-status"])
        require(status["processId"] == state["services"]["operator"]["pid"], "operator instance differs")
        drained = native("operator-drain", ["drain-operator", "--instance", status["instanceId"],
                         "--pid", str(status["processId"]), "--timeout-seconds", "600"])
        require(drained.get("format") == "mini-operator-drain-v1" and drained.get("phase") == "drained"
                and drained.get("admissionClosed") is True and drained.get("drained") is True
                and all(drained.get(k) == 0 for k in ("acceptedConnections", "queuedRequests", "activeRequests", "unresolvedConnections")), "operator did not confirm source quiescence")
        require(all(drained.get(k) == status.get(k) for k in ("processId", "instanceId", "hostSha256", "configSha256"))
                and drained["hostSha256"] == read(deployment["manifest"]["path"])["sha256"]["host"]
                and drained["configSha256"] == deployment["config"]["sha256"], "drain source changed")
        journal["drain"] = drained; write(journal_path, journal)
        world.stop(["operator"])
    else:
        require("drain" in journal, "operator absent without retained native drain")
    journal["stopped"] = True; write(journal_path, journal)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("prepare", "stop"))
    parser.add_argument("--request")
    parser.add_argument("--output", required=True)
    args = parser.parse_args(); os.umask(0o077)
    output = Path(args.output).absolute()
    if args.mode == "prepare":
        require(not output.exists(), "fresh proposal directory required")
        output.mkdir(mode=0o700); prepare(read(args.request), output)
    else: stop(output)


if __name__ == "__main__": main()
