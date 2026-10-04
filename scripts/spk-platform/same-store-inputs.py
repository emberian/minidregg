#!/usr/bin/env python3
"""Derive same-Store SPK adapter inputs from a supplied world's own inventory.

  same-store-inputs.py profile   --platform-inputs P --selection S --output O
  same-store-inputs.py attach    --platform-inputs P --selection S --output O
  same-store-inputs.py connector --platform-inputs P --selection S --attached A --output O
  same-store-inputs.py journey   --platform-inputs P --selection S --provisioned R --output O

The constructor's `platform-inputs.json`, its pinned manifest, configuration and
genesis, and each participant's own workspace supply every identity, key
selector, authority and policy value. The selection names only what an operator
chooses: which member owns the app, who receives sessions, the package, the
entrance hosts and the unused resource and capability numbers to allocate.
Nothing here writes to the Store. `attach` and `connector` read each
participant's current signing-key status from the Host; the other commands
read files only. Outputs are written once.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("continuity_fixture", HERE / "ws-continuity-fixture.py")
f = importlib.util.module_from_spec(spec); spec.loader.exec_module(f)
load, save, require, sha, absolute = f.load, f.save, f.require, f.sha, f.absolute

SELECTION = "mini-spk-same-store-selection-v1"
APP_RESOURCES = ["app", "packageManifest", "snapshotManifest"]
APP_CAPABILITIES = ["appOwnerCapability", "appControlCapability", "packageOwnerCapability", "packageControlCapability",
                    "snapshotOwnerCapability", "snapshotControlCapability"]
SESSION_RESOURCES = ["session", "descriptor", "ticket"]
SESSION_CAPABILITIES = ["cap", "sessionControlCapability", "descriptorOwnerCapability", "descriptorControlCapability",
                        "appObserve", "pkgObserve", "ticketOwner", "ticketControl", "ticketObserve"]
# Linux sun_path holds 108 bytes including its terminator.
SOCKET_BOUND = 107


def route_name(label):
    # The attach adapter's bounded route directory name for a member label.
    return "m" + hashlib.sha256(label.encode()).hexdigest()[:12]


def decimal(value):
    return isinstance(value, str) and re.fullmatch(r"0|[1-9][0-9]*", value) is not None


def exact(value, required, optional, what):
    require(isinstance(value, dict) and set(required) <= set(value) <= set(required) | set(optional), what + " fields differ")
    return value


def consecutive(first, names, what):
    require(decimal(first) and first != "0", what + " allocation must start at a positive canonical decimal")
    return {name: str(int(first) + index) for index, name in enumerate(names)}


def named_selection(context, selection, world):
    """Resolve inventory names only after matching both retained world inventories."""
    require(world.get("type") == "mini-world-identity-v1", "unknown named world inventory")
    members = world.get("members", {})
    require(isinstance(members, dict) and members, "named world inventory has no members")
    subjects = []
    for name, row in members.items():
        subject = row.get("subject")
        retained = context["memberInventory"].get(subject)
        require(retained is not None and retained.get("subject") == subject
                and all(retained.get(key) == row.get(key) for key in ("workspace", "home")),
                "world inventory and constructor participant differ: " + name)
        subjects.append(subject)
    require(len(set(subjects)) == len(subjects), "named world inventory subjects repeat")
    result = json.loads(json.dumps(selection))
    def subject(name):
        require(isinstance(name, str) and name in members, "selection must name a world inventory member: " + str(name))
        return members[name]["subject"]
    result["app"]["owner"] = subject(result["app"]["owner"])
    for row in result["app"]["members"].values():
        row["subject"] = subject(row["subject"])
    if "connector" in result:
        result["connector"]["subject"] = subject(result["connector"]["subject"])
        result["connector"]["reader"]["subject"] = subject(result["connector"]["reader"]["subject"])
    return result


class World:
    """The supplied world's retained inventory, checked against its own pins."""

    def __init__(self, platform_inputs, selection, world_inventory=None):
        self.inputs_path = absolute(platform_inputs)
        self.ctx = load(self.inputs_path)
        self.selection = exact(load(absolute(selection)),
            ["protocol", "evidence", "grainsRoot", "brokerSocket", "package", "app"], ["leaseSeconds", "sizeClass", "connector"], "selection")
        require(self.selection["protocol"] == SELECTION, "unknown selection protocol")
        if world_inventory is not None:
            self.selection = named_selection(self.ctx, self.selection, load(absolute(world_inventory)))
        identity = self.ctx["identity"]
        self.manifest_path = absolute(self.ctx["manifest"])
        require(sha(self.manifest_path) == identity["manifestSha256"], "supplied manifest pin differs")
        self.manifest = load(self.manifest_path)
        self.config_path = absolute(self.ctx["config"])
        require(sha(self.config_path) == identity["configSha256"], "supplied configuration pin differs")
        self.config = load(self.config_path)
        self.genesis = load(absolute(self.ctx["genesis"]))
        require(decimal(self.genesis["domain"]) and self.genesis["domain"] == str(identity["domain"]) and decimal(self.genesis["expectedSemantics"]),
                "genesis namespace differs from the supplied identity")
        for role in ["host", "mini", "store", "verifier", "spkHost", "bwrap"]:
            require(sha(absolute(self.manifest[role])) == self.manifest["sha256"][role], "manifest role bytes differ: " + role)
        self.custody = self.ctx["custody"]
        self.manager = self.custody["management"]
        policy = self.config["lifecycleManagement"]
        require(str(policy["managementSubject"]) == self.manager["subject"] and str(policy["managementKeyId"]) == self.manager["keyId"],
                "constructor management custody differs from the genesis-pinned lifecycle policy")
        self.grains = absolute(self.selection["grainsRoot"])
        self.broker = str(absolute(self.selection["brokerSocket"]))
        require(self.broker in ("/run/mini-spk-broker.sock", str(self.grains / "broker.sock")), "broker socket must be the default or belong to the grains root")
        self.evidence = absolute(self.selection["evidence"])
        f.protected_parent(self.evidence)
        seed = self.config.get("expectedSeed")
        require(isinstance(seed, int) and not isinstance(seed, bool) and seed >= 0,
                "configuration lacks its genesis expectedSeed")
        # The Store key is Mini's storeTag (Kernel/ApplicationLifecycleResidentProfile):
        # the low 64 bits of the genesis seed identity as 16 lowercase hex digits. The
        # Host reports it (`profile` storeTag) and init-store names the state root by it.
        self.state = self.grains / format(seed % 2**64, "016x") / "host"
        self.host_images = {str(absolute(self.manifest["host"]))}

    def member(self, subject):
        require(decimal(subject) and subject in self.ctx["memberInventory"], "selected participant is not in the world's member inventory: " + str(subject))
        row = self.ctx["memberInventory"][subject]
        workspace = absolute(row["workspace"])
        pin = load(workspace / "workspace.json")
        require(pin["type"] == "minidregg-participant-workspace-v1" and str(pin["subject"]) == subject and pin["config"] == str(self.config_path)
                and pin["socket"] == self.ctx["publicSocket"], "participant workspace is not bound to the supplied world: " + subject)
        # Installation may expose the sealed Host under another path; admit an
        # alias only through the exact pinned executable bytes, hashed once.
        if pin["host"] not in self.host_images:
            require(sha(absolute(pin["host"])) == self.manifest["sha256"]["host"], "participant workspace pins another Host: " + subject)
            self.host_images.add(pin["host"])
        return workspace, pin

    def member_key(self, subject):
        """The participant's own current signing selector, read from the Host."""
        workspace, pin = self.member(subject)
        seed = absolute(pin["key"])
        public = Path(str(seed) + ".pub")
        paid = self.ctx["memberInventory"][subject].get("paidEntry")
        if paid is not None:
            joined = absolute(paid["joinDir"])
            require(absolute(paid["miniKeyFile"]) == seed and seed == joined / "mini.key"
                    and workspace == joined / "workspace" and absolute(paid["workspace"]) == workspace,
                    "paid key custody differs from constructor inventory")
            # Native join_solana_v2 writes mini.key and mini.pub separately.
            public = joined / "mini.pub"
        require(public.is_file() and not public.is_symlink() and len(public.read_bytes()) == 32,
                "participant public key file absent from constructor custody: " + subject)
        try:
            output = subprocess.run([self.manifest["mini"], "key-status", "--workspace", str(workspace)], capture_output=True, timeout=120, check=False)
        except subprocess.TimeoutExpired:
            raise RuntimeError("key status timed out for " + subject)
        require(output.returncode == 0, "key status refused for " + subject + ": " + output.stderr.decode(errors="replace").strip()[:300])
        status = json.loads(output.stdout)
        require(status.get("type") == "subject-key-status-v1" and status.get("subject") == subject and status.get("isCurrent") is True
                and status.get("currentRevoked") is False and decimal(status.get("keyId")) and decimal(status.get("keyEpoch")),
                "participant workspace key is not the subject's current signing key: " + subject)
        return {"keyId": status["keyId"], "keyEpoch": status["keyEpoch"], "seedPath": str(seed), "publicKeyPath": str(public)}

    def custody_key(self, role):
        row = self.custody[role]
        return row["subject"], {"keyId": row["keyId"], "keyEpoch": row["keyEpoch"], "seedPath": row["seed"], "publicKeyPath": row["publicKey"]}

    def creator_account(self):
        rows = [row for row in self.genesis["enrollments"] if row["key"]["subject"] == self.manager["subject"]]
        require(len(rows) == 1 and rows[0]["accountId"] == self.manager["subject"] and decimal(rows[0]["spendCapabilityId"]),
                "genesis does not enroll the management subject with one own account")
        return rows[0]["spendCapabilityId"]

    def package(self):
        package = exact(self.selection["package"], ["path", "sha256"], [], "package")
        require(sha(absolute(package["path"])) == package["sha256"], "selected package bytes differ")
        return package

    def socket_bound(self, app, route_names):
        paths = [self.state / "apps" / app / "g99" / "checkpoint-control.sock",
                 *[self.state / "apps" / app / "routes" / name / "http.sock" for name in route_names]]
        longest = max(paths, key=lambda path: len(os.fsencode(path)))
        require(len(os.fsencode(longest)) <= SOCKET_BOUND,
                f"Unix socket pathname exceeds {SOCKET_BOUND} bytes ({len(os.fsencode(longest))}): {longest}; shorten the grains root, app number or route name")


def profile(world):
    manager = world.manager
    return {"protocol": "mini-spk-same-store-profile-input-v1", "root": str(world.evidence / "profile"),
        "manifest": str(world.manifest_path), "expectedSourceCommit": world.manifest["sourceCommit"],
        "miniConfig": str(world.config_path), "miniConfigSha256": world.ctx["identity"]["configSha256"],
        "semantics": world.genesis["expectedSemantics"], "grainsRoot": str(world.grains), "brokerSocket": world.broker,
        "privateSocket": world.ctx["privateSocket"],
        "management": {"subject": manager["subject"], "keyId": manager["keyId"], "keyEpoch": manager["keyEpoch"],
                       "seedPath": manager["seed"], "publicKeyPath": manager["publicKey"]},
        "completionPublicKey": world.custody["completionPublic"], "completionSeed": world.custody["completionSeed"],
        "bwrap": world.manifest["bwrap"], "leaseSeconds": world.selection.get("leaseSeconds", 120)}


def attach(world):
    app = exact(world.selection["app"], ["owner", "room", "members", "resources", "capabilities"], ["lifecycleRequestId"], "app selection")
    owner = app["owner"]
    owner_workspace, _ = world.member(owner)
    members = app["members"]
    require(isinstance(members, dict) and 1 <= len(members) <= 64, "between 1 and 64 session members required")
    order = list(members)
    application = {**consecutive(app["resources"], APP_RESOURCES, "app resource"), **consecutive(app["capabilities"], APP_CAPABILITIES, "app capability")}
    delegates, keys = {}, {}
    for role in ("owner", "management"):
        subject, key = world.custody_key(role)
        keys[subject] = key
    keys[owner] = world.member_key(owner)
    for index, label in enumerate(order):
        row = exact(members[label], ["subject", "expectedHost"], [], "session member")
        require(re.fullmatch("[A-Za-z0-9][A-Za-z0-9_-]{0,63}", label) is not None, "session member label invalid: " + label)
        require(isinstance(row["expectedHost"], str) and re.fullmatch(r"[a-z0-9]([a-z0-9.-]{0,251}[a-z0-9])?(:[1-9][0-9]{0,4})?", row["expectedHost"]) is not None,
                "entrance host must be a lowercase DNS name with an optional port")
        if row["subject"] not in keys:
            keys[row["subject"]] = world.member_key(row["subject"])
        delegates[label] = {"subject": row["subject"], "expectedHost": row["expectedHost"],
            **consecutive(str(int(app["resources"]) + len(APP_RESOURCES) + index * len(SESSION_RESOURCES)), SESSION_RESOURCES, "session resource"),
            **consecutive(str(int(app["capabilities"]) + len(APP_CAPABILITIES) + index * len(SESSION_CAPABILITIES)), SESSION_CAPABILITIES, "session capability")}
    require(len({d["subject"] for d in delegates.values()}) == len(delegates) and len({d["expectedHost"] for d in delegates.values()}) == len(delegates),
            "each session member needs its own subject and entrance host")
    resources = len(APP_RESOURCES) + len(order) * len(SESSION_RESOURCES)
    capabilities = len(APP_CAPABILITIES) + len(order) * len(SESSION_CAPABILITIES)
    first, last = int(app["resources"]), int(app["resources"]) + resources - 1
    require(last < int(app["capabilities"]) or int(app["capabilities"]) + capabilities - 1 < first, "resource and capability allocations overlap")
    require(last < 1 << 64, "app resources exceed the host volume range")
    world.socket_bound(application["app"], [route_name(label) for label in order])
    room = load(owner_workspace / "refs" / (app["room"].replace("/", ".") + ".json"))
    require(room["kind"] == "object" and decimal(room["target"]) and decimal(room["observeCapability"]), "owner room reference is not a held object")
    authority = world.ctx["authority"]
    tariff = world.config["grainBirthTariff"]
    package = world.package()
    value = {"protocol": "mini-spk-same-store-attach-v1", "root": str(world.evidence / ("app-" + application["app"])),
        "manifest": str(world.manifest_path), "expectedSourceCommit": world.manifest["sourceCommit"],
        "miniConfig": str(world.config_path), "miniConfigSha256": world.ctx["identity"]["configSha256"],
        "workspace": world.ctx["operatorWorkspace"], "genesis": world.ctx["genesis"],
        "publicSocket": world.ctx["publicSocket"], "privateSocket": world.ctx["privateSocket"],
        "grainsRoot": str(world.grains), "brokerSocket": world.broker,
        "profileResult": str(world.evidence / "profile/profile-result.json"), "initStoreResult": str(world.evidence / "profile/init-store.json"),
        "spk": package["path"], "spkSha256": package["sha256"], "sizeClass": world.selection.get("sizeClass", "S"),
        "namespace": {"domain": world.genesis["domain"], "semantics": world.genesis["expectedSemantics"]},
        "room": {"target": room["target"], "capability": room["observeCapability"]},
        "authority": {"owner": owner, "creator": world.manager["subject"], "creatorAccountCapability": world.creator_account(),
            "factory": {"target": authority["factory"]["target"], "capability": authority["factory"]["managementCapability"]},
            "tool": {"task": authority["tool"]["task"], "capability": authority["tool"]["managementCapability"], "observeCapability": authority["tool"]["managementCapability"]},
            "parent": {"task": authority["parent"]["task"], "capability": authority["parent"]["managementCapability"], "observeCapability": authority["parent"]["managementCapability"]},
            "template": {name: str(world.config[name]) for name in ("issuer", "ownerBudget", "lifetime")},
            "tariff": {name: str(tariff[name]) for name in ("base", "perBirth")}},
        "application": application, "keys": keys, "delegates": delegates}
    # The owner is an enrolled member, never the host's manager: hosting is
    # always the owner's explicit delegation from their own workspace.
    request = app.get("lifecycleRequestId", "hosting-" + application["app"])
    require(isinstance(request, str) and re.fullmatch("[A-Za-z0-9][A-Za-z0-9_-]{0,39}", request) is not None, "lifecycle request ID invalid")
    value["lifecycleDelegation"] = {"ownerWorkspace": str(owner_workspace), "manager": world.manager["subject"], "requestId": request}
    return value


def connector_selection(world):
    require("connector" in world.selection, "selection names no connector")
    return exact(world.selection["connector"], ["subject", "name", "expectedHost", "sheet", "role", "task", "document", "resources", "capabilities",
                                                "reader", "endpoint", "ca", "operation"], [], "connector selection")


def connector(world, attached_path):
    c = connector_selection(world)
    attached = load(absolute(attached_path))
    require(attached["protocol"] == "mini-spk-same-store-attached-v1" and attached["miniConfigSha256"] == world.ctx["identity"]["configSha256"],
            "attachment result belongs to another world")
    fixture = absolute(attached["fixture"])
    taken = load(fixture)
    require(c["subject"] not in taken["keys"], "connector must be a principal independent of the app's owner and session members")
    workspace, _ = world.member(c["subject"])
    require(re.fullmatch(r"[a-z][a-z0-9-]{0,31}", c["name"]) is not None, "connector route name invalid")
    require(decimal(c["role"]), "signed role number required")
    world.socket_bound(attached["appId"], [c["name"]])
    delegate = {"name": c["name"], "subject": c["subject"], "sessionKind": "web", "expectedHost": c["expectedHost"],
        **consecutive(c["resources"], SESSION_RESOURCES, "connector resource"), **consecutive(c["capabilities"], SESSION_CAPABILITIES, "connector capability")}
    used = {taken["application"][k] for k in APP_RESOURCES + APP_CAPABILITIES} | {d[k] for d in taken["delegates"].values() for k in SESSION_RESOURCES + SESSION_CAPABILITIES}
    require(not used & {delegate[k] for k in SESSION_RESOURCES + SESSION_CAPABILITIES}, "connector allocation overlaps the attached app")
    return {"protocol": "mini-app-document-provision-v1", "root": str(world.evidence / ("connector-" + attached["appId"] + "-" + c["name"])),
        "fixture": str(fixture), "fixtureSha256": sha(fixture), "delegate": delegate, "key": world.member_key(c["subject"]),
        "workspace": str(workspace), "task": c["task"], "document": c["document"],
        "roleBasis": {"type": "role", "id": c["role"]}, "sheet": c["sheet"]}


def journey(world, provisioned_path):
    c = connector_selection(world)
    provisioned = absolute(provisioned_path)
    result = load(provisioned)
    require(result["protocol"] == "mini-app-document-provisioned-v1" and result["subject"] == c["subject"], "provision result belongs to another connector")
    reader = exact(c["reader"], ["subject", "document"], [], "independent reader")
    require(reader["subject"] != c["subject"], "readback must use an independent participant")
    reader_workspace, _ = world.member(reader["subject"])
    require(re.fullmatch(r"https://[a-z0-9.-]+(:[1-9][0-9]{0,4})?/", c["endpoint"]) is not None, "connector endpoint must be an https origin ending in /")
    require(c["ca"] is None or absolute(c["ca"]).is_file(), "route CA file absent")
    return {"protocol": "mini-app-document-journey-v1", "root": str(Path(result["fixture"]).parent / "journey"),
        "provisioned": str(provisioned), "provisionedSha256": sha(provisioned),
        "mini": {"path": world.manifest["mini"], "sha256": world.manifest["sha256"]["mini"]},
        "endpoint": c["endpoint"], "ca": c["ca"], "operation": c["operation"],
        "taskReference": c["task"], "documentReference": c["document"],
        "reader": {"workspace": str(reader_workspace), "document": reader["document"]}}


def main():
    os.umask(0o077)
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=["profile", "attach", "connector", "journey"])
    for name in ("platform-inputs", "selection", "output"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--world-inventory", help="WORLD-IDENTITY.json: selection participant fields contain inventory names")
    parser.add_argument("--attached")
    parser.add_argument("--provisioned")
    args = parser.parse_args()
    require(os.getuid() != 0, "run as the Store operator")
    world = World(args.platform_inputs, args.selection, args.world_inventory)
    if args.command == "profile":
        value = profile(world)
    elif args.command == "attach":
        value = attach(world)
    elif args.command == "connector":
        require(args.attached is not None, "connector needs --attached ATTACHMENT_RESULT")
        value = connector(world, args.attached)
    else:
        require(args.provisioned is not None, "journey needs --provisioned PROVISION_RESULT")
        value = journey(world, args.provisioned)
    output = absolute(args.output)
    f.protected_parent(output.parent)
    save(output, value)
    print(json.dumps({"written": str(output), "sha256": sha(output), "protocol": value["protocol"], "root": value["root"]}))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, KeyError, OSError) as error:
        print("same-Store inputs: " + str(error), file=sys.stderr)
        sys.exit(1)
