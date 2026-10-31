#!/usr/bin/env python3
"""Package role binaries as a Mini candidate: the one shipping format.

  package.py --roles ROLES.json --source-archive SOURCE.tar --out NEW_DIR [--toolchains T.json]
             [--host-build-manifest MANIFEST.txt] [--into-existing]
  package.py --overlay BASE_DIR --role ROLE=BINARY... --source-archive B.tar --toolchains T.json
             --into PARENT_DIR --name LABEL [--host-build-manifest MANIFEST.txt]
                                 a hot-swap candidate PARENT_DIR/<id>: BASE_DIR with whole build families of
                                 roles replaced by binaries built from B.tar's commit, every pin re-emitted;
                                 BASE_DIR is hard-linked, never written. provenance.json .overlay records name,
                                 id, base, sources and roles; <id> is 12 hex (overlay_id: sha256 of the
                                 provenance without id and stamps), the form ship.sh takes
  package.py --rust-roles        one line per Rust role: ROLE CRATE BINARY (the builders' list)
  package.py --fixture-roles     one line per journey fixture: ROLE CRATE BINARY (built beside, never shipped)

A candidate directory (deploy/candidate/INTERFACES.md) is what every consumer
reads: edge/mini/ship.sh, verify.sh, service-upgrade.sh, run.sh, the journey's
M7 step. It holds bin/<role binary>, SHA256SUMS, provenance.json
(minidregg-candidate-provenance-v1, one 40-hex source commit), source.tar,
logs/source-files.sha256, the operator scripts from the SAME archive (run.sh,
lib.sh, genesis.sh, genesis-params.example.json, INTERFACES.md) and
manifest.json (the journey-format manifest: absolute paths + SHA-256 pins for
this directory).

--roles: ROLES.json is a journey-format manifest of already-built binaries:
  {"sourceCommit": "<40 hex>", "host": "/abs/...", "mini": "/abs/...", ...,
   "sha256": {"host": "<hex>", ...}}
The archive's commit (git get-tar-commit-id) must equal sourceCommit: every
binary is claimed to be built from exactly that commit, and nothing else.
build.sh calls this after building (with --into-existing, the binaries already
in NEW_DIR/bin); a lane build on hbox calls it with its own role manifest.

ABI: every ELF's non-weak GLIBC version needs (readelf -V) are recorded in
provenance.json .abi; ship.sh refuses a box whose glibc is older than
.abi.glibcRequired, and the box's own loader checks every binary before
publication.
"""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time

# role -> file name under bin/. Aliases (shell = mini, hermes = grainRuntime,
# browserProxy = spkBrowserProxy) are names for these, never separate bytes.
ROLES = {
    "host": "minidregg-host",
    "consent": "minidregg-client-consent",
    "mini": "mini",
    # The ssh forced command (a box installs a root-owned copy as /usr/local/lib/mini/mini-shell-ssh):
    # hands a line to the member's resident shell (`mini line-resident`); built with mini, from the
    # same crate.
    "miniLine": "mini-line",
    "store": "minidregg-link-sqlite-store",
    "verifier": "minidregg-credential-signature-verifier",
    "grainRuntime": "grain-runtime",
    "grainProviderBridge": "grain-provider-bridge",
    "inferenceScheduler": "mini-inference-scheduler",
    "spkHost": "spk-host",
    "spkBrowserProxy": "spk-browser-proxy",
    "spkBroker": "mini-spk-broker",
    "spkVolumeHelper": "mini-spk-volume-helper",
    "discord": "mini-discord",
    # The self-serve door (deploy/door/README.md): the /join form and its root processor.
    "door": "mini-door",
    "doorProcess": "mini-door-process",
    # The room mirror ships so it can be enabled; it is off unless configured (deploy/discord/README.md).
    "discordMirror": "mini-discord-mirror",
    "payWatcher": "pay-watcher",
    "keys": "mini-keys",
    # The grain launch gate: deploy/grain-host/install-controller and bwrap require it beside the
    # launcher, so it is a product binary (native/launch-gate builds deploy/grain-host/launch-gate.rs).
    "launchGate": "launch-gate",
    # The web front end (deploy/web-frontend/INSTALL.md): the gateway and its root session helper.
    "web": "mini-web",
    "webSpawn": "mini-web-spawn",
    # The research-labelled four-party private compute demo (native/private-backend, feature `demo`):
    # the `mini private-compute` verb and the jprivate row run it.
    "privateCompute": "mini-private-compute",
}
# The Rust roles, role -> crate (the binary is ROLES[role]). The ONE list both builders read
# (`package.py --rust-roles`): build.sh and lane-build.sh each kept their own copy, and the lane
# copy silently lacked mini-keys and mini-spk-broker. host and consent are Lean roles.
RUST_ROLES = (("mini", "resource-client"), ("miniLine", "resource-client"), ("store", "hyperdocument-link-sqlite-store"),
              ("verifier", "credential-signature-verifier"), ("grainRuntime", "grain-runtime"),
              ("grainProviderBridge", "grain-runtime"), ("inferenceScheduler", "inference-scheduler"),
              ("spkHost", "spk-host"), ("spkBrowserProxy", "spk-host"), ("spkBroker", "spk-host"),
              ("spkVolumeHelper", "spk-host"),
              ("discord", "discord-entrance"), ("door", "discord-entrance"), ("doorProcess", "discord-entrance"), ("discordMirror", "discord-entrance"),
              ("payWatcher", "pay-watcher"),
              ("keys", "mini-keys"), ("launchGate", "launch-gate"),
              ("web", "mini-web"), ("webSpawn", "mini-web-spawn"),
              ("privateCompute", "private-backend"))
# Cargo features a Rust role's binary requires (its [[bin]] required-features), printed as the fourth
# column of `--rust-roles`; both builders pass it as `--features`.
RUST_ROLE_FEATURES = {"privateCompute": "demo"}
# Journey fixtures: built from the tip they test by the journey tooling (lane-build.sh rust puts them in
# LANE_DIR/fixtures, pack copies them to OUT/fixtures/ with their own SHA256SUMS; journey-runner reads
# $set/fixtures/<binary>; scripts/check-journey.sh builds them from the tree), never in bin/, the
# manifest or the shipped SHA256SUMS: the deterministic OpenAI-compatible provider is not a product.
FIXTURES = (("testProvider", "hermes-test-provider", "mini-hermes-test-provider"),)
# consent is required: a candidate whose friends cannot sign (the client refuses to sign without a
# locally selected consent pair) is not shippable, so a roles manifest without it is refused.
# keys is required: split tenancy (step B) is the box's shape, and install.sh under split has no
# broker without bin/mini-keys, so a candidate without it cannot be installed there.
REQUIRED = ("host", "consent", "mini", "store", "verifier", "keys")
ALIASES = {"shell": "mini", "hermes": "grainRuntime", "browserProxy": "spkBrowserProxy", "consentHost": "consent"}
# The Linux friend bundle (W1.9 consent shipping): one directory a friend copies
# whole, hard links to bin/ (every candidate carries the consent pair).
LINUX = "x86_64-unknown-linux-gnu"
BUNDLE = ("mini", "minidregg-host", "minidregg-client-consent",
          "minidregg-credential-signature-verifier", "minidregg-link-sqlite-store")
# The operator scripts travel with the binaries, from the same archive.
SCRIPTS = {"check-tamper.sh": ("deploy/candidate/check-tamper.sh", 0o555),
           "run.sh": ("deploy/candidate/run.sh", 0o555), "lib.sh": ("deploy/candidate/lib.sh", 0o555),
           "params.sh": ("deploy/candidate/params.sh", 0o555),
           "genesis.sh": ("native/resource-client/genesis.sh", 0o555),
           "genesis-params.example.json": ("native/resource-client/genesis-params.example.json", 0o444),
           "INTERFACES.md": ("deploy/candidate/INTERFACES.md", 0o444)}
# The example programs a member publishes (world/<app>/*.obend and their data) travel read-only
# under world/, from the same archive: the demo seed's TALLY_SRC defaults to world/activity/Tally.obend.
WORLD = "world/"
HEX40 = re.compile(r"[0-9a-f]{40}")
HEX64 = re.compile(r"[0-9a-f]{64}")


def die(message):
    print("package: " + message, file=sys.stderr)
    raise SystemExit(1)


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def tar_commit(archive):
    with open(archive, "rb") as stream:
        out = subprocess.run(["git", "get-tar-commit-id"], stdin=stream, capture_output=True, text=True)
    commit = out.stdout.strip()
    if out.returncode != 0 or not HEX40.fullmatch(commit):
        die(f"{archive} carries no commit id; create it with `git archive <commit>`")
    return commit


def archive_tree(archive):
    """The git tree id of the archive's files, written in a throw-away repository. It needs no
    checkout of the commit, and for `git archive COMMIT` (the tree has no export-subst or
    export-ignore attributes) it equals COMMIT^{tree}."""
    with tempfile.TemporaryDirectory(prefix="package-tree-") as tmp:
        tmp = Path(tmp)
        work = tmp / "files"
        work.mkdir()
        subprocess.run(["tar", "-xf", str(Path(archive).resolve()), "-C", str(work)], check=True)
        env = {**os.environ, "GIT_DIR": str(tmp / "git"), "GIT_WORK_TREE": str(work),
               "GIT_INDEX_FILE": str(tmp / "index"), "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull}
        def git(*args):
            out = subprocess.run(["git", *args], cwd=work, env=env, capture_output=True, text=True)
            if out.returncode:
                die(f"{archive}: cannot compute its tree (git {' '.join(args)}): {out.stderr.strip()}")
            return out.stdout.strip()
        init = subprocess.run(["git", "init", "-q", "--bare", str(tmp / "git")], capture_output=True, text=True,
                              env={k: v for k, v in env.items() if k not in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE")})
        if init.returncode:
            die(f"{archive}: cannot compute its tree (git init): {init.stderr.strip()}")
        for key, value in (("core.filemode", "true"), ("core.symlinks", "true"), ("core.autocrlf", "false")):
            git("config", key, value)
        git("add", "-A", "-f", ".")
        tree = git("write-tree")
    if not HEX40.fullmatch(tree):
        die(f"{archive}: no tree id computed")
    return tree


def version_key(v):
    return tuple(int(x) for x in v.split("."))


def abi(path):
    """Non-weak GLIBC version needs of one ELF, from its verneed section."""
    with open(path, "rb") as stream:
        if stream.read(4) != b"\x7fELF":
            return None
    out = subprocess.run(["readelf", "-V", "--wide", str(path)], capture_output=True, text=True)
    if out.returncode != 0:
        die(f"readelf -V failed on {path}: {out.stderr.strip()}")
    strong, weak = set(), set()
    for line in out.stdout.splitlines():
        m = re.search(r"Name: GLIBC_([0-9]+(?:\.[0-9]+)+)\s+Flags: (\S+)", line)
        if m:
            (weak if "WEAK" in m.group(2) else strong).add(m.group(1))
    needed = subprocess.run(["readelf", "-d", "--wide", str(path)], capture_output=True, text=True).stdout
    libs = sorted(set(re.findall(r"\(NEEDED\)\s+Shared library: \[([^\]]+)\]", needed)))
    top = max(strong, key=version_key) if strong else None
    return {"glibcRequired": top, "glibcStrong": sorted(strong, key=version_key),
            "glibcWeakOnly": sorted(weak - strong, key=version_key), "needed": libs}


def source_file_list(archive, out):
    """sha256sum lines of every archived file, the format build.sh writes
    (`find . -type f ! -path './.lake/*' | sort -z | xargs sha256sum`)."""
    rows = []
    with tarfile.open(archive) as tar:
        for member in tar.getmembers():
            if not member.isfile():
                continue
            name = member.name if member.name.startswith("./") else "./" + member.name
            if name.startswith("./.lake/"):
                continue
            data = tar.extractfile(member).read()
            rows.append((name.encode(), hashlib.sha256(data).hexdigest()))
    rows.sort(key=lambda r: r[0])
    with open(out, "wb") as stream:
        for name, digest in rows:
            stream.write(digest.encode() + b"  " + name + b"\n")


def extract(archive, member, target, mode):
    with tarfile.open(archive) as tar:
        try:
            info = tar.getmember(member)
        except KeyError:
            die(f"{archive} lacks {member}")
        data = tar.extractfile(info).read()
    Path(target).write_bytes(data)
    os.chmod(target, mode)


def extract_tree(archive, prefix, out):
    """Every regular file under PREFIX in the archive, at the same relative path under OUT, read-only."""
    written = []
    with tarfile.open(archive) as tar:
        for info in tar.getmembers():
            if not info.isfile() or not info.name.startswith(prefix):
                continue
            rel = Path(info.name)
            if rel.is_absolute() or ".." in rel.parts:
                die(f"{archive}: unsafe member {info.name}")
            target = out / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(tar.extractfile(info).read())
            os.chmod(target, 0o444)
            written.append(info.name)
    if not written:
        die(f"{archive} lacks {prefix}")
    return sorted(written)


def roles_from_manifest(manifest, label):
    """Shipped roles of a journey-format manifest, each pinned and present."""
    pins = manifest.get("sha256", {})
    chosen = {}
    for role in ROLES:
        if role not in manifest:
            continue
        path = Path(manifest[role])
        if not path.is_absolute():
            die(f"{label}: .{role} is not an absolute path")
        want = pins.get(role)
        if not (isinstance(want, str) and HEX64.fullmatch(want)):
            die(f"{label}: .sha256.{role} is not a SHA-256")
        if not path.is_file():
            die(f"{label}: .{role} {path} is not a file")
        got = sha(path)
        if got != want:
            die(f"{label}: {role} {path} is {got}, pinned {want}")
        chosen[role] = (path, want)
    missing = [r for r in REQUIRED if r not in chosen]
    if missing:
        die(f"{label}: required role(s) absent: {', '.join(missing)}")
    for alias, role in ALIASES.items():
        if alias in manifest and role in chosen and pins.get(alias) not in (None, chosen[role][1]):
            die(f"{label}: alias {alias} pins other bytes than {role}")
    return chosen


def build_identity(archive, commit, toolchains):
    """Require builder evidence; never substitute the packager's compiler for it."""
    rustc = toolchains.get("rustc", "")
    flags = toolchains.get("buildFlags")
    if not isinstance(rustc, str) or not all(x in rustc for x in
            ("rustc ", "commit-hash:", "host:", "release:", "LLVM version:")):
        die("build provenance requires the builder's rustc -vV")
    if not isinstance(flags, dict) or not flags.get("rust") or not flags.get("native"):
        die("build provenance requires buildFlags.rust and buildFlags.native")
    tree = archive_tree(archive)
    # A repository that holds the commit (lane-build, a checkout) must agree with the archive's own
    # tree: the archive is `git archive COMMIT` or it is refused. Without one (build.sh
    # --source-archive in an extracted tree) the archive's tree is the identity.
    repo = subprocess.run(["git", "rev-parse", "--verify", "-q", commit + "^{tree}"], capture_output=True, text=True)
    if repo.returncode == 0 and repo.stdout.strip() != tree:
        die(f"{archive}: its files hash to tree {tree}, but {commit[:12]}^{{tree}} in this repository is "
            f"{repo.stdout.strip()}: the archive is not `git archive {commit[:12]}`")
    with tarfile.open(archive) as tar:
        try:
            lean = tar.extractfile("lean-toolchain").read().decode()
        except KeyError:
            die("source archive lacks lean-toolchain")
        try:
            locks = {"Cargo.lock": hashlib.sha256(tar.extractfile("Cargo.lock").read()).hexdigest()}
        except KeyError:
            die("source archive lacks workspace Cargo.lock")
    return {"sourceTree": tree, "rustcVerbose": rustc,
            "leanToolchain": lean, "cargoLockSha256": locks, "flags": flags}


def package(chosen, archive, commit, out, toolchains, origin, host_build_manifest, into_existing):
    if tar_commit(archive) != commit:
        die(f"source archive commit is not {commit}")
    identity = build_identity(archive, commit, toolchains)
    if host_build_manifest is not None:
        args = Path(host_build_manifest).parent / "compile-args.txt"
        if not args.is_file():
            die("native build evidence lacks compile-args.txt")
        identity["flags"]["native"]["compileArgs"] = args.read_text()
        identity["flags"]["native"]["linkCommand"] = "leanc -o BINARY @OBJECT_RESPONSE_FILE"
        identity["flags"]["native"]["manifestSha256"] = sha(host_build_manifest)
    out = Path(out)
    if into_existing:
        if not (out / "bin").is_dir():
            die(f"--into-existing: {out}/bin does not exist")
    else:
        if out.exists() or out.is_symlink():
            die(f"refusing existing output: {out}")
        out.mkdir(parents=True)
        (out / "bin").mkdir()
    (out / "logs").mkdir(exist_ok=True)
    out = out.resolve()
    if tar_commit(archive) != commit:
        die(f"source archive commit is not {commit}")
    source_tar = out / "source.tar"
    if Path(archive).resolve() != source_tar:
        shutil.copyfile(archive, source_tar)
    binaries, abis = {}, {}
    for role, (path, want) in sorted(chosen.items()):
        target = out / "bin" / ROLES[role]
        if Path(path).resolve() != target:
            if target.exists():
                die(f"{target} exists and is not {role}'s source {path}")
            shutil.copyfile(path, target)
        os.chmod(target, 0o555)
        if sha(target) != want:
            die(f"{role} changed while copying")
        binaries[role] = {"path": f"bin/{ROLES[role]}", "sha256": want}
        found = abi(target)
        if found is not None:
            abis[role] = found
    for name, (member, mode) in SCRIPTS.items():
        extract(source_tar, member, out / name, mode)
    world_files = extract_tree(source_tar, WORLD, out)
    source_file_list(source_tar, out / "logs" / "source-files.sha256")
    floors = [a["glibcRequired"] for a in abis.values() if a["glibcRequired"]]
    provenance = {
        "type": "minidregg-candidate-provenance-v1",
        "source": {"commit": commit, "tree": identity["sourceTree"], "archive": "source.tar", "archiveSha256": sha(source_tar),
                   "origin": origin["type"], "fileList": "logs/source-files.sha256",
                   "fileListSha256": sha(out / "logs" / "source-files.sha256")},
        "target": "x86_64-linux",
        "toolchains": toolchains,
        "binaries": binaries,
        "abi": {"glibcRequired": max(floors, key=version_key) if floors else None, "binaries": abis},
        "packaging": origin,
        "builtUtc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    if host_build_manifest is not None:
        provenance["hostBuildManifest"] = {"path": str(host_build_manifest), "sha256": sha(host_build_manifest)}
    clients = {LINUX: {"path": "bin/mini", "sha256": binaries["mini"]["sha256"], "consent": None}}
    bundle_files = []
    bundle = out / "bin" / "clients" / LINUX
    bundle.mkdir(parents=True, exist_ok=True)
    for name in BUNDLE:
        link = bundle / name
        if not link.exists():
            os.link(out / "bin" / name, link)
        if sha(link) != sha(out / "bin" / name):
            die(f"friend bundle {name} differs from bin/{name}")
        bundle_files.append(f"bin/clients/{LINUX}/{name}")
    rel = f"bin/clients/{LINUX}"
    pin = lambda name: sha(out / "bin" / name)
    clients[LINUX]["consent"] = {
        "localHost": {"env": "MINI_LOCAL_HOST", "path": f"{rel}/minidregg-host", "sha256": pin("minidregg-host")},
        "consentHost": {"env": "MINI_CONSENT_HOST", "path": f"{rel}/minidregg-client-consent",
                        "sha256": pin("minidregg-client-consent")},
        "verifier": {"path": f"{rel}/minidregg-credential-signature-verifier",
                     "sha256": pin("minidregg-credential-signature-verifier")},
        "store": {"path": f"{rel}/minidregg-link-sqlite-store", "sha256": pin("minidregg-link-sqlite-store")}}
    extra_clients = sorted((out / "bin" / "clients").glob("*/mini")) if (out / "bin" / "clients").is_dir() else []
    for client in extra_clients:
        if client.parent.name != LINUX:
            clients[client.parent.name] = {"path": str(client.relative_to(out)), "sha256": sha(client), "consent": None}
    provenance["clients"] = clients
    # Include each physical shipping path, including the friend bundle and cross clients.
    outputs = {str(p.relative_to(out)): {"sha256": sha(p), "build": identity}
               for p in sorted((out / "bin").rglob("*")) if p.is_file()}
    provenance["outputs"] = outputs
    write_json(out / "provenance.json", provenance)
    listed = [f"bin/{ROLES[r]}" for r in sorted(chosen)] + [c["path"] for t, c in sorted(clients.items())
                                                            if c["path"] != "bin/mini"]
    listed += bundle_files + ["provenance.json", *SCRIPTS, "source.tar", "logs/source-files.sha256"]
    listed += world_files
    with open(out / "SHA256SUMS", "w") as stream:
        for rel in listed:
            stream.write(f"{sha(out / rel)}  {rel}\n")
    manifest = {role: str(out / "bin" / ROLES[role]) for role in chosen}
    pins = {role: want for role, (_, want) in chosen.items()}
    for alias, role in ALIASES.items():
        if role in chosen:
            manifest[alias] = manifest[role]
            pins[alias] = pins[role]
    manifest.update({"type": "minidregg-candidate-manifest-v2", "outputs": outputs,
                     "candidate": str(out / "provenance.json"), "sourceCommit": commit,
                     "spkHostFeatures": [],
                     "clients": {t: str(out / c["path"]) for t, c in clients.items()}})
    pins["candidate"] = sha(out / "provenance.json")
    manifest["sha256"] = pins
    write_json(out / "manifest.json", manifest)
    print(json.dumps({"candidate": str(out), "commit": commit, "roles": sorted(chosen),
                      "glibcRequired": provenance["abi"]["glibcRequired"],
                      "sha256sumsSha256": sha(out / "SHA256SUMS")}, indent=2))


# Roles that one build produces together: an overlay swaps a whole family or refuses. A world that
# mixes one crate's binaries from two commits fails at run time (spk-host's broker socket custody,
# integrator 2026-10-31), so a family is never split.
def families():
    by_crate = {}
    for role, crate in RUST_ROLES:
        by_crate.setdefault(crate, []).append(role)
    fam = {role: tuple(by_crate[crate]) for role, crate in RUST_ROLES}
    fam["host"] = fam["consent"] = ("host", "consent")
    return fam


def replace_file(target, data_from=None, link_from=None, json_value=None):
    """Write TARGET as a NEW inode (an overlay's files start as hard links of the base's)."""
    tmp = target.with_name(target.name + ".overlay.tmp")
    if tmp.exists():
        tmp.unlink()
    if link_from is not None:
        os.link(link_from, tmp)
    elif data_from is not None:
        shutil.copyfile(data_from, tmp)
    else:
        tmp.write_text(json.dumps(json_value, indent=2, sort_keys=True) + "\n")
    os.replace(tmp, target)


def overlay_id(prov):
    """An overlay's 12-hex candidate id (ship.sh takes 12 hex): sha256 of its provenance.json content
    without the id itself and the wall-clock stamps, canonical JSON. Path-independent (provenance names
    files relative to the candidate), so the directory is named by it; the same overlay twice is one id."""
    p = json.loads(json.dumps(prov))
    p.pop("builtUtc", None)
    p["overlay"].pop("id", None)
    for r in p["overlay"]["roles"].values():
        r.pop("overlaidUtc", None)
    return hashlib.sha256(json.dumps(p, sort_keys=True, separators=(",", ":")).encode()).hexdigest()[:12]


def overlay(base, swaps, archive, toolchains, parent, name, host_build_manifest):
    """PARENT/<id>: BASE with SWAPS (role -> built binary) from ARCHIVE's commit, re-pinned everywhere."""
    out = Path(parent).resolve() / f".overlay-{os.getpid()}"
    try:
        return _overlay(base, swaps, archive, toolchains, out, name, host_build_manifest)
    finally:
        if out.exists():
            shutil.rmtree(out)


def _overlay(base, swaps, archive, toolchains, out, name, host_build_manifest):
    base = Path(base).resolve()
    base_manifest = read(base / "manifest.json")
    if base_manifest.get("type") != "minidregg-candidate-manifest-v2":
        die(f"{base}: manifest.json is not minidregg-candidate-manifest-v2")
    roles_from_manifest(base_manifest, f"{base}/manifest.json")  # every base pin is the bytes
    if sha(base / "provenance.json") != base_manifest["sha256"].get("candidate"):
        die(f"{base}: provenance.json differs from the manifest's pin")
    base_prov = read(base / "provenance.json")
    fam = families()
    for role in swaps:
        if role not in ROLES:
            die(f"--role {role}: not a role ({', '.join(sorted(ROLES))})")
        missing = [r for r in fam.get(role, (role,)) if r not in swaps and r in base_prov["binaries"]]
        if missing:
            die(f"--role {role}: its build family is swapped whole; also give {', '.join(missing)}")
        if role not in base_prov["binaries"]:
            die(f"--role {role}: the base candidate carries no {role}")
    commit = tar_commit(archive)
    if not (isinstance(commit, str) and HEX40.fullmatch(commit)):
        die(f"{archive}: no 40-hex commit id (git archive COMMIT)")
    identity = build_identity(archive, commit, toolchains)
    if host_build_manifest is not None:
        args = Path(host_build_manifest).parent / "compile-args.txt"
        if not args.is_file():
            die("native build evidence lacks compile-args.txt")
        identity["flags"]["native"]["compileArgs"] = args.read_text()
        identity["flags"]["native"]["linkCommand"] = "leanc -o BINARY @OBJECT_RESPONSE_FILE"
        identity["flags"]["native"]["manifestSha256"] = sha(host_build_manifest)
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,63}", name or ""):
        die("--name: a short label (letters, digits, . _ -), recorded as provenance.json .overlay.name")
    out.parent.mkdir(parents=True, exist_ok=True)
    if out.exists():
        shutil.rmtree(out)
    out.mkdir()
    # 1. the base, hard-linked (the base is never written: every changed file below is a new inode)
    for root, dirs, files in os.walk(base):
        rel = Path(root).relative_to(base)
        for d in dirs:
            (out / rel / d).mkdir(exist_ok=True)
        for f in files:
            os.link(Path(root) / f, out / rel / f)
    # 2. the swapped binaries, and their friend-bundle links
    prov = json.loads(json.dumps(base_prov))
    stamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    for role, path in sorted(swaps.items()):
        target = out / prov["binaries"][role]["path"]
        replace_file(target, data_from=path)
        os.chmod(target, 0o555)
        prov["binaries"][role]["sha256"] = sha(target)
        found = abi(target)
        if found is not None:
            prov["abi"]["binaries"][role] = found
        else:
            prov["abi"]["binaries"].pop(role, None)
        link = out / "bin" / "clients" / LINUX / target.name
        if target.name in BUNDLE and link.exists():
            replace_file(link, link_from=target)
    floors = [a["glibcRequired"] for a in prov["abi"]["binaries"].values() if a.get("glibcRequired")]
    prov["abi"]["glibcRequired"] = max(floors, key=version_key) if floors else None
    # 3. the overlay's own source, beside the base's (operator scripts and world/ stay the base's)
    odir = out / "overlay"
    odir.mkdir(exist_ok=True)
    otar = odir / f"{commit}.source.tar"
    if not otar.exists():
        shutil.copyfile(archive, otar)
    record = json.loads(json.dumps(base_prov.get("overlay") or {"sources": {}, "roles": {}}))
    record["name"] = name
    record["base"] = {"provenance": str(base / "provenance.json"), "sha256": sha(base / "provenance.json"),
                      "commit": base_prov["source"]["commit"]}
    record["sources"][commit] = {"tree": identity["sourceTree"], "archive": str(otar.relative_to(out)),
                                 "archiveSha256": sha(otar), "toolchains": toolchains}
    for role in swaps:
        record["roles"][role] = {"commit": commit, "sha256": prov["binaries"][role]["sha256"], "overlaidUtc": stamp}
    prov["overlay"] = record
    # 4. clients and outputs: an unchanged file keeps the base's build identity, a changed one gets this one
    linux = prov["clients"][LINUX]
    linux["sha256"] = prov["binaries"]["mini"]["sha256"]
    for entry in (linux.get("consent") or {}).values():
        entry["sha256"] = sha(out / entry["path"])
    outputs = {}
    for p in sorted((out / "bin").rglob("*")):
        if not p.is_file():
            continue
        rel, digest = str(p.relative_to(out)), sha(p)
        old = base_prov["outputs"].get(rel)
        outputs[rel] = old if old and old["sha256"] == digest else {"sha256": digest, "build": identity}
    prov["outputs"] = outputs
    prov["builtUtc"] = stamp
    prov["overlay"]["id"] = overlay_id(prov)
    replace_file(out / "provenance.json", json_value=prov)
    # 5. SHA256SUMS: the base's list, re-hashed, plus the overlay archive
    listed = [line.split("  ", 1)[1] for line in (base / "SHA256SUMS").read_text().splitlines() if "  " in line]
    rel_tar = str(otar.relative_to(out))
    if rel_tar not in listed:
        listed.append(rel_tar)
    tmp = out / "SHA256SUMS.overlay.tmp"
    with open(tmp, "w") as stream:
        for rel in listed:
            stream.write(f"{sha(out / rel)}  {rel}\n")
    os.replace(tmp, out / "SHA256SUMS")
    # 6. the directory is the id (manifest.json's absolute paths name it, so it is written after the move)
    final = out.parent / prov["overlay"]["id"]
    if final.exists() or final.is_symlink():
        die(f"{final} exists: the same overlay (same base, roles and bytes) is already there")
    os.rename(out, final)
    out = final
    # 7. manifest.json: the base's, relocated to OUT, re-pinned
    prefix = str(base) + "/"
    manifest = {k: (str(out) + "/" + v[len(prefix):] if isinstance(v, str) and v.startswith(prefix) else v)
                for k, v in base_manifest.items()}
    manifest["clients"] = {t: (str(out) + "/" + v[len(prefix):] if v.startswith(prefix) else v)
                           for t, v in base_manifest.get("clients", {}).items()}
    pins = dict(base_manifest["sha256"])
    for role in prov["binaries"]:
        if role in manifest:
            pins[role] = prov["binaries"][role]["sha256"]
    for alias, role in ALIASES.items():
        if alias in manifest and role in prov["binaries"]:
            pins[alias] = pins[role]
    manifest["outputs"] = outputs
    manifest["candidate"] = str(out / "provenance.json")
    pins["candidate"] = sha(out / "provenance.json")
    manifest["sha256"] = pins
    replace_file(out / "manifest.json", json_value=manifest)
    roles_from_manifest(manifest, f"{out}/manifest.json")  # every new pin is the bytes
    print(json.dumps({"candidate": str(out), "id": prov["overlay"]["id"], "name": name, "base": str(base),
                      "overlayCommit": commit,
                      "roles": {r: prov["binaries"][r]["sha256"] for r in sorted(swaps)},
                      "sha256sumsSha256": sha(out / "SHA256SUMS")}, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--roles")
    parser.add_argument("--source-archive")
    parser.add_argument("--out")
    parser.add_argument("--toolchains")
    parser.add_argument("--host-build-manifest")
    parser.add_argument("--into-existing", action="store_true")
    parser.add_argument("--overlay", metavar="BASE_CANDIDATE")
    parser.add_argument("--role", action="append", default=[], metavar="ROLE=BINARY")
    parser.add_argument("--into", metavar="PARENT_DIR")
    parser.add_argument("--name")
    if sys.argv[1:] == ["--rust-roles"]:
        for role, crate in RUST_ROLES:
            print(role, crate, ROLES[role], *([RUST_ROLE_FEATURES[role]] if role in RUST_ROLE_FEATURES else []))
        return
    if sys.argv[1:] == ["--fixture-roles"]:
        for role, crate, binary in FIXTURES:
            print(role, crate, binary)
        return
    a = parser.parse_args()
    if shutil.which("readelf") is None or shutil.which("git") is None:
        die("readelf (binutils) and git are required")
    if a.overlay:
        if a.roles or a.into_existing:
            die("--overlay takes --role, not --roles or --into-existing")
        if not (a.role and a.source_archive and a.toolchains and a.into and a.name) or a.out:
            die("--overlay needs --role ROLE=BINARY (one or more), --source-archive, --toolchains, --into PARENT_DIR "
                "and --name LABEL (the candidate is PARENT_DIR/<12-hex id>), and no --out")
        swaps = {}
        for kv in a.role:
            role, sep, path = kv.partition("=")
            if not sep or not Path(path).is_file():
                die(f"--role {kv}: ROLE=BINARY with an existing BINARY")
            swaps[role] = Path(path).resolve()
        hbm = Path(a.host_build_manifest).resolve() if a.host_build_manifest else None
        overlay(a.overlay, swaps, a.source_archive, read(a.toolchains), a.into, a.name, hbm)
        return
    if not a.roles:
        die("--roles is required")
    if not a.out:
        die("--out is required")
    if not a.source_archive:
        die("--roles needs --source-archive")
    manifest = read(a.roles)
    commit = manifest.get("sourceCommit")
    if not (isinstance(commit, str) and HEX40.fullmatch(commit)):
        die("roles manifest .sourceCommit must be a 40-hex commit")
    chosen = roles_from_manifest(manifest, a.roles)
    # A builder ships every role it builds; a roles manifest missing one is a builder whose list drifted.
    absent = [r for r in ("host", "consent", *(r for r, _ in RUST_ROLES)) if r not in chosen]
    if absent:
        die(f"{a.roles}: the builders build every role; absent: {', '.join(absent)} "
            "(deploy/candidate/package.py --rust-roles is the list)")
    toolchains = read(a.toolchains) if a.toolchains else {"recorded": "none"}
    origin = {"type": manifest.get("origin", "roles-manifest"), "roles": str(Path(a.roles).resolve()),
              "rolesSha256": sha(a.roles)}
    hbm = Path(a.host_build_manifest).resolve() if a.host_build_manifest else None
    package(chosen, a.source_archive, commit, a.out, toolchains, origin, hbm, a.into_existing)


if __name__ == "__main__":
    main()
