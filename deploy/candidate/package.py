#!/usr/bin/env python3
"""Package role binaries as a Mini candidate: the one shipping format.

  package.py --roles ROLES.json --source-archive SOURCE.tar --out NEW_DIR [--toolchains T.json]
             [--host-build-manifest MANIFEST.txt] [--into-existing]
  package.py --capsule FAMILY_DIR --out NEW_DIR
  package.py --rust-roles        one line per Rust role: ROLE CRATE BINARY (the builders' list)

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

--capsule: a sealed hbox family (/home/hbox/build/mini-bigstep/family-*/):
seal-result.json's manifestSha256 must be the manifest's bytes, every shipped
role must hash to its pin, source.tar must hash to sourceArchiveSha256 and
carry sourceCommit, and every shipped role's recorded sourceCommit
(provenance.json .roles) must BE that commit. A family that reuses a role
built at another commit ("unchanged-role-reuse") is refused: the candidate's
provenance says one commit built every binary, and a reuse claim is not a
build. Qualification variants (integration-qualification features) and
box-external roles (bwrap) are never shipped.

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
    "store": "minidregg-link-sqlite-store",
    "verifier": "minidregg-credential-signature-verifier",
    "grainRuntime": "grain-runtime",
    "grainProviderBridge": "grain-provider-bridge",
    "inferenceScheduler": "mini-inference-scheduler",
    "spkHost": "spk-host",
    "spkBrowserProxy": "spk-browser-proxy",
    "spkBroker": "mini-spk-broker",
    "spkHostd": "spk-hostd",
    "spkVolumeHelper": "mini-spk-volume-helper",
    "discord": "mini-discord",
    "payWatcher": "pay-watcher",
    "keys": "mini-keys",
}
# The Rust roles, role -> crate (the binary is ROLES[role]). The ONE list both builders read
# (`package.py --rust-roles`): build.sh and lane-build.sh each kept their own copy, and the lane
# copy silently lacked mini-keys, mini-spk-broker and spk-hostd. host and consent are Lean roles.
RUST_ROLES = (("mini", "resource-client"), ("store", "hyperdocument-link-sqlite-store"),
              ("verifier", "credential-signature-verifier"), ("grainRuntime", "grain-runtime"),
              ("grainProviderBridge", "grain-runtime"), ("inferenceScheduler", "inference-scheduler"),
              ("spkHost", "spk-host"), ("spkBrowserProxy", "spk-host"), ("spkBroker", "spk-host"),
              ("spkHostd", "spk-host"), ("spkVolumeHelper", "spk-host"),
              ("discord", "discord-entrance"), ("payWatcher", "pay-watcher"),
              ("keys", "mini-keys"))
# consent is required: a candidate whose friends cannot sign (the client refuses to sign without a
# locally selected consent pair) is not shippable, so a roles manifest or sealed family without it is refused.
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


def capsule(family):
    family = Path(family).resolve()
    manifest_path, seal_path = family / "manifest.json", family / "seal-result.json"
    if not manifest_path.is_file() or not seal_path.is_file():
        die(f"{family} is not a sealed family (manifest.json + seal-result.json)")
    seal, manifest = read(seal_path), read(manifest_path)
    if seal.get("manifestSha256") != sha(manifest_path):
        die("manifest.json is not the bytes seal-result.json sealed")
    commit = manifest.get("sourceCommit")
    if not (isinstance(commit, str) and HEX40.fullmatch(commit)) or seal.get("sourceCommit") != commit:
        die("family sourceCommit is not one 40-hex commit agreed by seal and manifest")
    archive = Path(manifest.get("sourceArchive", ""))
    if not archive.is_file() or sha(archive) != manifest.get("sourceArchiveSha256") \
            or seal.get("sourceArchiveSha256") != manifest.get("sourceArchiveSha256"):
        die("source.tar is not the archive the family sealed")
    if tar_commit(archive) != commit:
        die("source.tar is not an archive of the family's sourceCommit")
    chosen = roles_from_manifest(manifest, str(manifest_path))
    provenance = read(manifest.get("roleProvenance") or family / "provenance.json")
    recorded = provenance.get("roles", {})
    mixed = []
    for role in chosen:
        row = recorded.get(role)
        if row is None:
            mixed.append(f"{role} (no role provenance)")
        elif row.get("sourceCommit") != commit:
            mixed.append(f"{role} built at {str(row.get('sourceCommit'))[:12]} ({row.get('mode', '?')})")
        elif row.get("sha256") != chosen[role][1]:
            mixed.append(f"{role} (role provenance pins other bytes)")
    build = manifest.get("buildSourceCommit", {})
    for part, at in (build.items() if isinstance(build, dict) else []):
        if at != commit:
            mixed.append(f"buildSourceCommit.{part} = {str(at)[:12]}")
    if mixed:
        die(f"family {family.name} is not one build of {commit[:12]}: " + "; ".join(mixed)
            + ". Rebuild those roles at that commit (or seal a family whose roles agree); a reuse claim is not a build.")
    toolchains = {"recorded": "capsule", "rustBuild": None, "nativeHostManifest": None}
    rust = family / "rust-build.json"
    if rust.is_file():
        toolchains["rustBuild"] = {"path": str(rust), "sha256": sha(rust)}
    native = family / "native-host-manifest.txt"
    if native.is_file():
        toolchains["nativeHostManifest"] = {"path": str(native), "sha256": sha(native)}
        for line in native.read_text().splitlines():
            if line.startswith("lean="):
                toolchains["lean"] = line[5:]
    excluded = sorted(k for k in manifest.get("sha256", {}) if k not in ROLES and k not in ALIASES)
    origin = {"type": "sealed-capsule", "family": str(family), "manifestSha256": seal["manifestSha256"],
              "rolesVerified": seal.get("rolesVerified"), "notShipped": excluded,
              "nativeQualification": manifest.get("nativeQualification")}
    return chosen, archive, commit, toolchains, origin, native if native.is_file() else None


def build_identity(archive, commit, toolchains):
    """Require builder evidence; never substitute the packager's compiler for it."""
    rustc = toolchains.get("rustc", "")
    flags = toolchains.get("buildFlags")
    if not isinstance(rustc, str) or not all(x in rustc for x in
            ("rustc ", "commit-hash:", "host:", "release:", "LLVM version:")):
        die("build provenance requires the builder's rustc -vV")
    if not isinstance(flags, dict) or not flags.get("rust") or not flags.get("native"):
        die("build provenance requires buildFlags.rust and buildFlags.native")
    tree = subprocess.run(["git", "rev-parse", commit + "^{tree}"], capture_output=True, text=True)
    if tree.returncode or not HEX40.fullmatch(tree.stdout.strip()):
        die("source tree unavailable: package in a repository containing the archive commit")
    with tarfile.open(archive) as tar:
        try:
            lean = tar.extractfile("lean-toolchain").read().decode()
        except KeyError:
            die("source archive lacks lean-toolchain")
        try:
            locks = {"Cargo.lock": hashlib.sha256(tar.extractfile("Cargo.lock").read()).hexdigest()}
        except KeyError:
            die("source archive lacks workspace Cargo.lock")
    return {"sourceTree": tree.stdout.strip(), "rustcVerbose": rustc,
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


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--roles")
    parser.add_argument("--capsule")
    parser.add_argument("--source-archive")
    parser.add_argument("--out", required=True)
    parser.add_argument("--toolchains")
    parser.add_argument("--host-build-manifest")
    parser.add_argument("--into-existing", action="store_true")
    if sys.argv[1:] == ["--rust-roles"]:
        for role, crate in RUST_ROLES:
            print(role, crate, ROLES[role])
        return
    a = parser.parse_args()
    if shutil.which("readelf") is None or shutil.which("git") is None:
        die("readelf (binutils) and git are required")
    if bool(a.roles) == bool(a.capsule):
        die("choose exactly one of --roles or --capsule")
    if a.capsule:
        if a.source_archive or a.toolchains or a.into_existing or a.host_build_manifest:
            die("--capsule takes its archive, toolchains and host build manifest from the family")
        chosen, archive, commit, toolchains, origin, hbm = capsule(a.capsule)
        package(chosen, archive, commit, a.out, toolchains, origin, hbm, False)
        return
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
