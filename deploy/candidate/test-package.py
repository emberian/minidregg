#!/usr/bin/env python3
"""deploy/candidate/package.py, run for real on stub role binaries in a throwaway git repo.

No Lean, no Rust build: the packager checks hashes, the archive commit, the roles it is
given and the shipping format, none of which needs a real ELF. Cases:

  * a full role set packages: bin/minidregg-client-consent exists, the Linux friend bundle is
    hard links of bin/, provenance pins the consent pair twice (.binaries.consent and
    .clients[linux].consent), SHA256SUMS verifies and lists every bundle file, manifest.json
    names consentHost with its pin;
  * the same set without the consent role is REFUSED by name (control: a candidate that
    cannot sign is not shippable);
  * the same set without keys (the split-tenancy key broker), or without any role the builders
    build (`package.py --rust-roles`), is REFUSED by name;
  * a roles manifest claiming another commit is REFUSED (control: the refusal is not only
    about consent);
  * a pin that does not match the bytes is REFUSED.

usage: python3 deploy/candidate/test-package.py
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PACKAGE = HERE / "package.py"
ROLE_FILES = {"host": "minidregg-host", "consent": "minidregg-client-consent"}
ROLE_FILES.update({role: name for role, _, name in (
    line.split() for line in subprocess.run([sys.executable, str(PACKAGE), "--rust-roles"], check=True,
                                            capture_output=True, text=True).stdout.splitlines())})
SCRIPTS = ["deploy/candidate/check-tamper.sh", "lean-toolchain", "Cargo.lock", "deploy/candidate/run.sh", "deploy/candidate/lib.sh", "deploy/candidate/params.sh", "native/resource-client/genesis.sh",
           "native/resource-client/genesis-params.example.json", "deploy/candidate/INTERFACES.md"]
failures = []


def check(name, ok, detail=""):
    print(("ok   " if ok else "FAIL ") + name + (("  " + detail) if detail and not ok else ""))
    if not ok:
        failures.append(name)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(repo, *args):
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
               GIT_COMMITTER_EMAIL="t@t", GIT_CONFIG_GLOBAL="/dev/null", GIT_CONFIG_SYSTEM="/dev/null")
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True, env=env).stdout


def run(*args):
    return subprocess.run([sys.executable, str(PACKAGE), *args], capture_output=True, text=True)


if subprocess.run(["which", "readelf"], capture_output=True).returncode != 0:
    sys.exit("test-package: readelf (binutils) is required, as for package.py itself")


def roles_manifest(binaries, commit, drop=(), bad_pin=None):
    manifest = {"sourceCommit": commit, "origin": "test-package", "sha256": {}}
    for role, name in ROLE_FILES.items():
        if role in drop:
            continue
        manifest[role] = str(binaries / name)
        manifest["sha256"][role] = sha(binaries / name)
    if bad_pin:
        manifest["sha256"][bad_pin] = "0" * 64
    return manifest


with tempfile.TemporaryDirectory(prefix="package-test-") as tmp:
    tmp = Path(tmp)
    repo = tmp / "repo"
    for rel in SCRIPTS:
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        (repo / rel).write_text(f"stub {rel}\n")
    git(repo, "init", "-q")
    git(repo, "add", "-A")
    git(repo, "commit", "-q", "-m", "stub")
    commit = git(repo, "rev-parse", "HEAD").decode().strip()
    archive = tmp / "source.tar"
    archive.write_bytes(git(repo, "archive", "--format=tar", commit))
    toolchains = tmp / "toolchains.json"
    toolchains.write_text(json.dumps({"rustc": "rustc test\ncommit-hash: test\nhost: test\nrelease: test\nLLVM version: test",
        "buildFlags": {"rust": {"profile": "release"}, "native": {"builder": "test stub"}}}))
    binaries = tmp / "built"
    binaries.mkdir()
    for name in ROLE_FILES.values():
        (binaries / name).write_text(f"stub binary {name}\n")  # not an ELF: abi() skips it

    def package(manifest, out):
        roles = tmp / (out + ".roles.json")
        roles.write_text(json.dumps(manifest))
        return subprocess.run([sys.executable, str(PACKAGE), "--roles", str(roles), "--source-archive", str(archive),
                               "--out", str(tmp / out), "--toolchains", str(toolchains)],
                              cwd=repo, capture_output=True, text=True)

    # 1. the full set
    done = package(roles_manifest(binaries, commit), "cand")
    check("full role set packages", done.returncode == 0, done.stderr)
    cand = tmp / "cand"
    if done.returncode == 0:
        prov = json.loads((cand / "provenance.json").read_text())
        consent = prov["binaries"].get("consent", {})
        check("provenance .binaries.consent pins bin/minidregg-client-consent",
              consent.get("path") == "bin/minidregg-client-consent"
              and consent.get("sha256") == sha(cand / "bin/minidregg-client-consent"))
        linux = prov["clients"]["x86_64-unknown-linux-gnu"]["consent"] or {}
        check("provenance .clients[linux].consent names both executables and their pins",
              linux.get("consentHost", {}).get("sha256") == consent.get("sha256")
              and linux.get("localHost", {}).get("sha256") == prov["binaries"]["host"]["sha256"]
              and linux.get("consentHost", {}).get("env") == "MINI_CONSENT_HOST"
              and linux.get("localHost", {}).get("env") == "MINI_LOCAL_HOST")
        bundle = cand / "bin/clients/x86_64-unknown-linux-gnu"
        names = sorted(p.name for p in bundle.iterdir())
        check("friend bundle holds exactly the five executables", names == sorted(
            ["mini", "minidregg-host", "minidregg-client-consent",
             "minidregg-credential-signature-verifier", "minidregg-link-sqlite-store"]), str(names))
        check("friend bundle files are hard links of bin/",
              all(os.path.samefile(bundle / n, cand / "bin" / n) for n in names if (cand / "bin" / n).exists()))
        sums = dict((line.split("  ", 1)[1], line.split("  ", 1)[0])
                    for line in (cand / "SHA256SUMS").read_text().splitlines())
        check("SHA256SUMS lists the consent binary and every bundle file",
              "bin/minidregg-client-consent" in sums
              and all(f"bin/clients/x86_64-unknown-linux-gnu/{n}" in sums for n in names))
        check("SHA256SUMS verifies", all(sha(cand / rel) == digest for rel, digest in sums.items()))
        manifest = json.loads((cand / "manifest.json").read_text())
        check("manifest.json names consentHost with its pin",
              manifest.get("consentHost") == str(cand / "bin/minidregg-client-consent")
              and manifest["sha256"].get("consentHost") == consent.get("sha256"))

        check("v2 manifest pins every shipped file with build identity",
              manifest.get("type") == "minidregg-candidate-manifest-v2" and
              set(manifest["outputs"]) == {str(p.relative_to(cand)) for p in (cand / "bin").rglob("*") if p.is_file()} and
              all(v["sha256"] == sha(cand / rel) and v["build"]["sourceTree"] ==
                  git(repo, "rev-parse", "HEAD^{tree}").decode().strip() and
                  v["build"]["cargoLockSha256"]["Cargo.lock"] == sha(repo / "Cargo.lock")
                  for rel, v in manifest["outputs"].items()))
        # Missing builder evidence must refuse, not invent provenance from the current machine.
        no_evidence = run("--roles", str(tmp / "cand.roles.json"), "--source-archive", str(archive),
                          "--out", str(tmp / "no-evidence"))
        check("missing build evidence is refused", no_evidence.returncode != 0 and
              "requires the builder's rustc -vV" in no_evidence.stderr)

        def library(command, file):
            return subprocess.run(["sh", "-eu", "-c",
                                   '. "$1"; CANDIDATE_DIR=$2; ' + command,
                                   "test", str(HERE / "lib.sh"), str(cand), str(file)],
                                  capture_output=True, text=True)

        for label, value in (("missing", {}), ("empty", {"outputs": {}}),
                             ("null", {"outputs": None})):
            bad = tmp / (label + "-outputs.json")
            bad.write_text(json.dumps(value))
            refused = library('candidate_verify_outputs "$3"', bad)
            check(label + " outputs explicitly refuse in verifier", refused.returncode != 0 and
                  "manifest .outputs must be a nonempty object" in refused.stderr, refused.stderr)

        # Consent is selected from its output entry, not a fixed filename in bin/.
        old_rel, new_rel = "bin/minidregg-client-consent", "bin/selected-consent"
        os.rename(cand / old_rel, cand / new_rel)
        prov["outputs"][new_rel] = prov["outputs"].pop(old_rel)
        prov["binaries"]["consent"]["path"] = new_rel
        manifest["outputs"] = prov["outputs"]
        manifest["consent"] = manifest["consentHost"] = str(cand / new_rel)
        (cand / "provenance.json").write_text(json.dumps(prov))
        manifest["sha256"]["candidate"] = sha(cand / "provenance.json")
        (cand / "manifest.json").write_text(json.dumps(manifest))
        resolved = library('candidate_resolve "$3"; candidate_verify_outputs "$3"; printf "%s" "$CONSENT"',
                           cand / "manifest.json")
        check("consent resolves through its listed output", resolved.returncode == 0 and
              resolved.stdout == str(cand / new_rel), resolved.stderr)

        # Keep an existing executable on disk but remove its output entry and both
        # role pins. Null == null must never count as membership or a valid pin.
        del prov["outputs"][new_rel]
        prov["binaries"]["consent"]["sha256"] = None
        manifest["sha256"]["consent"] = None
        (cand / "provenance.json").write_text(json.dumps(prov))
        manifest["sha256"]["candidate"] = sha(cand / "provenance.json")
        (cand / "manifest.json").write_text(json.dumps(manifest))
        refused = library('candidate_resolve "$3"', cand / "manifest.json")
        check("unlisted consent executable refuses even with null role pins", refused.returncode != 0 and
              "manifest output identity is incomplete" in refused.stderr, refused.stderr)

    # 2. no consent role: refused by name
    refused = package(roles_manifest(binaries, commit, drop=("consent",)), "cand-no-consent")
    check("a role set without consent is refused, naming consent",
          refused.returncode != 0 and "consent" in refused.stderr and not (tmp / "cand-no-consent").exists(),
          refused.stderr)

    # 2b. no key broker: refused by name (split tenancy cannot install without it)
    nokeys = package(roles_manifest(binaries, commit, drop=("keys",)), "cand-no-keys")
    check("a role set without keys is refused, naming keys",
          nokeys.returncode != 0 and "keys" in nokeys.stderr and not (tmp / "cand-no-keys").exists(),
          nokeys.stderr)

    # 2c. a builder that dropped an optional role (spkBroker) is refused: the role list drifted
    drift = package(roles_manifest(binaries, commit, drop=("spkBroker",)), "cand-drift")
    check("a builder role set missing spkBroker is refused, naming it",
          drift.returncode != 0 and "spkBroker" in drift.stderr and not (tmp / "cand-drift").exists(),
          drift.stderr)

    # 3. wrong commit: refused (control)
    wrong = package(roles_manifest(binaries, "1" * 40), "cand-wrong-commit")
    check("a roles manifest for another commit is refused, naming the commit",
          wrong.returncode != 0 and "source archive commit is not" in wrong.stderr, wrong.stderr)

    # 4. a pin that is not the bytes: refused (control)
    pinned = package(roles_manifest(binaries, commit, bad_pin="consent"), "cand-bad-pin")
    check("a consent pin that is not the bytes is refused", pinned.returncode != 0
          and "consent" in pinned.stderr, pinned.stderr)

if failures:
    print(f"{len(failures)} FAILED: " + "; ".join(failures))
    sys.exit(1)
print("all package.py checks passed")
