#!/usr/bin/env python3
"""Stage an actual operator-authorized carry of a stopped carry-source fixture.

No builds or live service switches. The old fixture must remain stopped. Artifact
paths are pinned independently; neither the request nor new endpoint chooses the
operator key. Produces the actual signed edge/registry for the separate client
adoption journey. Does not claim that staging establishes client continuity.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey


def digest(path):
    with Path(path).open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def write_json(path, value):
    # Python integers preserve the original arbitrary-width JSON integer values.
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--target-host", required=True, type=Path)
    parser.add_argument("--target-store", required=True, type=Path)
    parser.add_argument("--run", required=True, type=Path)
    args = parser.parse_args()
    os.umask(0o077)
    source = args.source.resolve(strict=True)
    host = args.target_host.resolve(strict=True)
    store = args.target_store.resolve(strict=True)
    run = args.run.absolute()
    if run.exists() or run.is_symlink():
        raise SystemExit("refusing existing run directory")
    socket_directory = Path((source / "socket-directory.txt").read_text().strip())
    if (socket_directory / "host.sock").exists():
        raise SystemExit("source fixture is still serving")
    run.mkdir()
    (run / "logs").mkdir()
    rows = run / "rows.tsv"
    rows.write_text("step\tverdict\n")

    def invoke(label, command, refusal=False):
        result = subprocess.run([str(item) for item in command], capture_output=True)
        (run / "logs" / (label + ".out")).write_bytes(result.stdout)
        (run / "logs" / (label + ".err")).write_bytes(result.stderr)
        passed = result.returncode != 0 if refusal else result.returncode == 0
        with rows.open("a") as output:
            output.write(label + ("\tPASS\n" if passed else "\tFAIL\n"))
        if not passed:
            raise SystemExit("failed " + label + "; see private run logs")
        return result.stdout

    old_config_path = source / "deployment" / "pinned-config.json"
    old_config = json.loads(old_config_path.read_text())
    provenance = (source / "provenance.sha256").read_text().splitlines()
    old_host = Path(provenance[0].split("  ", 1)[1])
    for line in provenance:
        expected, artifact = line.split("  ", 1)
        if digest(artifact) != expected:
            raise SystemExit("retained source artifact changed")
    signature = Path(old_config["signatureBinary"])
    old_store = Path(old_config["storageBinary"])
    old_profile_path = run / "source-profile.json"
    old_profile_path.write_bytes(invoke("source-profile", [old_host, old_config_path, "profile"]))
    invoke("source-audit", [old_host, old_config_path, "audit"])

    operator = Ed25519PrivateKey.generate()
    (run / "operator.key").write_bytes(operator.private_bytes(
        serialization.Encoding.Raw, serialization.PrivateFormat.Raw, serialization.NoEncryption()))
    public = operator.public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw).hex()
    (run / "operator.pub").write_text(public + "\n")
    target_config = dict(old_config)
    target_config.update(storageBinary=str(store), storageRoot=str(run / "target-store"),
                         checkpointKey=str(run / "checkpoint.key"), birthSlack=0,
                         carryRegistry=str(run / "registry.json"), carryOperatorKey=public)
    (run / "checkpoint.key").write_bytes(os.urandom(32))
    config_path = run / "target-config.json"
    write_json(config_path, target_config)
    target_profile_path = run / "target-profile.json"
    target_profile_path.write_bytes(invoke("target-profile", [host, config_path, "profile"]))

    def capsule(binary, config_file, config, profile_file, storage):
        profile = json.loads(profile_file.read_text())
        return dict(host=str(binary), configuration=str(config_file), profile=str(profile_file),
                    signatureVerifier=str(signature), storageBinary=str(storage),
                    storageRoot=config["storageRoot"], checkpointKey=config["checkpointKey"],
                    identity=dict(algorithm="minidregg-continuity-v1",
                                  domain=profile["domain"], semantics=profile["semantics"],
                                  expectedSeed=profile["expectedSeed"]),
                    pins=dict(host=digest(binary), storageHelper=digest(storage),
                              signatureVerifier=digest(signature), configuration=digest(config_file),
                              profile=digest(profile_file)))

    request = dict(algorithm="minidregg-neutral-policy-carry-v1", nonce=os.urandom(32).hex(),
                   source=capsule(old_host, old_config_path, old_config, old_profile_path, old_store),
                   target=capsule(host, config_path, target_config, target_profile_path, store))
    request_path = run / "request.json"
    write_json(request_path, request)
    plan_path = run / "plan.json"
    invoke("actual-plan", [host, config_path, "carry-plan", request_path, plan_path])
    plan = json.loads(plan_path.read_text())
    edge = plan["edge"]
    edge["signature"] = operator.sign(bytes.fromhex(plan["signingBytes"])).hex()
    edge_path = run / "edge.json"
    write_json(edge_path, edge)
    bad = dict(edge, signature="00" * 64)
    bad_path = run / "bad-signature.json"
    write_json(bad_path, bad)
    invoke("wrong-operator-signature-refused", [host, config_path, "carry-receive",
           request_path, bad_path, run / "bad-result.json"], refusal=True)
    if (run / "target-store").exists():
        raise SystemExit("refused signature created staged Store")
    staged_path = run / "staged.json"
    invoke("actual-receive", [host, config_path, "carry-receive", request_path, edge_path, staged_path])
    staged = json.loads(staged_path.read_text())
    write_json(run / "registry.json", staged["registry"])
    invoke("target-audit", [host, config_path, "audit"])
    invoke("exact-stage-resume", [host, config_path, "carry-receive", request_path,
                                 edge_path, run / "resumed.json"])
    if json.loads((run / "resumed.json").read_text()) != staged:
        raise SystemExit("exact resumed carry changed result")
    artifacts = [host, store, signature, config_path, old_config_path, old_profile_path,
                 target_profile_path, request_path, edge_path, Path(__file__).resolve()]
    (run / "provenance.sha256").write_text("".join(
        digest(path) + "  " + str(path) + "\n" for path in artifacts))
    print(run)


if __name__ == "__main__":
    main()
