#!/usr/bin/env python3
"""Verify the exact tested dependency slice and attach it to the portable manifest.

Does not rewrite a manifest, download code, mutate Bread, or build anything.
The exact external source slice is still required; dependencies.lock.json pins
its contents rather than pretending an arbitrary Bread checkout is equivalent.
"""
import hashlib
import json
import pathlib
import sys


def verify(root, pins):
    for relative, expected in pins.items():
        source = root / relative
        if not source.is_file():
            raise ValueError(f"missing pinned source: {relative}")
        actual = hashlib.sha256(source.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"changed pinned source: {relative}: {actual}")


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: provision.py EXACT_TESTED_BREAD_SOURCE")
    root = pathlib.Path(sys.argv[1]).resolve(strict=True)
    crate = pathlib.Path(__file__).resolve().parent
    pins = json.loads((crate / "dependencies.lock.json").read_text())["files"]
    try:
        verify(root, pins)
    except ValueError as error:
        raise SystemExit(str(error)) from error
    destination = crate.parent / "bend-proof-deps" / "bread"
    if destination.exists() or destination.is_symlink():
        if not destination.is_symlink() or destination.resolve() != root:
            raise SystemExit(f"refusing to replace existing dependency path: {destination}")
    else:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.symlink_to(root, target_is_directory=True)
    print(f"Verified {len(pins)} pinned source files; attached {destination}")
    print("Manifest and lockfile unchanged; no build launched")


if __name__ == "__main__":
    main()
