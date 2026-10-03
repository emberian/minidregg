#!/usr/bin/env python3
"""Write only this crate's manifest against an existing isolated Bread snapshot.
Does not copy, edit, download or build the dependency. Captain allocates builds.
"""
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1]).resolve(strict=True)
crate = pathlib.Path(__file__).resolve().parent
for relative in ('circuit/Cargo.toml', 'vendor/plonky3-fri-82cfad73/Cargo.toml',
                 'vendor/plonky3-challenger-82cfad73/Cargo.toml'):
    if not (root / relative).is_file():
        raise SystemExit(f'missing pinned source: {root / relative}')
q = lambda p: json.dumps(str(p))
manifest = '''[package]
name = "bend-ir2-proof"
version = "0.1.0"
edition = "2024"
publish = false

[workspace]

[dependencies]
bend-proof-entropy = { path = "../bend-proof-entropy" }
getrandom = "=0.3.4"
postcard = { version = "1", features = ["alloc"] }
'''
manifest += 'dregg-circuit = { path = ' + q(root / 'circuit') + ' }\n'
for name in ('p3-baby-bear', 'p3-batch-stark', 'p3-challenger', 'p3-commit', 'p3-dft', 'p3-field',
             'p3-fri', 'p3-merkle-tree', 'p3-symmetric', 'p3-uni-stark'):
    manifest += name + ' = { git = "https://github.com/Plonky3/Plonky3", rev = "82cfad73cd734d37a0d51953094f970c531817ec" }\n'
manifest += '\n[patch."https://github.com/Plonky3/Plonky3"]\n'
for name in ('p3-fri', 'p3-challenger'):
    directory = 'plonky3-fri-82cfad73' if name == 'p3-fri' else 'plonky3-challenger-82cfad73'
    manifest += name + ' = { path = ' + q(root / 'vendor' / directory) + ' }\n'
(crate / 'Cargo.toml').write_text(manifest)
print(f'Wrote {crate / "Cargo.toml"}; no build launched')
