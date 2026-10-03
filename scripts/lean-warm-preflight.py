#!/usr/bin/env python3
"""Read-only preflight for a frozen, topologically ordered scoped Lean build.

This checks source pins and the actual first-namespace-root lookup, not merely
whether an olean exists somewhere on LEAN_PATH. It never builds or repairs files.
Warm manifest entries must contain module/path/sha256; CHECK-MANIFEST contains
imports/source_sha256/affected_topological. --completed is a newline module list
whose outputs were produced from this same frozen source manifest.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def resolve(module, roots):
    relative = Path(*module.split('.')).with_suffix('.olean')
    namespace = module.split('.')[0]
    for root in roots:
        # Lean chooses a package/namespace root before opening a module file.
        if (root / namespace).is_dir() or (root / (namespace + '.olean')).is_file():
            candidate = root / relative
            return candidate if candidate.is_file() else None, root
    return None, None


def inspect(manifest, warm, source, output, roots, completed=()):
    errors = []
    modules = manifest['imports']
    order = manifest['affected_topological']
    affected = set(order)
    if len(affected) != len(order):
        errors.append('duplicate scheduled module')
    warm_by = {x['module']: x for x in warm}
    positions = {x: i for i, x in enumerate(order)}
    completed = set(completed)
    for module, expected in manifest['source_sha256'].items():
        path = source / Path(*module.split('.')).with_suffix('.lean')
        try:
            if digest(path) != expected:
                errors.append('SOURCE_DRIFT ' + module)
        except OSError as exc:
            errors.append('SOURCE_MISSING ' + module + ': ' + str(exc))
    for module in sorted(set(modules) - affected):
        entry = warm_by.get(module)
        if not entry:
            errors.append('UNPINNED_WARM ' + module)
            continue
        actual, root = resolve(module, roots)
        if actual is None:
            errors.append('NAMESPACE_SHADOW_OR_MISSING ' + module + ' selected=' + str(root))
            continue
        try:
            if digest(entry['path']) != entry['sha256'] or digest(actual) != entry['sha256']:
                errors.append('WARM_HASH_MISMATCH ' + module)
        except OSError as exc:
            errors.append('WARM_MISSING ' + module + ': ' + str(exc))
    for module in order:
        for dep in modules[module]:
            if dep in affected and positions[dep] >= positions[module]:
                errors.append('BAD_ORDER ' + module + ' imports ' + dep)
        # Output must resolve in the writable owned root when it is produced.
        namespace = module.split('.')[0]
        selected = next((r for r in roots if r == output or (r / namespace).is_dir()), None)
        if selected != output:
            errors.append('OUTPUT_SHADOW ' + module + ' selected=' + str(selected))
    for module in sorted(completed):
        if module not in affected:
            errors.append('UNKNOWN_COMPLETED ' + module)
        actual, _ = resolve(module, roots)
        expected_path = output / Path(*module.split('.')).with_suffix('.olean')
        if actual != expected_path or not expected_path.is_file() or expected_path.is_symlink():
            errors.append('COMPLETED_OUTPUT_MISSING_OR_FOREIGN ' + module)
    external = sorted({d for deps in modules.values() for d in deps} - set(modules))
    for module in external:
        actual, root = resolve(module, roots)
        if actual is None:
            errors.append('EXTERNAL_MISSING ' + module + ' selected=' + str(root))
    return {'verdict': 'PASS' if not errors else 'ENVFAULT',
            'scope': 'Frozen source/import setup only; not source elaboration or qualification',
            'sourceModules': len(modules), 'scheduledModules': len(order),
            'warmModules': len(set(modules) - affected), 'externalModules': len(external),
            'completedModules': len(completed), 'errors': errors}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--warm-manifest', type=Path, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean-path', default=os.environ.get('LEAN_PATH', ''))
    parser.add_argument('--completed', type=Path)
    args = parser.parse_args()
    roots = [Path(p) for p in args.lean_path.split(os.pathsep) if p]
    completed = args.completed.read_text().splitlines() if args.completed else []
    result = inspect(json.loads(args.manifest.read_text()),
                     json.loads(args.warm_manifest.read_text()),
                     args.source, args.output, roots, completed)
    print(json.dumps(result, indent=2))
    return 0 if result['verdict'] == 'PASS' else 2


if __name__ == '__main__':
    raise SystemExit(main())
