#!/usr/bin/env python3
"""Bounded scoped Lean DAG runner. No lake, dependency downloads or cache deletion.

Run inside an aggregate resource guardian. A frozen manifest determines every
module. Failed nodes block dependents, not independent branches. The checkpoint
is a source/input/artifact pin, never a claim inferred from file presence.
"""
import argparse
import concurrent.futures
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import time

_HASH_CACHE = {}


def sha(path):
    path = Path(path)
    before = path.stat()
    signature = (before.st_dev, before.st_ino, before.st_size,
                 before.st_mtime_ns, before.st_ctime_ns)
    cached = _HASH_CACHE.get(str(path))
    if cached and cached[0] == signature:
        return cached[1]
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    after = path.stat()
    if signature != (after.st_dev, after.st_ino, after.st_size,
                     after.st_mtime_ns, after.st_ctime_ns):
        raise ValueError('Artifact changed while hashing: ' + str(path))
    value = digest.hexdigest()
    _HASH_CACHE[str(path)] = (signature, value)
    return value


def encoded_sha(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + '.tmp')
    with temp.open('w') as out:
        json.dump(value, out, indent=2, sort_keys=True)
        out.write('\n')
        out.flush()
        os.fsync(out.fileno())
    os.replace(temp, path)


def module_path(module, suffix):
    parts = module.split('.')
    if not parts or any(not p or p in ('.', '..') or '/' in p or '\\' in p for p in parts):
        raise ValueError('Unsafe module name: ' + module)
    return Path(*parts).with_suffix(suffix)


def lookup(module, roots):
    top = module.split('.')[0]
    for root in roots:
        if (root / top).is_dir() or (root / (top + '.olean')).is_file():
            path = root / module_path(module, '.olean')
            if not path.is_file():
                raise ValueError('namespace shadows missing import: ' + str(path))
            return path
    raise ValueError('missing import: ' + module)


def artifact_set(path):
    """Private/server companions participate when this Lean invocation emits them."""
    return [p for p in (path, Path(str(path) + '.private'), Path(str(path) + '.server'),
                        path.with_suffix('.ir'), path.with_suffix('.ilean'))
            if p.is_file()]


class Runner:
    def __init__(self, args):
        self.args = args
        self.source, self.output, self.c_output = args.source, args.output, args.c_output
        if (self.output.parent / 'COHORT.json').exists():
            raise ValueError('Refusing to compile into exported immutable cohort')
        self.roots = [Path(p) for p in args.lean_path.split(os.pathsep) if p]
        if not self.roots or self.roots[0] != self.output:
            raise ValueError('Owned output must be first LEAN_PATH root')
        self.manifest = json.loads(args.manifest.read_text())
        self.imports = self.manifest['imports']
        self.order = self.manifest['affected_topological']
        self.affected = set(self.order)
        if len(self.order) != len(self.affected):
            raise ValueError('Duplicate scheduled module')
        self.source_pins = self.manifest['source_sha256']
        self.warm = {x['module']: x for x in json.loads(args.warm_manifest.read_text())}
        self.tool_pin = sha(args.lean)
        self.external_pins = {}
        self.fingerprints = {}
        self.states = {}
        self.entries = {}
        self.old = json.loads(args.checkpoint.read_text()) if args.checkpoint.exists() else {}
        if self.old and self.old.get('schema') != 1:
            raise ValueError('Unsupported checkpoint schema')
        self.old_entries = self.old.get('modules', {})
        self.started = time.monotonic()
        self.run = args.runs / (datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S') + '-' + str(os.getpid()))
        self.run.mkdir(parents=True, exist_ok=False)

    def pin_external(self, module, active=None):
        if module in self.external_pins:
            return self.external_pins[module]
        path = lookup(module, self.roots)
        bundle = {str(p): sha(p) for p in artifact_set(path)}
        # External warm roots are a separately qualified, immutable prerequisite.
        # Do not recursively re-read all of Mathlib on every tiny resume; .ilean
        # metadata is also not the authoritative binary import closure. Placement
        # validates that closure once with Lean.readModuleData. Pin direct imported
        # bundles here and keep their producer roots read-only for the whole run.
        pin = encoded_sha({'artifacts': bundle, 'toolchain': self.tool_pin})
        self.external_pins[module] = pin
        return pin

    def fingerprint(self, module, active=None):
        if module in self.fingerprints:
            return self.fingerprints[module]
        if module not in self.imports:
            return self.pin_external(module)
        active = set() if active is None else active
        if module in active:
            raise ValueError('Source import cycle: ' + module)
        active.add(module)
        deps = [(d, self.fingerprint(d, active)) for d in self.imports[module]]
        active.remove(module)
        value = {'module': module, 'source': self.source_pins[module],
                 'dependencies': deps, 'toolchain': self.tool_pin}
        if module not in self.affected:
            entry = self.warm.get(module)
            if not entry:
                raise ValueError('No qualified warm pin: ' + module)
            actual = lookup(module, self.roots)
            if sha(entry['path']) != entry['sha256'] or sha(actual) != entry['sha256']:
                raise ValueError('Warm artifact drift: ' + module)
            value['warmArtifacts'] = {str(p): sha(p) for p in artifact_set(actual)}
        self.fingerprints[module] = encoded_sha(value)
        return self.fingerprints[module]

    def preflight(self):
        positions = {module: i for i, module in enumerate(self.order)}
        for module in self.order:
            for dep in self.imports[module]:
                if dep in positions and positions[dep] >= positions[module]:
                    raise ValueError('Manifest is not topological: ' + module + ' imports ' + dep)
        for module, expected in self.source_pins.items():
            if sha(self.source / module_path(module, '.lean')) != expected:
                raise ValueError('Frozen source drift: ' + module)
        for module in self.order:
            output = self.output / module_path(module, '.olean')
            if output.is_symlink():
                raise ValueError('Selected output is warm dependency symlink: ' + str(output))
            self.fingerprint(module)
            old = self.old_entries.get(module)
            reusable = bool(old and old.get('producerExit') == 0
                            and old.get('inputFingerprint') == self.fingerprints[module])
            if reusable:
                required = {str(output), str(self.c_output / module_path(module, '.c'))}
                artifacts = old.get('artifacts', {})
                reusable = required <= set(artifacts)
                for path, expected in artifacts.items():
                    q = Path(path)
                    if not q.is_file() or q.is_symlink() or sha(q) != expected:
                        reusable = False
                        break
                if reusable and old.get('dependencyArtifacts') != self.dependency_artifacts(module):
                    reusable = False
            if reusable:
                self.entries[module] = old
                self.states[module] = 'REUSED'
            else:
                self.states[module] = 'PENDING'
        # Never reuse a dependent while a producer is being rebuilt, even if
        # its source fingerprint is unchanged (its previous artifact may be bad).
        for module in self.order:
            if self.states[module] == 'REUSED' and any(
                    dep in self.affected and self.states[dep] != 'REUSED'
                    for dep in self.imports[module]):
                self.states[module] = 'PENDING'
                self.entries.pop(module, None)
        save(self.run / 'preflight.json', {'verdict': 'PASS', 'manifestSha256': sha(self.args.manifest),
             'toolchainSha256': self.tool_pin, 'warmModules': len(self.warm),
             'externalPinnedModules': len(self.external_pins),
             'externalScope': 'Direct imports in prequalified immutable warm roots; not a new transitive closure qualification',
             'states': self.states})

    def dependency_artifacts(self, module):
        result = {}
        for dep in self.imports[module]:
            try:
                result[dep] = {str(p): sha(p) for p in artifact_set(lookup(dep, self.roots))}
            except (ValueError, OSError):
                result[dep] = None
        return result

    def compile(self, module):
        leaf = self.run / 'modules' / module
        leaf.mkdir(parents=True)
        stage = leaf / 'staging'
        stage.mkdir()
        olean, c_file = stage / module_path(module, '.olean'), stage / module_path(module, '.c')
        olean.parent.mkdir(parents=True, exist_ok=True)
        c_file.parent.mkdir(parents=True, exist_ok=True)
        status = {'module': module, 'state': 'RUNNING', 'inputFingerprint': self.fingerprints[module],
                  'sourceSha256': self.source_pins[module], 'startedUTC': datetime.datetime.now(datetime.timezone.utc).isoformat()}
        status['dependencyArtifacts'] = self.dependency_artifacts(module)
        save(leaf / 'status.json', status)
        command = [str(self.args.lean), '-o', str(olean), '-c', str(c_file), str(module_path(module, '.lean'))]
        env = dict(os.environ, LEAN_PATH=self.args.lean_path, LEAN_NUM_THREADS=str(self.args.threads))
        try:
            if sha(self.source / module_path(module, '.lean')) != self.source_pins[module]:
                raise ValueError('Source changed after preflight')
            with (leaf / 'compiler.log').open('wb') as log:
                child = subprocess.Popen(command, cwd=self.source, env=env, stdout=log,
                                         stderr=subprocess.STDOUT, start_new_session=True,
                                         pass_fds=((self.args.lock_fd,) if getattr(self.args, 'lock_fd', None) is not None else ()))
                status['pid'] = child.pid
                save(leaf / 'status.json', status)
                try:
                    code = child.wait(timeout=self.args.module_timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGTERM)
                    try:
                        child.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL)
                        child.wait()
                    status.update(state='TIMEOUT', producerExit=None)
                    save(leaf / 'status.json', status)
                    return status
            status['producerExit'] = code
            if code < 0:
                status.update(state='ENVFAULT', reason='Compiler terminated by signal; inspect resource/toolchain guardian before inferring source failure')
            elif code:
                status['state'] = 'FAIL'
            elif not olean.is_file() or not c_file.is_file():
                status.update(state='ENVFAULT', reason='Compiler exit0 without full olean/C artifact set')
            elif sha(self.source / module_path(module, '.lean')) != self.source_pins[module]:
                status.update(state='ENVFAULT', reason='Source changed during compilation')
            elif status['dependencyArtifacts'] != self.dependency_artifacts(module):
                status.update(state='ENVFAULT', reason='Imported artifact changed during compilation')
            else:
                status.update(state='PASS', artifacts=self.publish(module, stage, olean, c_file, leaf))
        except Exception as exc:
            status.update(state='ENVFAULT', reason=str(exc))
        status['finishedUTC'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save(leaf / 'status.json', status)
        return status

    def publish(self, module, stage, olean, c_file, leaf):
        destinations = {p: self.output / p.relative_to(stage) for p in artifact_set(olean)}
        destinations[c_file] = self.c_output / c_file.relative_to(stage)
        # Preserve old files. Stage and output may be on different
        # filesystems (/tank versus /home), so copy into a same-directory
        # temporary file before each atomic replacement. Consumers start
        # only after ALL artifact publications complete.
        old_dir = leaf / 'previous'
        old_files = artifact_set(self.output / module_path(module, '.olean')) + [self.c_output / module_path(module, '.c')]
        for old in old_files:
            if old.exists():
                if old.is_symlink():
                    raise ValueError('Refusing to replace dependency symlink: ' + str(old))
                old_dir.mkdir(exist_ok=True)
                shutil.copy2(old, old_dir / old.name)
        for new, dest in destinations.items():
            dest.parent.mkdir(parents=True, exist_ok=True)
            temporary = dest.with_name('.' + dest.name + '.dag-' + self.run.name)
            with new.open('rb') as source, temporary.open('xb') as target:
                shutil.copyfileobj(source, target, 1024 * 1024)
            os.replace(temporary, dest)
        for old in old_files:
            if old.exists() and old not in destinations.values():
                retired = old.parent / '.dag-retired' / self.run.name
                retired.mkdir(parents=True, exist_ok=True)
                os.replace(old, retired / old.name)
        return {str(p): sha(p) for p in destinations.values()}

    def hold_unchanged_failures(self, prior):
        """Explicitly retain exact prior source failures while independent work runs."""
        held = {}
        for module in self.order:
            path = prior / 'modules' / module / 'status.json'
            if self.states[module] != 'PENDING' or not path.is_file():
                continue
            result = json.loads(path.read_text())
            if (result.get('state') == 'FAIL' and (result.get('producerExit') or 0) > 0
                    and result.get('inputFingerprint') == self.fingerprints[module]
                    and result.get('sourceSha256') == self.source_pins[module]
                    and result.get('dependencyArtifacts') == self.dependency_artifacts(module)):
                self.states[module] = 'FAIL'
                held[module] = str(path)
        save(self.run / 'held-unchanged-failures.json', held)
        print('LEAN DAG RETAINED SOURCE FAILURES ' + str(len(held)), flush=True)

    def recover(self, prior):
        """Adopt only known successful compiles whose publication failed with EXDEV."""
        recovered = []
        for module in self.order:
            leaf = prior / 'modules' / module
            status_path = leaf / 'status.json'
            if self.states[module] != 'PENDING' or not status_path.is_file():
                continue
            status = json.loads(status_path.read_text())
            if (status.get('producerExit') != 0 or status.get('state') != 'ENVFAULT'
                    or 'Invalid cross-device link' not in status.get('reason', '')
                    or status.get('inputFingerprint') != self.fingerprints[module]
                    or status.get('sourceSha256') != self.source_pins[module]
                    or status.get('dependencyArtifacts') != self.dependency_artifacts(module)):
                continue
            if any(self.states[d] not in ('PASS', 'REUSED') for d in self.imports[module] if d in self.affected):
                continue
            stage = leaf / 'staging'
            olean = stage / module_path(module, '.olean')
            c_file = stage / module_path(module, '.c')
            if not olean.is_file() or not c_file.is_file():
                continue
            frozen = {str(p): sha(p) for p in artifact_set(olean) + [c_file]}
            save(self.run / ('recover-' + module + '.json'), {'priorStatus': status, 'stagedArtifacts': frozen})
            artifacts = self.publish(module, stage, olean, c_file, leaf)
            if any(sha(p) != digest for p, digest in frozen.items()):
                raise ValueError('Recovered staging changed: ' + module)
            result = dict(status, state='PASS', artifacts=artifacts,
                          recoveredFrom=str(status_path), recoveredBy=str(self.run))
            result.pop('reason', None)
            self.entries[module] = result
            self.states[module] = 'REUSED'
            recovered.append(module)
            self.checkpoint()
        print('LEAN DAG RECOVERED ' + str(len(recovered)), flush=True)

    def export_complete(self):
        target = getattr(self.args, 'export_complete', None)
        if not target:
            return
        target.mkdir(parents=True, exist_ok=False)
        records = []
        # Copy, never hardlink: a later compiler may truncate an owned output.
        for module in self.imports:
            source = self.source / module_path(module, '.lean')
            if sha(source) != self.source_pins[module]:
                raise ValueError('Source drift before cohort export: ' + module)
            pairs = [(source, target / 'src' / module_path(module, '.lean'))]
            for artifact in artifact_set(lookup(module, self.roots)):
                pairs.append((artifact, target / 'olean' / module_path(module, '.olean').parent / artifact.name))
            c_file = self.c_output / module_path(module, '.c')
            if module in self.affected:
                pairs.append((c_file, target / 'c' / module_path(module, '.c')))
            for original, dest in pairs:
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(original, dest)
                dest.chmod(0o444)
                records.append({'path': str(dest.relative_to(target)), 'sha256': sha(dest)})
        save(target / 'COHORT.json', {'schema': 1, 'state': 'COMPLETE',
             'manifest': self.manifest, 'toolchainSha256': self.tool_pin,
             'externalPins': self.external_pins, 'artifacts': records,
             'qualification': 'Scoped compilation cohort, not native receiving or protocol qualification'})
        (target / 'COHORT.json').chmod(0o444)

    def checkpoint(self):
        save(self.args.checkpoint, {'schema': 1, 'manifestSha256': sha(self.args.manifest),
             'toolchainSha256': self.tool_pin, 'modules': self.entries})
        save(self.run / 'summary.json', {'states': self.states, 'checkpoint': str(self.args.checkpoint)})

    def execute(self):
        self.preflight()
        if getattr(self.args, 'recover_run', None):
            self.recover(self.args.recover_run)
        if getattr(self.args, 'hold_failures_from', None):
            self.hold_unchanged_failures(self.args.hold_failures_from)
        if self.args.plan_only:
            print(json.dumps({'verdict': 'PLAN', 'states': self.states, 'run': str(self.run)}))
            return 0
        active = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=self.args.jobs) as pool:
            while True:
                for module in self.order:
                    if self.states[module] != 'PENDING':
                        continue
                    deps = [d for d in self.imports[module] if d in self.affected]
                    if any(self.states[d] in ('FAIL', 'ENVFAULT', 'TIMEOUT', 'BLOCKED') for d in deps):
                        self.states[module] = 'BLOCKED'
                    elif len(active) < self.args.jobs and all(self.states[d] in ('PASS', 'REUSED') for d in deps):
                        self.states[module] = 'RUNNING'
                        active[pool.submit(self.compile, module)] = module
                self.checkpoint()
                if not active:
                    if any(v == 'PENDING' for v in self.states.values()):
                        raise ValueError('Unresolvable dependency order')
                    break
                done, _ = concurrent.futures.wait(active, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in done:
                    module = active.pop(future)
                    result = future.result()
                    self.states[module] = result['state']
                    if result['state'] == 'PASS':
                        self.entries[module] = result
                    print('LEAN DAG ' + result['state'] + ' ' + module, flush=True)
        self.checkpoint()
        counts = {state: list(self.states.values()).count(state) for state in sorted(set(self.states.values()))}
        passed = all(v in ('PASS', 'REUSED') for v in self.states.values())
        if passed:
            self.export_complete()
        print(json.dumps({'verdict': 'PASS' if passed else 'FAIL', 'counts': counts, 'run': str(self.run)}))
        return 0 if passed else 1


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('manifest', 'warm-manifest', 'source', 'output', 'c-output', 'checkpoint', 'runs', 'lean'):
        p.add_argument('--' + name, required=True, type=Path)
    p.add_argument('--lean-path', required=True)
    p.add_argument('--jobs', type=int, required=True)
    p.add_argument('--threads', type=int, required=True)
    p.add_argument('--module-timeout', type=int, default=300)
    p.add_argument('--plan-only', action='store_true')
    p.add_argument('--recover-run', type=Path)
    p.add_argument('--hold-failures-from', type=Path, help='Retain exact unchanged source failures; does not hold ENVFAULT or TIMEOUT')
    p.add_argument('--export-complete', type=Path,
                   help='New immutable copy cohort, emitted only after every scheduled module passes')
    args = p.parse_args()
    if args.jobs < 1 or args.threads < 1 or args.module_timeout < 1:
        p.error('jobs, threads and module-timeout must be positive')
    args.output.mkdir(parents=True, exist_ok=True)
    with (args.output / '.scoped-dag.lock').open('a') as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print('ENVFAULT: another DAG runner owns this output root')
            return 2
        try:
            args.lock_fd = lock.fileno()
            return Runner(args).execute()
        except Exception as exc:
            print('ENVFAULT: ' + str(exc), flush=True)
            return 2


if __name__ == '__main__':
    raise SystemExit(main())
