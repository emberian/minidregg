"""DAG scheduling regressions with a deterministic fake compiler, no Lean build."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

RUNNER = Path(__file__).with_name('lean-scoped-dag.py')
FAKE = '''#!/usr/bin/env python3
import json,os,pathlib,sys,time
a=sys.argv; source=pathlib.Path(a[-1]); spec=json.loads(source.read_text())
fd=os.open("events.jsonl",os.O_CREAT|os.O_APPEND|os.O_WRONLY,0o600)
os.write(fd,(json.dumps(["start",source.stem,time.monotonic()])+"\\n").encode())
time.sleep(.1)
if spec.get("fail"): sys.exit(1)
for flag in ("-o","-c"):
 p=pathlib.Path(a[a.index(flag)+1]);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(source.read_text())
os.write(fd,(json.dumps(["end",source.stem,time.monotonic()])+"\\n").encode())
os.close(fd)
'''


class DagTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='lean-dag-test-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.src = self.root / 'src'
        (self.src / 'Test').mkdir(parents=True)
        self.out = self.root / 'olean'
        self.compiler = self.root / 'fake-lean'
        self.compiler.write_text(FAKE)
        self.compiler.chmod(0o700)
        self.graph = {'Test.A': [], 'Test.B': ['Test.A'], 'Test.C': []}
        for name in self.graph:
            self.write(name, {})
        (self.root / 'warm.json').write_text('[]')

    def write(self, name, spec):
        (self.src / (name.replace('.', '/') + '.lean')).write_text(json.dumps(spec))

    def run_dag(self, jobs=2, recover=None, hold=None):
        manifest = {'imports': self.graph, 'affected_topological': list(self.graph),
                    'source_sha256': {n: hashlib.sha256((self.src / (n.replace('.', '/') + '.lean')).read_bytes()).hexdigest() for n in self.graph}}
        (self.root / 'manifest.json').write_text(json.dumps(manifest))
        args = [sys.executable, str(RUNNER), '--manifest', str(self.root / 'manifest.json'),
                '--warm-manifest', str(self.root / 'warm.json'), '--source', str(self.src),
                '--output', str(self.out), '--c-output', str(self.root / 'c'),
                '--checkpoint', str(self.root / 'checkpoint.json'), '--runs', str(self.root / 'runs'),
                '--lean', str(self.compiler), '--lean-path', str(self.out),
                '--jobs', str(jobs), '--threads', '1', '--module-timeout', '5']
        if recover:
            args += ['--recover-run', str(recover)]
        if hold:
            args += ['--hold-failures-from', str(hold)]
        result = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        run = max((self.root / 'runs').iterdir(), key=lambda x: x.stat().st_mtime_ns)
        summary = json.loads((run / 'summary.json').read_text())
        return result, summary['states']

    def test_failure_blocks_only_dependents(self):
        self.write('Test.A', {'fail': True})
        result, states = self.run_dag()
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertEqual(states, {'Test.A': 'FAIL', 'Test.B': 'BLOCKED', 'Test.C': 'PASS'})

    def test_parallel_ready_nodes_then_dependent(self):
        result, states = self.run_dag()
        self.assertEqual(result.returncode, 0, result.stdout)
        events = [json.loads(l) for l in (self.src / 'events.jsonl').read_text().splitlines()]
        when = {(kind, name): stamp for kind, name, stamp in events}
        self.assertLess(when['start', 'C'], when['end', 'A'])
        self.assertGreater(when['start', 'B'], when['end', 'A'])

    def test_resume_and_transitive_invalidation(self):
        result, _ = self.run_dag()
        self.assertEqual(result.returncode, 0, result.stdout)
        _, states = self.run_dag()
        self.assertTrue(all(s == 'REUSED' for s in states.values()))
        self.write('Test.A', {'revision': 2})
        result, states = self.run_dag()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(states, {'Test.A': 'PASS', 'Test.B': 'PASS', 'Test.C': 'REUSED'})

    def test_artifact_corruption_cannot_reuse(self):
        self.run_dag()
        (self.out / 'Test/C.olean').write_text('corrupt')
        result, states = self.run_dag()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(states['Test.C'], 'PASS')

    def test_corrupt_producer_invalidates_cached_dependent(self):
        self.run_dag()
        (self.out / 'Test/A.olean').write_text('corrupt')
        result, states = self.run_dag()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(states, {'Test.A': 'PASS', 'Test.B': 'PASS', 'Test.C': 'REUSED'})

    def test_successful_staging_recovers_without_recompile(self):
        self.run_dag()
        prior = max((self.root / 'runs').iterdir(), key=lambda x: x.stat().st_mtime_ns)
        checkpoint = self.root / 'checkpoint.json'
        value = json.loads(checkpoint.read_text())
        value['modules'].pop('Test.C')
        checkpoint.write_text(json.dumps(value))
        statusfile = prior / 'modules/Test.C/status.json'
        status = json.loads(statusfile.read_text())
        status.update(state='ENVFAULT', reason='[Errno 18] Invalid cross-device link')
        statusfile.write_text(json.dumps(status))
        (self.out / 'Test/C.olean').unlink()
        (self.root / 'c/Test/C.c').unlink()
        before = (self.src / 'events.jsonl').read_text()
        result, states = self.run_dag(recover=prior)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(states['Test.C'], 'REUSED')
        self.assertEqual((self.src / 'events.jsonl').read_text(), before)
        self.assertTrue((self.out / 'Test/C.olean').exists())

    def test_explicit_unchanged_failure_holds_only_until_source_changes(self):
        self.write('Test.A', {'fail': True})
        self.run_dag()
        prior = max((self.root / 'runs').iterdir(), key=lambda x: x.stat().st_mtime_ns)
        before = (self.src / 'events.jsonl').read_text()
        result, states = self.run_dag(hold=prior)
        self.assertEqual(states, {'Test.A':'FAIL', 'Test.B':'BLOCKED', 'Test.C':'REUSED'})
        self.assertEqual((self.src / 'events.jsonl').read_text(), before)
        self.write('Test.A', {})
        result, states = self.run_dag(hold=prior)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(states['Test.A'], 'PASS')


if __name__ == '__main__':
    unittest.main()
