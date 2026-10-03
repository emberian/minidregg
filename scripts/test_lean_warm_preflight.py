"""Narrow regressions for the scoped Lean import preflight; no Lean build."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    'preflight', Path(__file__).with_name('lean-warm-preflight.py'))
preflight = importlib.util.module_from_spec(spec)
spec.loader.exec_module(preflight)


class WarmLookupTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='lean-warm-test-')
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.source, self.output, self.warm = [root / x for x in ('source', 'owned', 'warm')]
        for directory in (self.source, self.output, self.warm):
            (directory / 'Theory').mkdir(parents=True)
        (self.source / 'Theory/A.lean').write_text('import Theory.B\n')
        (self.source / 'Theory/B.lean').write_text('def b := 1\n')
        self.artifact = self.warm / 'Theory/B.olean'
        self.artifact.write_bytes(b'pinned')
        self.manifest = {
            'imports': {'Theory.A': ['Theory.B'], 'Theory.B': []},
            'affected_topological': ['Theory.A'],
            'source_sha256': {n: preflight.digest(self.source / (n.replace('.', '/') + '.lean'))
                              for n in ('Theory.A', 'Theory.B')},
        }
        self.pins = [{'module': 'Theory.B', 'path': str(self.artifact),
                      'sha256': preflight.digest(self.artifact)}]

    def inspect(self):
        return preflight.inspect(self.manifest, self.pins, self.source,
                                 self.output, [self.output, self.warm])

    def link(self):
        (self.output / 'Theory/B.olean').symlink_to(self.artifact)

    def test_empty_namespace_hides_later_warm_module(self):
        self.assertTrue(any('NAMESPACE_SHADOW' in x for x in self.inspect()['errors']))

    def test_exact_symlink_closes_lookup(self):
        self.link()
        self.assertEqual(self.inspect()['verdict'], 'PASS')

    def test_mutated_warm_artifact_refuses(self):
        self.link()
        self.artifact.write_bytes(b'changed')
        self.assertTrue(any('WARM_HASH_MISMATCH' in x for x in self.inspect()['errors']))

    def test_source_changed_after_manifest_refuses(self):
        self.link()
        (self.source / 'Theory/A.lean').write_text('def a := 2\n')
        self.assertTrue(any('SOURCE_DRIFT' in x for x in self.inspect()['errors']))


if __name__ == '__main__':
    unittest.main()
