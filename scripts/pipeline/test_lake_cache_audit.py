"""lake-cache-audit on a synthetic shared cache: the two classes it purges and the exit codes callers rely on.

Run: cd scripts/pipeline && python3 -m unittest test_lake_cache_audit   (scripts/gates/unit-tests.tsv)
"""
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

AUDIT = Path(__file__).resolve().parent / "lake-cache-audit"


class LakeCacheAudit(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="lake-cache-audit-")
        t = Path(self.tmp.name)
        self.tree, self.cache = t / "tree", t / "cache"
        (self.tree / "Foo").mkdir(parents=True)
        (self.tree / "Foo/Bar.lean").write_text("def x := 1\n")
        self.out = self.cache / "outputs/minidregg"
        self.art = self.cache / "artifacts"
        self.out.mkdir(parents=True)
        self.art.mkdir(parents=True)
        self.env = os.environ | {"ARTIFACT_ROOT": str(t)}

    def tearDown(self):
        self.tmp.cleanup()

    def entry(self, name, c, text, at):
        (self.art / c).write_text(text)
        (self.out / f"{name}.json").write_text('{"data":{"c":"%s"}}' % c)
        os.utime(self.art / c, (at, at))
        os.utime(self.out / f"{name}.json", (at + 60, at + 60))

    def audit(self, *extra, tree=None):
        return subprocess.run([sys.executable, str(AUDIT), "--cache", str(self.cache), "--tree",
                               str(tree or self.tree), *extra], env=self.env, capture_output=True, text=True)

    def test_clean_cache_passes(self):
        self.entry("h1", "aa.c", "void initialize_minidregg_Foo_Bar(){}", 1_700_000_000)
        self.assertEqual(self.audit().returncode, 0)

    def test_written_through_artifact_is_purged(self):
        self.entry("h1", "aa.c", "void initialize_minidregg_Foo_Bar(){}", 1_700_000_000)
        self.entry("h2", "bb.c", "void initialize_minidregg_Foo_Bar(){}", 1_700_000_000)
        with open(self.art / "bb.c", "a") as f:     # a write through the restored hard link
            f.write("/* changed */")
        r = self.audit("--purge")
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("written-through:bb.c", r.stdout)
        self.assertFalse((self.out / "h2.json").exists())
        self.assertFalse((self.art / "bb.c").exists())
        self.assertTrue((self.out / "h1.json").exists())
        self.assertEqual(self.audit().returncode, 0)

    def test_unprefixed_initializer_is_purged(self):
        self.entry("h3", "cc.c", "void initialize_Foo_Bar(){}", 1_700_000_000)
        r = self.audit("--purge")
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertFalse((self.out / "h3.json").exists())

    def test_an_audit_that_cannot_run_exits_2(self):
        self.assertEqual(self.audit(tree=Path(self.tmp.name) / "absent").returncode, 2)


if __name__ == "__main__":
    unittest.main()
