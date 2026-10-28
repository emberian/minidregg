#!/usr/bin/env python3
"""Exercise the real journey's pre-Store checks; no native admission or Store."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(sys.platform.startswith('linux'), 'journey uses Linux stat and custody paths')
class PreflightTests(unittest.TestCase):
    def test_stop_receipt_must_match_selected_host_before_world_creation(self):
        for case in ('matching', 'old-host', 'failed', 'named-acl', 'default-acl'):
            with self.subTest(case=case), tempfile.TemporaryDirectory(prefix='oracle-preflight-', dir=ROOT) as tmp:
                root = Path(tmp)
                base = root / 'base'
                base.mkdir()
                host = base / 'minidregg-host'
                host.write_text('#!/bin/sh\nexit 99\n')
                host.chmod(0o700)
                own = root / 'own'
                own.mkdir()
                source = root / 'data'
                source.mkdir()
                spk = root / 'runtime.spk'
                spk.write_bytes(b'')
                inventory = root / 'inventory.json'
                inventory.write_text('{}\n')
                benchmark = root / 'benchmark.json'
                benchmark.write_text(json.dumps({
                    'schema': 'mini-stop-inspection-continuation-v1',
                    'passed': case != 'failed',
                    'host_sha256': '0' * 64 if case == 'old-host' else hashlib.sha256(host.read_bytes()).hexdigest(),
                }))
                run = root / 'run'
                if case == 'named-acl':
                    # Named self adds no other principal; it still carries the
                    # extended ACL that controller-stage must not rewrite.
                    subprocess.run(['setfacl', '-m', f'u:{os.getuid()}:--x', str(root)], check=True)
                elif case == 'default-acl':
                    subprocess.run(['setfacl', '-m', 'd:u::rwx,d:g::---,d:o::---', str(root)], check=True)

                env = {k: v for k, v in os.environ.items() if not k.startswith('ORACLE_')}
                # A matching receipt reaches the next independent refusal. This
                # control avoids ever starting native work or creating a Store.
                env.update(ORACLE_STOP_BENCHMARK_JSON=str(benchmark), ORACLE_BROWSER_B='1', ORACLE_BROWSER_PORT='0')
                result = subprocess.run(['bash', str(ROOT / 'scripts/oracle-shared-data-journey.sh'),
                    str(base), str(own), str(run), str(spk), str(source), str(inventory)],
                    env=env, capture_output=True, text=True, timeout=15)
                self.assertEqual(result.returncode, 1, result.stderr)
                expected = ('private ancestor has extended ACL' if case.endswith('-acl') else
                            'explicit browser port required' if case == 'matching' else
                            'STOP benchmark must qualify the selected Host binary')
                self.assertIn(expected, result.stderr)
                self.assertFalse(run.exists())


if __name__ == '__main__':
    unittest.main()
