"""Focused physical adapter checks; no Linux receiving claim."""
import importlib.util
from pathlib import Path
import unittest
import tempfile
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('rust_host_package', Path(__file__).with_name('rust-host-package.py'))
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)


class RustHostPackageTest(unittest.TestCase):
    def test_relocation_respects_path_boundaries_and_bundle_state(self):
        result = bridge.relocate({'checkout': '/build/oracle', 'path': '/build/oracle/root/a',
                                 'other': '/build/oracle-other', 'journal': '@state/journal.sqlite3'},
                                {'/build/oracle': '/opt/oracle'})
        self.assertEqual(result, {'checkout': '/opt/oracle', 'path': '/opt/oracle/root/a',
                                  'other': '/build/oracle-other', 'journal': '@state/journal.sqlite3'})

    def test_unadmitted_external_file_refuses_before_publication(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            payload = root / 'payload'
            payload.mkdir()
            manifest = {'schema': 'oracle-host-distribution-v1',
                        'files': {'lib/oracle-host': {'sha256': 'host', 'bytes': 1}},
                        'external_files': [{'path': '/host/private/image', 'sha256': 'bad'}]}
            (payload / 'host.template.json').write_text('{}')
            # The payload byte/inventory checks are independently owned by the
            # packager; exercise this adapter's signed-external admission boundary.
            receipt = {'expected_package_entries': {}, 'shared_data': None}
            with patch.object(bridge.stage, 'pinned_json', side_effect=[receipt, manifest]), \
                 patch.object(bridge.stage, 'verify_stage', return_value=receipt), \
                 patch.object(bridge.stage, 'inventory', return_value={
                     'lib/oracle-host': {'kind': 'file', 'sha256': 'host', 'size': 1, 'executable': True}}), \
                 patch.object(bridge.stage, 'linux_binary'):
                with self.assertRaisesRegex(ValueError, 'not admitted by base stage'):
                    bridge.adapt(root / 'base', 'basehash', payload, 'payloadhash', {}, root / 'new')
            self.assertFalse((root / 'new').exists())

    def test_launcher_starts_one_host_and_preserves_bridge(self):
        compile(bridge.LAUNCH, '<fixed Mini launcher>', 'exec')
        self.assertIn('/opt/oracle-host/bin/oracle-host', bridge.LAUNCH)
        self.assertIn('/var/oracle-host', bridge.LAUNCH)
        self.assertIn('/opt/oracle-bin/minidregg-oracle-appliance', bridge.LAUNCH)
        self.assertNotIn('adapter/serve.py', bridge.LAUNCH)


if __name__ == '__main__':
    unittest.main()
