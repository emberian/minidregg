#!/usr/bin/env python3
"""Read-only binding checks; no native commands are invoked."""
import importlib.util
import json
from pathlib import Path
import socket
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('receiving', Path(__file__).with_name('protected-document-same-store.py'))
receiving = importlib.util.module_from_spec(spec)
spec.loader.exec_module(receiving)


class BindingChecks(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.sock = socket.socket(socket.AF_UNIX)
        self.sock.bind(str(self.root / 'world.sock'))
        for name in ('host', 'mini', 'config.json'):
            (self.root / name).write_bytes(b'fixture')
            (self.root / name).chmod(0o700)
        (self.root / 'store').mkdir()
        manifest = {role: str(self.root / role) for role in ('host', 'mini')}
        manifest['sha256'] = {role: receiving.digest(self.root / role) for role in ('host', 'mini')}
        (self.root / 'manifest.json').write_text(json.dumps(manifest))
        self.binding = {'protocol': 'mini-protected-same-store-v1', 'manifestPath': str(self.root / 'manifest.json'),
            'manifestSha256': receiving.digest(self.root / 'manifest.json'), 'configPath': str(self.root / 'config.json'),
            'socketPath': str(self.root / 'world.sock'), 'storePath': str(self.root / 'store')}
        for index, role in enumerate(('owner', 'member')):
            workspace = self.root / role
            home = self.root / (role + '-home')
            workspace.mkdir(); home.mkdir()
            state = {'subject': str(index + 1), 'host': manifest['host'],
                     'config': self.binding['configPath'], 'socket': self.binding['socketPath']}
            (workspace / 'workspace.json').write_text(json.dumps(state))
            self.binding[role] = {'workspace': str(workspace), 'home': str(home)}

    def tearDown(self):
        self.sock.close()
        self.tmp.cleanup()

    def test_actual_distinct_workspace_binding_is_read_only(self):
        before = {str(p.relative_to(self.root)) for p in self.root.rglob('*')}
        receiving.validate(self.binding)
        self.assertEqual(before, {str(p.relative_to(self.root)) for p in self.root.rglob('*')})

    def test_modified_native_binary_is_refused(self):
        (self.root / 'mini').write_bytes(b'other')
        with self.assertRaisesRegex(AssertionError, 'mini changed'):
            receiving.validate(self.binding)

    def test_host_bytes_that_differ_from_the_pin_are_refused(self):
        other = self.root / 'other-host'
        other.write_bytes(b'not the pinned Host')
        state_path = self.root / 'member/workspace.json'
        state = json.loads(state_path.read_text())
        self.assertNotIn('hostSha256', state)
        state['host'] = str(other); state_path.write_text(json.dumps(state))
        with self.assertRaisesRegex(AssertionError, 'Host differs|Host pin differs'):
            receiving.validate(self.binding)

    def test_other_socket_and_duplicate_subject_are_refused(self):
        state_path = self.root / 'member/workspace.json'
        state = json.loads(state_path.read_text())
        state['socket'] = 'other.sock'; state_path.write_text(json.dumps(state))
        with self.assertRaisesRegex(AssertionError, 'socket differs'):
            receiving.validate(self.binding)
        state['socket'] = self.binding['socketPath']; state['subject'] = '1'; state_path.write_text(json.dumps(state))
        with self.assertRaisesRegex(AssertionError, 'distinct'):
            receiving.validate(self.binding)

    def test_optional_roles_are_bound_and_distinct(self):
        self.binding['reader'] = self.binding['member']
        with self.assertRaisesRegex(AssertionError, 'distinct'):
            receiving.validate(self.binding)

    def test_existing_native_custody_needs_no_room_passphrase(self):
        custody = self.root / 'owner/protected-documents'; custody.mkdir()
        (custody / 'keys.json').write_bytes(b'existing')
        receiving.validate(self.binding)
        password = self.root / 'secret'; password.write_text('private-value'); password.chmod(0o600)
        self.binding['owner']['cachePassphraseFile'] = str(password)
        receiving.validate(self.binding)
        self.assertEqual((custody / 'keys.json').read_bytes(), b'existing')
        password.chmod(0o644)
        with self.assertRaisesRegex(AssertionError, 'permissions'):
            receiving.validate(self.binding)


if __name__ == '__main__':
    unittest.main()
