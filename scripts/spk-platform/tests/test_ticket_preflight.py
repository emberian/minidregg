"""A refused issuer fee grant must not leave a new ToolTask hold."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

HERE = Path(__file__).resolve().parents[1]
def module(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), HERE / (name + '.py'))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

class Preflight(unittest.TestCase):
    def check_refusal(self, name, method):
        m = module(name)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            x = Mock()
            x.f = {'delegates': {'m0': {'subject': '7'}}}
            x.m = {'spkHost': {'path': '/pinned/spk-host'}}
            x.issue_preflight.side_effect = RuntimeError('current issuer account grant revoked')
            c = {'delegate': {'name': 'm0'}}
            entered = (c, root, x) if method == 'attach' else (c, root, root / 'workspace', x)
            with patch.object(m, 'enter', return_value=entered):
                with self.assertRaisesRegex(RuntimeError, 'account grant revoked'):
                    getattr(m, method)(root / 'input.json')
            x.issue_preflight.assert_called_once_with()
            steps = [call.args[0] for call in x.step.call_args_list]
            self.assertFalse(any(step.endswith('ticket-reserve') or step.endswith(':ticket') for step in steps))
            x.reserve.assert_not_called()
            x.issue.assert_not_called()
    def test_completed_hold_is_preserved_without_new_preflight(self):
        for name, method, reserve, ticket in [
            ('same-store-app', 'attach', 'member:m0:ticket-reserve', 'member:m0:ticket'),
            ('app-document-provision', 'provision', 'connector:ticket-reserve', 'connector:ticket')]:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                m = module(name)
                root = Path(tmp)
                x = Mock()
                x.f = {'delegates': {'m0': {'subject': '7'}}, 'steps': {'done': [reserve]}}
                x.m = {'spkHost': {'path': '/pinned/spk-host'}}
                def step(name, *args, **kwargs):
                    if name == ticket:
                        raise RuntimeError('retained issue boundary')
                x.step.side_effect = step
                c = {'delegate': {'name': 'm0'}}
                entered = (c, root, x) if method == 'attach' else (c, root, root / 'workspace', x)
                with patch.object(m, 'enter', return_value=entered):
                    with self.assertRaisesRegex(RuntimeError, 'retained issue boundary'):
                        getattr(m, method)(root / 'input.json')
                x.issue_preflight.assert_not_called()
                x.reserve.assert_not_called()
    def test_member_ticket_fee_refusal_precedes_hold(self):
        self.check_refusal('same-store-app', 'attach')
    def test_connector_ticket_fee_refusal_precedes_hold(self):
        self.check_refusal('app-document-provision', 'provision')

if __name__ == '__main__':
    unittest.main()
