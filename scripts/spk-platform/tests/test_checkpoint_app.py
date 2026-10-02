import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC=importlib.util.spec_from_file_location('checkpoint_app',Path(__file__).resolve().parents[1]/'checkpoint-app.py')
m=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(m)

class CheckpointCallbacks(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(dir=Path.home());self.root=Path(self.temp.name);self.root.chmod(0o700)
        self.state=self.root/'host';self.state.mkdir(mode=0o700)
        self.journal=self.state/'apps/97/g4';self.journal.mkdir(parents=True,mode=0o700)
        self.resident=self.journal/'resident.json';self.resident.write_text(json.dumps({'journalDir':str(self.journal),'unit':'mini-grain-fixture.service','miniConfigSha256':'a'*64}))
        self.image=self.root/'spk-host';self.image.write_bytes(b'pinned-source')
        self.config=self.root/'config.json';self.config.write_text('{}')
        self.value={'protocol':'mini-spk-checkpoint-app-config-v1','app':97,'stateRoot':str(self.state),'profilePath':'/protected/profile.json','spkHost':str(self.image),'spkHostSha256':m.sha(self.image)}
        self.status={'protocol':'mini-spk-grain-status-v2','app':97,'store':'native-store-tag','runs':[{'state':'running','generation':4,'unit':'mini-grain-fixture.service'}]}
        self.custody=patch.object(m,'root_config',return_value=self.value);self.custody.start()
        self.source=patch.object(m.subprocess,'check_output',return_value=json.dumps(self.status).encode());self.source_mock=self.source.start()
    def tearDown(self):self.source.stop();self.custody.stop();self.temp.cleanup()
    def run_phase(self,action):return m.run(action,str(self.config),'job-01')
    def test_refused_pause_retains_exact_plan_then_retry_and_resume(self):
        captured=self.run_phase('capture');plan=m.load(Path(captured['plan']));nonce=plan['request']['nonceHex']
        with patch.object(m,'invoke',return_value={'protocol':m.PROTOCOL,'status':'refused'}):
            with self.assertRaisesRegex(RuntimeError,'refused'):self.run_phase('quiesce')
        state=Path(captured['plan']).parent
        self.assertFalse((state/'quiesce-result.json').exists());self.assertTrue(list(state.glob('quiesce-response-*.json')))
        seen=[]
        def receive(req):
            seen.append(req);return {'protocol':m.PROTOCOL,'status':'paused' if req['action']=='pause' else 'resumed','intent':{'request':plan['request']}}
        with patch.object(m,'invoke',side_effect=receive):
            q=self.run_phase('quiesce');again=self.run_phase('quiesce');r=self.run_phase('resume')
        self.assertEqual(q,again);self.assertTrue(r['ready']);self.assertEqual(q['pausedUnits'],['mini-grain-fixture.service'])
        self.assertEqual([x['nonceHex'] for x in seen],[nonce]*3)
        inventory=m.load(Path(q['pauseInventory']));self.assertEqual(inventory['apps'],[{'store':'native-store-tag','request':plan['request']}])
        self.assertEqual(self.source_mock.call_count,1)
    def test_capture_rejects_uncertain_generation_and_mutated_config(self):
        self.status['runs'].append({'state':'uncertain-start','generation':3})
        self.source_mock.return_value=json.dumps(self.status).encode()
        with self.assertRaisesRegex(RuntimeError,'prior generation'):self.run_phase('capture')
        self.status['runs'].pop();self.source_mock.return_value=json.dumps(self.status).encode();self.run_phase('capture')
        self.config.write_text('{"changed":true}')
        with self.assertRaisesRegex(RuntimeError,'changed since capture'):self.run_phase('quiesce')
    def test_unsafe_state_and_conflicting_retry_are_refused(self):
        linked=self.root/'linked';linked.symlink_to(self.state)
        with self.assertRaisesRegex(RuntimeError,'custody'):m.private_directory(linked)
        self.state.chmod(0o777)
        with self.assertRaisesRegex(RuntimeError,'custody'):self.run_phase('capture')
        self.state.chmod(0o700);self.run_phase('capture')
        target=self.state/'proof.json';m.save(target,{'exact':1});m.save(target,{'exact':1})
        with self.assertRaisesRegex(RuntimeError,'retry differs'):m.save(target,{'exact':2})
        hard=self.state/'alias';os.link(target,hard)
        with self.assertRaisesRegex(RuntimeError,'custody'):m.save(target,{'exact':1})
    def test_checkpoint_id_and_image_pin_are_bound_before_capture(self):
        with self.assertRaisesRegex(RuntimeError,'ID invalid'):m.run('capture',str(self.config),'../other')
        self.image.write_bytes(b'changed')
        with self.assertRaisesRegex(RuntimeError,'image pin'):self.run_phase('capture')
        self.assertEqual(self.source_mock.call_count,0)

if __name__=='__main__':unittest.main()
