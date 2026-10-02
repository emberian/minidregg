import importlib.util,json,pathlib,tempfile,unittest
from unittest import mock
spec=importlib.util.spec_from_file_location('dispatch',pathlib.Path(__file__).with_name('mini-hermes-dispatch.py'));dispatch=importlib.util.module_from_spec(spec);spec.loader.exec_module(dispatch)
class DispatcherTests(unittest.TestCase):
 def test_retained_history_is_paged_and_other_members_advance(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);homes=[root/'a',root/'b'];payload={'recipient':'8','roomCell':'70','task':'71'};bundle={'payloadHex':json.dumps(payload).encode().hex()};registry={('8','70','71'):root/'reg.json'}
   for n in range(1100):
    assignment=homes[0]/'outbox/8/room-70'/f'assignment-{n}';assignment.mkdir(parents=True);(assignment/'handoff.json').write_text(json.dumps(bundle))
   assignment=homes[1]/'outbox/8/room-70/assignment-1';assignment.mkdir(parents=True);(assignment/'handoff.json').write_text(json.dumps(bundle))
   c={'memberHomes':list(map(str,homes))};cursors={};first=list(dispatch.jobs(c,registry,cursors,0));self.assertGreaterEqual(len(first),17);self.assertTrue(any(str(p).startswith(str(homes[1])) for p,_,_ in first))
   following=list(dispatch.jobs(c,registry,cursors,0));self.assertTrue(set(p for p,_,_ in first if str(p).startswith(str(homes[0]))).isdisjoint(p for p,_,_ in following if str(p).startswith(str(homes[0]))));self.assertTrue(str(first[1][0]).startswith(str(homes[1])))
 def test_malformed_member_hints_do_not_block_another_member(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=pathlib.Path(tmp);homes=[root/'a',root/'b'];
   for home,content in [(homes[0],'{bad'),(homes[1],json.dumps({'payloadHex':json.dumps({'recipient':'8','roomCell':'70','task':'71'}).encode().hex()}))]:
    assignment=home/'outbox/8/room-70/assignment-1';assignment.mkdir(parents=True);(assignment/'handoff.json').write_text(content)
   jobs=list(dispatch.jobs({'memberHomes':list(map(str,homes))},{('8','70','71'):root/'registration'},{},0));self.assertEqual(len(jobs),1);self.assertTrue(str(jobs[0][0]).startswith(str(homes[1])))
 def test_json_duplicate_key_refuses_hint(self):
  with tempfile.TemporaryDirectory() as tmp:
   path=pathlib.Path(tmp)/'duplicate.json';path.write_text('{"a":1,"a":2}')
   with self.assertRaises(ValueError):dispatch.read(path)
if __name__=='__main__':unittest.main()
