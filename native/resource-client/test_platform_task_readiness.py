import importlib.util,json,tempfile,unittest
from pathlib import Path
from unittest.mock import Mock
p=Path(__file__).with_name('platform-task-readiness.py');spec=importlib.util.spec_from_file_location('ready',p);r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
def grain(generation,status,reserved,remaining='100'):
 return dict(generation=generation,status=status,reserved=reserved,remaining=remaining)
class StateBoundary(unittest.TestCase):
 def test_fresh_soft_attach_then_bounded_parent_reserve(self):
  self.assertEqual(r.classify('parent',grain('0','0','0')),'attach')
  self.assertEqual(r.classify('parent',grain('1','2','0')),'reserve')
  for status in ('3','4'):self.assertEqual(r.classify('parent',grain('1',status,'1')),'ready')
  for status in ('1','2'):self.assertEqual(r.classify('tool',grain('1',status,'0')),'ready')
 def test_unknown_held_other_generation_and_noncanonical_refuse(self):
  for role,state in [('parent',grain('1','3','2')),('parent',grain('2','3','1')),('parent',grain('1','1','0')),('tool',grain('1','3','1')),('tool',grain('2','1','0')),('tool',grain('01','1','0')),('tool',grain(1,'1','0'))]:
   with self.subTest(role=role,state=state),self.assertRaises(ValueError):r.classify(role,state)
 def instance(self,root):
  x=r.Ready.__new__(r.Ready);x.root=root;x.nonce=1;x.manifest={'mini':'mini','host':'host'};x.ctx={'config':'config','publicSocket':'socket'}
  return x
 def test_retained_call_blocks_new_submission(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);(root/'parent-attach-attempt').mkdir();x=self.instance(root)
   x.query=Mock(return_value=({'task':'7901'},{'subject':'7','seed':'key'},'71',{'root':'signed-root','grain':grain('0','0','0')}));x.invoke=Mock()
   with self.assertRaisesRegex(ValueError,'refuse fresh effect'):x.prepare('parent')
   x.invoke.assert_not_called()
 def test_pre_submit_publication_cut_preserves_original_intent(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);original=root/'parent-attach-intent.json';original.write_text('retained exact source')
   x=self.instance(root);x.query=Mock(return_value=({'task':'7901'},{'subject':'7','seed':'key'},'71',{'root':'signed-root','grain':grain('0','0','0')}));x.invoke=Mock()
   with self.assertRaisesRegex(ValueError,'retained preparation intent'):x.prepare('parent')
   x.invoke.assert_not_called();self.assertEqual(original.read_text(),'retained exact source')
 def test_native_nonterminal_decision_stops_before_tool(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp);x=self.instance(root)
   x.query=Mock(return_value=({'task':'7901'},{'subject':'7','seed':'key'},'71',{'root':'signed-root','grain':grain('0','0','0')}))
   def submit(label,words):
    attempt=root/(label+'-attempt');attempt.mkdir();(attempt/'outcome.json').write_text(json.dumps({'type':'unknown'}))
   x.invoke=Mock(side_effect=submit)
   with self.assertRaisesRegex(ValueError,'exact retry required'):x.prepare('parent')
   intent=json.loads((root/'parent-attach-intent.json').read_text());self.assertEqual(intent['grain']['operation'],{'type':'attach','soft':True});self.assertEqual(intent['grain']['expectedTargetRoot'],'signed-root');self.assertEqual(intent['grants'],[{'kind':'object','target':'7901','capability':'71'}]);self.assertEqual(x.invoke.call_count,1)
if __name__=='__main__':unittest.main()
