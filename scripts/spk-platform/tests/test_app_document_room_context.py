import importlib.util
from pathlib import Path
import unittest
import copy
spec=importlib.util.spec_from_file_location("context",Path(__file__).resolve().parents[1]/"app-document-room-context.py")
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
class ContextTests(unittest.TestCase):
    def inputs(self):
        request={"protocol":"mini-resident-room-capture-request-v1","worldConfig":"/world/config","socket":"/world/public.sock","founderSubject":"7","founderWorkspace":"/member0/ws","founderHome":"/member0","roomAlias":"lab","roomTarget":"80","documentAlias":"lab-captured","documentTarget":"81"}
        journey={"operation":"csv1","workspace":"/connector/ws","reader":{"workspace":"/member0/ws","document":"lab-captured"}}
        result={"protocol":"mini-app-document-journey-result-v1","status":"saved","subject":"9","operation":"csv1","target":"81","receipt":{"bodyBytes":"4","bodySha256":"a"*64,"operation":"100","transaction":"101"},"callSha256":"b"*64,"evidence":"/receiving/run1"}
        status={"type":"mini-app-document-result-v1","status":"saved","id":"csv1","subject":"9","target":"81","attempt":"/connector/ws/attempts/app-csv1","receipt":result["receipt"],"outcome":{"type":"confirmed","confirmation":"installed","transactionId":"102","eventId":"103","worldRoot":"104","acceptedCount":"1"}}
        return request,journey,result,status
    def test_receipts_keep_app_admission_and_document_publication_distinct(self):
        context=module.construct(*self.inputs())
        self.assertEqual(context["exportCustody"]["transaction"],"101")
        self.assertEqual(context["publicationReceipt"]["transactionId"],"102")
        self.assertEqual(context["documentTarget"],"81")
        self.assertNotIn("token",context);self.assertNotIn("body",context)
    def test_other_reader_or_document_does_not_join(self):
        for change in (lambda args:args[1]["reader"].update(workspace="/member1/ws"),lambda args:args[3].update(target="82"),lambda args:args[3].update(subject="8")):
            args=self.inputs();change(args)
            with self.assertRaises(RuntimeError):module.construct(*args)
    def test_unconfirmed_or_other_export_does_not_join(self):
        for change in (lambda args:args[3].update(status="uncertain"),lambda args:args[3]["outcome"].update(confirmation="recoveredAfterUncertainResponse"),lambda args:args[2].update(operation="other"),lambda args:args[3].update(receipt={"bodySha256":"x"})):
            args=copy.deepcopy(self.inputs());change(args)
            with self.assertRaises(RuntimeError):module.construct(*args)
if __name__=="__main__":unittest.main()
