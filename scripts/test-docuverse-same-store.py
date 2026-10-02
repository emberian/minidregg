import importlib.util
from pathlib import Path
import tempfile
import unittest
import json
import os
import subprocess
spec=importlib.util.spec_from_file_location("ordinary",Path(__file__).with_name("docuverse-same-store.py"))
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
class SuppliedActorTests(unittest.TestCase):
    def actors(self,root):
        return {role:(root/(role+"-workspace"),root/(role+"-home"),str(index+1),None)
            for index,role in enumerate(("owner","member","reader","reviewer"))}
    def test_roles_are_real_distinct_workspaces(self):
        with tempfile.TemporaryDirectory() as tmp:
            actors=self.actors(Path(tmp));module.preflight(actors)
            env=module.role_environment(actors)
            self.assertEqual(env["JDV_REVIEWER_WS"],str(actors["reviewer"][0]))
            self.assertEqual(env["JDV_MEMBER_HOME"],str(actors["member"][1]))
            self.assertEqual(env["JDV_SUPPLIED_STORE"],"1")
            actors["reader"]=actors["owner"]
            with self.assertRaises(RuntimeError):module.preflight(actors)
    def test_existing_native_receiving_custody_is_never_overwritten(self):
        for target in ("refs/paper.json","proposals/g-ben","attempts/p1"):
            with tempfile.TemporaryDirectory() as tmp:
                actors=self.actors(Path(tmp));path=actors["owner"][0]/target
                path.parent.mkdir(parents=True);path.write_text("retained")
                with self.assertRaises(RuntimeError):module.preflight(actors)
                self.assertEqual(path.read_text(),"retained")
        with tempfile.TemporaryDirectory() as tmp:
            actors=self.actors(Path(tmp));path=actors["member"][1]/"requests"/"notes.md"
            path.parent.mkdir(parents=True);path.write_text("member work")
            with self.assertRaises(RuntimeError):module.preflight(actors)
            self.assertEqual(path.read_text(),"member work")
    def test_fewer_roles_do_not_fake_negative_permission_coverage(self):
        with tempfile.TemporaryDirectory() as tmp:
            actors=self.actors(Path(tmp));del actors["reader"]
            with self.assertRaises(RuntimeError):module.preflight(actors)
    def test_supplied_mode_records_no_local_cold_audit_without_store_effects(self):
        script=Path(__file__).resolve().parents[1]/"native/resource-client/journey.d/jdocuverse.sh"
        section="# Shared Store lifecycle/checkpoint"+script.read_text().split("# Shared Store lifecycle/checkpoint",1)[1].split("# ------------------------------------------------ AUDIT",1)[0]
        with tempfile.TemporaryDirectory() as tmp:
            env=os.environ.copy();env.update(SD=tmp,JDV_SUPPLIED_STORE="1")
            subprocess.run(["bash","-c","set -euo pipefail\nfinish(){ :; }\n"+section],env=env,check=True)
            state=json.loads((Path(tmp)/"cold-audit.json").read_text())
            self.assertEqual(state["state"],"not-run");self.assertFalse(state["serviceRestart"])
if __name__=="__main__":unittest.main()
