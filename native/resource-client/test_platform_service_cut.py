#!/usr/bin/env python3
"""Refute a process stop without a native zero-work drain boundary."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

loader = importlib.util.spec_from_file_location("cut", Path(__file__).with_name("platform-service-cut.py"))
cut = importlib.util.module_from_spec(loader); loader.loader.exec_module(cut)


class DrainBoundary(unittest.TestCase):
    def case(self, change, accepted, absent=None, no_drain=False):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve(); directory = str(root)
            for name, value in (("config", {}), ("manifest", {"sha256": {"host": "a"*64}}), ("cli", {})):
                cut.write(root/name, value)
            import os
            pid = os.getpid()
            owned = {"public": {"pid": pid}, "operator": {"pid": pid}}
            state = {"root": directory, "identity": {"id": "world"}, "services": dict(owned),
                     "privateSocket": str(root/"operator.sock")}
            cut.write(root/"runtime", state)
            proposal = {"runtime": cut.pin(root/"runtime"), "sourceIdentity": state["identity"],
                "ownedServices": owned, "ownedCwds": {name: str(Path.cwd().resolve()) for name in owned},
                "artifacts": {"platform-service-cut.py": cut.digest(cut.__file__)}, "descriptor": {"dataRoot": directory,
                    "deployment": {"memberCommands": [], "rolePaths": {"host": "/native-host"},
                        **{name: cut.pin(root/name) for name in ("config", "manifest", "cli")}}}}
            cut.write(root/"proposal.json", proposal)
            (root/"platform-service-cut.py").write_bytes(Path(cut.__file__).read_bytes())
            status = {"processId": pid, "instanceId": "instance", "hostSha256": "a"*64,
                      "configSha256": proposal["descriptor"]["deployment"]["config"]["sha256"]}
            drained = {**status, "format": "mini-operator-drain-v1", "phase": "drained",
                "admissionClosed": True, "drained": True, "acceptedConnections": 0,
                "queuedRequests": 0, "activeRequests": 0, "unresolvedConnections": 0, **change}
            if absent == "operator" and not no_drain: cut.write(root/"stop-journal.json", {"drain": drained})
            replies = iter((status, drained)); stops = []
            class World:
                def __init__(self, *args): pass
                def stop(self, names): stops.extend(names)
            def native(*args, **kwargs):
                return subprocess.CompletedProcess(args[0], 0, json.dumps(next(replies)).encode(), b"")
            alive=iter((absent not in ("public", "operator"), absent != "operator"))
            with patch.object(cut, "protected", side_effect=lambda path: Path(path)), \
                 patch.object(cut, "owned_alive", side_effect=lambda retained, cwd: next(alive)), \
                 patch.object(cut.provision, "World", World), patch.object(cut.subprocess, "run", side_effect=native):
                if accepted: cut.stop(root)
                else:
                    with self.assertRaises(ValueError): cut.stop(root)
            self.assertEqual(stops, [] if no_drain else ["public", "operator"] if accepted else ["public"])
            self.assertEqual(len(list(root.glob("*.command.json"))), 0 if absent == "operator" else 2)
            journal=cut.read(root/"stop-journal.json") if (root/"stop-journal.json").exists() else {}
            self.assertEqual(journal.get("stopped", False), accepted)

    def test_unresolved_native_connection_retains_operator(self): self.case({"unresolvedConnections": 1}, False)
    def test_unavailable_native_count_retains_operator(self): self.case({"activeRequests": None}, False)
    def test_replaced_native_instance_retains_operator(self): self.case({"instanceId": "replacement"}, False)
    def test_exact_drained_instance_stops_operator(self): self.case({}, True)
    def test_exit_after_native_drain_before_runtime_publication(self): self.case({}, True, "operator")
    def test_public_exit_before_runtime_publication(self): self.case({}, True, "public")
    def test_absent_operator_without_native_drain_refuses(self): self.case({}, False, "operator", True)
    def test_reused_live_pid_is_not_absence(self):
        import os
        identity=cut.provision.proc_identity(os.getpid()); identity['uid']+=1
        with self.assertRaises(ValueError): cut.owned_alive(identity, str(Path.cwd().resolve()))


if __name__ == "__main__": unittest.main()
