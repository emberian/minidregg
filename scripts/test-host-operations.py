#!/usr/bin/env python3
"""Mutation checks for the operation-allocation gate, using the actual sources."""
import copy
import importlib.util
import json
import re
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("host_operations", ROOT / "scripts/host-operations.py")
ops = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ops)

class GateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="mini-op-gate-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        data, _ = ops.load(ROOT)
        paths = {ops.REGISTRY, ops.GENERATED, Path("Host/Main.lean"), Path("native/resource-client/src/transport.rs")}
        paths.update(Path(binding["path"]) for binding in data["client_constants"])
        for path in paths:
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / path, self.root / path)

    def edit(self, path, old, new):
        file = self.root / path
        text = file.read_text()
        self.assertIn(old, text)
        file.write_text(text.replace(old, new, 1))

    def registry(self, mutate):
        path = self.root / ops.REGISTRY
        data = json.loads(path.read_text())
        mutate(data)
        path.write_text(json.dumps(data))

    def rejects(self, expected):
        with self.assertRaisesRegex(ops.Invalid, expected):
            ops.check(self.root)

    def test_actual_sources_match_registry(self):
        result = ops.check(self.root)
        self.assertGreater(result["active"], 100)

    def test_duplicate_reservation_cannot_take_job_money_161(self):
        def mutate(data):
            entry = copy.deepcopy(next(e for e in data["operations"] if e["code"] == 164))
            entry["code"] = 161
            entry["symbol"] = "COLLIDING_NEW_DISPATCH"
            data["operations"].append(entry)
        self.registry(mutate)
        self.rejects("duplicate request allocation: 161")

    def test_duplicate_json_key_refuses(self):
        self.edit(ops.REGISTRY, '"format":', '"format":"shadowed","format":')
        self.rejects("duplicate JSON object key")

    def test_duplicate_host_arm_refuses(self):
        self.edit("Host/Main.lean", "                        | 161 =>", "                        | 160 =>")
        self.rejects("duplicate request arm")

    def test_cross_dispatch_shadow_refuses(self):
        self.edit("Host/Main.lean", "  | 130 =>", "  | 161 =>")
        self.rejects("duplicate/shadowed request 161")

    def test_unregistered_receiver_refuses(self):
        self.edit("Host/Main.lean", "  | 130 =>", "  | 149 =>")
        self.rejects("Host allocations differ")

    def test_reserved_receiver_must_be_promoted_explicitly(self):
        self.edit("Host/Main.lean", "  | 130 =>", "  | 191 =>")
        self.rejects("unregistered/reserved receiving")

    def test_multiline_host_pattern_requires_parser_update(self):
        self.edit("Host/Main.lean", "  | 130 =>", "  | 130\n      =>")
        self.rejects("unsupported multiline/unknown arm header")

    def test_unknown_named_host_pattern_requires_parser_update(self):
        self.edit("Host/Main.lean", "  | 130 =>", "  | requestOperation =>")
        self.rejects("unknown request pattern")

    def test_logic_before_direct_match_requires_parser_update(self):
        self.edit("Host/Main.lean", "  match operation with\n  | 0 =>", "  if operation == 149 then pure ()\n  match operation with\n  | 0 =>")
        self.rejects("unsupported logic before operation match")

    def first_interception(self):
        source = (self.root / "Host/Main.lean").read_text()
        frame = ops.lean_function(ops.masked(source, "lean"), "serveFrame")
        header = re.search(r"^    if (.+) then$", frame, re.M)
        self.assertIsNotNone(header)
        return header[0]

    def test_unknown_intercept_shape_requires_parser_update(self):
        header = self.first_interception()
        self.edit("Host/Main.lean", header, "    if (operation == 34) then")
        self.rejects("unknown interception shape")

    def test_literal_or_interception_tracks_both_requests(self):
        self.edit("Host/Main.lean", self.first_interception(), "    if operation == 34 || operation == 164 then")
        receivers = ops.host_receivers((self.root / "Host/Main.lean").read_text())
        self.assertEqual(receivers[34], "serveFrame")
        self.assertEqual(receivers[164], "serveFrame")

    def test_literal_or_duplicate_interception_refuses(self):
        self.edit("Host/Main.lean", self.first_interception(), "    if operation == 34 || operation == 34 then")
        self.rejects("duplicate/shadowed request 34")

    def test_literal_or_unknown_operand_refuses(self):
        self.edit("Host/Main.lean", self.first_interception(), "    if operation == 34 || routeBound then")
        self.rejects("unknown interception shape")

    def test_literal_or_out_of_byte_namespace_refuses(self):
        self.edit("Host/Main.lean", self.first_interception(), "    if operation == 34 || operation == 256 then")
        self.rejects("request outside byte namespace")

    def forwarded_fixture(self, body="fnDispatch operation payload"):
        file = self.root / "Host/Main.lean"
        source = file.read_text()
        direct = ops.lean_function(ops.masked(source, "lean"), "dispatchSession")
        start = direct.index("  | 130 =>")
        end = direct.index("\n  |", start + 1)
        rewritten = direct[:start] + "  | 130 => " + body + direct[end:]
        source = source.replace(ops.lean_function(source, "dispatchSession"), rewritten)
        source = source.replace("                        | 161 =>", "                        | 130 =>", 1)
        file.write_text(source)
        return source

    def test_exact_delegation_has_one_receiving_owner(self):
        receivers = ops.host_receivers(self.forwarded_fixture())
        self.assertEqual(receivers[130], "fnDispatch")

    def test_changed_delegation_arguments_still_refuse_shadow(self):
        self.forwarded_fixture("fnDispatch 161 payload")
        self.rejects("duplicate/shadowed request 130")

    def test_delegation_without_target_refuses(self):
        source = self.forwarded_fixture().replace("                        | 130 =>", "                        | 161 =>", 1)
        with self.assertRaisesRegex(ops.Invalid, "forwarding lacks fnDispatch receiver"):
            ops.host_receivers(source)

    def test_duplicate_transport_selector_refuses(self):
        self.edit("native/resource-client/src/transport.rs", "[0..=11, ..]", "[0..=12, ..]")
        self.rejects("duplicate/shadowed selector")

    def test_route_widening_requires_registry_change(self):
        self.edit("native/resource-client/src/transport.rs", "[0..=11, ..]", "[0..=11 | 22, ..]")
        self.rejects("registered routes.*differ")

    def test_route_to_missing_host_refuses(self):
        self.edit("native/resource-client/src/transport.rs", "[0..=11, ..]", "[0..=11 | 149, ..]")
        self.rejects("socket routes lack active Host receiver")

    def test_unknown_transport_shape_requires_parser_update(self):
        prefix = "fn allowed_operation(request: &[u8], catalog_enabled: bool) -> bool {\n    "
        self.edit("native/resource-client/src/transport.rs", prefix + "match request {", prefix + "match request.as_ref() {")
        self.rejects("expected match request")

    def test_true_transport_fallback_refuses(self):
        self.edit("native/resource-client/src/transport.rs", "_ => false,", "_ => true,")
        self.rejects("unknown fallback")

    def test_registered_client_constant_drift_refuses(self):
        data, ids = ops.load(self.root)
        binding = data["client_constants"][0]
        entry = next(e for e in ids.values() if e["symbol"] == binding["operation"])
        self.edit(binding["path"], f"{binding['constant']}: u8 = {entry['code']};", f"{binding['constant']}: u8 = 161;")
        self.rejects("client constant drift")

    def test_generated_constant_reference_is_checked(self):
        data, ids = ops.load(self.root)
        binding = data["client_constants"][0]
        entry = next(e for e in ids.values() if e["symbol"] == binding["operation"])
        self.edit(binding["path"], f"{binding['constant']}: u8 = {entry['code']};", f"{binding['constant']}: u8 = crate::host_operations::{entry['symbol']};")
        ops.check(self.root)

    def test_generated_output_drift_refuses(self):
        with (self.root / ops.GENERATED).open("a") as file: file.write("// stale\n")
        self.rejects("generated request constants drift")

    def test_echoed_response_and_payload_literals_are_not_allocations(self):
        # This test asserts the gate's scope, not correctness of the deliberately
        # changed response; runtime receiving checks still own response codecs.
        self.edit("Host/Main.lean", "return ((161 : UInt8), ingress)", "return ((164 : UInt8), ingress)")
        ops.check(self.root)
        data, _ = ops.load(self.root)
        self.assertTrue(any(e["code"] == 164 and not e["request_reserved"] for e in data["response_markers"]))

    def test_comments_and_strings_are_not_receivers(self):
        with (self.root / "Host/Main.lean").open("a") as file:
            file.write('\n/- nested /- | 161 => -/\n  | 161 =>\n-/\n')
        with (self.root / "native/resource-client/src/transport.rs").open("a") as file:
            file.write('\n// fn allowed_operation() { match request { [161] => true, _ => true } }\n')
        ops.check(self.root)

if __name__ == "__main__":
    unittest.main()
