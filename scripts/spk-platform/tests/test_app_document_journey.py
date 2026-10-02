import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

source = Path(__file__).resolve().parents[1] / "app-document-journey.py"
spec = importlib.util.spec_from_file_location("app_document_journey", source)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class IndependentReadback(unittest.TestCase):
    def test_another_store_and_wrong_host_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            config, host, alias = root / "config.json", root / "host", root / "host-alias"
            config.write_bytes(b"same-store-config")
            host.write_bytes(b"sealed-host")
            alias.write_bytes(host.read_bytes())
            exporter = {"type": "minidregg-participant-workspace-v1", "config": str(config), "socket": str(root / "public.sock"), "host": str(host)}
            reader = {**exporter, "host": str(alias)}
            fixture = {"attachment": {"miniConfig": str(config), "miniConfigSha256": m.sha(config), "publicSocket": exporter["socket"]}, "artifacts": {"host": {"path": str(host), "sha256": m.sha(host)}}}
            m.same_world(exporter, reader, fixture)
            with self.assertRaisesRegex(RuntimeError, "another Store"):
                m.same_world(exporter, {**reader, "socket": str(root / "other.sock")}, fixture)
            with self.assertRaisesRegex(RuntimeError, "another Store"):
                m.same_world(exporter, {**reader, "config": str(root / "other.json")}, fixture)
            alias.write_bytes(b"different-host")
            with self.assertRaisesRegex(RuntimeError, "Host pin differs"):
                m.same_world(exporter, reader, fixture)

    def test_reference_file_matches_native_flat_room_spelling(self):
        self.assertEqual(m.reference_path(Path("/ws"), "joinedv1-r0/notes"), Path("/ws/refs/joinedv1-r0.notes.json"))
        for name in ("../notes", "room//notes", "room.notes", "room/with_underscore"):
            with self.subTest(name=name), self.assertRaises(RuntimeError):
                m.reference_path(Path("/ws"), name)

    def status(self, body):
        return {"receipt": {"bodySha256": hashlib.sha256(body).hexdigest(), "bodyBytes": str(len(body)), "operation": "81", "transaction": "91"}}

    def document(self, body, status):
        r = status["receipt"]
        return ("old notes\nSheet example · app 1 generation 2 · exported by 3\nExport " + r["bodySha256"] + " · operation 81 · receipt 91\n").encode() + body + b"\nother notes\n"

    def test_exact_unicode_crlf_and_unterminated_body(self):
        for body in ("name,value\r\nλ,7\r\n".encode(), b"name,value\nfinal,7", b""):
            with self.subTest(body=body):
                status = self.status(body)
                result = m.verified_readback(self.document(body, status), status)
                self.assertEqual(result["bodySha256"], status["receipt"]["bodySha256"])

    def test_duplicate_export_attribution_refused(self):
        body = b"a,b\n"
        status = self.status(body)
        with self.assertRaisesRegex(RuntimeError, "one exact export attribution"):
            m.verified_readback(self.document(body, status) * 2, status)

    def test_changed_or_truncated_body_refused(self):
        body = b"a,b\n"
        status = self.status(body)
        for changed in (b"x,b\n", b"a"):
            with self.subTest(changed=changed), self.assertRaisesRegex(RuntimeError, "bytes differ"):
                m.verified_readback(self.document(changed, status), status)

    def test_other_receipt_cannot_substitute(self):
        body = b"a,b\n"
        status = self.status(body)
        doc = self.document(body, status).replace(b"receipt 91", b"receipt 92")
        with self.assertRaisesRegex(RuntimeError, "one exact export attribution"):
            m.verified_readback(doc, status)

    def test_readback_source_target_and_own_live_atoms(self):
        page = {"type": "document", "host": "31", "lines": [
            {"kind": "atom", "text": "λ,7\r", "struck": False},
            {"kind": "atom", "text": "old", "struck": True},
            {"kind": "embed", "text": "source quote"}]}
        self.assertEqual(m.readback_bytes(page, "31"), "λ,7\r\n".encode())
        with self.assertRaisesRegex(RuntimeError, "another document"):
            m.readback_bytes(page, "32")


if __name__ == "__main__":
    unittest.main()
