"""One synthetic native owner held open for Mini's durable B3 reply post."""

import json
import os
from pathlib import Path
import socket
import subprocess
import time

from tests.test_native_hybrid_author import NativeHybridAuthorTest, OPENSSL


class NativeB3Handoff(NativeHybridAuthorTest):
    def test_mini_reply_post_and_reopen(self):
        handoff = Path(os.environ["FN_B3_HANDOFF_DIR"])
        self.assertTrue(handoff.is_absolute())
        self.assertFalse(handoff.exists())

        raw_ml = self.root / "ml-public.raw"
        exported = subprocess.run(
            [OPENSSL, "asn1parse", "-inform", "PEM", "-in",
             str(self.ml_public), "-strparse", "17", "-noout",
             "-out", str(raw_ml)],
            capture_output=True, timeout=30, check=False,
        )
        self.assertEqual(exported.returncode, 0, exported.stderr)
        self.assertEqual(len(raw_ml.read_bytes()), 1952)

        owner = self.start_owner()
        enrolled = self.invoke("hybrid-enroll", str(self.control), "1",
                               str(self.principal), str(self.ed_public),
                               str(self.ml_public))
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr)

        handoff.mkdir(parents=True)
        ready = {
            "version": 1,
            "control": str(self.control),
            "principal": str(self.principal),
            "ed_public": str(self.ed_public),
            "ed_secret": str(self.ed_secret),
            "ml_public": str(self.ml_public),
            "ml_private": str(self.ml_private),
            "ml_public_raw": str(raw_ml),
            "generation": 1,
            "image": os.environ["FN_NATIVE_HOST"],
            "store": str(self.store),
            "config": str(self.config),
        }
        temporary = handoff / "ready.json.tmp"
        temporary.write_text(json.dumps(ready, sort_keys=True) + "\n",
                             encoding="ascii")
        temporary.replace(handoff / "ready.json")

        deadline = time.monotonic() + 900
        marker = handoff / "mini-finished.json"
        while not marker.is_file() and time.monotonic() < deadline:
            self.assertIsNone(owner.poll(), "synthetic owner died during Mini post")
            time.sleep(0.1)
        self.assertTrue(marker.is_file(), "Mini B3 handoff timed out")
        outcome = json.loads(marker.read_text(encoding="ascii"))
        self.assertEqual(outcome["result"], "accepted")
        msgid = outcome["message_id"]
        self.assertTrue(msgid.startswith("<") and msgid.endswith(">"))
        exact_source = (handoff / "posted.source").read_bytes()

        self.stop_owner(owner)
        reopened = self.start_owner()
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as conn:
                with conn.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))
                    stream.write(("ARTICLE " + msgid + "\r\n").encode("ascii"))
                    self.assertTrue(stream.readline().startswith(b"220 "))
                    article = bytearray()
                    while True:
                        line = stream.readline()
                        self.assertTrue(line, "ARTICLE terminated early")
                        if line == b".\r\n":
                            break
                        article.extend(line[1:] if line.startswith(b"..") else line)
                    self.assertIn(b"FN-Authorship: ", bytes(article)[:200])
                    self.assertTrue(bytes(article).endswith(exact_source))
                    reopened_carrier = self.root / "b3-reopened-carrier.eml"
                    reopened_carrier.write_bytes(bytes(article))
                    verified = self.invoke("hybrid-verify-source",
                                           str(reopened_carrier),
                                           str(self.ml_public))
                    self.assertEqual(verified.returncode, 0,
                                     verified.stderr.decode("utf-8", "replace"))
                    fields = verified.stdout.decode("ascii").strip().split()
                    self.assertEqual(len(fields), 6, verified.stdout)
                    self.assertEqual(fields[0], "fn-portable-v1")
                    self.assertEqual(fields[1], self.principal.read_bytes().hex())
                    self.assertEqual(fields[2], outcome["source_identity"])
                    self.assertEqual(fields[3], self.ed_public.read_bytes().hex())
                    self.assertEqual(fields[4], raw_ml.read_bytes().hex())
                    self.assertEqual(bytes.fromhex(fields[5]), exact_source)
                    (handoff / "reopened-carrier.eml").write_bytes(bytes(article))
                    (handoff / "verified-source.txt").write_bytes(verified.stdout)
                    stream.write(("HDR :fn-verified " + msgid + "\r\n").encode("ascii"))
                    self.assertEqual(stream.readline(), b"225 headers follow\r\n")
                    verdict = stream.readline()
                    self.assertTrue(verdict.startswith(b"0 verified "), verdict)
                    self.assertTrue(verdict.endswith(b" keyring 1\r\n"), verdict)
                    self.assertEqual(stream.readline(), b".\r\n")
        finally:
            self.stop_owner(reopened)
