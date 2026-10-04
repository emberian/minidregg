#!/usr/bin/env python3
"""render-enrol, run for real (no Lean, no Rust, no network). usage: python3 deploy/pay/test-render-enrol.py

Pins the operator ruling (50 DREGG per week, receiving address 5N2u...) to the integers the tariff
carries, shows the floor rounding cannot journal an honest payer, and that every refusal is by name.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
RENDER = HERE / "render-enrol"
TERMS = HERE / "enrol-terms.json"
ADDRESS = "5N2uUG4TEwvM4acjWRpZ981CJa4p5e9RcuAYQvuUZLp6"
sys.path.insert(0, str(HERE))
from importlib.machinery import SourceFileLoader  # noqa: E402
render_module = SourceFileLoader("render_enrol", str(RENDER)).load_module()


def run(out, terms=TERMS, version="1", extra=()):
    return subprocess.run([sys.executable, str(RENDER), "--terms", str(terms), "--out", str(out), "--version", version,
                           "--control", "53", "--observer-capability", "4030", "--enrol-capability", "4032", *extra],
                          capture_output=True, text=True)


class Rendered(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="render-enrol-")
        cls.out = Path(cls.tmp.name) / "out"
        done = run(cls.out)
        assert done.returncode == 0, done.stderr
        cls.book = json.loads((cls.out / "book.json").read_text())
        cls.on = json.loads((cls.out / "tariff-on.json").read_text())

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_rate_is_the_floor_of_fifty_tokens_a_week(self):
        tariff = self.book["tariff"]
        self.assertEqual(tariff["nodeHourRate"], "297619")
        week_credit = 168 * int(tariff["nodeHourRate"])  # Kernel.PayTariff.Tariff.weekCredit
        self.assertEqual(week_credit, 49_999_992)
        self.assertEqual(tariff["creditPerAtomic"], "1")
        self.assertEqual(tariff["decimals"], "6")
        # 50 tokens at 6 decimals is 50_000_000 atomic; the floor leaves the week 8 atomic cheaper.
        self.assertLessEqual(week_credit, 50 * 10 ** 6)
        self.assertGreater(week_credit + 168, 50 * 10 ** 6)  # and is the largest such integer rate

    def test_a_payer_of_exactly_the_asked_amount_is_never_journaled_below_price(self):
        week_credit = 168 * int(self.book["tariff"]["nodeHourRate"])
        for birth_fee in (0, 7, 9, 1000):  # Kernel.PayEnrolDecision.enrolPrice = birthFee + weekCredit
            self.assertGreaterEqual(50 * 10 ** 6 + birth_fee, birth_fee + week_credit)
        # one hourly step more would have priced exactly that payer out
        self.assertLess(50 * 10 ** 6, 168 * (int(self.book["tariff"]["nodeHourRate"]) + 1))
        # a renewal of exactly 50 tokens buys one whole week (RenewPlan.weeks = credit / weekCredit)
        self.assertEqual(50 * 10 ** 6 // week_credit, 1)

    def test_the_address_is_book_row_zero_and_the_pins_name_it(self):
        self.assertEqual(self.book["book"][0], ADDRESS)
        self.assertIsNone(self.book["tariff"]["enrolIndex"])
        self.assertEqual(self.on["book"], [])
        self.assertEqual(self.on["tariff"]["enrolIndex"], "0")
        self.assertEqual(self.on["tariff"]["version"], "2")
        v1 = json.loads((self.out / "enrol.json").read_text())
        v2 = json.loads((self.out / "enrol-v2.json").read_text())
        self.assertEqual((v1["type"], v1["enrolAddress"]), ("minidregg-enrol-pin-v1", ADDRESS))
        self.assertEqual((v2["type"], v2["enrolAddress"], v2["decimals"]), ("minidregg-enrol-pin-v2", ADDRESS, "6"))
        self.assertEqual(sorted(v2), sorted(["type", "enrolAddress", "mint", "tokenProgram", "decimals", "login"]))
        self.assertEqual(len(render_module.b58_decode32(ADDRESS, "address")), 32)

    def test_the_tick_env_carries_the_enrollment_quartet_and_no_address_or_rate(self):
        env = (self.out / "watcher.env").read_text()
        lines = dict(l.split("=", 1) for l in env.splitlines() if l and not l.startswith("#"))
        self.assertEqual(lines["PAY_ENROL_INDEX"], "0")
        self.assertEqual(lines["PAY_JOURNAL_FLOOR"], "1000000")
        self.assertEqual(lines["PAY_ENROL_CAPABILITY"], "4032")
        self.assertEqual(lines["PAY_OPERATOR_SOCKET"], "/var/lib/mini/store/node/operator/mini.sock")
        self.assertNotIn(ADDRESS, env)
        self.assertNotIn("297619", env)

    def test_base58_round_trip_and_one_source(self):
        for raw in (bytes(range(1, 33)), b"\0" + bytes(range(1, 32))):
            self.assertEqual(render_module.b58_decode32(render_module.b58_encode(raw), "k"), raw)
        # the address and the rate are stated in the terms file and in prose docs, in no script or config
        repo = HERE.parents[1]
        for path in [p for p in (repo / "deploy").rglob("*") if p.is_file() and p.suffix in {".sh", ".json", ".py", ".service", ".timer", ".env", ""}]:
            if path.name in {"enrol-terms.json", "test-render-enrol.py"}:
                continue
            try:
                text = path.read_text()
            except UnicodeDecodeError:
                continue
            self.assertNotIn(ADDRESS, text, str(path))
            self.assertNotIn("297619", text, str(path))


class Refusals(unittest.TestCase):
    def refuse(self, mutate, want, extra=()):
        terms = json.loads(TERMS.read_text())
        mutate(terms)
        with tempfile.TemporaryDirectory(prefix="render-enrol-r-") as tmp:
            path = Path(tmp) / "terms.json"
            path.write_text(json.dumps(terms))
            done = run(Path(tmp) / "out", terms=path, extra=extra)
            self.assertNotEqual(done.returncode, 0, "accepted")
            self.assertIn(want, done.stderr)
            self.assertFalse((Path(tmp) / "out").exists(), "left an output directory behind")

    def test_refusals(self):
        self.refuse(lambda t: t.update(enrolAddress=ADDRESS[:-3]), "is not a 32-byte")  # a 31-byte key
        self.refuse(lambda t: t.update(enrolAddress="1" * 32), "non-zero")  # the all-zero key
        self.refuse(lambda t: t.update(enrolAddress="EMBER_ENROL_ADDRESS"), "not base58")  # the old placeholder
        self.refuse(lambda t: t.update(weekPriceAtomic="100"), "below one credit per hour")
        self.refuse(lambda t: t.update(weekPriceAtomic="05000000"), "canonical decimal")
        self.refuse(lambda t: t.update(journalFloor="60000000"), "journalFloor above the week price")
        self.refuse(lambda t: t.update(decimals="39"), "decimals exceed")
        self.refuse(lambda t: t.update(extra="x"), "fields differ")
        self.refuse(lambda t: t.update(operatorSocket="mini.sock"), "absolute path")
        self.refuse(lambda t: t.update(enrolIndex="1"), "enrolIndex must be 0")

    def test_existing_output_and_duplicate_rows_are_refused(self):
        with tempfile.TemporaryDirectory(prefix="render-enrol-e-") as tmp:
            existing = Path(tmp) / "out"
            existing.mkdir()
            done = run(existing)
            self.assertNotEqual(done.returncode, 0)
            self.assertIn("refusing existing output", done.stderr)
            extras = Path(tmp) / "extra"
            extras.write_text(ADDRESS + "\n")
            done = run(Path(tmp) / "out2", extra=("--book-extra", str(extras)))
            self.assertNotEqual(done.returncode, 0)
            self.assertIn("repeats an address", done.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
