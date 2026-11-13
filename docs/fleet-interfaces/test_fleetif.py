"""python3 -m unittest discover -s docs/fleet-interfaces -p 'test_*.py'

1. the committed vectors are what make_vectors.py derives;
2. fleetif.py answers every vector exactly;
3. the JSON Schemas agree with fleetif.py on every structural refusal;
4. KNOWN-RED CONTROLS: each planted weakening of the reference must make some vector fail.
   A vector set that a broken checker also passes has no teeth, so its passes are not read.
"""
import contextlib
import json
import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fleetif as f  # noqa: E402


def load(name):
    with open(os.path.join(HERE, "vectors", name)) as fh:
        return json.load(fh)["vectors"]


def answer(name, v):
    i = v["input"]
    if name == "land-record.json":
        return f.check_land_record(i).as_json()
    if name == "verdict.json":
        return f.check_verdict(i).as_json()
    if name == "anchor-ref.json":
        return f.check_anchor_ref(i).as_json()
    if name == "anchor-step.json":
        return f.anchor_step(i["prev"], i["next"]).as_json()
    if name == "pinned-land.json":
        return f.pinned_land(i["read_set"], i["changes"]).as_json()
    if name == "land-ledger.json":
        led = f.LandLedger(roles=i["roles"])
        return [{"name": s["name"], **led.append(s["record"]).as_json()} for s in i["steps"]]
    raise KeyError(name)


FILES = ["land-record.json", "verdict.json", "anchor-ref.json", "anchor-step.json",
         "pinned-land.json", "land-ledger.json"]


def mismatches():
    bad = []
    for name in FILES:
        for v in load(name):
            if answer(name, v) != v["expect"]:
                bad.append(f"{name}:{v['name']}")
    return bad


@contextlib.contextmanager
def planted(attr, replacement):
    old = getattr(f, attr)
    setattr(f, attr, replacement)
    try:
        yield
    finally:
        setattr(f, attr, old)


class Vectors(unittest.TestCase):
    def test_vectors_are_derived(self):
        r = subprocess.run([sys.executable, "-I", os.path.join(HERE, "make_vectors.py"), "--check"],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_reference_answers_every_vector(self):
        self.assertEqual(mismatches(), [])

    def test_vector_counts(self):
        counts = {n: len(load(n)) for n in FILES}
        self.assertTrue(all(counts.values()), counts)


class Schemas(unittest.TestCase):
    # what a JSON Schema cannot say: a signature, the canonical size, and set order
    INVISIBLE = {"bad-signature", "too-large"}
    UNORDERED = {"land-record.json:unsorted-verdicts"}

    def test_schema_agrees_with_reference(self):
        try:
            import jsonschema
        except ImportError:  # an absent cross-check is a failure, not a pass
            self.fail("pip install jsonschema: the schema cross-check cannot run without it")
        for name, schema in (("land-record.json", "land-record"), ("verdict.json", "verdict"),
                             ("anchor-ref.json", "anchor-ref")):
            with open(os.path.join(HERE, "schemas", f"{schema}.v1.schema.json")) as fh:
                validator = jsonschema.Draft202012Validator(json.load(fh))
            for v in load(name):
                key = f"{name}:{v['name']}"
                schema_ok = validator.is_valid(v["input"])
                ref_ok = "ok" in v["expect"] or v["expect"]["refused"] in self.INVISIBLE \
                    or key in self.UNORDERED
                self.assertEqual(schema_ok, ref_ok, key)


class KnownRedControls(unittest.TestCase):
    """Each control weakens one rule of the reference; the vectors must notice."""

    def assert_control_reads_red(self, attr, replacement):
        with planted(attr, replacement):
            self.assertNotEqual(mismatches(), [], f"control {attr}: vectors still pass, they have no teeth")

    def test_signatures_ignored(self):
        self.assert_control_reads_red("sig_ok", lambda rec, keyid: True)

    def test_first_moved_only(self):
        orig = f.moved
        self.assert_control_reads_red("moved", lambda rs, cs: orig(rs, cs)[:1])

    def test_listing_ignored(self):
        def no_list(entry, change):
            return False if entry["how"] == "list" else HITS(entry, change)
        HITS = f.hits
        self.assert_control_reads_red("hits", no_list)

    def test_control_rule_ignored(self):
        self.assert_control_reads_red("verdict_reading", lambda result, control: result)

    def test_anchor_may_weaken(self):
        self.assert_control_reads_red("anchor_step", lambda a, b: f.Ok("same"))


if __name__ == "__main__":
    unittest.main()
