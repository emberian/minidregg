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
    if name == "habit-record.json":
        return f.check_habit_record(i).as_json()
    if name == "fire-record.json":
        return f.check_fire_record(i["record"], i["habits"], i["admitted_facts"], i["completed_acts"]).as_json()
    if name == "habit-fold.json":
        return f.habit_status(i["habit"], i["fire_times"], i["now_ms"])
    if name == "fire-batch.json":
        return f.fire_batches(i)
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
         "pinned-land.json", "land-ledger.json", "habit-record.json", "fire-record.json",
         "habit-fold.json", "fire-batch.json"]


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
    CONTEXTUAL = {"unknown-habit", "trigger-not-admitted-or-mismatched", "act-not-completed",
                  "act-mismatch", "not-after-act"}

    def test_schema_agrees_with_reference(self):
        try:
            import jsonschema
        except ImportError:  # an absent cross-check is a failure, not a pass
            self.fail("pip install jsonschema: the schema cross-check cannot run without it")
        for name, schema in (("land-record.json", "land-record"), ("verdict.json", "verdict"),
                             ("anchor-ref.json", "anchor-ref"),
                             ("habit-record.json", "habit-record"), ("fire-record.json", "fire-record")):
            with open(os.path.join(HERE, "schemas", f"{schema}.v1.schema.json")) as fh:
                validator = jsonschema.Draft202012Validator(json.load(fh))
            for v in load(name):
                key = f"{name}:{v['name']}"
                record = v["input"]["record"] if name == "fire-record.json" else v["input"]
                schema_ok = validator.is_valid(record)
                ref_ok = "ok" in v["expect"] or v["expect"]["refused"] in self.INVISIBLE | self.CONTEXTUAL \
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


def habit_observations(answerer=answer):
    """Receiver entry point: run real fixtures, plus post-act failure and budget probes."""
    import make_vectors as g
    bad = [f"{name}:{v['name']}" for name in FILES if name.startswith(("habit-", "fire-"))
           for v in load(name) if answerer(name, v) != v["expect"]]
    effects = []

    def act():
        effects.append("act")
        return "completed"

    def unavailable(result):
        assert result == "completed" and effects == ["act"]
        effects.append("record")
        raise OSError("synthetic recording unavailable")

    try:
        result, receipt = f.act_then_record(act, unavailable)
        if result != "completed" or effects != ["act", "record"] or receipt != f.Refused("record-failed", ("OSError",)):
            bad.append("post-act-failure")
    except Exception:
        bad.append("post-act-failure")
    h = g.habit()
    if f.habit_budget(h, [g.T0, g.T0 + 999], g.T0 + 999):
        bad.append("budget-full")
    if not f.habit_budget(h, [g.T0, g.T0 + 999], g.T0 + 1000):
        bad.append("budget-open-left-boundary")
    return bad


def habit_controls():
    """Independent weakenings. Each must fail an actual fixture, not a theorem-name scan."""
    def gate_on_record(act, record):
        receipt = record("not-completed")
        return act(), receipt

    def resurrect(habit, times, now):
        last = max([habit["ts_ms"]] + [t for t in times if t <= now])
        return "retired" if now - last >= habit["retirement"]["idle_ms"] else "current"

    return [
        ("signature-ignored", "sig_ok", lambda rec, key: True),
        ("trigger-ignored", "habit_matches", lambda *args: True),
        ("act-binding-ignored", "check_fire_record", lambda rec, *args: f.Ok(f.record_digest(rec))),
        ("retirement-resurrected", "habit_status", resurrect),
        ("per-fire-batches", "fire_batches", lambda rows: [{"fire": f.record_digest(r)} for r in rows]),
        ("budget-ignored", "habit_budget", lambda *args: True),
        ("record-gates-act", "act_then_record", gate_on_record),
    ]


def run_habit_suite(answerer=answer, controls=None):
    """Like S0 run_suite: absent, incomplete or surviving controls => UNREAD.
    `answerer(file, vector)` is the candidate receiver adapter, not an upstream runtime.
    """
    required = {name for name, _, _ in habit_controls()}
    controls = habit_controls() if controls is None else controls
    observations = {}
    for name, attr, replacement in controls:
        with planted(attr, replacement):
            observations[name] = habit_observations()
    controlled = set(observations) == required and all(observations.values())
    failures = habit_observations(answerer)
    return {"reading": f.verdict_reading("red" if failures else "green", "red" if controlled else "absent"),
            "failures": failures, "controls": observations}


class HabitFire(unittest.TestCase):
    def test_qualified_suite_and_controls(self):
        report = run_habit_suite()
        self.assertEqual(report["reading"], "green", report)
        self.assertEqual(len(report["controls"]), 7)
        print("habit/fire controls:", json.dumps(report, sort_keys=True))

    def test_absent_or_surviving_controls_unread(self):
        self.assertEqual(run_habit_suite(controls=[])["reading"], "unread")
        weak = habit_controls()
        weak[0] = (weak[0][0], "sig_ok", f.sig_ok)
        self.assertEqual(run_habit_suite(controls=weak)["reading"], "unread")

    def test_candidate_cannot_ignore_completed_act(self):
        def weak(name, vector):
            if name == "fire-record.json":
                return {"ok": f.record_digest(vector["input"]["record"])}
            return answer(name, vector)
        self.assertEqual(run_habit_suite(weak)["reading"], "red")

    def test_fire_ledger_retry_conflict_and_input_snapshot(self):
        import copy
        import make_vectors as g
        c = g.fire_case()
        led = f.FireLedger(c["habits"], c["admitted_facts"], c["completed_acts"])
        rec = c["record"]
        self.assertIn("appended", led.append(rec).value)
        self.assertIn("replayed", led.append(rec).value)
        later = f.sign({**f.unsigned(rec), "ts_ms": rec["ts_ms"] + 1}, g.LANDER)
        self.assertEqual(led.append(later), f.Refused("conflict"))
        snapshot = copy.deepcopy(rec)
        rec["turn"] = 99
        self.assertEqual(led.log, [snapshot])
        self.assertIn("replayed", led.append(snapshot).value)

    def test_no_receipt_is_required_to_act(self):
        self.assertEqual(f.act_then_record(lambda: 42, lambda result: f.Refused("offline")),
                         (42, f.Refused("offline")))
        effects = []
        def failed_act():
            raise ValueError("synthetic act refusal")
        with self.assertRaises(ValueError):
            f.act_then_record(failed_act, effects.append)
        self.assertEqual(effects, [])

    def test_stale_persists_with_late_history(self):
        import make_vectors as g
        h = g.habit()
        for more in ([], [g.T0 + 5000], [g.T0 + 5001, g.T0 + 7000]):
            self.assertEqual(f.habit_status(h, more, g.T0 + 8000), "retired")

    def test_new_domains_and_signature_binding(self):
        import make_vectors as g
        body = {"synthetic": 1}
        kinds = ("fleet.habit-record", "fleet.fire-record", "fleet.fire-batch", "fleet.chat-row")
        self.assertEqual(len({f.digest(k, body) for k in kinds}), len(kinds))
        h = g.habit()
        h["kind"] = "fleet.fire-record"
        self.assertFalse(f.sig_ok(h, g.K_REVIEWER))

    def test_batch_s0_adapter_no_per_fire_admission(self):
        import make_vectors as g
        import chat_backend as cb
        cases = [g.fire_case(act_over={"turn": i}) for i in range(1000)]
        self.assertTrue(all(isinstance(g.fire_answer(c), f.Ok) for c in cases))
        records = [c["record"] for c in cases]
        payloads = f.fire_batches(records)
        self.assertEqual(len(payloads), 1)
        self.assertEqual(payloads[0]["count"], 1000)
        self.assertEqual(payloads, f.fire_batches(list(reversed(records)) + records))
        backend = cb.FakeAnchorBackend(g.LANDER, admit_s=0)
        rows = [backend.sign("fleet.fire-batch", p) for p in payloads]
        ref = backend.anchor(rows)
        self.assertEqual(len(ref["covers"]), 1)
        self.assertTrue(backend.verify(rows[0], ref)["valid"])
        self.assertEqual(backend.anchor(rows), ref)

    def test_delivered_not_obeyed(self):
        import make_vectors as g
        c = g.fire_case()
        behavior = {"delivered": True, "obeyed": False}  # a concrete counterexample
        self.assertEqual(c["record"]["delivery"], "delivered")
        self.assertIsInstance(g.fire_answer(c), f.Ok)
        self.assertFalse(behavior["obeyed"])
        self.assertNotIn("obeyed", c["record"])


if __name__ == "__main__":
    unittest.main()
