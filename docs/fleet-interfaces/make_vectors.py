"""make_vectors.py [--check]: derive vectors/*.json from fixed test seeds.

The vectors are generated, never hand-edited: `--check` regenerates them in memory and exits 1
when a committed file differs (test_fleetif.py runs it). Ed25519 is deterministic, so the same
seeds give the same bytes on every machine.

Each vector is {"name", "why", "input", "expect"}; `expect` is {"ok": ...} or
{"refused": REASON, "names": [...]}, exactly what fleetif.py answers.
"""
import copy
import hashlib
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fleetif as f  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def seed(name):
    return hashlib.sha256(b"fleet-interfaces test key " + name.encode()).digest()


LANDER, REVIEWER, STRANGER = seed("lander-1"), seed("reviewer-1"), seed("stranger-1")
K_LANDER, K_REVIEWER, K_STRANGER = (f.keyid_of_seed(s) for s in (LANDER, REVIEWER, STRANGER))
T0 = 1794556800000  # 2026-11-13T00:00:00Z


def sha(tag):
    return hashlib.sha1(tag.encode()).hexdigest()


READ_SET = [
    {"path": "fleetd/land.py", "how": "read"},
    {"path": "fleetd/land_rules.toml", "how": "absent"},
    {"path": "tests", "how": "list"},
    {"path": "tests/test_land.py", "how": "read"},
]


def verdict(**over):
    body = {"kind": "fleet.verdict", "v": 1, "unit": "suite:tests.test_land", "subject": sha("tree-1"),
            "result": "green", "control": "red", "read_set": f.read_set_digest(READ_SET),
            "read_set_size": len(READ_SET), "producer": K_REVIEWER, "role": "reviewer", "ts_ms": T0}
    body.update(over)
    return f.sign(body, REVIEWER)


def land(seed_=LANDER, **over):
    body = {"kind": "fleet.land-record", "v": 1, "land_id": sha("patch-1"),
            "repo": "example.org/fleet", "base_sha": sha("main-41"), "landed_sha": sha("main-42"),
            "tested_tree": sha("tree-1"), "test_receipt": f.digest("fleet.verdict", {"receipt": 1}),
            "verdicts": [f.record_digest(verdict())], "member": K_LANDER, "ts_ms": T0 + 60000}
    body.update(over)
    return f.sign(body, seed_)


def expect(result):
    return result.as_json()


def land_vectors():
    out = []

    def add(name, why, rec):
        out.append({"name": name, "why": why, "input": rec, "expect": expect(f.check_land_record(rec))})

    good = land()
    add("ok", "a well-formed, signed record", good)
    tampered = copy.deepcopy(good)
    tampered["landed_sha"] = sha("main-43")
    add("tampered-after-signing", "any byte change breaks the signature", tampered)
    add("signed-by-other-key", "member names the lander but a stranger signed",
        land(seed_=STRANGER))
    as_verdict = dict(good)
    as_verdict["kind"] = "fleet.verdict"
    add("domain-swap", "the same bytes under another kind are another digest and do not verify",
        as_verdict)
    add("unsorted-verdicts", "cited verdicts are a sorted set",
        land(verdicts=[f.digest("fleet.verdict", {"b": 2}), f.digest("fleet.verdict", {"a": 1})]))
    add("short-sha", "shas are full 40-hex", land(base_sha="abc123"))
    big = land(repo="x" * 200, verdicts=sorted(f.digest("fleet.verdict", {"i": i}) for i in range(12)))
    add("too-large", "the canonical record must fit in 1024 bytes (store module lists by digest)", big)
    extra = dict(good)
    extra["modules"] = ["a", "b"]
    add("unknown-field", "no field outside the schema; the module list goes behind test_receipt", extra)
    return out


def verdict_vectors():
    out = []

    def add(name, why, rec):
        out.append({"name": name, "why": why, "input": rec, "expect": expect(f.check_verdict(rec))})

    add("ok-green", "green with a control that read red", verdict())
    add("ok-red", "a red verdict is a verdict", verdict(result="red"))
    add("green-without-red-control", "control did not read red: the run has no verdict (must read unread)",
        verdict(control="green"))
    add("green-no-control", "a unit with no known-red control cannot say green", verdict(control="absent"))
    add("unread-no-control", "unread is the honest reading when the control is missing",
        verdict(result="unread", control="absent"))
    add("forged-producer", "producer names the reviewer, the lander signed",
        f.sign(dict(f.unsigned(verdict())), LANDER))
    return out


def anchor(**over):
    body = {"kind": "fleet.anchor-ref", "v": 1, "backend": "mini", "ref": "0x" + "ab" * 32,
            "covers": sorted([f.record_digest(land()), f.record_digest(verdict())]),
            "at_height": None, "state": "pending", "proof_state": "n/a", "reason": None}
    body.update(over)
    return body


def anchor_vectors():
    out = []

    def add(name, why, rec):
        out.append({"name": name, "why": why, "input": rec, "expect": expect(f.check_anchor_ref(rec))})

    add("ok-pending", "admitted, no height yet", anchor())
    add("ok-final", "final carries the admission height", anchor(state="final", at_height=812))
    add("final-without-height", "final must name where", anchor(state="final"))
    add("failed-proof-final", "a failed proof cannot be final", anchor(state="final", at_height=9,
                                                                     proof_state="failed", reason="prover"))
    add("failed-proof-pending", "a failed proof leaves the rows valid and the anchor pending, named",
        anchor(proof_state="failed", reason="prover exited 137"))
    add("empty-covers", "an anchor covers at least one row", anchor(covers=[]))
    return out


def anchor_step_vectors():
    p = anchor()
    fin = anchor(state="final", at_height=812)
    rdy = anchor(state="final", at_height=812, proof_state="ready")
    cases = [
        ("pending-to-final", "strengthening is allowed", p, fin),
        ("final-to-ready", "a proof completing later", fin, rdy),
        ("exact-retry", "the same rows anchored again answer the same ref", p, anchor()),
        ("final-to-pending", "never weakens", fin, p),
        ("ready-to-pending", "a ready proof never regresses", rdy, anchor(state="final", at_height=812)),
        ("covers-changed", "a ref covers exactly the rows it was given",
         p, anchor(covers=[f.record_digest(land())])),
        ("height-moved", "a final height is fixed", fin, anchor(state="final", at_height=813)),
    ]
    return [{"name": n, "why": w, "input": {"prev": a, "next": b}, "expect": expect(f.anchor_step(a, b))}
            for n, w, a, b in cases]


def pinned_vectors():
    cases = [
        ("unrelated-change", "a change outside the read set does not stale the land",
         [{"op": "modify", "path": "docs/readme.md"}]),
        ("read-path-modified", "a read file changed", [{"op": "modify", "path": "fleetd/land.py"}]),
        ("absent-path-added", "a file the check looked for and missed now exists",
         [{"op": "add", "path": "fleetd/land_rules.toml"}]),
        ("listed-dir-grew", "a new test in a listed directory moves the listing",
         [{"op": "add", "path": "tests/test_new.py"}]),
        ("nested-add-not-listed", "a grandchild does not move a one-level listing",
         [{"op": "add", "path": "tests/data/x.json"}]),
        ("every-moved-named", "the refusal names every moved entry, not the first",
         [{"op": "modify", "path": "tests/test_land.py"}, {"op": "delete", "path": "fleetd/land.py"},
          {"op": "add", "path": "fleetd/land_rules.toml"}]),
    ]
    return [{"name": n, "why": w, "input": {"read_set": READ_SET, "changes": c},
             "expect": expect(f.pinned_land(READ_SET, c))} for n, w, c in cases]


def ledger_vectors():
    roles = [{"member": K_LANDER, "role": "lander", "from_ms": T0, "until_ms": T0 + 86400000},
             {"member": K_REVIEWER, "role": "reviewer", "from_ms": T0, "until_ms": T0 + 86400000}]
    second = land(land_id=sha("patch-2"), base_sha=sha("main-42"), landed_sha=sha("main-43"))
    steps = [
        ("first", land()),
        ("exact-retry", land()),
        ("same-id-other-bytes", land(landed_sha=sha("main-99"))),
        ("second-land", second),
        ("expired-grant", land(land_id=sha("patch-3"), ts_ms=T0 + 86400000)),
        ("reviewer-cannot-land", land(seed_=REVIEWER, member=K_REVIEWER, land_id=sha("patch-4"))),
    ]
    led = f.LandLedger(roles=roles)
    return [{"name": "land-ledger", "why": "S1 invariants 1, 4, 5 over one sequence",
             "input": {"roles": roles, "steps": [{"name": n, "record": r} for n, r in steps]},
             "expect": [{"name": n, **led.append(r).as_json()} for n, r in steps]}]


# Synthetic admitted inputs: these are NOT fabricated runtime admission proofs.
FACT = f.digest("fleet.chat-row", {"event": "example.review.ready", "n": 1})


def habit(seed_=REVIEWER, **over):
    body = {"kind": "fleet.habit-record", "v": 1,
            "trigger": {"kind": "event", "value": "example.review.ready"},
            "steer": {"rule": "example.show-review-checklist", "scope": "example/lane"},
            "budget": {"max_fires": 2, "window_ms": 1000}, "owner": K_REVIEWER,
            "retirement": {"idle_ms": 5000}, "ts_ms": T0}
    body.update(over)
    return f.sign(body, seed_)


def fire_case(habit_=None, act_over=None, seed_=LANDER, **over):
    h = habit_ if habit_ is not None else habit()
    hd = f.record_digest(h)
    act = {"habit": hd, "trigger_fact": FACT, "turn": 7, "lane": "example/lane",
           "bytes": f.digest("fleet.chat-row", {"text": "Synthetic checklist"}),
           "member": K_LANDER, "delivery": "delivered", "ts_ms": T0 + 100}
    act.update(act_over or {})
    ad = f.digest("fleet.chat-row", {"completed_act": act})
    rec = {"kind": "fleet.fire-record", "v": 1,
           **{k: v for k, v in act.items() if k != "ts_ms"}, "act": ad, "ts_ms": T0 + 101}
    rec.update(over)
    return {"record": f.sign(rec, seed_), "habits": {hd: h},
            "admitted_facts": {FACT: {"event": "example.review.ready", "ts_ms": T0 + 10}},
            "completed_acts": {ad: act}}


def fire_answer(case):
    return f.check_fire_record(case["record"], case["habits"], case["admitted_facts"], case["completed_acts"])


def habit_vectors():
    cases = [
        ("not-object", []),
        ("event-trigger", habit()),
        ("fact-trigger", habit(trigger={"kind": "fact", "value": FACT})),
        ("not-a-fact-digest", habit(trigger={"kind": "fact", "value": "example.ready"})),
        ("empty-event", habit(trigger={"kind": "event", "value": ""})),
        ("unknown-trigger-field", habit(trigger={"kind": "event", "value": "x", "regex": ".*"})),
        ("no-rule", habit(steer={"scope": "example/lane"})),
        ("zero-budget", habit(budget={"max_fires": 0, "window_ms": 1000})),
        ("boolean-budget", habit(budget={"max_fires": True, "window_ms": 1000})),
        ("zero-retirement", habit(retirement={"idle_ms": 0})),
        ("forged-owner", habit(seed_=STRANGER)),
    ]
    tampered = habit()
    tampered["steer"]["rule"] = "example.skip-checklist"
    cases.append(("tampered-rule", tampered))
    return [{"name": n, "why": "S10 owner, trigger and rule structure", "input": r,
             "expect": expect(f.check_habit_record(r))} for n, r in cases]


def fire_vectors():
    cases = [("after-act", fire_case()),
             ("exact-fact-trigger", fire_case(habit(trigger={"kind": "fact", "value": FACT}))),
             ("same-time-is-not-after", fire_case(ts_ms=T0 + 100)),
             ("pre-act", fire_case(ts_ms=T0 + 99)),
             ("wrong-act-turn", fire_case(turn=8)),
             ("wrong-act-bytes", fire_case(bytes=f.digest("fleet.chat-row", {"other": 1}))),
             ("unmatched-event", fire_case(habit(trigger={"kind": "event", "value": "example.other"}))),
             ("unmatched-fact", fire_case(habit(trigger={"kind": "fact", "value": f.digest("fleet.chat-row", {})}))),
             ("late-truthful-receipt", fire_case(ts_ms=T0 + 6000))]
    for name, field in (("no-admitted-trigger", "admitted_facts"),
                        ("no-completed-act", "completed_acts"), ("unknown-habit", "habits")):
        c = fire_case()
        c[field] = {}
        cases.append((name, c))
    c = fire_case()
    c["record"]["delivery"] = "attempted"
    cases.append(("tampered-fire", c))
    c = fire_case()
    c["record"] = f.sign(c["record"], STRANGER)
    cases.append(("forged-member", c))
    c = fire_case()
    c["record"]["obeyed"] = True
    c["record"] = f.sign(c["record"], LANDER)
    cases.append(("delivery-is-not-obedience", c))
    c = fire_case()
    c["admitted_facts"][FACT]["ts_ms"] = T0 + 200
    cases.append(("fact-after-act", c))
    c = fire_case()
    c["admitted_facts"][FACT]["ts_ms"] = T0 - 100
    cases.append(("historical-admitted-trigger", c))
    cases.append(("habit-after-act", fire_case(habit(ts_ms=T0 + 200))))
    c = fire_case()
    c["record"] = []
    cases.append(("not-object", c))
    return [{"name": n, "why": "S11 exact post-act binding; no obedience assertion", "input": c,
             "expect": expect(fire_answer(c))} for n, c in cases]


def habit_fold_vectors():
    cases = [("not-started", [], -1), ("current", [], 4999), ("idle-boundary", [], 5000),
             ("fire-renews", [4000], 5000), ("renewed-boundary", [4000], 9000),
             ("late-fire-cannot-resurrect", [5000, 6000], 6001),
             ("future-fire-ignored", [7000], 5000)]
    return [{"name": n, "why": "Complete synthetic history, monotone retirement after an idle gap",
             "input": {"habit": habit(), "fire_times": [T0 + t for t in ts], "now_ms": T0 + now},
             "expect": f.habit_status(habit(), [T0 + t for t in ts], T0 + now)} for n, ts, now in cases]


def fire_batch_vectors():
    a = fire_case()["record"]
    b = fire_case(act_over={"turn": 8})["record"]
    c = fire_case(ts_ms=T0 + 3600000)["record"]
    d = fire_case(act_over={"member": K_REVIEWER}, seed_=REVIEWER)["record"]
    return [{"name": n, "why": "One digest payload per seat-hour; verified records are the input",
             "input": rs, "expect": f.fire_batches(rs)} for n, rs in
            [("empty", []), ("one-seat-hour", [a, b]), ("retry-and-order", [b, a, a]),
             ("hour-boundary", [a, c]), ("separate-seats", [a, d])]]


FILES = {
    "habit-record.json": habit_vectors,
    "fire-record.json": fire_vectors,
    "habit-fold.json": habit_fold_vectors,
    "fire-batch.json": fire_batch_vectors,
    "land-record.json": land_vectors,
    "verdict.json": verdict_vectors,
    "anchor-ref.json": anchor_vectors,
    "anchor-step.json": anchor_step_vectors,
    "pinned-land.json": pinned_vectors,
    "land-ledger.json": ledger_vectors,
}


def render(fn):
    return json.dumps({"generated_by": "make_vectors.py", "vectors": fn()}, indent=1, sort_keys=True) + "\n"


def main():
    check = "--check" in sys.argv
    stale = []
    for name, fn in FILES.items():
        path = os.path.join(HERE, "vectors", name)
        text = render(fn)
        if check:
            if not os.path.exists(path) or open(path).read() != text:
                stale.append(name)
        else:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            open(path, "w").write(text)
    if stale:
        print("stale vectors:", ", ".join(stale), "(run make_vectors.py)")
        return 1
    print("vectors", "current" if check else "written", len(FILES), "files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
