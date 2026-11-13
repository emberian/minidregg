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


FILES = {
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
