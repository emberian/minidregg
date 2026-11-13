"""chat_backend.py: the S0 ChatBackend contract as a conformance suite any backend can be run under.

A backend is an object with
    sign(domain, payload: dict) -> row: dict          local; never waits on anchoring
    anchor(rows: list[dict]) -> AnchorRef dict | None  admits a batch; None only for `none`
    verify(row, anchor_ref | None) -> {"valid", "anchored": none|pending|final, "reason"}
    status() -> {"backend", "lag_rows"}
    refresh(anchor_ref) -> AnchorRef dict              the backend's current word on that ref

`NoneBackend` is the reference (fleet's behaviour today). `FakeAnchorBackend` stands in for
`mini` or `dregg`: it admits after a delay, finalizes on a later refresh, and can fail proofs or be
unavailable. A real adapter (for example one that drives `mini fleet --action publish`) is run
under the same suite with `run_suite(make_backend)`.

`run_suite` runs the KNOWN-RED CONTROLS first: three planted broken backends, each of which must
fail at least one invariant. If any control passes, the suite's results are UNREAD.
"""
import threading
import time

import fleetif as f

SIGN_BUDGET_S = 0.05     # invariant 1: signing is local; an anchor in flight never slows it


class NoneBackend:
    name = "none"

    def __init__(self, seed32):
        self.seed = seed32
        self.keyid = f.keyid_of_seed(seed32)

    def sign(self, domain, payload):
        row = {"kind": "fleet.chat-row", "domain": domain, "payload": payload, "member": self.keyid}
        return self._sign(row)

    def _sign(self, row):
        d = bytes.fromhex(f.digest("fleet.chat-row", f.unsigned(row)).split(":", 1)[1])
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
        out = dict(f.unsigned(row))
        out["sig"] = Ed25519PrivateKey.from_private_bytes(self.seed).sign(d).hex()
        return out

    @staticmethod
    def row_digest(row):
        return f.digest("fleet.chat-row", f.unsigned(row))

    def row_valid(self, row):
        from cryptography.exceptions import InvalidSignature
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
        try:
            pub = Ed25519PublicKey.from_public_bytes(bytes.fromhex(row["member"].split(":", 1)[1]))
            pub.verify(bytes.fromhex(row["sig"]), bytes.fromhex(self.row_digest(row).split(":", 1)[1]))
            return True
        except (InvalidSignature, ValueError, KeyError):
            return False

    def anchor(self, rows):
        return None

    def refresh(self, ref):
        return ref

    def verify(self, row, ref):
        if not self.row_valid(row):
            return {"valid": False, "anchored": "none", "reason": "bad-signature"}
        if ref is None:
            return {"valid": True, "anchored": "none", "reason": None}
        if self.row_digest(row) not in ref["covers"]:
            return {"valid": True, "anchored": "none", "reason": "not-covered"}
        return {"valid": True, "anchored": ref["state"], "reason": ref["reason"]}

    def status(self):
        return {"backend": self.name, "lag_rows": 0}


class FakeAnchorBackend(NoneBackend):
    """Admission takes `admit_s`; the second refresh after admission makes it final; proofs fail
    when `fail_proofs`; `available=False` queues rows and reports them as lag."""
    name = "test"

    def __init__(self, seed32, admit_s=0.2, fail_proofs=False):
        super().__init__(seed32)
        self.admit_s, self.fail_proofs = admit_s, fail_proofs
        self.available = True
        self.lock = threading.Lock()
        self.refs = {}       # covers tuple -> anchor dict
        self.refreshes = {}
        self.queued = []
        self.height = 100

    def anchor(self, rows):
        covers = sorted({self.row_digest(r) for r in rows})
        if not self.available:
            with self.lock:
                self.queued.extend(covers)
            return None
        time.sleep(self.admit_s)     # the admission round trip
        with self.lock:
            key = tuple(covers)
            if key not in self.refs:  # exact retry answers the same ref
                self.refs[key] = {"kind": "fleet.anchor-ref", "v": 1, "backend": "test",
                                  "ref": "t-%d" % len(self.refs), "covers": covers, "at_height": None,
                                  "state": "pending", "proof_state": "pending", "reason": None}
            return dict(self.refs[key])

    def refresh(self, ref):
        with self.lock:
            cur = self.refs[tuple(ref["covers"])]
            n = self.refreshes[cur["ref"]] = self.refreshes.get(cur["ref"], 0) + 1
            if n >= 2 and cur["state"] == "pending":
                self.height += 1
                cur["state"], cur["at_height"] = "final", self.height
                cur["proof_state"] = "failed" if self.fail_proofs else "ready"
                if self.fail_proofs:
                    cur["state"], cur["at_height"], cur["reason"] = "pending", None, "prover exited 137"
            return dict(cur)

    def status(self):
        return {"backend": self.name, "lag_rows": len(self.queued)}


# ---------------------------------------------------------------- the invariants

def inv1_sign_is_local(b):
    """Signing never waits on an anchor in flight."""
    rows = [b.sign("chat", {"n": i}) for i in range(4)]
    t = threading.Thread(target=b.anchor, args=(rows,))
    t.start()
    t0 = time.monotonic()
    b.sign("chat", {"n": 99})
    took = time.monotonic() - t0
    t.join()
    assert took < SIGN_BUDGET_S, f"sign took {took:.3f} s with an anchor in flight"


def inv2_anchor_idempotent(b):
    rows = [b.sign("chat", {"n": 1}), b.sign("chat", {"n": 2})]
    a, c = b.anchor(rows), b.anchor(list(reversed(rows)))
    if a is None:
        assert c is None
        return
    assert a["ref"] == c["ref"] and a["covers"] == c["covers"], "exact retry gave another ref"


def inv3_unanchored_is_valid(b):
    r = b.sign("chat", {"n": 3})
    v = b.verify(r, None)
    assert v == {"valid": True, "anchored": "none", "reason": None}, v
    bad = dict(r)
    bad["payload"] = {"n": 4}
    assert b.verify(bad, None)["valid"] is False, "a changed payload verified"


def inv4_only_strengthens(b):
    rows = [b.sign("chat", {"n": 5})]
    a = b.anchor(rows)
    if a is None:
        return
    seen = [a]
    for _ in range(4):
        seen.append(b.refresh(seen[-1]))
    for prev, nxt in zip(seen, seen[1:]):
        step = f.anchor_step(prev, nxt)
        assert isinstance(step, f.Ok), (step, prev, nxt)
        assert isinstance(f.check_anchor_ref(nxt), f.Ok), f.check_anchor_ref(nxt)
        assert b.verify(rows[0], nxt)["valid"] is True, "an anchor state made a valid row invalid"


def inv5_backend_never_changes_bytes(b, reference):
    r = b.sign("chat", {"n": 6})
    b.anchor([r])
    assert reference.row_valid(r), "the reference cannot verify this backend's row"
    assert reference.sign("chat", {"n": 6}) == r, "same key, same payload, different row bytes"


def inv6_unavailable_degrades(b):
    if not hasattr(b, "available"):
        return
    b.available = False
    rows = [b.sign("chat", {"n": 7}), b.sign("chat", {"n": 8})]
    assert b.anchor(rows) is None
    assert all(b.verify(r, None)["valid"] for r in rows), "rows dropped while the backend was down"
    assert b.status()["lag_rows"] >= 2, "lag is not visible"
    b.available = True


INVARIANTS = [inv1_sign_is_local, inv2_anchor_idempotent, inv3_unanchored_is_valid,
              inv4_only_strengthens, inv5_backend_never_changes_bytes, inv6_unavailable_degrades]


def check(make_backend, seed32):
    """Run every invariant on a fresh backend; return [(name, None|error text)]."""
    out = []
    for inv in INVARIANTS:
        b = make_backend(seed32)
        try:
            if inv is inv5_backend_never_changes_bytes:
                inv(b, NoneBackend(seed32))
            else:
                inv(b)
            out.append((inv.__name__, None))
        except AssertionError as e:
            out.append((inv.__name__, str(e) or "assertion"))
    return out


# ---------------------------------------------------------------- known-red controls

class _BlocksSign(FakeAnchorBackend):
    def sign(self, domain, payload):
        with self.lock:     # waits for the anchor lock: what an inline anchor does
            time.sleep(self.admit_s)
        return super().sign(domain, payload)

    def anchor(self, rows):
        with self.lock:
            time.sleep(self.admit_s)
        return super().anchor(rows)


class _Weakens(FakeAnchorBackend):
    def refresh(self, ref):
        r = super().refresh(ref)
        if self.refreshes[r["ref"]] == 3:
            r = dict(r, state="pending", at_height=None)
        return r


class _Restamps(FakeAnchorBackend):
    def sign(self, domain, payload):
        row = super().sign(domain, payload)
        return self._sign(dict(row, anchored_by="test"))


CONTROLS = {"blocks-sign": _BlocksSign, "weakens-anchor": _Weakens, "restamps-row": _Restamps}


def run_suite(make_backend, seed32):
    """-> {"controls": {name: "red"|"PASSED"}, "results": [(inv, verdict)]}. A result is
    "ok", "RED: why", or "UNREAD" when a control failed to read red."""
    controls = {}
    for name, cls in CONTROLS.items():
        reds = [e for _, e in check(lambda s, c=cls: c(s, admit_s=0.1), seed32) if e]
        controls[name] = "red" if reds else "PASSED"
    teeth = all(v == "red" for v in controls.values())
    results = []
    for inv, err in check(make_backend, seed32):
        results.append((inv, "UNREAD" if not teeth else ("ok" if err is None else "RED: " + err)))
    return {"controls": controls, "results": results}


if __name__ == "__main__":
    import hashlib
    import json
    seed = hashlib.sha256(b"fleet-interfaces test key chat-1").digest()
    for label, mk in (("none", NoneBackend), ("fake-anchor", lambda s: FakeAnchorBackend(s)),
                      ("fake-anchor failing proofs", lambda s: FakeAnchorBackend(s, fail_proofs=True))):
        print(label, json.dumps(run_suite(mk, seed)))
