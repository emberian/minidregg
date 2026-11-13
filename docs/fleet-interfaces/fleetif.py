"""fleetif.py: the reference reading of the fleet interface records (README.md, S0, S1, S5, S7).

Python 3.10+, standard library plus `cryptography` for Ed25519. This is fleet's reading, offered
so a Mini receiver can be checked against the same vectors; it decides nothing for Mini.

Every function here is pure over its arguments. A refusal is a `Refused(reason, names)` value,
never an exception, so a vector can state the exact refusal it expects.
"""
import hashlib
import json
import re
from dataclasses import dataclass, field

HEX40 = re.compile(r"^[0-9a-f]{40}$")
DIGEST = re.compile(r"^sha256:[0-9a-f]{64}$")
KEYID = re.compile(r"^ed25519:[0-9a-f]{64}$")
SIG = re.compile(r"^[0-9a-f]{128}$")

DOMAIN = {
    "fleet.land-record": b"FLEET.LAND-RECORD/v1",
    "fleet.verdict": b"FLEET.VERDICT/v1",
    "fleet.read-set": b"FLEET.READ-SET/v1",
    "fleet.anchor-ref": b"FLEET.ANCHOR-REF/v1",
    "fleet.chat-row": b"FLEET.CHAT-ROW/v1",
}
MAX_RECORD_BYTES = 1024
MAX_CITED = 32
MAX_COVERS = 256


@dataclass(frozen=True)
class Refused:
    reason: str
    names: tuple = ()

    def as_json(self):
        return {"refused": self.reason, "names": list(self.names)}


@dataclass(frozen=True)
class Ok:
    value: object = None

    def as_json(self):
        return {"ok": self.value}


# ---------------------------------------------------------------- canonical bytes and digests

def canonical(obj):
    """Sorted keys, no whitespace, UTF-8, integers only (a float is refused: its text is not
    portable across languages)."""
    def walk(v):
        if isinstance(v, float):
            raise ValueError("float in a canonical record")
        if isinstance(v, dict):
            for x in v.values():
                walk(x)
        if isinstance(v, list):
            for x in v:
                walk(x)
    walk(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(kind, body):
    """`sha256:` hex of SHA-256(domain || 0x00 || canonical(body)). The domain separates kinds,
    so a land record's bytes never digest (or verify) as a verdict's (S2 invariant 1)."""
    return "sha256:" + hashlib.sha256(DOMAIN[kind] + b"\0" + canonical(body)).hexdigest()


def unsigned(rec):
    return {k: v for k, v in rec.items() if k != "sig"}


def record_digest(rec):
    return digest(rec["kind"], unsigned(rec))


# ---------------------------------------------------------------- signatures (S2)

def keyid_of_seed(seed32):
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
    from cryptography.hazmat.primitives import serialization
    pub = Ed25519PrivateKey.from_private_bytes(seed32).public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw)
    return "ed25519:" + pub.hex()


def sign(rec, seed32):
    """Return rec with `sig` = Ed25519 over the 32 digest bytes. Local: no network, no anchor."""
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
    d = bytes.fromhex(record_digest(rec).split(":", 1)[1])
    out = dict(unsigned(rec))
    out["sig"] = Ed25519PrivateKey.from_private_bytes(seed32).sign(d).hex()
    return out


def sig_ok(rec, keyid):
    from cryptography.exceptions import InvalidSignature
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
    try:
        pub = Ed25519PublicKey.from_public_bytes(bytes.fromhex(keyid.split(":", 1)[1]))
        pub.verify(bytes.fromhex(rec["sig"]), bytes.fromhex(record_digest(rec).split(":", 1)[1]))
        return True
    except (InvalidSignature, ValueError, KeyError):
        return False


# ---------------------------------------------------------------- read sets and staleness (S5, S6, S7)

def parent_dir(path):
    return path.rsplit("/", 1)[0] if "/" in path else ""


def hits(entry, change):
    """Does `change` move what `entry` read? `read`: the path was opened (a modify or delete
    moves it); `absent`: the path was looked up and missing (an add moves it); `list`: the
    directory was listed (an add or delete of a direct child moves it). FleetLaws.lean `hits`."""
    how, p = entry["how"], entry["path"]
    op, q = change["op"], change["path"]
    if how == "read":
        return op in ("modify", "delete") and q == p
    if how == "absent":
        return op == "add" and q == p
    if how == "list":
        return op in ("add", "delete") and parent_dir(q) == p
    return False


def moved(read_set, changes):
    """Every read-set entry some change moves, in read-set order (never just the first)."""
    return [e for e in read_set if any(hits(e, c) for c in changes)]


def read_set_digest(read_set):
    rows = sorted({(e["path"], e["how"]) for e in read_set})
    return digest("fleet.read-set", [{"path": p, "how": h} for p, h in rows])


def pinned_land(read_set, changes_since_base):
    """S5: land only if nothing the land's checks read has moved since its base; otherwise
    refuse `stale`, naming every moved entry. No partial effect either way."""
    m = moved(read_set, changes_since_base)
    if m:
        return Refused("stale", tuple(f'{e["how"]}:{e["path"]}' for e in m))
    return Ok("landed")


def verdict_reading(result, control):
    """S6 invariant 1 (nanodregg gates/runs.py:11-18): a unit whose known-red control did not
    read red has no verdict: its result reads `unread`, whatever it says."""
    return result if control == "red" else "unread"


def verdict_current(verdict_read_set, changes_since_subject):
    """S7 invariant 2: a verdict is current for a later tree only while nothing it read moved.
    Staleness is computed, never stored: a verdict record is never edited or deleted."""
    m = moved(verdict_read_set, changes_since_subject)
    return Ok("current") if not m else Refused("stale", tuple(f'{e["how"]}:{e["path"]}' for e in m))


# ---------------------------------------------------------------- structural checks

def _need(rec, spec):
    """spec: field -> (predicate, reason). Returns the first Refused or None."""
    missing = [k for k in spec if k not in rec]
    if missing:
        return Refused("missing-field", tuple(sorted(missing)))
    extra = sorted(set(rec) - set(spec))
    if extra:
        return Refused("unknown-field", tuple(extra))
    for k, (pred, why) in spec.items():
        if not pred(rec[k]):
            return Refused(why, (k,))
    return None


def _int(lo=0):
    return lambda v: isinstance(v, int) and not isinstance(v, bool) and v >= lo


def _sorted_unique(xs, pat):
    return isinstance(xs, list) and all(isinstance(x, str) and pat.match(x) for x in xs) \
        and xs == sorted(set(xs))


def check_land_record(rec):
    bad = _need(rec, {
        "kind": (lambda v: v == "fleet.land-record", "wrong-kind"),
        "v": (lambda v: v == 1, "wrong-version"),
        "land_id": (lambda v: isinstance(v, str) and bool(HEX40.match(v)), "bad-hex40"),
        "repo": (lambda v: isinstance(v, str) and 0 < len(v) <= 200, "bad-repo"),
        "base_sha": (lambda v: isinstance(v, str) and bool(HEX40.match(v)), "bad-hex40"),
        "landed_sha": (lambda v: isinstance(v, str) and bool(HEX40.match(v)), "bad-hex40"),
        "tested_tree": (lambda v: isinstance(v, str) and bool(HEX40.match(v)), "bad-hex40"),
        "test_receipt": (lambda v: isinstance(v, str) and bool(DIGEST.match(v)), "bad-digest"),
        "verdicts": (lambda v: _sorted_unique(v, DIGEST) and len(v) <= MAX_CITED, "bad-verdict-list"),
        "member": (lambda v: isinstance(v, str) and bool(KEYID.match(v)), "bad-keyid"),
        "ts_ms": (_int(), "bad-ts"),
        "sig": (lambda v: isinstance(v, str) and bool(SIG.match(v)), "bad-sig-shape"),
    })
    if bad:
        return bad
    if len(canonical(rec)) > MAX_RECORD_BYTES:
        return Refused("too-large", (str(len(canonical(rec))),))
    if not sig_ok(rec, rec["member"]):
        return Refused("bad-signature", ("member",))
    return Ok(record_digest(rec))


def check_verdict(rec):
    bad = _need(rec, {
        "kind": (lambda v: v == "fleet.verdict", "wrong-kind"),
        "v": (lambda v: v == 1, "wrong-version"),
        "unit": (lambda v: isinstance(v, str) and 0 < len(v) <= 200, "bad-unit"),
        "subject": (lambda v: isinstance(v, str) and bool(HEX40.match(v)), "bad-hex40"),
        "result": (lambda v: v in ("green", "red", "incomplete", "unread"), "bad-result"),
        "control": (lambda v: v in ("red", "green", "absent"), "bad-control"),
        "read_set": (lambda v: isinstance(v, str) and bool(DIGEST.match(v)), "bad-digest"),
        "read_set_size": (_int(), "bad-size"),
        "producer": (lambda v: isinstance(v, str) and bool(KEYID.match(v)), "bad-keyid"),
        "role": (lambda v: v in ("runner", "reviewer"), "bad-role"),
        "ts_ms": (_int(), "bad-ts"),
        "sig": (lambda v: isinstance(v, str) and bool(SIG.match(v)), "bad-sig-shape"),
    })
    if bad:
        return bad
    if rec["result"] != verdict_reading(rec["result"], rec["control"]):
        return Refused("control-not-red", (rec["control"],))
    if len(canonical(rec)) > MAX_RECORD_BYTES:
        return Refused("too-large", (str(len(canonical(rec))),))
    if not sig_ok(rec, rec["producer"]):
        return Refused("bad-signature", ("producer",))
    return Ok(record_digest(rec))


ANCHOR_STATES = ("pending", "final")
PROOF_STATES = ("n/a", "pending", "ready", "failed")


def check_anchor_ref(rec):
    bad = _need(rec, {
        "kind": (lambda v: v == "fleet.anchor-ref", "wrong-kind"),
        "v": (lambda v: v == 1, "wrong-version"),
        "backend": (lambda v: v in ("mini", "dregg", "test"), "bad-backend"),
        "ref": (lambda v: isinstance(v, str) and 0 < len(v) <= 200, "bad-ref"),
        "covers": (lambda v: _sorted_unique(v, DIGEST) and 0 < len(v) <= MAX_COVERS, "bad-covers"),
        "at_height": (lambda v: v is None or _int()(v), "bad-height"),
        "state": (lambda v: v in ANCHOR_STATES, "bad-state"),
        "proof_state": (lambda v: v in PROOF_STATES, "bad-proof-state"),
        "reason": (lambda v: v is None or (isinstance(v, str) and 0 < len(v) <= 200), "bad-reason"),
    })
    if bad:
        return bad
    if rec["proof_state"] == "failed" and (rec["state"] != "pending" or rec["reason"] is None):
        return Refused("failed-proof-must-stay-pending-with-reason")
    if rec["state"] == "final" and rec["at_height"] is None:
        return Refused("final-needs-height")
    return Ok(digest("fleet.anchor-ref", rec))


# ---------------------------------------------------------------- sequences (ledgers)

@dataclass
class LandLedger:
    """S1 invariants 1 and 4, and 5 against a role table: append-only, exact retry answers
    `replayed`, one record per land_id, the member held `lander` at ts_ms."""
    roles: list = field(default_factory=list)   # [{"member","role","from_ms","until_ms"}]
    by_id: dict = field(default_factory=dict)
    log: list = field(default_factory=list)

    def held(self, member, role, at):
        return any(r["member"] == member and r["role"] == role and r["from_ms"] <= at < r["until_ms"]
                   for r in self.roles)

    def append(self, rec):
        c = check_land_record(rec)
        if isinstance(c, Refused):
            return c
        prior = self.by_id.get(rec["land_id"])
        if prior is not None:
            if canonical(prior) == canonical(rec):
                return Ok({"replayed": record_digest(prior)})
            return Refused("conflict", (rec["land_id"],))
        if not self.held(rec["member"], "lander", rec["ts_ms"]):
            return Refused("not-lander", (rec["member"],))
        self.by_id[rec["land_id"]] = rec
        self.log.append(rec)
        return Ok({"appended": record_digest(rec)})


def anchor_step(prev, nxt):
    """S0 invariant 4: anchoring only strengthens. Same (backend, ref) must cover the same rows;
    state never goes final -> pending; proof_state never leaves `ready`."""
    if (prev["backend"], prev["ref"]) != (nxt["backend"], nxt["ref"]):
        return Refused("different-anchor")
    if prev["covers"] != nxt["covers"]:
        return Refused("covers-changed")
    if prev["state"] == "final" and nxt["state"] != "final":
        return Refused("final-to-pending")
    if prev["proof_state"] == "ready" and nxt["proof_state"] != "ready":
        return Refused("ready-regressed")
    if prev["at_height"] is not None and nxt["at_height"] != prev["at_height"]:
        return Refused("height-changed")
    return Ok("strengthens" if nxt != prev else "same")
