"""Generate/check synthetic room-log contract examples, never run a backend.

Canonical bytes mirror PR #19: sorted keys, compact UTF-8 JSON, integers only.
The proposed wrapper domain is new. Synthetic rows are not signed ChatBackend
rows; existing upstream signature/anchor tests remain separate and unchanged.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DOMAIN = b"CHAT.ROOM-LINK/v1\0"


def canonical(value):
    if isinstance(value, float):
        raise ValueError("no float in canonical fixture")
    if isinstance(value, dict):
        for child in value.values():
            canonical(child)
    elif isinstance(value, list):
        for child in value:
            canonical(child)
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(body):
    return "sha256:" + hashlib.sha256(DOMAIN + canonical(body)).hexdigest()


def cursor(rows, after):
    return {"room": "room-a", "after": after, "head": rows[after - 1]["digest"] if after else None}


def valid_chain(rows, start=None):
    prev = start or {"room": "room-a", "after": 0, "head": None}
    for row in rows:
        body = {key: value for key, value in row.items() if key != "digest"}
        if (row["room"] != prev["room"] or row["position"] != prev["after"] + 1
                or row["previous"] != prev["head"] or row["digest"] != digest(body)):
            return False
        prev = {"room": row["room"], "after": row["position"], "head": row["digest"]}
    return True


def generated():
    rows = []
    for n, text in enumerate(("alpha", "beta", "gamma"), 1):
        body = {"kind": "room-log-link", "v": 1, "room": "room-a", "position": n,
                "previous": rows[-1]["digest"] if rows else None,
                "row": {"fixture_id": "row-" + str(n), "text": text}}
        rows.append(dict(body, digest=digest(body)))

    def page(start, end, source="hot"):
        return {"kind": "room-log-page", "v": 1, "room": "room-a", "after": cursor(rows, start),
                "next": cursor(rows, end), "rows": rows[start:end], "more": end < len(rows),
                "source": source, "scanned_from_start": False}

    def gap(reason, history=True, resume=True):
        return {"kind": "room-log-gap", "v": 1, "room": "room-a", "reason": reason,
                "resume": cursor(rows, 1) if resume else None, "history_available": history}

    vectors = []

    def add(name, why, data, expect):
        vectors.append({"name": name, "why": why, "input": data, "expect": expect})

    add("cursor-resume", "Only bounded new rows after the saved frontier, no byte-zero reparse",
        {"after": cursor(rows, 1), "max_rows": 1, "available": [1, 2, 3]}, {"response": page(1, 2)})
    add("compaction-resume", "Moving physical bytes does not change a logical cursor",
        {"after": cursor(rows, 1), "physical_generation_changed": True}, {"response": page(1, 2, "journal")})
    add("cold-history", "Hot eviction does not erase journal history",
        {"after": cursor(rows, 1), "hot_positions": [3], "journal_positions": [1, 2, 3]},
        {"response": page(1, 3, "journal")})
    add("hot-window-boundary", "Proposed half-open seven-day window plus independent byte/row/pin bounds",
        {"now_ms": 604800000, "hot_window_ms": 604800000,
         "admitted_ms": [0, 1, 604800000], "max_hot_rows": 2, "max_hot_bytes": 4096,
         "max_pin_bytes": 1024},
        {"hot_positions": [2, 3], "journal_positions": [1, 2, 3], "clock_policy": "server-admission-time",
         "note": "Requested semantics; counters and actual RAM bounds not exercised"})
    wake = {"kind": "room-log-wake", "v": 1, "page": page(1, 2)}
    add("inline-wake", "Wake includes the new rows; no second lookup required to inspect this batch",
        {"subscription_frontier": cursor(rows, 1), "append": 2}, {"response": wake, "second_read_required": False})
    add("subscribe-race", "An append between initial read and registration has no lost interval",
        {"schedule": ["read-through-1", "append-2", "subscribe-from-1"]},
        {"response": wake, "allowed_duplicate_identity": rows[1]["digest"]})
    add("retry-identity", "Lost acknowledgement/exact retry keeps one immutable entry",
        {"schedule": ["append-key-a-row-2", "lose-ack", "retry-key-a-row-2"]},
        {"same_entry_digest": rows[1]["digest"], "positions_added": 1})
    add("retry-conflict", "One idempotency key cannot authorize different row bytes",
        {"key": "key-a", "first_row": {"text": "beta"}, "retry_row": {"text": "changed"}},
        {"refused": "conflict", "positions_added_by_retry": 0})
    add("slow-subscriber", "Overflow stays bounded and explicitly resumes from the journal",
        {"after": cursor(rows, 1), "max_queue_rows": 1, "max_queue_bytes": 1024, "new_positions": [2, 3]},
        {"response": gap("subscriber-overflow"), "silent_drop": False, "queue_growth_unbounded": False})
    add("missing-history", "Deleted/unavailable history is not an empty complete page",
        {"after": cursor(rows, 1), "journal_available": False},
        {"response": gap("history-unavailable", history=False), "complete_empty_success": False})
    add("cross-room-cursor", "A cursor never widens room authorization or leaks another room",
        {"requested_room": "room-a", "cursor_room": "room-b"},
        {"response": gap("cursor-room-mismatch", history=False, resume=False), "rows_disclosed": 0})
    add("row-too-large", "A page byte limit cannot silently skip an oversized row or advance its cursor",
        {"after": cursor(rows, 1), "max_page_bytes": 8}, {"response": gap("row-too-large")})
    add("late-stream-frontier", "Current merge order needs a stable frontier before advancing a cursor",
        {"visible_merge_keys": [[12, 1, 1, 2]], "unsettled_earlier_key": [11, 2, 2, 1]},
        {"response": gap("ordering-frontier-unsettled"), "silently_skip_late_entry": False})
    add("journal-ack-failure", "Signing, anchoring and durable room-log acknowledgement are different states",
        {"signed_row_available": True, "journal_write_succeeded": False},
        {"durably_committed": False, "committed_wake_emitted": False,
         "signed_row_still_available": True, "reason": "not-durable"})

    changed = copy.deepcopy(rows)
    changed[1]["row"]["text"] = "changed"
    add("hash-chain-replay", "Wrapper hashes bind order and original row values, without modifying them",
        {"links": rows}, {"chain_valid": True})
    add("changed-row-control", "A planted row mutation must not verify", {"links": changed}, {"chain_valid": False})
    add("reorder-control", "A planted reorder must not verify", {"links": [rows[1], rows[0], rows[2]]}, {"chain_valid": False})
    add("missing-link-control", "A planted dropped predecessor must not verify",
        {"links": [rows[0], rows[2]]}, {"chain_valid": False})
    return {"generated_by": "room_log_vectors.py", "status": "proposed-contract-examples",
            "scope": "Synthetic wrapper/schema checks only; not adapter, signature, durability, resource or concurrency qualification",
            "hash_rule": "sha256(CHAT.ROOM-LINK/v1 || 0x00 || canonical(link without digest)); canonical JSON follows PR19",
            "fixtures": {"links": rows}, "vectors": vectors}


def verify(data):
    import jsonschema
    schema = json.loads((HERE / "room-log.v1.schema.json").read_text())
    jsonschema.Draft202012Validator.check_schema(schema)
    validator = jsonschema.Draft202012Validator(schema)
    assert len(data["vectors"]) == 18
    assert len({v["name"] for v in data["vectors"]}) == 18
    assert valid_chain(data["fixtures"]["links"])
    responses = controls = 0
    for case in data["vectors"]:
        assert set(case) == {"name", "why", "input", "expect"}
        expect = case["expect"]
        if "response" in expect:
            response = expect["response"]
            validator.validate(response)
            page = response.get("page", response)
            if page["kind"] == "room-log-page":
                assert page["room"] == page["after"]["room"] == page["next"]["room"]
                assert valid_chain(page["rows"], page["after"])
                assert page["rows"][-1]["digest"] == page["next"]["head"]
            responses += 1
        if "chain_valid" in expect:
            assert valid_chain(case["input"]["links"]) is expect["chain_valid"]
            controls += int(not expect["chain_valid"])
    # Schema teeth for the two tempting weakening paths.
    for invalid in [{"kind": "room-log-wake", "v": 1},
                    dict(data["vectors"][0]["expect"]["response"], scanned_from_start=True)]:
        assert not validator.is_valid(invalid)
    assert responses == 10 and controls == 3
    return responses, controls


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = generated()
    encoded = json.dumps(data, indent=1, ensure_ascii=False, sort_keys=True) + "\n"
    path = HERE / "room-log.vectors.json"
    if args.check:
        assert path.read_text() == encoded, "vectors differ from deterministic generator"
    else:
        path.write_text(encoded)
    responses, controls = verify(data)
    print(f"artifact checks only: 18 deterministic vectors; {responses} schema-valid responses; {controls} rejected chain controls; 2 rejected schema controls")


if __name__ == "__main__":
    main()
