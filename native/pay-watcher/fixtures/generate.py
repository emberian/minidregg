#!/usr/bin/env python3
"""Regenerate the pay-watcher fixture vectors: python3 fixtures/generate.py

Every vector is a directory:
  config.json        the watcher config (receiptsDir = receipts)
  receipts/          retained receipts, one file per credited signature
  endpoints/a, /b    one fixture endpoint each (file naming: transport::fixture_key)
  expect.json        exit code, observation count, and the event reasons that must appear

Keys are sha256 of a label and signatures sha512 of a label, so every value is a real
32/64-byte string with a real base58 spelling. Output is deterministic; rerunning rewrites
the same bytes.
"""
import base64
import hashlib
import json
import os
import shutil

HERE = os.path.dirname(os.path.abspath(__file__))
ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58(raw: bytes) -> str:
    n = int.from_bytes(raw, "big")
    out = ""
    while n:
        n, r = divmod(n, 58)
        out = ALPHABET[r] + out
    pad = len(raw) - len(raw.lstrip(b"\0"))
    return "1" * pad + out


def key(label: str) -> bytes:
    return hashlib.sha256(label.encode()).digest()


def sig(label: str) -> bytes:
    return hashlib.sha512(label.encode()).digest()


TOKEN_2022 = "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb"
TOKEN_LEGACY = "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
MINT = b58(key("fixture mint"))
OTHER_MINT = b58(key("another mint"))
BOOK0 = b58(key("book 0"))
BOOK1 = b58(key("book 1"))
OTHER_WALLET = b58(key("another wallet"))
ATA0 = b58(key("token account 0"))
ATA0B = b58(key("token account 0b"))
PAYER = b58(key("payer wallet"))
PAYER_TA = b58(key("payer token account"))
TIP_SLOT = 1000
TIP_TIME = 1759250000


def block_time(slot):
    return TIP_TIME - (TIP_SLOT - slot) // 2


def envelope(result=None, error=None):
    body = {"jsonrpc": "2.0", "id": 1}
    if error is not None:
        body["error"] = error
    else:
        body["result"] = result
    return body


def token_account_entry(pubkey, owner=BOOK0, mint=MINT, program=TOKEN_2022):
    return {
        "pubkey": pubkey,
        "account": {
            "owner": program,
            "lamports": 2039280,
            "executable": False,
            "rentEpoch": 18446744073709551615,
            "space": 170,
            "data": {
                "program": "spl-token-2022" if program == TOKEN_2022 else "spl-token",
                "space": 170,
                "parsed": {
                    "type": "account",
                    "info": {
                        "isNative": False,
                        "mint": mint,
                        "owner": owner,
                        "state": "initialized",
                        "tokenAmount": {"amount": "0", "decimals": 6},
                    },
                },
            },
        },
    }


def balance(index, amount, owner=BOOK0, mint=MINT, program=TOKEN_2022):
    return {
        "accountIndex": index,
        "mint": mint,
        "owner": owner,
        "programId": program,
        "uiTokenAmount": {"amount": str(amount), "decimals": 6, "uiAmountString": str(amount / 1e6)},
    }


MEMO_V2 = "MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr"
MEMO_V1 = "Memo1UhkJRfHyvLMcVucJwxXeuD728EqVDDwQDxFMNo"
SYSTEM = "11111111111111111111111111111111"


def transfer_ix(source=None, dest=None, amount=0, program=None, stack=None):
    """A jsonParsed transferChecked, as the RPC renders it (cosmetic: the watcher reads balances)."""
    return {
        "parsed": {
            "info": {
                "authority": PAYER, "destination": dest or ATA0, "mint": MINT,
                "source": source or PAYER_TA,
                "tokenAmount": {"amount": str(amount), "decimals": 6},
            },
            "type": "transferChecked",
        },
        "program": "spl-token-2022",
        "programId": program or TOKEN_2022,
        "stackHeight": stack,
    }


def memo_ix(text, program=MEMO_V2, stack=None):
    """A parsed SPL Memo: `parsed` is the memo text itself (a JSON string)."""
    return {"parsed": text, "program": "spl-memo", "programId": program, "stackHeight": stack}


def raw_memo_ix(data: bytes, program=MEMO_V2, stack=None):
    """Memo bytes that are not UTF-8: the RPC cannot parse them and falls back to base58 `data`."""
    return {"accounts": [], "data": b58(data), "programId": program, "stackHeight": stack}


def transaction(signature, slot, keys, pre, post, err=None, loaded=None, instructions=None,
                inner=None):
    if instructions is None:
        instructions = [transfer_ix()]
    return {
        "slot": slot,
        "blockTime": block_time(slot),
        "version": 0 if loaded else "legacy",
        "meta": {
            "err": err,
            "fee": 5000,
            "preTokenBalances": pre,
            "postTokenBalances": post,
            "loadedAddresses": loaded or {"writable": [], "readonly": []},
            "innerInstructions": inner or [],
        },
        "transaction": {
            "signatures": [b58(signature)],
            "message": {
                "accountKeys": [
                    {"pubkey": k, "signer": i == 0, "writable": True, "source": "transaction"}
                    for i, k in enumerate(keys)
                ],
                "instructions": instructions,
            },
        },
    }


def listing(*entries):
    return [
        {
            "signature": b58(s),
            "slot": slot,
            "err": err,
            "memo": None,
            "blockTime": block_time(slot),
            "confirmationStatus": "finalized",
        }
        for (s, slot, err) in entries
    ]


# The standard transactions ------------------------------------------------------------------
PAY1, PAY2, PAY3 = sig("pay-1"), sig("pay-2"), sig("pay-3")
FAILED1, TOUCH0, FUTURE, OLD0 = sig("failed-1"), sig("touch-0"), sig("future"), sig("old-0")
KEYS = [PAYER, PAYER_TA, ATA0, MINT, TOKEN_2022]


def pay1(**over):
    """1000 DREGG into ATA0, which this transaction creates (absent from PRE)."""
    post0 = balance(2, over.pop("amount", 1_000_000_000), **over)
    return transaction(
        PAY1, 900, KEYS,
        pre=[balance(1, 5_000_000_000, owner=PAYER)],
        post=[balance(1, 4_000_000_000, owner=PAYER), post0],
    )


def pay2():
    """A v0 transaction: ATA0 arrives through the lookup table (index 4)."""
    return transaction(
        PAY2, 950, [PAYER, PAYER_TA, MINT, TOKEN_2022],
        pre=[balance(1, 4_000_000_000, owner=PAYER), balance(4, 1_000_000_000)],
        post=[balance(1, 3_750_000_000, owner=PAYER), balance(4, 1_250_000_000)],
        loaded={"writable": [ATA0], "readonly": []},
    )


def pay3():
    return transaction(
        PAY3, 990, KEYS,
        pre=[balance(1, 3_750_000_000, owner=PAYER), balance(2, 1_250_000_000)],
        post=[balance(1, 3_700_000_000, owner=PAYER), balance(2, 1_300_000_000)],
    )


def touch0():
    """Touches ATA0 without changing its balance."""
    return transaction(
        TOUCH0, 970, KEYS,
        pre=[balance(2, 1_250_000_000)],
        post=[balance(2, 1_250_000_000)],
    )


class Endpoint:
    def __init__(self):
        self.files = {}

    def put(self, name, body):
        self.files[name] = body

    def base(self, accounts=((BOOK0, [ATA0]),), overrides=None):
        self.put("getSlot/finalized.json", envelope(TIP_SLOT))
        self.put(f"getBlockTime/{TIP_SLOT}.json", envelope(TIP_TIME))
        for owner, accts in accounts:
            entries = [token_account_entry(a, owner=owner) for a in accts]
            self.put(
                f"getTokenAccountsByOwner/{owner}.{MINT}.json",
                envelope({"context": {"slot": TIP_SLOT}, "value": entries}),
            )
        return self

    def sigs(self, account, entries, before=None):
        name = f"{account}.json" if before is None else f"{account}.before.{b58(before)}.json"
        self.put(f"getSignaturesForAddress/{name}", envelope(listing(*entries)))

    def tx(self, signature, body):
        self.put(f"getTransaction/{b58(signature)}.json", envelope(body))


def vector(name, description, expect, book=(BOOK0,), page_size=25, max_pages=4,
           endpoints=None, receipts=(), enrol=None, root=None):
    root = os.path.join(root or HERE, name)
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(os.path.join(root, "receipts"))
    with open(os.path.join(root, "receipts", ".keep"), "w") as f:
        f.write("")
    for r in receipts:
        with open(os.path.join(root, "receipts", r), "w") as f:
            f.write("")
    config = {
        "asset": {"mint": MINT, "tokenProgram": TOKEN_2022},
        "book": [{"index": i, "address": a} for i, a in enumerate(book) if a is not None],
        "maxPages": max_pages,
        "pageSize": page_size,
        "minEndpoints": 2,
        "receiptsDir": "receipts",
    }
    if enrol is not None:
        config["enrol"] = enrol
    expect.setdefault("memos", ["none"] * expect["observations"])
    dump(os.path.join(root, "config.json"), config)
    for label, ep in endpoints.items():
        for rel, body in ep.files.items():
            dump(os.path.join(root, "endpoints", label, rel), body)
    dump(os.path.join(root, "expect.json"), dict(description=description, **expect))


def dump(path, value):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(value, f, indent=2, sort_keys=True)
        f.write("\n")


def same(build):
    """Two endpoints that give the same answers."""
    return {"a": build(), "b": build()}


def single_tx(tx_body, signature=PAY1, slot=900, err=None):
    def build():
        ep = Endpoint().base()
        ep.sigs(ATA0, [(signature, slot, err)])
        if tx_body is not None:
            ep.tx(signature, tx_body)
        return ep
    return build


def happy():
    ep = Endpoint().base(accounts=((BOOK0, [ATA0]), (BOOK1, [])))
    ep.sigs(ATA0, [
        (FUTURE, 1100, None),       # above the tip: not read this run
        (TOUCH0, 970, None),        # zero delta
        (FAILED1, 960, {"InstructionError": [0, {"Custom": 1}]}),
        (PAY2, 950, None),
        (PAY1, 900, None),
    ])
    ep.tx(TOUCH0, touch0())
    ep.tx(PAY2, pay2())
    ep.tx(PAY1, pay1())
    return ep


# Enrolment (PAY.md §11) ---------------------------------------------------------------------
# The enrollment address is the book row named by config `enrol.index`. Its observations carry
# the transaction's one memo as raw bytes; the kernel parses them. The memos below follow the
# §11.3 grammar, enrol:v1:<mini hex 64>:<ssh blob base64 68>:<mini-sig hex 128>:<ssh-sig hex 128>
# (400 bytes), but their SIGNATURES ARE PLACEHOLDERS (sha512 of a label): nothing here holds a
# key, and the watcher verifies nothing.
ENROL = b58(key("enrollment address"))
ENROL_TA = b58(key("enrollment token account"))
BOOK5 = b58(key("book 5"))
ATA5 = b58(key("token account 5"))
EXCHANGE = b58(key("exchange hot wallet"))
EXCHANGE_TA = b58(key("exchange token account"))
ROUTER = b58(key("a router program"))
FLOOR = 1_000_000  # 1 DREGG (PAY §11.8)


def ssh_blob(label):
    return base64.b64encode(b"\x00\x00\x00\x0bssh-ed25519\x00\x00\x00\x20" + key(label)).decode()


def enrol_memo(who="alice", mini=None, ssh=None, version="v1"):
    return ":".join(["enrol", version, mini or key(who + " mini key").hex(), ssh or ssh_blob(who + " ssh key"),
                     sig(who + " mini-sig").hex(), sig(who + " ssh-sig").hex()])


ALICE = enrol_memo("alice")
assert len(ALICE) == 400, len(ALICE)


def enrol_tx(signature, slot, amount, memos=(), inner_memos=(), payer=PAYER, payer_ta=PAYER_TA,
             pre_enrol=None, memo_program=MEMO_V2, memo_first=True):
    """A payment of `amount` into ENROL_TA. `memos` are top-level memo instructions, placed
    immediately BEFORE the transfer (where Token-2022's MemoTransfer extension looks) unless
    `memo_first` is false; `inner_memos` are memo CPIs made by a router program."""
    keys = [payer, payer_ta, ENROL_TA, MINT, TOKEN_2022, memo_program, ROUTER]
    as_ix = lambda m, stack=None: m if isinstance(m, dict) else memo_ix(m, program=memo_program, stack=stack)
    top = [as_ix(m) for m in memos]
    inner = []
    if inner_memos:
        transfer = [{"accounts": [payer, payer_ta, ENROL_TA], "data": b58(b"route"),
                     "programId": ROUTER, "stackHeight": None}]
    else:
        transfer = [transfer_ix(source=payer_ta, dest=ENROL_TA, amount=amount)]
    ixs = top + transfer if memo_first else transfer + top
    if inner_memos:
        inner.append({"index": ixs.index(transfer[0]), "instructions": [
            *[as_ix(m, 2) for m in inner_memos],
            transfer_ix(source=payer_ta, dest=ENROL_TA, amount=amount, stack=2),
        ]})
    pre = [balance(1, 10_000_000_000, owner=payer)]
    post = [balance(1, 10_000_000_000 - amount, owner=payer),
            balance(2, (pre_enrol or 0) + amount, owner=ENROL)]
    if pre_enrol is not None:
        pre.append(balance(2, pre_enrol, owner=ENROL))
    return transaction(signature, slot, keys, pre=pre, post=post, instructions=ixs, inner=inner)


def enrol_endpoint(entries, txs, plain=None, tip=TIP_SLOT, until=None, pages=None):
    """`entries` newest first for ENROL_TA as (sig, slot[, err]); `plain` = (entries, txs) for the
    ordinary row BOOK0 (index 1). `until` = the cursor signature the watcher will send; `pages`
    splits the enrollment listing into pages of that size (the watcher follows `before`)."""
    ep = Endpoint()
    ep.put("getSlot/finalized.json", envelope(tip))
    ep.put(f"getBlockTime/{tip}.json", envelope(block_time(tip)))
    for owner, acct in ((ENROL, ENROL_TA), (BOOK0, ATA0)):
        ep.put(f"getTokenAccountsByOwner/{owner}.{MINT}.json",
               envelope({"context": {"slot": tip}, "value": [token_account_entry(acct, owner=owner)]}))
    rows = [(e[0], e[1], e[2] if len(e) > 2 else None) for e in entries]
    suffix = f".until.{b58(until)}" if until else ""
    size = pages or 25
    chunks = [rows[k:k + size] for k in range(0, len(rows), size)] or [[]]
    if len(chunks[-1]) == size:
        chunks.append([])
    before = None
    for chunk in chunks:
        name = ENROL_TA + (f".before.{b58(before)}" if before else "") + suffix
        ep.put(f"getSignaturesForAddress/{name}.json", envelope(listing(*chunk)))
        before = chunk[-1][0] if chunk else None
    for s_, body in txs.items():
        ep.tx(s_, body)
    p_entries, p_txs = plain or ([], {})
    ep.sigs(ATA0, [(s_, slot, None) for (s_, slot) in p_entries])
    for s_, body in p_txs.items():
        ep.tx(s_, body)
    return ep


def enrol_vector(name, description, expect, build=None, endpoints=None, page_size=25, max_pages=4,
                 root=None, cursor_file=None, receipts=()):
    vector(name, description, expect, book=(ENROL, BOOK0), page_size=page_size, max_pages=max_pages,
           enrol={"index": 0, "journalFloor": FLOOR, **({"cursorFile": cursor_file} if cursor_file else {})},
           endpoints=endpoints or same(build), root=root, receipts=receipts)


def enrol_vectors():
    E1, E2, E3, E4, E5 = (sig(f"enrol-{n}") for n in range(1, 6))

    def happy():
        return enrol_endpoint(
            [(E5, 980), (E4, 970), (E3, 960), (E2, 940), (E1, 920)],
            {
                # a top-level v2 memo immediately before the transfer
                E1: enrol_tx(E1, 920, 5_000_000_000, memos=[ALICE]),
                # the memo is an inner instruction (a CPI through a router program)
                E2: enrol_tx(E2, 940, 5_000_000_000, inner_memos=[enrol_memo("bob")], pre_enrol=5_000_000_000),
                # the legacy Memo1 program
                E3: enrol_tx(E3, 960, 5_000_000_000, memos=[enrol_memo("carol")], pre_enrol=10_000_000_000,
                             memo_program=MEMO_V1),
                # exactly the journal floor: emitted. The watcher does not know the price.
                E4: enrol_tx(E4, 970, FLOOR, memos=[enrol_memo("dave")], pre_enrol=15_000_000_000),
                # the SAME memo as E1 again: a second observation; the kernel decides renewal
                E5: enrol_tx(E5, 980, 5_000_000_000, memos=[ALICE], pre_enrol=15_000_000_000 + FLOOR),
            },
            plain=([(PAY1, 900)], {PAY1: pay1()}),
        )
    enrol_vector("enrol-happy", "enrolment payments: a top-level v2 memo, an inner-instruction (CPI) memo, "
                 "a legacy Memo1 memo, a payment of exactly the journal floor, and alice's memo twice (two "
                 "observations); plus an ordinary payment to book row 1 whose memo is never read",
                 {"exit": 0, "observations": 6, "reasons": [],
                  "memos": ["memo", "memo", "memo", "memo", "memo", "none"]}, happy)

    M1, E6 = sig("memo-only-1"), sig("enrol-6")

    def other_tx():
        memo_only = transaction(M1, 930, [PAYER, PAYER_TA, ENROL_TA, MINT, TOKEN_2022, MEMO_V2],
                                pre=[balance(2, 0, owner=ENROL)], post=[balance(2, 0, owner=ENROL)],
                                instructions=[memo_ix(ALICE)])
        return enrol_endpoint([(E6, 940), (M1, 930)],
                              {M1: memo_only, E6: enrol_tx(E6, 940, 5_000_000_000, pre_enrol=0)})
    enrol_vector("enrol-memo-other-tx", "alice's memo in a transaction that moves nothing, then the transfer "
                 "in a DIFFERENT transaction with no memo: the memo is not joined to it (memo null)",
                 {"exit": 0, "observations": 1, "reasons": ["zeroDelta"], "memos": ["none"]}, other_tx)

    X1, P1, BOUNCE = sig("exchange-1"), sig("assigned-payer-plain"), sig("memo-transfer-bounce")

    def no_memo():
        return enrol_endpoint(
            [(P1, 960), (BOUNCE, 955, {"InstructionError": [0, {"Custom": 1}]}), (X1, 950)],
            {X1: enrol_tx(X1, 950, 7_000_000_000, payer=EXCHANGE, payer_ta=EXCHANGE_TA),
             P1: enrol_tx(P1, 960, 2_000_000_000, pre_enrol=7_000_000_000)})
    enrol_vector("enrol-no-memo", "an exchange-style withdrawal with no memo and a plain payment from an "
                 "assigned payer (both emitted, memo null, memoError null: the kernel's memoMissing), and a "
                 "memo-less send the MemoTransfer extension bounced (failed: skipped)",
                 {"exit": 0, "observations": 2, "reasons": ["failedTransaction"], "memos": ["none", "none"]},
                 no_memo)

    long_ok = "x" * 566
    cases = [
        ("two-memos", [enrol_memo("erin"), enrol_memo("mallory")], True, "memoUnbound"),
        ("note-after-transfer", ["thanks!", enrol_memo("frank")], False, "memoUnbound"),
        ("inner-plus-top", None, True, "memoUnbound"),
        ("not-utf8", [raw_memo_ix(b"enrol:v1:\xff\xfe")], True, "memoInvalid"),
        ("567-bytes", ["x" * 567], True, "memoInvalid"),
        ("566-bytes", [long_ok], True, "memo"),
        ("v2", [enrol_memo("gina", version="v2")], True, "memo"),
        ("prose", ["hello, please enrol me"], True, "memo"),
    ]
    C = [sig(f"bind-{n}") for n, *_ in cases]

    def binding():
        txs = {}
        for i, (s_, (n, m, first, _)) in enumerate(zip(C, cases)):
            if n == "inner-plus-top":
                txs[s_] = enrol_tx(s_, 900 + 10 * i, FLOOR, memos=[enrol_memo("hana")],
                                   inner_memos=[enrol_memo("ivan")], pre_enrol=i * FLOOR)
            else:
                txs[s_] = enrol_tx(s_, 900 + 10 * i, FLOOR, memos=m, pre_enrol=i * FLOOR, memo_first=first)
        return enrol_endpoint([(s_, 900 + 10 * i) for i, s_ in reversed(list(enumerate(C)))], txs)
    enrol_vector("enrol-memo-bind", "the memo binding: two memos, a note plus a memo, a top-level plus an inner "
                 "memo (memoUnbound); non-UTF-8 bytes as base58 `data`, 567 bytes (memoInvalid); 566 bytes, a v2 "
                 "memo and prose (one UTF-8 memo: emitted byte-exact, the kernel refuses the grammar)",
                 {"exit": 0, "observations": len(cases), "reasons": ["memoInvalid", "memoUnbound"],
                  "memos": [c[3] for c in cases]}, binding)

    D1, D2, D3 = sig("dust-1"), sig("dust-floor-minus-1"), sig("dust-at-floor")

    def dust():
        return enrol_endpoint([(D3, 960), (D2, 950), (D1, 940)], {
            D1: enrol_tx(D1, 940, 1, memos=["spam"]),
            D2: enrol_tx(D2, 950, FLOOR - 1, memos=[ALICE], pre_enrol=1),
            D3: enrol_tx(D3, 960, FLOOR, memos=[ALICE], pre_enrol=FLOOR),
        })
    enrol_vector("enrol-dust", "1 unit and journalFloor-1 to the enrollment address are not emitted "
                 "(belowJournalFloor, amount recorded); exactly journalFloor is",
                 {"exit": 0, "observations": 1, "reasons": ["belowJournalFloor"], "memos": ["memo"]}, dust)

    S1 = sig("shared-0-and-5")

    def shared():
        ep = Endpoint().base(accounts=((ENROL, [ENROL_TA]), (BOOK0, [ATA0]), (BOOK5, [ATA5])))
        for owner, acct in ((ENROL, ENROL_TA), (BOOK5, ATA5)):
            ep.put(f"getTokenAccountsByOwner/{owner}.{MINT}.json",
                   envelope({"context": {"slot": TIP_SLOT}, "value": [token_account_entry(acct, owner=owner)]}))
        ep.sigs(ENROL_TA, [(S1, 940, None)])
        ep.sigs(ATA5, [(S1, 940, None)])
        ep.sigs(ATA0, [])
        ep.tx(S1, transaction(
            S1, 940, [PAYER, PAYER_TA, ENROL_TA, ATA5, MINT, TOKEN_2022, MEMO_V2],
            pre=[balance(1, 10_000_000_000, owner=PAYER)],
            post=[balance(1, 3_000_000_000, owner=PAYER), balance(2, 5_000_000_000, owner=ENROL),
                  balance(3, 2_000_000_000, owner=BOOK5)],
            instructions=[memo_ix(ALICE), transfer_ix(dest=ENROL_TA, amount=5_000_000_000),
                          transfer_ix(dest=ATA5, amount=2_000_000_000)]))
        return ep
    vector("enrol-shared-tx", "one transaction pays the enrollment address (index 0) and book row 5: two "
           "observations with one signature, the memo on index 0 only",
           {"exit": 0, "observations": 2, "reasons": [], "memos": ["memo", "none"]},
           book=(ENROL, BOOK0, None, None, None, BOOK5), enrol={"index": 0, "journalFloor": FLOOR},
           endpoints=same(shared))

    def disagree(alice, bob):
        return enrol_endpoint([(E2, 940), (E1, 920)], {
            E1: enrol_tx(E1, 920, 5_000_000_000, memos=[alice]),
            E2: enrol_tx(E2, 940, 5_000_000_000, memos=[bob], pre_enrol=5_000_000_000),
        })
    enrol_vector("enrol-disagree", "for enrol-1 endpoint b reports a memo with eve's ssh key; for enrol-2 b "
                 "reports the mini key in UPPERCASE: both are disagreements and nothing is emitted",
                 {"exit": 3, "observations": 0, "reasons": ["endpointsDisagree"], "memos": []},
                 endpoints={"a": disagree(ALICE, enrol_memo("bob")),
                            "b": disagree(enrol_memo("alice", ssh=ssh_blob("eve ssh key")),
                                          enrol_memo("bob", mini=key("bob mini key").hex().upper()))})

    OLD, B1, B2, B3 = sig("enrol-behind-dust"), sig("behind-1"), sig("behind-2"), sig("behind-3")

    def behind():
        return enrol_endpoint(
            [(B3, 960), (B2, 950), (B1, 940), (OLD, 900)],
            {OLD: enrol_tx(OLD, 900, 5_000_000_000, memos=[ALICE]),
             **{b: enrol_tx(b, 940 + 10 * k, 1, memos=["spam"], pre_enrol=5_000_000_000 + k)
                for k, b in enumerate([B1, B2, B3])}},
            pages=2)
    enrol_vector("enrol-behind-dust", "an enrollment older than three dust transfers, with pageSize 2 and "
                 "maxPages 1: an ordinary row would stop after one page; the enrollment index pages to the "
                 "end and finds it",
                 {"exit": 0, "observations": 1, "reasons": ["belowJournalFloor"], "memos": ["memo"]}, behind,
                 page_size=2, max_pages=1)

    H1, H2 = sig("held-1"), sig("held-2")

    def held(order):
        return enrol_endpoint(order, {H1: enrol_tx(H1, 940, 1, memos=["spam"]),
                                      H2: enrol_tx(H2, 940, 2, memos=["spam"], pre_enrol=1)})
    enrol_vector("enrol-cursor-held", "two dust transfers in one slot, listed in opposite orders by the two "
                 "endpoints: both are settled, but `until` cuts at a position, so the cursor does not move",
                 {"exit": 0, "observations": 0, "reasons": ["belowJournalFloor", "cursorHeld"], "memos": [],
                  "cursorAfter": {}},
                 endpoints={"a": held([(H2, 940), (H1, 940)]), "b": held([(H1, 940), (H2, 940)])})

    # Two runs over one cursor file. Phase 1 (tip 1000): 300 memo-bearing dust transfers at slots
    # 600..899 (12 pages of 25, past maxPages 4), all settled, so the cursor moves to the newest;
    # the enrollment at slot 1050 is above the tip. Phase 2 (tip 1100): the watcher lists with
    # `until` = the cursor, so its fixture has ONLY the `.until.` listing and no dust transaction:
    # re-reading any dust would be a `transport` refusal.
    DUST = [sig(f"cursor-dust-{k}") for k in range(300)]
    LATE = sig("enrol-after-dust")
    root = os.path.join(HERE, "enrol-cursor")
    shutil.rmtree(root, ignore_errors=True)

    def phase1():
        return enrol_endpoint(
            [(LATE, 1050)] + [(DUST[k], 600 + k) for k in reversed(range(300))],
            {d: enrol_tx(d, 600 + k, 1 + k % 7, memos=["spam"], pre_enrol=k) for k, d in enumerate(DUST)})
    enrol_vector("phase1", "300 memo-bearing dust transfers (12 pages) settle and move the cursor; the "
                 "enrollment is above the tip",
                 {"exit": 0, "observations": 0, "reasons": ["belowJournalFloor"], "memos": [],
                  "cursorAfter": {key("enrollment token account").hex(): DUST[299].hex()}},
                 endpoints={"a": phase1()}, root=root, cursor_file="../cursor.json")
    # The two endpoints' answers are identical here; endpoint b is a symlink to a (1.4 MB saved).
    os.symlink("a", os.path.join(root, "phase1", "endpoints", "b"))

    def phase2():
        return enrol_endpoint([(LATE, 1050)], {LATE: enrol_tx(LATE, 1050, 5_000_000_000, memos=[ALICE],
                                                              pre_enrol=4000)},
                              tip=1100, until=DUST[299])
    enrol_vector("phase2", "the cursor from phase 1: only the enrollment is listed and fetched",
                 {"exit": 0, "observations": 1, "reasons": [], "memos": ["memo"],
                  "cursorAfter": {key("enrollment token account").hex(): DUST[299].hex()}},
                 phase2, root=root, cursor_file="../cursor.json")


def main():
    for entry in os.listdir(HERE):
        if os.path.isdir(os.path.join(HERE, entry)):
            shutil.rmtree(os.path.join(HERE, entry))

    vector("happy", "two finalized payments to book 0 (one creating the token account, one v0 via "
           "a lookup table); a failed, a zero-delta and an above-tip signature; book 1 has no token account",
           {"exit": 0, "observations": 2, "reasons": ["failedTransaction", "noTokenAccount", "zeroDelta"]},
           book=(BOOK0, BOOK1), endpoints=same(happy))

    vector("wrong-program", "the POST balance of the watched account is owned by the legacy Tokenkeg program",
           {"exit": 3, "observations": 0, "reasons": ["wrongTokenProgram"]},
           endpoints=same(single_tx(pay1(program=TOKEN_LEGACY))))

    def wrong_program_account():
        ep = Endpoint()
        ep.put("getSlot/finalized.json", envelope(TIP_SLOT))
        ep.put(f"getBlockTime/{TIP_SLOT}.json", envelope(TIP_TIME))
        ep.put(f"getTokenAccountsByOwner/{BOOK0}.{MINT}.json",
               envelope({"context": {"slot": TIP_SLOT},
                         "value": [token_account_entry(ATA0, program=TOKEN_LEGACY)]}))
        return ep
    vector("wrong-program-account", "the token account itself is owned by the legacy Tokenkeg program",
           {"exit": 3, "observations": 0, "reasons": ["wrongTokenProgram"]},
           endpoints=same(wrong_program_account))

    vector("wrong-mint", "the POST balance of the watched account is for another mint",
           {"exit": 3, "observations": 0, "reasons": ["wrongMint"]},
           endpoints=same(single_tx(pay1(mint=OTHER_MINT))))

    vector("other-owner", "the POST balance of the watched account names another wallet as owner",
           {"exit": 3, "observations": 0, "reasons": ["wrongTokenOwner"]},
           endpoints=same(single_tx(pay1(owner=OTHER_WALLET))))

    vector("zero-delta", "a transaction touches the watched account and adds nothing",
           {"exit": 0, "observations": 0, "reasons": ["zeroDelta"]},
           endpoints=same(single_tx(touch0(), signature=TOUCH0, slot=970)))

    failed = pay1()
    failed["meta"]["err"] = {"InstructionError": [2, {"Custom": 1}]}
    vector("failed-tx", "the signature list says success but the transaction's meta.err is non-null",
           {"exit": 0, "observations": 0, "reasons": ["failedTransaction"]},
           endpoints=same(single_tx(failed)))

    vector("pruned", "a listed finalized signature whose getTransaction result is null",
           {"exit": 3, "observations": 0, "reasons": ["prunedTransaction"]},
           endpoints=same(single_tx(None)))
    # single_tx(None) wrote no getTransaction file; write the null result explicitly.
    for label in ("a", "b"):
        dump(os.path.join(HERE, "pruned", "endpoints", label, "getTransaction", b58(PAY1) + ".json"),
             envelope(None))

    disagree = pay1()
    disagree["meta"]["preTokenBalances"].append(balance(2, 7, owner=OTHER_WALLET))
    vector("pre-post-disagree", "PRE and POST balances of the watched account name different owners",
           {"exit": 3, "observations": 0, "reasons": ["balanceEntriesDisagree"]},
           endpoints=same(single_tx(disagree)))

    out_of_range = pay1()
    out_of_range["meta"]["postTokenBalances"].append(balance(9, 1, owner=PAYER))
    vector("index-out-of-range", "a token balance entry's accountIndex is past the account-key list",
           {"exit": 3, "observations": 0, "reasons": ["accountIndexOutOfRange"]},
           endpoints=same(single_tx(out_of_range)))

    def retained():
        ep = Endpoint().base()
        ep.sigs(ATA0, [(PAY3, 990, None), (PAY2, 950, None), (PAY1, 900, None)])
        ep.tx(PAY3, pay3())
        ep.tx(PAY1, pay1())
        # PAY2 is retained: no getTransaction answer exists for it, so fetching it would
        # refuse with `transport`. PAY1 is OLDER than the receipt and has none (say the
        # endpoints disagreed about it last run): it must still be read and emitted.
        return ep
    vector("retained", "pay-2 has a retained receipt (named in hex) and is not fetched; the newer "
           "pay-3 and the OLDER unreceipted pay-1 are both emitted",
           {"exit": 0, "observations": 2, "reasons": ["alreadyRetained"]},
           endpoints=same(retained), receipts=[PAY2.hex()])

    def same_signature():
        ep = Endpoint().base(accounts=((BOOK0, [ATA0B, ATA0]),))
        ep.sigs(ATA0, [(PAY2, 950, None), (PAY1, 900, None)])
        ep.sigs(ATA0, [(PAY1, 900, None), (OLD0, 800, {"InstructionError": [0, "InvalidAccountData"]})],
                before=PAY1)
        ep.sigs(ATA0, [], before=OLD0)
        ep.sigs(ATA0B, [(PAY2, 950, None)])
        ep.tx(PAY1, pay1())
        ep.tx(PAY2, transaction(
            PAY2, 950, [PAYER, PAYER_TA, ATA0, ATA0B, MINT],
            pre=[balance(1, 4_000_000_000, owner=PAYER), balance(2, 1_000_000_000), balance(3, 0)],
            post=[balance(1, 3_650_000_000, owner=PAYER), balance(2, 1_250_000_000),
                  balance(3, 100_000_000)],
        ))
        return ep
    vector("same-signature", "pay-1 is listed on two overlapping pages and pay-2 in the histories of "
           "both of the owner's token accounts: one observation each, pay-2 = 250M + 100M",
           {"exit": 0, "observations": 2, "reasons": ["duplicateSignature", "failedTransaction",
                                                      "ignoredReceiptName"]},
           page_size=2, endpoints=same(same_signature), receipts=["not-a-signature"])

    def disagree_b():
        ep = single_tx(pay1())()
        ep.tx(PAY1, pay1(amount=2_000_000_000))
        return ep
    vector("disagree", "endpoint b reports 2000 DREGG where endpoint a reports 1000",
           {"exit": 3, "observations": 0, "reasons": ["endpointsDisagree"]},
           endpoints={"a": single_tx(pay1())(), "b": disagree_b()})

    enrol_vectors()


if __name__ == "__main__":
    main()
