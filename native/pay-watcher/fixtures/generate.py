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


def transaction(signature, slot, keys, pre, post, err=None, loaded=None):
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
        },
        "transaction": {
            "signatures": [b58(signature)],
            "message": {
                "accountKeys": [
                    {"pubkey": k, "signer": i == 0, "writable": True, "source": "transaction"}
                    for i, k in enumerate(keys)
                ]
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
           endpoints=None, receipts=()):
    root = os.path.join(HERE, name)
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(os.path.join(root, "receipts"))
    with open(os.path.join(root, "receipts", ".keep"), "w") as f:
        f.write("")
    for r in receipts:
        with open(os.path.join(root, "receipts", r), "w") as f:
            f.write("")
    config = {
        "asset": {"mint": MINT, "tokenProgram": TOKEN_2022},
        "book": [{"index": i, "address": a} for i, a in enumerate(book)],
        "maxPages": max_pages,
        "pageSize": page_size,
        "minEndpoints": 2,
        "receiptsDir": "receipts",
    }
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


if __name__ == "__main__":
    main()
