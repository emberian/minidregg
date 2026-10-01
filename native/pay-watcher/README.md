# pay-watcher

This crate is the PAY watcher (PAY.md §3, §11). It turns finalized Solana token transfers to the book's addresses into
`Observation` records for the kernel. The reports are `planning/pay/p1-watcher.md` (P1) and
`planning/pay/p1b-enroll.md` (P1b, the enrollment index).

```
pay-watcher --config FILE --out DIR [--rpc-fixture DIR]... [--spool DIR]
```

## The enrollment index keeps a cursor; no other index does

Every book index is read statelessly. Each run lists the newest `maxPages × pageSize` signatures of the index's token
accounts. The only memory it has is the receipts directory, and the kernel's nullifier makes a resubmission harmless.

The enrollment index (`enrol.index`, PAY.md §11.2) is the one exception. It pages back to a **persistent cursor** kept in
`enrol.cursorFile`, with no page bound.

The reason is the difference between the two kinds of address:
- **A per-payer address** receives a few transfers, all from its payer, so a newest-N window over it loses nothing.
- **The enrollment address** is public: it is a shared queue that anyone can fill. On-chain, memo-bearing dust costs a
  spammer only the transaction fee, so the address's history can grow without bound. Under a newest-N window, enough dust
  pushes a real enrollment out of the window, and it is never read again. That is PAY §2.2's dust hole.
- **Paging the whole history every tick** would close the hole, but it makes every tick cost O(all history).

The cursor gives both properties at once:
- **The rule.** Per token account, the cursor is the newest signature at and below which every listing is **settled**.
  Settled means one of two things. Either a receipt retains the transfer. Or every endpoint agreed on a permanent skip:
  a failed transfer, a zero delta, a net debit, or an amount below the journal floor.
- **The next run** lists with `until` set to the cursor, so a settled listing is never listed or fetched again.
- **An unsettled listing holds the cursor below it**, so it is read again next run. That covers an emitted but
  unreceipted credit, a refusal and an endpoint disagreement. The cursor therefore cannot lose anything that the
  stateless rule would have retried.
- **Cost.** Dust is fetched once, recorded once as `belowJournalFloor` in `events.json`, and then passed.
- **Listing order.** `until` cuts at a position in the RPC's listing order, not at a slot. So the cursor advances only
  when every endpoint lists the account identically; otherwise the run notes `cursorHeld`.
- **Writes.** The cursor file is written after `observations.json` and `events.json`. A crash in between leaves the old
  cursor, which re-derives the same run.
- **A malformed cursor file refuses to load** (exit 2). It is never read as "no cursor".

## Output

`observations.json` holds `{"observations": [...], "tip": {"slot", "blockTime"}}`. Each observation has these fields:

| field | value |
|---|---|
| `index`, `slot`, `blockTime`, `amount` | integers |
| `address`, `mint`, `tokenProgram` | 64 lowercase hex digits (the 32 raw bytes) |
| `signature` | 128 lowercase hex digits (the 64 raw bytes) |
| `memo` | enrollment index only: lowercase hex of the raw bytes of the transaction's **one** SPL Memo instruction. Otherwise `null`. |
| `memoError` | enrollment index only: `"memoUnbound"` (two or more memo instructions) or `"memoInvalid"` (one memo that is not UTF-8 or is longer than 566 bytes). Otherwise `null`. |

Three cases follow from the memo fields:
- `memo` and `memoError` are never both non-null.
- An enrollment payment with no memo instruction has both null; the kernel treats that as `memoMissing`.
- The watcher never parses the memo. The grammar and both signatures are the kernel's (PAY §11.3/§11.4).

`events.json` lists every refusal, every skip and every note. Its `kind` is one of `refused`, `skipped` or `noted`.

## Fixtures

`python3 fixtures/generate.py` rewrites every vector byte-identically. The hooks are `journey.d/jpay1.sh` (J-PAY-1, the
ordinary vectors) and `journey.d/jpay-e1.sh` (J-PAY-E1, the `enrol-*` vectors). Each hook runs the binary on a private
copy of each vector, because the binary writes its cursor beside the config.
