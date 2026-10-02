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

## Durable service ticks

The deployed wrapper uses `--durable-ticks`. Before it advances any enrollment
cursor, the watcher fsyncs `OUT/pending.json`, containing the complete observations,
audit events, previous/next cursor and observer/asset identity. Directory entries
are synced as well as file contents. A restart republishes that exact pending
report without RPC access. A cursor outside its recorded before/after states or a
changed observer/asset is refused; recovery never rolls a newer cursor backwards.

After `mini pay observe` settles, the wrapper calls:

```
pay-watcher --config FILE --out DIR --ack-tick 00000000000000000001
```

This atomically moves the pending bundle to `OUT/ticks/ID.json` and syncs both
directories. A repeated acknowledgement of the same archived ID is harmless;
an acknowledgement naming another pending tick is refused. Each bundle keeps the
original events once. Existing daily journal files remain historical; new audit
consumers read archived bundles plus the pending bundle. Nothing deletes them.
The service holds a lock through scan, observation and acknowledgement. The
binary separately locks the durable spool while publishing or acknowledging.

An uncertain observer result keeps the pending tick. Recovery still uses the
resource client's exact retained call; this spool does not replace kernel
nullifiers or decide credits. `--durable-ticks` without acknowledgement intentionally
keeps returning the same report. Ordinary fixture/CLI mode remains available
without this flag. Errors can leave a durable pending record; exit 2 means no
new report should be submitted, not that the output directory is empty.

The source wrapper is `deploy/pay/mini-pay-watcher`; dregg-infra's installed copy
shares its body, with only an installation header. DEPLOY-4 validation added:

- `cargo test --test durable_tick`: three process-level restart snapshots,
  including failure after pending creation, lost output views after cursor advance,
  offline recovery, repeated acknowledgement and changed-cursor/observer refusal.
- Existing `units` and `vectors`: 43 passing decoder/Token-2022/memo/cursor cases.
- dregg-infra `journey/jpay-tick-recovery.sh`: actual SIGKILL of its own fixture
  wrapper after the observer fixture records an effect; restart offline, preserve
  both below-floor audit entries, replay the identical report, and archive once.
  Its idempotent observer is a fixture, not proof of the kernel credit receiver;
  the composed receiver/enrollment obligation remains J-PAY-E4.

Read-only mainnet orientation, 2026-10-02: the public Solana mainnet RPC
`getAccountInfo` at finalized slot **452520553** returned the known mint
`XkeTXo1125vz5H9svJpGiw4JvLbN8VmMu9cmMvspump` as initialized `Dregg` / `DREGG`,
**6 decimals**, owned by `TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb`
(`spl-token-2022`). This is a single-endpoint public read, not a watched payment,
recipient choice, or mainnet paid-entry qualification. No transaction was sent.
