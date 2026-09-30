# The PAY watcher on a Mini box

The pay rail is described in PAY.md. This directory has what runs it on the box:

- `mini-pay-watcher`: one tick. It derives the watcher config from the signed pay view, runs
  `pay-watcher`, archives the tick's `events.json`, and submits one report with `mini pay observe`.
- `mini-pay-watcher.service` / `.timer`: the tick runs as a oneshot in `mini.slice`, 60 s after
  the previous tick finished.

The watcher keeps no cursor and no ledger. The ticks connect only through the observer
workspace's retained attempts and the kernel's nullifiers.

## What ember does, once

1. **Genesis names the observer.** Before bootstrap:
   - Generate the observer key on the box:
     `mini keygen --secret /etc/mini/pay/observer.key --public /etc/mini/pay/observer.pub`.
     The key file must be mode 0600, owned by `mini`.
   - Enroll the observer in the genesis source like any subject: a key record, an account, and
     its capabilities.
   - Add `"payObserver": {"subject": "<S>", "capability": "<C>"}`, where C is an unused
     capability id.

   At genesis this installs two things:
   - the pay cell's law, `all [eq request/verb 6, eq request/subject S]`;
   - the observer's root capability: verb `observePayment`, target and policy the pay cell.

   `native/resource-client/newparticipant-acceptance.sh` does exactly this (subject 30,
   capability 4030) and is the template. A genesis without `payObserver` has no pay law, so
   every report is refused.

   `mini bootstrap` also retains `DEPLOYMENT/pay-ledger-genesis.json`. This is the issuer well
   before any payment, and `mini pay audit --offline true` needs it.
2. **The observer workspace:**

   ```
   mini workspace --action init --host HOST --config DEPLOYMENT/pinned-config.json \
     --socket PUBLIC-SOCKET --key /etc/mini/pay/observer.key --subject S \
     --dir /var/lib/mini/pay/observer
   ```

   The workspace holds `attempts/` (every report, byte for byte), `pay/receipts/` and
   `pay/quarantine/`. Back it up with the Store. If you lose it, the next tick resubmits the old
   transfers and the kernel refuses each one once. That costs extra reports; it never credits
   twice.
3. **The book and the tariff.** Run this from ember's own workspace (the factory controller):

   ```
   mini pay book --dir EMBER-WS --source book.json
   ```

   `book.json` has this shape:

   ```
   {"control": "<factory control cap>",
    "book": ["<address base58|hex>", ...],
    "tariff": {"version": "1", "asset": "0", "mint": "<base58|hex>", "tokenProgram": "<base58|hex>",
               "decimals": "6", "creditPerAtomic": "...", "maxPerObservation": "...",
               "minTickSlots": "1500"}}
   ```

   - Rows are appended at the view's `bookSize`.
   - `"tariff": null` changes only the book.
   - A tariff's version must increase.
4. **`/etc/mini/pay/rpc.env`** (0600, `mini`):

   ```
   PAY_RPC_ENDPOINTS=https://…?api-key=… https://…
   ```

   Use two providers. The URLs never reach argv or a log.
5. **`/etc/mini/pay/watcher.env`:**

   ```
   PAY_OBSERVER_WS=/var/lib/mini/pay/observer
   PAY_OBSERVER_CAPABILITY=C
   MINI=/opt/mini/bin/mini
   PAY_WATCHER=/opt/mini/bin/pay-watcher
   # PAY_ENROL_INDEX=… PAY_JOURNAL_FLOOR=1000000   (PAY §11, once Tariff v2 lands)
   ```

   `PAY_RPC_FIXTURES="DIR_A DIR_B"` replaces the endpoints for a rehearsal on recorded answers.
6. **Install the units:**

   ```
   install -m 755 mini-pay-watcher /opt/mini/bin/
   install -m 644 mini-pay-watcher.service mini-pay-watcher.timer /etc/systemd/system/
   systemctl daemon-reload && systemctl enable --now mini-pay-watcher.timer
   ```

   `journalctl -u mini-pay-watcher` shows one summary per tick, for example
   `pay observe: tip S reports R credited C already-credited A quarantined Q [waiting REASON]`.
   `/var/lib/mini/pay/journal/YYYY-MM-DD.jsonl` holds every watcher event, one line each, with
   the tick's tip.

## What one tick decides

- **One report per tip.** Every record the watcher read at tip T goes into one report. The
  report spends T's tick nullifier, so no other report can be accepted at T.
- **The report is signed against a fresh view.** The client re-reads the pay view (op 107)
  immediately before each report, because every report writes the pay cell.
- **How the client acts on the Host's answer:**

  | Host answer | client action |
  |---|---|
  | `confirmed` | Credited. Each record gets a receipt, `pay/receipts/SIGNATURE.ADDRESS` → the attempt. |
  | `stalePay` / `staleAuthority` | An assignment or tariff change landed after the read. Re-read and re-sign once. |
  | `tickTooSoon` / `tipBehindClock` | Wait for the next tick. |
  | `alreadyConsumed` at a tip equal to the clock | That tip is already reported. Wait. |
  | `alreadyConsumed` at a newer tip, or a per-observation refusal | Probe the records one per report (below). |
  | anything else | Stop: exit 3 (refused) or 4 (undecided). |

  - **Probing.** A refused report consumes nothing, so the client submits the records one per
    report. A spent record is "already credited" and gets a receipt linking the refusing
    attempt. A record refused on its own merits (for example `unassignedIndex` or `wrongMint`)
    is quarantined. The first record that is accepted spends the tip; any records left wait
    for the next tick.
- **A crash mid-submit is settled first.** A report with a submit marker but no outcome is
  looked up exactly (op 111) before anything new is sent. If it was confirmed, its records get
  their receipts. If it is `absent`, its records are simply observed again.

## What a friend sees (PAY §5)

```
mini> pay address
index 7 → 9xQeWvG8…3k
send the token with mint XkeT…pump (token program TokenzQd…) to this address from a wallet you control.
1 atomic unit (6 decimals) = 1 credit; at most 10000000000 atomic units are credited per payment.
mini> pay status
account 8811  index 7  address 9xQeWvG8…3k
credit 1000000000  (asset 0)
clock slot 312004391  blockTime 1759261382
tariff v1  valid true
```

- `pay address` is idempotent. The index is retained in the friend's workspace
  (`pay/address-ACCOUNT.json`), because the public view does not publish the assignment map.
- `pay status` cannot list the friend's individual transfers: the observation journal is the
  operator's.
