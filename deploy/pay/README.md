# The PAY watcher on a Mini box

The pay rail is described in PAY.md. This directory has what runs it on the box:

- `mini-pay-watcher`: one tick. It derives the watcher config from the signed pay view, runs
  `pay-watcher`, retains and archives the complete tick, and submits one report with `mini pay observe`;
  each enrollment-index record goes alone to the self-enrollment receiver (below), and while some
  wait for a tip the tick asks the watcher again.
- `mini-pay-watcher.service` / `.timer`: the tick runs as a oneshot in `mini.slice`, 60 s after
  the previous tick finished.

The watcher keeps no ledger, and no cursor except the enrollment row's (P1b, gated by receipts). The ticks connect only through the observer
workspace's retained attempts and the kernel's nullifiers.

## What ember does, once

1. **Genesis names the observer.** Before bootstrap:
   - Generate the observer key on the box:
     `mini keygen --secret /etc/mini/pay/observer.key --public /etc/mini/pay/observer.pub`.
     The key file must be mode 0600, owned by `mini`.
   - Enroll the observer in the genesis source like any subject: a key record, an account, and
     its capabilities.
   - Name the observer: `"payObserver": {"subject": "<S>", "capability": "<C>",
     "controlCapability": "<K>", "enrolCapability": "<E>"}` (C, K, E unused capability
     ids). With `native/resource-client/genesis.sh`, put the observer's enrollment in
     `EXTRA_GENESIS_ENROLLMENTS` and this object in a file named by `GENESIS_PAY_OBSERVER`.

   At genesis this installs:
   - the pay cell's law: the observer may report (`observePayment`), the factory controller
     may manage the pay cell (install, revoke, delegate) and may not report;
   - the observer's root capability C: verb `observePayment`, target and policy the pay cell;
   - the controller's pay-cell capability K (replace the observer: revoke C, delegate anew);
   - `C_enrol` E: the observer's `installPolicy` on the factory, narrowed by the factory law
     to self-enrollment (PAY P3b).

   `native/resource-client/newparticipant-acceptance.sh` does exactly this (subject 30,
   capabilities 4030/4031/4032) and is the template. A genesis without `payObserver` has no
   pay law, so every report is refused.

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
   PAY_ENROL_INDEX=0 PAY_JOURNAL_FLOOR=1000000      # PAY §11: the enrollment row
   PAY_ENROL_CAPABILITY=E                         # genesis payObserver.enrolCapability (C_enrol)
   PAY_OPERATOR_SOCKET=/var/lib/mini/store/node/operator/mini.sock
   ```

   **Self-enrollment needs the Host's operator socket.** Ops 117-120 (the self-enrollment
   plan, assembly, submit and lookup) are admitted only on an owner-private operator socket,
   never on the public one (op 117 runs the native verifier twice per call). One Store has one
   Host, so the service serves both sockets from the same Host process:
   `mini serve --host HOST --config CONFIG --socket PUBLIC/mini.sock --operator-socket
   OPERATOR/mini.sock`, with `OPERATOR/` a new `0700` directory owned by `mini` (the tick runs
   as `mini`; the operator socket checks the peer UID). Without `PAY_ENROL_CAPABILITY` and
   `PAY_OPERATOR_SOCKET`, an enrollment-index record is left undecided every tick
   (`enrol-unconfigured`, exit 3) and holds the enrollment cursor.

   `PAY_RPC_FIXTURES="DIR_A DIR_B"` replaces the endpoints for a rehearsal on recorded answers.
6. **Install the units:**

   ```
   install -m 755 mini-pay-watcher /opt/mini/bin/
   install -m 644 mini-pay-watcher.service mini-pay-watcher.timer /etc/systemd/system/
   systemctl daemon-reload && systemctl enable --now mini-pay-watcher.timer
   ```

   `journalctl -u mini-pay-watcher` shows one summary per tick, for example
   `pay observe: tip S reports R credited C already-credited A quarantined Q [waiting REASON]`.
   `/var/lib/mini/pay/tick/ticks/ID.json` holds each acknowledged tick, including all
   watcher events, observations, tip, and cursor transition. A tick awaiting an exact
   observer decision stays in `tick/pending.json`; it is retained before the cursor advances.
   Existing `journal/YYYY-MM-DD.jsonl` files are historical and remain untouched.

   To inspect retained events (including an unresolved pending tick):

   ```sh
   find /var/lib/mini/pay/tick -type f \( -path '*/ticks/*.json' -o -name pending.json \) \
     -exec jq -c '.observations.tip as $tip | .id as $tick | .events[] | . + {tick:$tick, tip:$tip}' {} +
   ```

   These event records explain watcher decisions, including dust below the journal floor.
   Credit acceptance is established separately by `mini pay audit` and the retained
   observer attempts/receipts. A watcher event alone is not proof of credit.

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

## What one tick decides at the enrollment index (PAY §11)

- **Never in a report.** A record at the tariff's `enrolIndex` is routed out of the report (the
  observation receiver would refuse the whole report: `enrolIndexNeedsReceiver`). Each one is
  submitted ALONE through ops 117-120 under `C_enrol`, and the kernel's `decideEnrol` decides:
  **enrol** (a new subject, its account funded `amount − price`, its own book index, one or more
  node weeks of lease, its ssh key), **renew** (the same memo again: the lease extends from its
  end), or **journal** (memo missing, malformed or unverifiable, below the price, an ssh key
  already taken: nothing minted, kept for ember to comp). The client decides nothing; it reads
  which one happened back from the public enrollment view (op 112) and prints
  `enrolled|renewed|journalled INDEX SIG… detail ATTEMPT`.
- **One decision per tip.** Every self-enrollment spends the tip's tick nullifier, as a report
  does. Ordinary records go first, exactly as before; with no ordinary record, the enrollment is
  the tip's submission (it advances the clock as a heartbeat would). Records left over print
  `enrol-pending N`, and the tick script runs the watcher again for a newer finalized tip, at
  most `PAY_ENROL_ROUNDS` (default 8) more times, stopping when the tip does not move.
- **How the client acts on the Host's answer** (op 119, the observer's signed channel, named reasons):

  | Host answer | client action |
  |---|---|
  | `confirmed` | Decided (enrolled, renewed or journalled). Receipt `pay/receipts/SIGNATURE.ADDRESS` → the attempt; the enrollment cursor may pass it. |
  | `alreadyConsumed` at a newer tip than the clock | Decided before (`already-decided`). Receipt. Next record at the same tip. |
  | `alreadyConsumed` at the clock's tip, `tipBehindClock` | Wait for the next tip. |
  | `stalePay` / `staleAuthority` | Re-read and re-sign once. |
  | `verifier:…` (the native verifier failed) | Nothing decided or consumed: wait, exit 4, retry next tick. |
  | `decision:…`, `keyTaken`, `allocation`, … (refused, nothing consumed) | Quarantined, no receipt (read again next tick). Next record. |
  | anything else | Stop: exit 3 (refused) or 4 (undecided; settled by op 120 before anything new). |
- **Audit.** `mini pay audit --operator-socket S` replays every decided self-enrollment through op
  120. An enrolment or renewal mints `creditFor amount` into the enrollment float exactly as a
  credited report does, so the offline identity is `-well_now = -well_genesis + Σ reports + Σ
  enrolments/renewals`; a journal row mints nothing.
- **What the friend runs** is `mini join --solana|--wait|--renew` (deploy/shell/FRIENDS.md,
  "joining by yourself"). `deploy/pay/enrol.json` is the template of the pin it reads: its
  `enrolAddress` stays `EMBER_ENROL_ADDRESS` until ember publishes index 0's address, and the
  client refuses to print a memo until then. The roster sync reads the same view with
  `mini enrollment-view --socket PUBLIC/mini.sock`.

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

## Published paid-member workspace context

Include a `minidregg-participant-birth-context-v1` file in the friend bundle, with
`genesis` copied exactly from the bootstrap's `deployment/genesis-source.json` and
`template` copied from the pinned Host's `profile.template`. These are public
deployment data; never include private keys. A reconstructed genesis cannot be
substituted: the Host checks its identity against the deployment seed.

`mini join --wait ... --birth-context birth-context.json` creates
`JOIN-DIR/workspace` and imports the member's account and factory observation.
It retains the exact genesis/template and uses only the member's own derived
payer and grants. Repeating the same command resumes local setup and refuses
changed identities, configuration, or context. Enter with
`mini shell --workspace JOIN-DIR/workspace --home JOIN-DIR/home`.

The exact admission price buys enrollment and the first week. A member needs an
additional deposit or renewal remainder to pay for resource/app creation. The
v1 enrollment memo has no next-key commitment; it does not provide prerotation
recovery merely because ordinary `mini keygen` supports that feature.

## Current composed rehearsal (2026-10-02)

With the source-matched native Host from `6a085328` (SHA-256
`9afaf8ecaabde58e42975023260bcc455b519a39ee9e3322582ed64e11a09d42`), the
adapted client and fresh private stores passed:

- J-PAY-E4 **32/32**: Token-2022 fixture enrollment, exact replay, refusal cases,
  renewal, rendered forced SSH proxy line, Mini shell subject, own-account read,
  member-funded content birth (500 → 493), foreign-genesis refusal without debit,
  cold read, and online/offline ledger audits.
- J-PAY4 **25/25**: observer killed after submit marker, pending tick recovery,
  exact lookup, one credit, retained below-floor audit events, and conservation.
- J-ROSTER **26/26** in dregg-infra: actual private SSH server, live/lapsed keys,
  forced commands, pin refusals, and rejection of old/malformed views.

Evidence on persvati: `/tmp/pay-entry-a22-4/jpay-e4/rows.tsv`,
`/tmp/pay-rail-a22-1/rt/jpay4/rows.tsv`, and
`/tmp/jroster-paid-v3/jroster-result.json`. These use recorded/constructed chain
responses; no mainnet transaction or public-service change was performed.
