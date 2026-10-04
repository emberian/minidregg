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

## The price and the address: one source

Ember's ruling (2026-10-04): enrollment costs **50 DREGG per node week**, paid to the Solana pubkey
**`5N2uUG4TEwvM4acjWRpZ981CJa4p5e9RcuAYQvuUZLp6`** (a fresh devnet-quality key). Both live in
exactly one file, `enrol-terms.json`, and `render-enrol` turns it into every consumer:

```
python3 deploy/pay/render-enrol --out OUT --version N --control CAP \
    --observer-capability C --enrol-capability E [--book-extra FILE]
```

(`CAP` is genesis `factoryControllerCapability`, `C`/`E` are `payObserver.capability` / `.enrolCapability`
of THIS genesis, `N` exceeds the installed tariff version.) It writes `book.json` and `tariff-on.json`
(for `mini pay book`, below), `enrol.json` / `enrol-v2.json` (the friend's pin) and `watcher.env`. Nothing
else in the repo states the address or the rate; `test-render-enrol.py` pins the integers.

**The exact integers.** The mint has 6 decimals (`decimals: 6`, READ `native/pay-watcher/README.md`) and
`creditPerAtomic` is 1, so 50 DREGG is `weekPriceAtomic = 50000000` atomic units. The tariff does not
store a week price; it stores the *hourly* integer `nodeHourRate` and the kernel prices a week as
`weekCredit = 168 * nodeHourRate` (`Kernel/PayTariff.lean`), an enrollment as `birthFee + weekCredit`
(`Kernel/PayEnrolDecision.lean` `enrolPrice`) and a renewal as `credit / weekCredit` whole weeks.
`50000000 / 168` is not an integer, so the script takes the floor: **`nodeHourRate = 297619`,
`weekCredit = 49999992`** atomic units (49.999992 DREGG, 8 atomic units under the asked price). The floor is
deliberate: a payer who sends exactly 50 DREGG plus the one-time birth fee is at or over the price
(`297620` would make the week 50.00016 DREGG and journal that payer `belowPrice`), and exactly 50 DREGG
renews one whole week. The friend never sees these integers computed on their side: `mini join --solana`
prints the Host's own quote (op 121; `join_solana.rs` takes `atomicAmount` verbatim, no client formula),
which is `birthFee + 49999992`. If Ember wants an exact 50.000000 DREGG week, the unit of the tariff
must change from hourly to weekly (a Lean change to `Tariff`, `weekCredit` and its fixtures, then a
re-genesis); that is a design choice, not a rounding fix.

The old Lean `genesisDefault` still carries `nodeHourRate := 5952380` (about 1000 DREGG a week, PAY §11.8).
It is a placeholder that is invalid by construction (`genesisDefault_invalid`: version 0, zero mint) and is
replaced by the first `mini pay book` tariff before any enrollment can be decided; it is not an operating
source of the rate.

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
3. **The book and the tariff.** Render the files (above), then run this from ember's own workspace (the
   factory controller), in this order:

   ```
   mini pay book --dir EMBER-WS --source OUT/book.json       # row 0 = the receiving address; tariff N, enrolIndex null
   mini pay address --dir FLOAT-WS                           # the enrollment float takes row 0 (prints "index 0 → 5N2u…")
   mini pay book --dir EMBER-WS --source OUT/tariff-on.json  # tariff N+1 names the enrollment index
   ```

   The third step must come after the second: the book receiver refuses an `enrolIndex` whose row is not
   assigned (`enrolIndexUnassigned`). `book.json` has this shape (`render-enrol` writes it; the example
   shows the fields, not values to copy):

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
5. **`/etc/mini/pay/watcher.env`:** `render-enrol` writes it (installed with
   `mini-config install pay-watcher-env`). The enrollment variables are all or none:

   ```
   PAY_OBSERVER_WS=/var/lib/mini/pay/observer
   PAY_OBSERVER_CAPABILITY=C                 # genesis payObserver.capability
   PAY_ENROL_INDEX=0                         # from enrol-terms.json (PAY §11: the enrollment row)
   PAY_JOURNAL_FLOOR=1000000                 # from enrol-terms.json, atomic units
   PAY_ENROL_CAPABILITY=E                    # genesis payObserver.enrolCapability (C_enrol)
   PAY_OPERATOR_SOCKET=/var/lib/mini/store/node/operator/mini.sock
   ```

   (`MINI`, `PAY_WATCHER` and `PAY_STATE` are the unit's, set from the candidate; they do not go here.)
   The file holds neither the address nor the rate: the tick reads both from the Host's signed pay view,
   i.e. from what step 3 installed.

   **Self-enrollment needs the Host's operator socket.** Ops 117-120 (the self-enrollment plan,
   assembly, submit and lookup) are admitted only on an owner-private operator socket, never on the
   public one (op 117 runs the native verifier twice per call). On the box the socket is
   `/var/lib/mini/store/node/operator/mini.sock`, served by `mini serve-operator` (`store-entry.sh`)
   in a `0700` directory (`mini-service-config` creates it) owned by the Store's uid, with the public
   socket a filtered relay (`mini-public-ingress`) over it. That is the **ingress topology**
   (`/etc/mini/ingress.json`, written by `install.sh` on a clean frame and at `ship.sh --regenesis`).
   The old single-socket entry (`run.sh serve`, DEPLOY-2b's `5688775a`) has no operator socket, so
   self-enrollment cannot run there. The operator socket checks the peer UID: the tick must run as the
   Store's uid (`mini`; in split tenancy `install.sh` runs every Mini unit as `mini-core`, tick
   included). `mini-pay-watcher.service` keeps `ReadWritePaths=/var/lib/mini`, which covers
   connecting to that socket. Without `PAY_ENROL_CAPABILITY` and `PAY_OPERATOR_SOCKET`, an
   enrollment-index record is left undecided every tick (`enrol-unconfigured`, exit 3) and holds the
   enrollment cursor.

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
  "joining by yourself"). The pin it reads (`--enrol enrol.json`; `--memo-version v2` reads
  `enrol-v2.json`) is rendered from `enrol-terms.json` and published with the friend bundle. The client
  refuses a pin whose address differs from the box's book row at the enrollment index, and refuses an
  unset one (`EMBER_ENROL_ADDRESS`). The roster sync reads the same view with
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
