# Agreement mesh cutover runbook (DRAFT, 2026-10-05)

Status: draft. Nothing here has been run against the live mesh. Section 2
records Ember's decision on 00f711. Every step that
starts, stops or reconfigures a unit on hbox belongs to the infra owner; key
custody and topology are Ember's decisions. Tags: READ (looked at), RECORD (from
another lane's files), INFERRED, MEASURED (on a copy).

## 1. What runs the live mesh today

READ by lane AGREEMENT on hbox, 2026-10-05, read-only:

- Two user units, active since 2026-10-03:
  - `resident-context-four-source-r1.service`: the resident operator (`mini-f
    serve` with `.../codex-agreement-20261003/evidence/four-source-operator-r1/`).
  - `mini-agreement-backend-20261003-r1.service`: the session broker
    (`generic-simplex-session.py serve ... serve-session-native-r1.sh ...
    attempts 2000 180 owner-private`).
  - Their `*-persistent` twins are inactive.
- The engine is request-driven. Each broker attempt runs the pinned fixture
  binary (sha `e07af258…`) as `serve-calls` against the live root
  `/home/hbox/workbox/codex-runtime-lieutenant-20261003/evidence/four-source-r1`,
  with a DEBUG crypto helper. No standing `serve-replica` process runs.
- Journals are the legacy whole-image `replica-N/agreement.bin` (replica 0:
  3,448,412 B, last written 2026-10-03 15:18). Four context fields, no
  `agreement.log`.

## 2. Call 00f711: abandoned (Ember, 2026-10-05)

Ember's decision: the live mesh's call 00f711 is abandoned at the next mesh
re-genesis. Nothing is resolved on the pre-fix-C build and no work is spent on
it.

- 00f711 is the init call (record 3) and is uninstalled on the live mesh
  (INFERRED: no lane touched the live mesh, and its journal has not been written
  since 2026-10-03 15:18). It stalled because two replicas timed out before
  collecting q VOTEs in views 17-19 (scout R2-3). That schedule is now
  reproduced in `Verify.GenericSimplexHarness`.
- `init` derives a FRESH source genesis with new committee keys and empty
  source stores (READ, `Verify/NativeJointSourceFixture.lean`
  `initializeStores`). Nothing in the old domain carries over, record 3
  included. The caller's outcome stays "uncertain", and the init operation is
  redone on the new genesis.
- The old root is archived read-only (with SHA256SUMS) when the broker stops.
  It is never reopened by a current build: its four-field context refuses by
  name.

## 3. What the live mesh needs before the fix-C cutover

Code (each queued in MERGE-QUEUE.md by lane AGREEMENT-2):

- Fix C, the adaptive view timer (LANDED 4db78b30): a fifth `Config` field
  `backoffCap`. The fixture's context uses cap 3: a 100 s timer growing to
  800 s while no view commits.
- Quiescent leader (LANDED 02c427b8): a leader proposes only with work, and late
  when work arrives mid-view. Without it an idle mesh commits an empty block
  every view. MEASURED on a copy of the live evidence with the pre-fix-C build:
  CPU per appended input rose 0.57 s to 1.68 s over 45 minutes, with every
  replica one core busy.
- Incremental validation discovery (LANDED dd7f725e).
- Journal checkpoints (queued: 009b2adb on lane/agreement-2-land): reopen decodes a snapshot instead of
  replaying from genesis; `audit-journal` replays the retained segment chain.

Supervision (infra owner, units not written here):

- Four units, one per replica: `minidregg-four-source-fixture serve-replica
  ROOT/replica-i PEERS STORE SIG AG 100`, `Restart=always`, a `MemoryMax`, and
  logs kept. A replica never returns; a crash restarts it from its journal.
- The RELEASE crypto helper, rebuilt with OP_REPLACE (the checkpoint swap).
- The session broker unit is retired: engines no longer run inside client
  requests. Clients place requests in the spool (`await-call`, or
  `testing/generic-simplex-operator.py`, which never starts or signals engines).
- Each replica prints a `stats:` line per minute and `checkpoint` lines. Alert
  on a rising `us/packet` at steady load, and on a replica with no `stats:`
  line for two minutes.

Topology and custody (Ember's pause list): `init` writes every replica's
committee secret key and every pair key under ONE root. Four replicas on one
host are one failure domain. To spread them, MOVE a replica directory (that
host stops serving it). Never copy a live replica: the same journal and key in
two places is an equivocating signer.

## 4. Fix-C cutover sequence

1. Stop the broker. Archive the old root read-only (00f711 is abandoned, section 2).
2. Build the fixture and the release helper from the landed main that carries
   section 3's commits; record both shas.
3. `init NEWROOT STORE SIG AG ALICE_PUB BOB_PUB`. Ember chooses the two Ed25519
   subject keys; the old `subject-7.pub` and `subject-8.pub` can be reused.
4. Start the four units. Every replica must print `SERVE replica i listening`.
5. Smoke, in order:
   - 10 minutes idle: `stats:` lines show the view advancing on the backoff
     timer, packets/minute flat, and the journal growing by only a few deltas.
   - One operation end to end (the new domain's init operation): four exact
     identical receipts.
   - Restart one unit: time from start to `SERVE` (the target is under 10 s),
     and the same state.
   - `audit-journal NEWROOT i` for each replica: "AUDITED ... from genesis".
6. Point the resident operator at NEWROOT's spool, then announce the
   re-genesis.

## 5. What refuses, by name

- A four-field `context.bin`: "context.bin does not decode as a five-field
  Config context (a pre-timeout-backoff four-field context.bin refuses here;
  re-genesis with init)".
- A journal of log format 1, 2 or 3 under the current build: "agreement journal
  ... is log format version N; this build reads only version 4 ... re-genesised
  with init, never converted".
- Every old COMMIT certificate: signatures cover the encoded context.
- `convert-journal` and the whole-image `agreement.bin` path are deleted with
  the checkpoint commit: an old mesh is re-genesised, never converted.

## 6. Measured, and still open

- Before (pre-fix-C build, copy of the live evidence, 45 min idle): CPU per
  appended input 0.57 / 1.14 / 1.34 / 1.64 / 1.68 s per 10-minute window;
  journals 0.5-1.5 MB/min per replica; reopen 97 s per replica (AGREEMENT).
- Same fresh-genesis setup, pre-fix-C build (persvati evidence/fresh-before-p3,
  30 min idle): each replica uses 0.98 of a core, appends 162 deltas/min, and
  its journal reaches 9.6 MB in 30 minutes. A restart did not reach SERVE
  within the 120 s the driver waited.
- After fix C, the quiescent leader, incremental discovery and checkpoints
  (persvati evidence/idle-after-p123, fresh genesis, 2 h idle, MEASURED):
  - CPU is 0.04-0.05 of a core per replica in every 20-minute window from
    minute 20 to minute 120.
  - Receive+service costs 1.0-1.4 ms per packet in every minute's `stats:`
    line, with no upward trend: 992 us in the last sampled window against
    1572 us at minute 20.
  - About 7 deltas per view change; the view advances on the backoff timer.
    The journal is 11.7 KB after 2 h.
  - Reopen to SERVE takes 0.62 s per replica.
  - The synthetic 100 000-delta image restores in 2.08 s, and its checkpoint
    in 1.75 s (generic-simplex-log-reopen).
  - Packets per minute come from the 1 s retry round over the retained outbox,
    which still grows by a few messages per view. That is about 2000/min
    after 2 h.
- Still open:
  - Decided-view retirement. State still keeps every view, message and audit
    event, so a busy mesh's per-input cost still grows with operations, though
    no longer with idle time.
  - Blocks carry their exact ancestry, so each operation lengthens every later block.
  - The fourth host.
  - Supervision units.
