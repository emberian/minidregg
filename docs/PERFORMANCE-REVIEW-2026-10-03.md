# Why whole actions are slow: performance source review, 2026-10-03

Scope: a member's signed read, a document append, room creation, shared-name
resolution, an app HTTP request through `spk-host`, and one Hermes tool call,
traced end to end in `dev` at `2a075e68`. Every claim is tagged:

- **[measured]**: timed on hbox tonight (12th-gen i9, 24 threads, SHA-NI); load average given.
- **[traced]**: read along the code path at the cited file:line.
- **[inferred]**: follows from traced code, but the magnitude or a step was not observed.

Prior work in `planning/handoff-2026-10-02/PROGRAMMING-PERFORMANCE.md` still
stands and is not repeated. In particular these are already settled: an
unchanged session does **not** replay genesis or reread every directory per
request; the DFinsupp tree replaced quadratic nested-update reconstruction;
the 16-query batch exists; and the warm issue certificate serves op55 ticket lookup.

## What was measured tonight

The world is fresh: accepted height 28, six members, no rooms yet.

| Action (via forced-SSH Mini shell) | Wall | Load |
|---|---|---|
| `whoami`, `help`, `room list`, `inbox` (no Host exchange) | 0.15–0.16 s | 4.9–5.2 |
| `credit`, a signed read at height 28 (members 0, 1, 3) | 0.90–1.12 s | 5.0–6.0 |
| `pay status` (signed read + clock) | 0.98 s | 5.0 |
| `minidregg-host CONFIG profile` (bare spawn of the 159 MB Host) | 0.04 s (one outlier 0.17 s), 80 MB RSS | 5.2 |
| SHA-256 of the 159 MB Host image (`sha256sum`/`openssl`, page cache warm) | 0.09 s | 5.1 |

Older measurements (room creation ~190 s, submits 3–128 s, reads ~7 s, a
16-query reference flow 26.6 s) were taken on worlds with long histories. At
height 28 a read costs about 1 s. Small history is therefore not where the
seconds go. The seconds come from (a) fixed per-action process and exchange
counts, which are large but bounded, and (b) Host terms that grow with history
and are paid by every request after any write. App traffic adds to history
once per HTTP request (finding 1), so (b) arrives quickly once a browser app is in use.

## Ranked structural causes

Shares are honest estimates, not profiles. The only profile anyone has is the
old one (~39% `lean_apply` closure chains), and it predates the DFinsupp repair.

### 1. Every app HTTP request is a full Mini transaction, run serially (largest for apps; it also drives history growth)

**Per request [traced].** `ResidentHuman::deliver_once`
(`native/spk-host/src/dispatch_delivery.rs:65`) calls `author_and_submit`
(`dispatch_native.rs:921`), which runs:

1. Spawn Host `author application-dispatch-request` (`dispatch_native.rs:729`).
2. Socket op 36, the dispatch plan (`:736`).
3. Spawn Host `inspect application-dispatch-plan` (`:743`).
4. Spawn Host `signatures` (`:757`).
5. Socket op 37, assemble (`:768`).
6. Hot routes only: spawn Host `author application-route-bound-dispatch` (`:946`).
7. Socket op 34 or the route-bound submit (`:974`). This is a durable Store append.
8. Spawn Host `inspect application-dispatch-committed` (`:980`).

Every one of these 7–8 calls first runs `PrivateOperator::check_pin`
(`dispatch_native.rs:260-295`), which re-reads and SHA-256-hashes the whole
159 MB Host ELF. That makes 7–8 full-image hashes per HTTP request. The fd3
app call itself is cheap by comparison.

**Fixed cost [measured parts, inferred total].**
- Hashing: 8 × 0.09 s ≈ 0.7 s.
- Spawns: 5 × 0.04 s ≈ 0.2 s.
- Three Host operations, including one fsynced append with readback (see 2 and 4).
- So each asset fetch costs well over a second before the app runs.

**Serialization [traced].** The resident's HTTP loop dispatches one request at
a time (`http_entrance.rs:1009-1025`). Each principal may hold only 2 pending
requests (`:736-737`). The operator Host is single-threaded for the whole
world (`native/resource-client/src/transport.rs:1383-1390`, "runs one request
at a time"). A browser's six parallel asset fetches therefore queue behind one
another. They also queue behind every other member's reads, writes and Hermes calls.

**Growth [traced + inferred].** Op 34 commits a record into the single
accepted history (`matched.accepted_count`, `dispatch_transaction`). So every
page load, static asset and long-poll appends to the history that every later
request walks (cause 2). An open spreadsheet tab that polls becomes a steady writer.

**Remedy, in order.**
- **(a) Rust, safe, done tonight (B).** Verify the Host image once per inode
  and execute exactly the verified inode. Hash on first use. On later uses
  re-check `(dev, ino, size, mtime, ctime)` of both the held descriptor and the
  path, and re-hash only if anything moved. Spawn through the held descriptor
  (`/proc/self/fd/N`). This removes 7 of 8 hashes. It also closes a
  time-of-check gap: today the path is hashed, then re-opened by `execve`. The
  operator already compares the envelope pin with the image it started
  (`transport.rs:165-175`). So the per-call file hash before a *socket* op only
  re-confirmed the file on disk, which is not the Host that answers. What is
  verified does not change.
- **(b) Lean + Rust.** The four Host spawns per request are pure codecs:
  `author`, `inspect` and `signatures` are functions of config and input
  (`Host/Main.lean:5647-5790`; no Store). Two ways to remove them:
  - Serve them from a long-lived helper process (a `serve-codecs` loop beside `stdio`).
  - Better: link the compiled Lean codec modules into `spk-host` and `mini` as
    a static library, so the codec runs in-process.

  Either way the codecs remain the verified Lean code. A Rust re-implementation
  of `inspect` would put "what spk-host believes it is signing" into
  unverified Rust. That is a real widening of the trusted base, so do not port
  them. Do not route them through the operator socket either: they would then
  contend with every member's Host work on the single Host thread.
- **(c) Protocol, the decisive one.** Admit a browser session, not every
  request. The kernel already has the shape: route-bound hot enrollment
  (op 154) and the read-only stream-continuity attestation (op 152,
  `dispatch_native.rs:516-598`) keep a WebSocket authorized with periodic
  renewals and no Store record. Give ordinary HTTP on a hot route the same
  lease:
  - one admission per lease period;
  - each renewal is a signed op 152 read, bound to the same session fingerprint and tip;
  - requests inside the lease are delivered against the physical journal only.

  Trust story:
  - The Lean admission rules still decide who may use the route, and when.
  - Revocation takes effect within one lease period rather than at the next request.
  - Mini history no longer holds a per-request record. Per-request audit
    becomes host custody (the hostd journal), as it already is for WebSocket frames.

  This is a product decision as much as an engineering one. It needs a Lean
  change and is **not** started tonight.

Estimated share for app use: (a) ~0.7 s per request; (b) ~0.2 s plus Host
contention; (c) removes the Host from the per-request path entirely, plus all
history growth from app traffic.

### 2. Host work that grows with history runs on every request after any write (the main growth driver)

The Host is long-lived (`transport.rs:1226-1229`; `Host/Main.lean:5808-5814`).
Per request, `NativeHostSession.refresh` reads only the Store suffix
(`Kernel/NativeHostSession.lean:46-58` → `Compiler/DurableReceiverIO.lean:1153`).
That part is fine. But whenever the suffix is non-empty, which after any write
means the next request by anyone, it rebuilds whole-history structures [traced]:

- **`Image.cellIds`** (`Kernel/DurableReceiver.lean:183-185`) is
  `(seed ++ accepted.flatMap writes).eraseDups`. It is recomputed from the full
  accepted list and never memoized. Cost: O(W) to collect plus `eraseDups`
  (list based, O(W·C)) [inferred from Lean core], with W total writes and C
  distinct cells. Users:
  - `cellsLawfulFrom` (`Kernel/NativeHostContext.lean:300-303`) iterates every
    cell and compares its canonical bytes against the prior snapshot;
  - `Loaded.cells` (`Compiler/DurableReceiverIO.lean:648-650`);
  - checkpoints.
- **`Image.append`** is `accepted ++ [record]` (`DurableReceiver.lean:177-179`).
  That is an O(H) list copy for every accepted record, both on write and on refresh.
- **`historicalReceipt`** scans linearly for the transaction id
  (`Kernel/NativeHost.lean:894`) on every submit confirmation and every lookup: O(H).
- **`receiptRoot`** for a non-head index rebuilds the world root of the prefix
  (`NativeHost.lean:886-888` → `worldRoot`/`worldEntries` → `currentBytes`,
  which is `accepted.reverse.findSome?` per cell; `Compiler/NativeHostCodec.lean:63-70`,
  `DurableReceiver.lean:265-268`). Cost: O(C·H). It is hit by every
  `*LookupLoaded` and by `sessionConfirmed` when a concurrent append moved the head.
- **Checkpoint** every 64 appends: `State.ofSnapshot` over all cells and all
  nullifiers (`DurableReceiverIO.lean:998-1001`, `Kernel/DurableCheckpoint.lean:279-284`).

So with H accepted records, each request after a write costs at least O(H)
and plausibly O(H·C) of pure Lean list work, on the one Host thread.

**Remedy (Lean; proposals tonight, no Lean edits):**
- Keep **persistent indexed state** in the session beside the list semantics:
  - a cell-id set maintained per appended record (`Std.HashSet`/`RBMap`), with
    the theorem `cellsIncremental = Image.cellIds` as a refinement;
  - a transaction-id → index map;
  - `Array` for `accepted`;
  - the per-record log/world root kept at append time (the chain digest is
    already computed per record), so `receiptRoot` is a lookup.
- Make `cellsLawfulFrom` iterate only cells written by the new suffix. The
  refinement proof follows the existing `cellsLawfulFrom_eq`.

All of this stays inside the verified Host. Nothing moves to Rust. The
admission rules are unchanged: they are proven equal to the list
definitions, so the contract does not move. This is the work that turns
"fine at height 28" into "fine at height 100 000".

Estimated share at large H: most of the growth that the old 7 s reads and
3–128 s submits showed. That is inferred, because the growth curve has not
been measured on this build (see "Measure next").

### 3. Cold re-verification from genesis inside ordinary operations

[traced]
- **`confirmReadback`** runs `openExisting` + `verifyLoaded` from genesis after
  a successful append (`Kernel/FnEmptyPollReceiverV2.lean:38-48`). It
  re-admits every record and re-verifies every historical signature, each
  verification a fork/exec (cause 4). Callers:
  - fn empty-poll and selected-poll (`Host/Main.lean:1331`, `1301`);
  - consumer namespace (`:1267`);
  - agent-lifetime grant (`:1524`; `ApplicationAgentLifetimeGrantReceiver.lean:91`).

  Cost: O(H) signature verifications per operation, times the per-step terms
  of cause 2, so about O(H²).
- **First walk-family request per Host process** (`NativeHostSession.lean:72-76`):
  a full `verifyLoaded` (op 8, op 26, agent/fn ops).
- **`extendVerified`** (`Kernel/NativeHostReplay.lean:3007-3018`) re-encodes the
  old prefix and the matching new prefix and compares them byte for byte.
  Each call is O(H).
- **`CreatedHistory.select`** (`Kernel/ApplicationLifecycleCreatedHistory.lean:84-145`)
  replays the prefix from genesis twice and validates twice. This happens per
  continue-BEGIN and per such record inside every walk. The 636cd09a planner
  fix covers the unsigned planner only.

**Remedy (Lean).**
- `confirmReadback` should confirm against the warm session: refresh plus the
  exact receipt at the returned index, which is how `sessionConfirmed` already
  works. It should not reopen the Store from genesis.
- `extendVerified` should carry "this image extends the session's image" in
  the type. The session only ever appends suffixes it has validated, so prefix
  equality holds by construction and needs no runtime re-encoding.
  - Do **not** replace the byte comparison with a chain-hash comparison. That
    adds a collision-resistance assumption to a theorem that is currently exact.
- `CreatedHistory.select` should use a retained per-record certificate, which
  the 636 planner already does for the unsigned path.

All of this stays verified.

### 4. Helper coprocesses fork/exec a fresh child for every call

[traced] The signature verifier and the SQLite Store are started once as
`serve` coprocesses (`Compiler/NativeCoprocess.lean:71-81`). But each `serve`
loop spawns a fresh one-shot child per request:
- `native/credential-signature-verifier/src/main.rs:181`;
- `native/hyperdocument-link-sqlite-store/src/main.rs:279`.

Each signature verification:
- creates a temp directory;
- writes three files;
- does a coprocess round trip;
- does a fork/exec (`Compiler/CredentialSignatureIO.lean:56-70`).

Each Store call:
- fork/execs;
- opens SQLite and re-runs PRAGMAs (`lib.rs:442-446`);
- re-publishes the anchor with two fsyncs even when it is unchanged
  (`anchor.rs:141-150`, called at the end of `durable_read`, `lib.rs:814`).

A signed read costs at least one Store read plus one verification. A submit
costs one verification per signing slot, plus append, readback and the
confirm refresh (three Store calls). The fsync of an unchanged file is cheap
on Linux and expensive on macOS [inferred].

**Remedy (Rust, safe; outside this lane's files tonight).**
- Have `serve` handle requests in-process with the same functions the one-shot
  command calls: the Rust verifier is already in the trusted base, and it
  already runs as a child of the coprocess.
- Keep one SQLite connection open in the Store server.
- Publish the anchor only when the head changed.
  - Keep the crash-retry durability step, but run it once at server start,
    not on every read.

None of this changes what is verified. Estimated share at small history:
- per verification: about one process spawn plus file setup, on the order of 5–20 ms;
- per read: perhaps 10–30% of the Host-side time [inferred].

### 5. Client whole-action exchange counts (bounded, but large)

[traced] Each SSH command is one `mini` process (`shell.rs:3080`, `shell.rs:2544`),
so per-process caches never outlive an action. Every client↔operator exchange
opens a new Unix connection, rereads the config file (`transport.rs:1068`,
`:1111`) and fsyncs the reply file (`main.rs:1232`).

| Unit | Cost |
|---|---|
| One signed read (`main.rs:1716-1757`, `2117-2143`) | 7 exchanges: author intent, challenge, inspect, signatures, observe-assemble, query, inspect view. 4 of these are pure codecs through the world's single Host thread. |
| One submit (`main.rs:1804-1924`) | 10–11 exchanges. Also fsyncs the call file and every ancestor directory (`main.rs:1268-1286`). |
| A batch of N reads (`main.rs:2226-2288`) | 5N+6 exchanges. It buys one snapshot, not fewer exchanges. |
| Receipt continuity around every read (`receipt_continuity.rs:294-314`, `:576-585`) | `Settings::check` spawns the 159 MB Lean verifier (`profile`) on every call, 3–4 times per read. Each continuity hop adds one op 151 exchange plus two more Lean spawns. |
| `read ROOM/NAME` | Resolves the shared name twice: `workspace.rs:6050`, then again inside `read()` at `:1021`. About 70 exchanges and 5 continuity cycles; the room is read 5 times. |
| `room new` | About 19 exchanges and 10 spawns. `--in PARENT` is resolved twice (`workspace.rs:4599`, `:4224`). The continuity pass runs again after `submit_once` already finished it (`workspace.rs:4551`). |
| `doc append` | Two SSH logins. Propose costs about 9 exchanges plus 4 spawns. Submit re-authors the already-authored intent (`main.rs:1726`), about 12 exchanges. |
| `home ROOM` | About 8 exchanges. Scans every retained attempt (O(attempt history), `member.rs:82-108`). |

**Remedy.**
- **(C), Rust, safe, this lane:**
  - resolve once per action;
  - cache the `Settings::check` verifier identity per process (the image
    SHA-256 is already cached by inode at `main.rs:392-424`);
  - drop the duplicate continuity pass after birth;
  - resolve `--in PARENT` once;
  - keep one ref index per process.
- **Larger:** the same in-process Lean codec library as 1(b). It removes 4 of
  7 exchanges per read and about 6 of 11 per submit, and takes pure work off
  the world's Host thread.

Estimated share at small history: of the 0.9–1.1 s read, ~0.15 s is SSH and
process setup [measured], ~0.1 s is the Host image hash [measured], ~0.15–0.25 s
is Lean verifier spawns [measured per spawn, count traced], and the rest is 7–8
serialized exchanges with Host refresh, verification and Store fork costs [inferred].

### 6. Hermes tool calls multiply all of the above

[traced]
- **Read.** One read tool (`mini_doc_show`) spawns `mini shell --line …`
  (`native/grain-runtime/src/resource_tools.rs:895-915`). That is one process
  and one signed read.
- **Paid write.** One paid write (`mini_doc_append`, `grain-runtime/src/room_task.rs:164-219`) costs:

  | Item | Count |
  |---|---|
  | Child processes | about 11 |
  | Signed submits | 5: reserve, Book payment (`credit.rs:805-813`), append, settle, disconnect |
  | Signed reads | about 8 |
  | Host round trips | about 110 [inferred from per-unit counts] |
- **Idle polling.** `prepare_resident` (`hermes_room.rs:510-554`) runs about 7
  processes on every driver loop. It includes `room ls --since 0`, which
  fetches the full roster history and keeps the last 20 (`hermes_room.rs:546-548`).
  This grows with room history while idle.
- **Final reply.** Delivery re-enters the full paid path through
  `room_call_with_id("mini_say")` (`resident_delivery.rs:875`).

**Remedy.**
- **(Rust):**
  - run tool operations in-process in the runtime, instead of spawning `mini shell` per call;
  - poll `room ls --since LAST_HEIGHT` rather than `--since 0`.
- **(Lean + Rust):** one paid-tool transition that reserves, charges, applies
  and settles atomically. Four of the five submits exist to make a sequence of
  separate transactions crash-safe. The kernel can admit the composite as one
  checked effect with the same accounting theorems.

### 7. Global staleness turns concurrency into retries

[traced] A stale-root answer replans up to 5 times with backoff
(`replan.rs:175-183`, `main.rs` usage text: "when a tick, certify or another
write lands between an observation and its use").

[inferred] Preconditions are against a world-level root. So with N concurrent
writers, each write can force the others to observe again, and the work
amplifies with member count, independent of footprints.

**Remedy (Lean):** admission preconditions scoped to the cells an intent
actually reads, so two members writing different documents never invalidate
each other. The checked contract stays in Lean, and gets more precise.

## What moves to Rust, and what that does to the trust story

| Move | Stays verified | Untrusted accelerator, checked by Host | Would widen the trusted base |
|---|---|---|---|
| Host-image verification once per inode, exec of the verified inode (done, 1a) | Same pin, same bytes executed (stronger: no hash/exec gap) | — | — |
| Verifier/Store coprocesses serve in-process (4) | The same Rust verifier and Store code that already runs, minus the fork | — | — |
| Client exchange reductions (C) | Every signed read and submit still goes through the Host unchanged | Name resolution caching within one action: the guards re-check the pointer in the same batch | — |
| Lean codecs linked as a library (1b, 5) | Codec is still the verified Lean code | — | — |
| Re-implementing `inspect`/`author` in Rust | — | — | **Yes**: the custody would sign what unverified Rust says the plan contains. Avoid. |
| Rust maintaining Host indices (cell set, txid map) out of process | — | Possible as hints the Host re-checks, but the Host must still check membership. That gives no saving over doing it in Lean with a refinement proof. | Yes, if trusted. Do it in Lean. |
| Session leases for HTTP (1c) | Kernel decides route admission and renewal | — | Per-request authorization moves from the kernel's history to host custody, bounded by the lease. A product decision; state it explicitly. |

## Order I would build it

1. **Tonight, Rust:** spk-host browser defects (A), the Host-image verification
   cache with fd-bound exec (B), and the safe client reductions (C).
2. **Next, Rust, small:** verifier/Store coprocess in-process serving and
   anchor publish-on-change (4).
3. **Lean, the growth killer:** incremental cell set, txid index, `Array`
   accepted, per-record roots, suffix-only `cellsLawfulFrom` (2); warm-session
   `confirmReadback` and structural `extendVerified` (3).
4. **Lean + Rust:** codecs as a linked library (1b/5). This removes most
   process spawns and pure exchanges and takes them off the single Host thread.
5. **Protocol:** HTTP session leases (1c), a composite paid-tool transition
   (6), footprint-scoped staleness (7).

## Measure next (what would refute this review)

- Growth curve on this build: time `credit`, `room resolve`, `doc append` at
  H = 30, 300, 3 000 with the same member, and a Host CPU profile (`perf
  record -g` on the Host pid) at H = 3 000. If the per-request time stays flat
  in H, cause 2 is overestimated.
- One HTTP request through a hot route with `strace -f -c -e trace=execve,fsync`
  on spk-host. This confirms the 4–5 Host spawns and gives the fsync count.
- Before and after B: the same HTTP request should lose about 0.6 s.

## Lean change that the CSV capture does *not* need

The export-capture header was put into the Mini-signed header list
(`http_entrance.rs:532`). The kernel admits only ordinary header names
(`Kernel/ApplicationDispatchAdmission.lean:114-119,173`), so a CSV capture
could never be admitted. The capture nonce is host/TLS custody of the
response, not an app input. Carrying it beside the request, outside the signed
list, is therefore the correct repair, and no kernel change is needed. The
signed request admitted by the kernel is byte-identical to the same GET
without capture.

## Status after tonight's engineering lane

- `fc1e98a9`: the spk-host browser repairs (capture intent outside the
  signed list, RFC 9110 Accept, pre-commit projection, human fenced release,
  bounded accept queue) and remedy 1(a), the Host image verified once per
  inode with fd-bound exec.
- `1f9ccc5a`: the client reductions from cause 5:
  - shared name resolved once per `read`;
  - `--in PARENT` resolved once;
  - verifier `profile` identity cached per process;
  - no second continuity pass for an attempt this process just finished.
- Not yet measured end to end. The hbox world still runs the sealed
  `2a075e68` binaries, and no app is installed there. The expected effects
  (≈0.6 s less per app HTTP request; 24 fewer exchanges per shared `read`;
  3–4 fewer Lean spawns per signed read) are inferred from the traced counts
  and the per-unit measurements above.
- Remedies 1(b), 1(c), 2, 3, 6 and 7 are Lean or protocol work and remain
  proposals. Remedy 4 is Rust, but lives in
  `native/credential-signature-verifier` and
  `native/hyperdocument-link-sqlite-store`, outside this lane's files tonight.

## Round 2: persistent helpers (cause 4), Rust side done, Lean caller proposal

On main: `9309a9be` (signature verifier) and `4eeb1b1f` (SQLite store). Both
`serve` loops now answer each argv frame in-process with the one-shot
command's own function, so the reply bytes are unchanged and
`Compiler/NativeCoprocess.lean` needs no change. The store's crash and hold
fixtures still fork. An unchanged anchor is fsynced once per process.

Changes still worth making on the Lean side (proposals, not edits):

1. **Verification bytes in the frame, not in three temp files.**
   - Today: `Compiler/CredentialSignatureIO.lean:53-70` `verify` runs
     `IO.FS.withTempDir`, writes `public-key.bin`, `frame.bin` and
     `signature.bin`, sends their paths, and the server reads them back.
     That is a directory create, three writes and a recursive delete per
     signature.
   - Proposed verifier command `verify-hex KEYHEX FRAMEHEX SIGHEX`, the same
     `verify_strict` over decoded bytes. The frame bound is 64 KiB per
     argument, so the Lean caller falls back to files above it.
   - Proposed Lean change: `verify` sends
     `#["verify-hex", hex publicKey, hex frame, hex signature]` when
     `frame.length ≤ 32 KiB`, and otherwise keeps the current temp-file path.
     `parseOutput` is unchanged.
   - The trust story is unchanged: the same Rust verifier and the same
     response grammar.
2. **One open SQLite connection in the store server.** Each in-process
   request still opens the database and runs its PRAGMAs (`lib.rs:442-446`).
   A per-root connection cache in `serve` is Rust-only. It needs the
   anchor/flock discipline reviewed before it ships, so it was not attempted
   tonight.
3. **Fewer store round trips per refresh.** `durable-read` returns the
   suffix, but the Host still asks for a read after every append to confirm
   it (`readBackEntry`). The append reply could carry the read-back entry.
   That changes the frame contract, so it needs a Lean change on the caller
   (`Compiler/DurableReceiverIO.lean:1080`) and a matching verified decode of
   the combined reply.
