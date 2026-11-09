# PERF-CLIENT

The member's side of the Host: the `mini` client (shell, workspace, chat), the consent provider
and its residents, and the web body. A present-state table, rewritten whole. Lane `lane/perf-client`
(worktree `/Users/ember/dev/minidregg-lanes/perf-client`, hbox pool tree `t4`, scratch worlds and
tools under `hbox:/ci/pc`, the demo Store copy under `hbox:/ci/pc/demo`). Neighbours: the exorcist
owns the Host's read ops, the fsync removal and the web shell-child pool; hot-path owns submit,
propose, FORMAT, the consent snapshot start, the `Patch.run`/`setAll` chain and
`DeclaredResourceController`'s guards; store-retained owns the served state's representation.

**The budget is 10 ms per member operation** (ember, 2026-11-06), with a cold open under 1 s as the
floor. Every cost below is read against it.

## How it is measured

`hbox:/ci/pc/wN` are scratch worlds (`/ci/pc/up9.sh CANDIDATE wN PORT`: `jworld-scratch.sh up`,
five members). `/ci/pc/pcm.py WORLD MEMBER MINI REPS LINE...` runs a shell line the way the forced
ssh command does (the world's `mini-shell-ssh`, a chosen `mini`) and reports wall time and the CPU
each role spent (client, Store Host, Store helper, consent provider, codec, relay), summed over every
thread (`/proc/PID/task/*/schedstat`). `/ci/pc/demo/meas.py SETTLE CMD...` runs a Host command,
samples RSS every 20 ms and timestamps the `MINI_OPEN_TIMING` lap lines; `/ci/pc/demo/mc.py
PROVIDER CONFIG` cold-starts a consent provider on a Store and times its first admission (it sends a frame the provider admits before refusing).
`/ci/pc/demo/overlay.sh NAME` copies the base candidate and swaps in this lane's `mini` and consent
provider. Wall numbers on hbox are inflated by its load; CPU numbers much less.

The demo-scale census (`hbox:/ci/pc/census`): `/ci/pc/w13` is a scratch world of the sponsor and 7
members on candidate f2dae81d3680, grown by `grow13.sh` (2,400 rounds: a `say` in the shared room
each, a `doc new` on 2 of every 9) to 3,600 records with ~540 births, a story (`tale1`, sealed), a
room (`croom1`) and documents. `spec.sh WORLD OUT REPS` runs the census: member-1, warm (call slots
and consent resident warmed first), each line REPS times through the forced-command wrapper with ONE
fixed `MINI_TRACE` path per member (the line resident is keyed by `MINI_*`); `census.py` records wall
time and every traced hop (Host op, codec frame, consent frame) per run; `summ.py` makes the tables.
`swap13.sh WORLD DIR` installs a built Host, consent provider and `mini` in place in the world's
published candidate, rewrites their digests (SHA256SUMS, manifest, provenance, the Store's
`state.json`, the members' live workspace pins) and restarts the Store: the same world, before and
after. (A Store and its members pin the Host image; this rewrite is a scratch-world device, and a
real world changes image only through the re-genesis, `docs/WORLD-MIGRATION.md`.) App grains are not
measured: a scratch world has no apps worker or market index (`apps list`: `appsWorkerUnavailable`).

## The census at demo scale (`/ci/pc/w13`, 3,600 records, ~540 births, member-1 warm, ms wall)

Columns: base (f2dae81d3680: Host 994123619ffe), round 1 (37a2dc2c6: Host 81ac22c072f5), round 2
(this lane's round 2: Host 3742acf93cd7, consent provider rebuilt). Same world, 8 runs each, p50 (p95).
hbox load: base and round 1 ~5; round 2 ~15 (other tenants' obend jobs), so round 2's wall numbers
are inflated; its isolated rerun is the last column.

| command | base | round 1 | round 2 | round 2, isolated rerun (5 runs) | where it goes now |
|---|---|---|---|---|---|
| `whoami`, `inbox`, `chat rooms`, `room list`, `story list`, `history -n 20` | 1 to 4 | 1 to 7 | 1 to 3 | | local |
| `home` | 13 (137) | 16 | 18 | | local (one op 144) |
| `key-status` | 7 | 7 | 2 | | op 144 x2 |
| `credit` | 164 (277) | 7 (15) | 10 (11) | 11 to 12 | op 4 + op 5; was 6 signed reads (row 29) |
| `tariff feedback`, `read feedback`, `room status feedback`, `doc show`, `doc outline`, `doc pull`, `doc append` | 8 to 34 | 7 to 13 | 8 to 17 | | op 4 + op 5 (1.5 to 2.6), codec, consent |
| `can feedback` | 14 (52) | 30 | 15 | | two signed reads |
| `refs` | 48 | 49 | 24 | | resolves every name (shared names by signed discovery): intended |
| `room members feedback` | 20 (54) | 27 | 36 | | step 2 (b88411fc5) as above. Step 3 (this commit): the directory is held as data, one lifecycle image per identifier in a `SparseMap` with the used set beside it (`HeldImages`; a first use is a `Finset.cons` decided by the image), and a step writes only the cells it wrote (`loadServedDirectoryStep`, `loadServedDirectoryStep_eq`). `ServedDirectory`'s field is `exact` in place of `decoded`; `unique`, `load_eq`, `loadServedDirectory_ofLoaded` and `loadServedDirectoryFrom_eq` keep their statements. `loadServedDirectoryFrom` (the refresh) decodes only the cells whose bytes differ (`changedCells`), still a compare over every cell. With rows 37 and 38 below, w13 (~4,200 records, load ~4.5, base and lane back to back, 15 `say` and 15 `topic` each): op 2 p50 37.6 to 14.4 ms (`say`) and 36.7 to 13.1 ms (`topic`); `say` wall p50 95.3 to 64.0 ms. Open: the refresh's compare, and op 2's ~13 ms (row 37's misses, the policy load, the light basis) |
| `tail -n 20` | 144 (215) | 109 (182) | 121 (206) | 160 to 175 at load 15 | roster + one `tail` window per author; the window that scanned the log 55 to 60 -> 3.3; the rest decode each entry's signed command per read (row 31) |
| `look` (story) | 79 (91) | 21 | 42 | | three signed reads |
| `say`, `react`, `topic` | 176 to 182 | 89 to 90 | 157 to 172 | `say` 117 to 165 | op 2 (submit) 36 (round 1, load 5) to 80 (load 15); op 1 5 to 13; the member's own provider admitting the previous record inline 10 to 30 (row 32) |
| `doc push` | 198 (1640) | 104 | 172 | | as `say`, plus a pull |
| `doc new` (a birth, two records) | 986 (1235) | 769 | 2092 (7921) | | op 2 x2 (the birth submit ~300 of it), op 1 x2 (91 to 167), consent 284 to 604 (row 34) |
| `doc history cdoc1` | 176 (226) | 7,484 | 30,712 | | one past read (op 5 `at`) per write of the document: 5, then 15, then 25 as the census wrote it; 490 ms to 1.2 s each (row 30) |
| `doc history g1503` (born ~2,300) | 1,406 to 1,532 | | | | three past reads at ~450 ms (row 30) |

Host ops over the base census (all commands): op 2 (submit) 62% of Host op time, p50 153 ms; op 5
(query) 20%, p50 6 ms, p95 35; op 4 (challenge) 7%, p50 1.2; op 1 (prepare) 7%, p50 6, p95 106 (births);
op 144 (key status) 4%, p50 1.0; op 91 (birth context) p50 8. After round 1: op 2 p50 36.6 ms; op 5
is 90% of Host op time, almost all of it `doc history`'s past reads. How they grow with height: op 2
was 21 ms at height ~60 and 60 ms at ~1,560 before round 1 (quadratic in the authority's directory
rows); op 5's stream window grew with the log (it scanned it; round 2); a past read grows with the
checkpoint it decodes (the state's size), and `doc history` makes one per write of the document.
The first signed read after a Store restart: 16.3 s (round 1) and 19.7 s (round 2): the cold full
open (row 20), now paid on every restart of a Host at this height.

What a migration must carry is unchanged by rounds 1 and 2: no record layout, index, cell or key
read moves (the checks compile differently; the served bytes are the same).

## The demo Store, measured (2026-11-06, `hbox:/ci/pc/demo`, base candidate ae74dca4ec2d)

A consistent copy of the demo Store: 3,544 records, 44.1 MB of record bytes (median record
1,975 B; 534 resource births at 62 to 107 KB each are 33 MB of it: every birth carries the whole
authority cell's post image), 0.6 MB of tags, newest checkpoint 5.9 MB, 55 checkpoints kept
(176 MB, every one since height 64), 131,652 node rows (8.6 MB).

| open | what runs it | wall (hbox, load 1 to 14) | peak RSS | held after | where it goes |
|---|---|---|---|---|---|
| light (`NativeHostSession.start` -> `DurableServed.openHead`: checkpoint + suffix) | every Store Host (`minidregg-host CONFIG stdio`) at start | 1.45 to 1.98 s cold | 375 MB | 376 MB RSS, 306 MB anon | read 0.25 s, checkpoint decode, root and MAC 0.76 s (0.35 s warm), records/tags/index/replay 0.45 s |
| full (`DurableReceiverIO.loadChained`) | a Store Host the first time it serves a full-shaped op (`sessionOpened`/`sessionFull`/`sessionWalked`: grain births, dry runs, lifecycle and walk families, ~33 Host ops), every consent provider's start (`ClientConsentCore.verifyInitial`), every consent rebase (lag of 64 records) | 8.9 s | 2,226 MB | 1,215 MB | read of all 3,544 entries 3.4 s (RSS 0 -> 1.29 GB), checkpoint 1.0 s (-> 1.39 GB), gate and rebuild 4.4 s (-> 2.23 GB; decoding every record alone 3.7 s) |
| cold consent provider (`minidregg-client-consent CONFIG stdio`, first admission) | each member's provider: a resident, or the delegated worker's own child (`serve-controller-consent` without `--resident-dir`) | 10.6 s (26.6 s at load 14) | 2,230 MB | 1,253 MB RSS, 1,181 MB anon, 1,252 MB PSS | the full open above, then the walk from the checkpoint |

Where the memory is: every byte is a `List UInt8` cell (24 bytes per byte). The read turns the
44 MB of record bytes into ~1.06 GB of lists, decoding every prefix record allocates another
~1.06 GB (the records' `canonicalPostBytes` and event bytes), and the checkpoint (5.9 MB) is
another ~141 MB as a list and again as its decoded cells. What a full open holds afterwards is the
decoded records (`Loaded.image.accepted`, ~1.06 GB) plus the state's cells: 1.2 GB, about 210x the
checkpoint. 71% of the open's samples are in the kernel (page faults zeroing that memory), 25% in
the Host's own code. Peak = the entry lists and the decoded records alive together.

What a warm member command costs, against 10 ms (the demo's zero-lag `credit`, 1,051 ms under split tenancy with `--resident-dir`, is NOT reproduced by any hbox world: split tenancy needs root and separate uids; see the report's trace recipe) (scratch world on the base candidate, member-1,
`mini-shell-ssh` with residents warm): `credit` 7 to 10 ms when nothing was written since the
member's last command; **+~8 ms of consent CPU per record anyone else wrote meanwhile** (10 records:
93 to 105 ms; 30 records: 228 to 256 ms), and a full open (8.9 s here, 7 s on the demo) once the
lag reaches 64. On the demo, where the clock, Hermes and other members write between a member's
commands, that is the 1,050 ms `credit`. Row 19 below removes it from the command path.

## Findings

Staging 7fee25ff's `mini` (it carries the exorcist's batches) unless said otherwise. ms.

| # | where | what it does | why nobody would do it on purpose | cost | fix | state |
|---|---|---|---|---|---|---|
| 1 | every receiver's `readGuards` (`ResourceBirthReceiver`, `ResourceBirthController`, fleet turn, clock tick, certify, pay, capability, ... 21 files) | the filter lambda evaluates `writes prepared` once **per guard**: every post cell rebuilt and canonically encoded per guard, the authority cell's post patch included | the written ids are one list | a birth (`doc new`, two records) costs a member's consent provider 0.5 to 1.1 s of CPU; 56% of the provider's catch-up profile is the birth walk, 36% of it this filter; the Host runs the same receivers | ids bound once before the filter; the authority write encodes its post once; the birth intent's charge reads the writes and guards the intent already holds (`chargeWith`) | dafd69ac1 (batch 6): a member's catch-up of two births (4 records) 1155 to 555 ms of consent CPU; the filter (17% inclusive) and `Loaded.writes` (19%) are gone from the profile |
| 2 | `main.rs` `host_image_sha256` | SHA-256 of the 182 MB Host image once per process unless a loaded workspace pinned it; chat reads, bend, activity, clock, job and checkpoint read `workspace.json` raw and never pin | a digest of an unchanged file | chat `tail -n 5`: 170 of 186 ms of client CPU | the digest is kept by file identity in the owner-private resident directory | 60b0dbf20: `tail` client CPU 176 to 26 ms |
| 3 | consent provider cold start (`Host/ClientConsentCore.verifyInitial`) | a new provider opens the Store (`loadChained`: `openState`, `foldRecords`, `World.admit`) and walks every record above the Store base or its retained anchor | a resumed provider needs the anchor's state, not the history below it | member-3, no anchor, height ~165: 6.1 s (walk 39%, the Store open 23%); with a one-record-old anchor 2.3 s. (`checkpointEvery: null` in the deployed config is read as 64 everywhere: not a cause.) | the walk: rows 1 and 9; the open: hot-path (its row 11, the FORMAT batch) | split |
| 4 | `mini_sdk::consent` resident idle exit (600 s) | consent and codec residents ended after ten idle minutes and the next command paid row 3 | the member comes back; a web session lasts a day idle | 2 to 61 s on the first command after ten minutes away | no idle exit: a resident ends with its world, its child, or a superseded binding (another file at its executable path, other bytes at its settings path), and outlives the attempt whose settings copy started it; `serve-controller-consent` the same, and it polls its listener instead of sleeping 20 ms per accept | 86428a2f1, 1e37efc44: 11 min idle then `credit`: the resident stayed (catch-up of the records written meanwhile only) |
| 5 | consent catch-up (`refresh` -> `ConsentAnchor.Basis.extendAppended` -> `NativeHostReplay.walkSuffix`, plus `DurableReceiverIO.extendFrom`) | every member's provider re-executes every record since it last looked | independent verification is the design (ember's question pending) | ~150 ms per record at load 25 (11 records, 1.73 s): walk 46% (DRC authority legs 21%, capability evidence 18%, issuerCheck 14.5%: hot-path), `extendFrom` -> `WorldTrack.advance` -> `World.admit` -> `pinFails` -> `DeployedBridge.cellRoot` 16% (row 9) | rows 1 and 9, hot-path's DRC and issuer work | open |
| 6 | `workspace::recheck_commitment` | one Host key-status round trip per `mini` process, before any verb | a verb process per ssh command makes "once per process" once per command | a missing-reference `doc show` still spends 30 ms of Host CPU at load 30 (op 144, 4 to 5 ms idle) | open (a security check; the Host op is the exorcist's) | open |
| 7 | `shell.rs` `history` (web `/receipts`, `history all`) | judged every retained attempt (a read_dir and a last-outcome read each) and the page listed them all | a page shows the newest few | O(attempts): 25 ms client CPU at 474 attempts, load 25; 45 to 68 ms at ~700 (explorer) | `history [all] -n N`: attempts ordered by directory mtime (one stat each), judged newest first until N rows; `/receipts` shows the newest 50 | bf842496c: `history all -n 50` 12 ms at 474 attempts |
| 8 | resident footprint | each member's consent provider and codec Host do byte-identical work (one Store, one pinned config, one image) | one verifier and one codec per box serve them all | single tenancy, per member ~87 MB PSS (provider 56 to 90 MB private, flat over 117 records; codec 12 MB private); split tenancy, per member a 2.5 MB worker + a 91 MB provider child running a pinned memfd COPY of the 194 MB image (its code pages not shared) + the member's codec | single tenancy: one resident directory (`/etc/mini/session-residents`, dev `residents`); split tenancy (ember's ruling 2026-10-31): `serve-controller-consent --resident-dir` relays each member connection to ONE operator consent resident (fresh connection per member connection: the Store re-check per command kept), and `mini serve-codec` is one codec for every member account (`/etc/mini/session-codec`; clients check the greeting's image and config digests) | ae39dfeb4 single: 5 members 582 to 311 MB PSS. a36d8bdfa + 394039fb1 split: worker 2.0 MB PSS and no provider per member; infra renders the units with batch 7, then a forge measurement |
| 9 | `Kernel.World` `World.admit` -> `pinCheck` -> `pinFails` -> `DeployedBridge.cellRoot` (in `WorldTrack.advance`) | re-encodes the World's own copy of every pinned cell (a fresh value after each write, its byte cache cold) to compare its root, per record | the executed snapshot already holds those cells' canonical bytes | 16% of a warm catch-up; the Host's append runs the same advance | pins judged from the snapshot's bytes (`snapPinFails`, proved equal at a represented World); `World.admitPinned` with `admit_eq_admitPinned` (rfl) | 5415aecf7: lane-check green; awaits a Host/consent build for the number |
| 9b | `Compiler/WorldCompact.compactEvery` | rebuilds every cell's store and the cell map every 32 heights | only cells written since the last compaction changed | O(World) per 32 records | superseded: retained-mode's L0 makes the World's cells and system SparseMap trees, and `WorldCompact` goes | retained-mode (L0) |
| 10 | the member ssh wrapper (`deploy/shell/mini-shell-ssh`, and dregg-infra's deployed copy) | `#!/usr/bin/env bash` probes PATH (8 to 11 failed execve per command), `readlink`/`dirname`/`dirname`/`basename` for MINI_CANDIDATE_SHA, and under split tenancy `sha256sum` of the 194 MB consent provider and the config per command (`mini-web-spawn` per body start) | the digests change once per ship; the client knows its own path | 12 of 15 execve of an ssh `say`; ~176 ms CPU per command where `consent/peer.sock` exists | the candidate's wrapper carries every deployed feature in two processes (bash, mini), files read with builtin `read`; the pins come from a ship-rendered `HOME/consent/peer.pins` (hashing only without it); the client derives its candidate id (f95edc7bf) | b34173dad; infra installs it from batch 7 and renders `peer.pins` in ship.sh |
| 12 | consent provider per member connection (`serve`: frame 233 `recheckHeld`, then `refresh` -> `extendFrom`) | two Store reads per command: the tag at `height`, then the entries from `height + 1` | the resident sends 233 and the command back to back under one lock: one read from `height` serves both | one Store helper round trip per command | 233 answers at once and the re-check is owed: the next frame makes it on its own admitting read (`refreshHeld`: `ConsentAnchor.checkHeld` on the first entry, `DurableReceiverIO.extendStored` on the rest) or, if it admits nothing, as a read of its own (`recheckOrEnd`); `checkHeld` is now the one judgement `recheckHeld` applies | 5517f6f57 + d7e252590 (batch 7) |
| 13 | a birth's authority leg (`ResourceBirthPolicyController.rawLeg .authority` -> `ResourceBirthAuthority.request` -> Theory's generic `authState`) | rebuilds the authority projection per leg built: revoked and parent sets each a `Finset.biUnion` over `DFinsupp.support` (quadratic dedups over the whole authority store) | the snapshot holds that projection (`authStateExact`), built once through hot-path's fast `@[csimp]` | 12.8% of a batch-6 consent catch-up of births; the Host builds the same legs | the leg asks `factoryRequest` at `oldAuthority prepared`, as the other legs do; `requestExact` proved from `authStateExact` | ff9ebd756 (batch 7) |
| 14 | every Store open (`DurableReceiverIO.openLoaded` -> `trackOfWorld` -> `HostRefinesWorld.representsCheck`): a cold or lagging consent provider, the Host's open | judged each system row by `List` membership in every transaction id, nullifier key and cell id of the log, over `DFinsupp.support` (a dedup of the whole map): quadratic in the log | each list read once into a hash set; the maps' own support multisets iterated | a member's first read after idling 150 records, height ~920: 20.8 s, 56 to 66% in `rowOk` (the explorer's 19 s first `GET /doc/NAME`) | `representsCheckFast` behind `@[csimp] representsCheck_eq_fast` (statement and `_sound` unchanged) | 36612f028 + 6a088183f: the same read 3.9 s on an overlay (hbox, candidates/131e045779bf), `representsCheckFast` 9%; the rest is the open itself (`loadChained`) and the walk from the checkpoint |
| 15 | every client binary's `print!` (std) on a closed stdout | std panics on a failed write and the runtime ignores SIGPIPE: `mini --help \| grep -q` exited 101 (explorer, batch 8 world-up) | a reader that left is not an error | a red, not a cost | `native/mini-streams`: the crates' `print!` family (via `#[macro_use] extern crate mini_streams`) unwinds with a marker on a closed stdout; `guard` ends `main` with 141; a resident ends only that command; closed stderr drops the message. One implementation for mini, mini-line, mini-web, mini-web-spawn, mini-keys, spk-host, grain-runtime | d73a0cdea, 096c881e5 (batch 9) |
| 16 | the consent provider's anchored suffix walk (`ConsentAnchor.resume` -> `walkSuffix` -> `NativeHostReplay.advance` -> `Loaded.extend`) | advances its own World per record (`WorldTrack.advance`: the turn derived, cells decoded, admitted) beside the provider's replay of the same records from the Store (`extendStored` -> `Loaded.replay`), which already judges each as a turn; nothing reads the walk's World | one judgement per record | 7.9% of a batch-8 provider's CPU during `doc new` (the replay's copy is another 9.6%) | the walk starts from `Loaded.untracked`; the Host's walks stay tracked (receivers append from a verified walk's image) | 042f2a0c1 (lane-check green; batch 10): after-number on its candidate |
| 17 | twin selection of a member's delegated consent and shared codec (`mini-line`, `mini-web-spawn`) | each read `consent/peer.sock`, `peer.pins` (or hashed the provider) and `/etc/mini/session-codec` itself | one member's two sessions must select alike | correctness, not cost | `native/mini-session-env` is the one reading | caa988a88 |
| 18 | `workspace::recheck_commitment` in a resident (`line-resident`, `command-resident`, the client resident) | cached "checked" in a process static: once per resident lifetime | a rotation or revocation by another holder between commands is what the check exists to catch | a correctness bug, not a cost (batches 8 and 9 not shippable without it) | `capture::argv` forgets the checks before each resident command; composing verbs' in-process steps still share one check | d035d8250 (batch 10) |
| 11 | world bring-up (`jworld-scratch.sh up`, dregg-infra) | 219 s for a five-member scratch world | | every measurement world and journey pays it | for whoever owns world bring-up | noted |
| 19 | the consent provider's admission of other writers' records (`ClientConsentCore.serve` -> `refresh`/`refreshHeld`), made on the member's next frame | every record anyone appended since the member's last command was admitted inside that command; a shared provider started cold inside the first command after a restart (38 s on the demo) | the records landed seconds or hours earlier; the member is waiting now | ~8 ms of consent CPU per foreign record on the command path (30 records: `credit` 228 to 256 ms); the demo's 1,047 ms `credit`; at a lag of 64, a full open (row 20) | the member's resident (`mini_sdk::consent`, which `--resident-dir` workers relay to) and the delegated worker's own verifier run a catch-up thread: `HeadWatch` stats the Store's `STORE.head-anchor` (renamed on every append) every 100 ms, once a second without it, and sends an intent frame with no intent (220, empty): the provider admits to the head before it judges, then refuses it; the provider then still answering its anchor (229) confirms the admission. The first catch-up is the start admission. No new frame: the Host image is unchanged (9b9ca712 rebuilt byte-identical) | 82a555e85 (frame 237, withdrawn: it changed the Host image through the protocol table); 7b20a1379 (236, withdrawn: row 26); 1b753fe15 (empty intent) on main and `hotfix/door-on-8f2d`. Demo Store copy: a cold resident admits once in 11 s (1.25 GB), then 0 to 8 ms per catch-up; restarted with its retained anchor, 11 s once, then idle. 30 foreign records then `credit`: 228 to 256 ms before, 8 to 12 ms after; idle cost ~2 ms CPU per second across six residents |
| 20 | every full open (`DurableReceiverIO.loadChained`: `transport.read 1 true`, `openState`, `openLoaded`) | reads every entry into `List UInt8` lists, decodes every prefix record, keeps the decoded log (`Loaded.image.accepted`) | the checkpoint already holds the prefix's state; `List UInt8` is 24 bytes per byte | demo Store: 8.9 s, 2.23 GB peak, 1.22 GB held (row in the table above); a consent provider's start 10.6 s and 1.25 GB | the structural fix is an open that neither reads nor holds the prefix (the "journal read at use" unit of `DurableFastForwardSpec`; the KN2 deletion of the full shape) and bytes as `ByteArray`; a constant-factor step inside the current types: parse the read into one packed buffer and decode prefix records from it (`StreamCodec.decodeAt`, already native for `recordFrame`) without building the entry lists (peak ~-1 GB, the held 1.2 GB unchanged) | bytes-repr (this lane's seat file, board/seats/bytes-repr.md): record bodies and checkpoints are `ByteArray` (one slice of the read, hashed by the cSHAKE kernel and decoded on the cursor in place, each `_eq` to its list spec); the whole-log read is paged (`readWhole`, 256 heights per Store call) because w13 at height ~3,860 passed the 64 MiB coprocess reply bound and every consent provider refused to start. Consent cold start on a w13 copy (3,777 records, hbox load 27 to 29): 42.8/40.6 s -> 32.6/29.2 s, peak 2.95 GB -> 1.66 to 1.71 GB, the read 10.3 s -> 0.8 to 1.2 s; held unchanged (1.65 GB: the decoded records' `canonicalPostBytes` lists). Open: the open that neither reads nor holds the prefix (KN2 2b, then read-path's consent port) and `DataWrite.canonicalPostBytes` as `ByteArray` |
| 21 | split tenancy as deployed on the demo: each hosted member's `serve-controller-consent` runs its OWN provider (no `--resident-dir`) | one 1.25 GB provider per member, each admitting every record | the providers are byte-identical work (row 8) | 1.25 GB resident and the whole admission CPU per member | render the units with `--resident-dir` (a36d8bdfa: ONE operator resident; a member's worker is a 2 MB relay); infra's | ops: ready since batch 7 |
| 22 | consent rebase (`refreshExtended`: lag >= `checkpointEvery` -> `verifyInitial`) | a provider 64 records behind restarts from the checkpoint with a full open | the open is O(the whole log) (row 20) while the catch-up it replaces is O(lag) | 7 to 9 s at the demo's height, growing with the log | with row 19 the lag stays at the last moment's records, so it fires only after a restart or outage; the open itself is row 20 | mitigated by row 19 |
| 23 | the Store Host's full image (`NativeHostSession.materialize`) | the first full-shaped op (grain birth prepare, dry run 130, op 5's fallback, lifecycle and walk families; 33 functions in `Host/Main.lean`) opens the whole log and keeps it | the light opening serves the rest | 375 MB -> ~1.6 GB resident, 8.9 s once per Host process | porting those families to the light opening (`scripts/ports/full-loaded-callers.txt`, the KN2 ratchet) | open (KN2) |
| 24 | `durable_checkpoint` | every checkpoint is kept (55 on the demo, 176 MB) | the open reads only the newest; `Reader.stateAt` and `durable-checkpoint-at` want one at or below a past height | disk and backup size, not time | keep the newest few plus a sparse ladder for past-height reads; needs `checkpointAt`'s users to accept a longer replay | open |
| 25 | the delegated worker's lock (`consent_proxy::serve_connection`) | waits for a busy verifier with `try_lock` and a 10 ms sleep | a blocking wait with the same deadline wakes at once | up to 10 ms per frame whenever a catch-up (row 19) or another connection holds the verifier | a condition variable with the REPLAY deadline | open (small) |
| 26 | full readiness (236: `ClientConsentCore.upgrade` -> `Basis.full?` -> `NativeHostReplay.verifyStart`) on an anchored admission | a second full open, then a re-admission walk | the admission it upgrades already covers the head | demo Store copy: no answer within 200 s (199 s CPU, 2.26 GB); on the demo, three providers at 100% for 9+ minutes when 7b20a1379's catch-up sent it. `mini consent-full-ready` (an explicit readiness command) sends it too | the catch-up no longer sends it (row 19); the upgrade itself should walk only from the anchored height (hot-path's `verifyStart`/`verifyFrom`); until then nothing on a live box should run `consent-full-ready` | open (hazard) |
| 27 | a warm read's Store Host op 5 (the signed view query) -> capability evidence -> `domainPortal.verifyIssuer` -> `issuerCheck` | decided `∃ address ∈ support, issuedAt ...`: walked the authority cell's support, encoding and hashing every stored capability until one matched, per check | the commitments change only when the cell does | 0.8 ms at height ~60, 11 to 13 ms at 350 births (scratch), 36 to 137 ms per `credit` on the demo (534 births, 230 capabilities); the search alone 3.1 ms per check on the demo Store copy (`store-bench`) | `issuerCheck_eq_indexed` (statement first, `@[csimp]`): the issued index `CredentialAuthorityDomain.issuedOf`, a `Thunk` held with the cell (`Snapshot.issued`, `ServedAuthority.issued`, shared by every request's snapshot) | on main (Host image change, next re-genesis): op 5 11 -> 1.3 to 1.5 ms and warm `credit` 16 -> 6 ms at 400 births (/ci/pc/w12 against /ci/pc/w9); 0 ms per check on the demo copy |
| 28 | receipt continuity after every signed read (`receipt_continuity::finish` -> `HostProof`) | sealed the 185 MB verifier image and started it for `continuity-point` on every read, and again for `continuity-verify` per hop when the head moved (plus `profile` once per process) | an unmoved head's point is the one the verifier just derived | warm resident shell, continuity on (/ci/pc/w9): `credit` 56 ms (op5 11, `continuity-point` spawn 39 to 50); after the head moved 143 to 258 ms (`continuity-point` 40 to 146, op 151 19, `continuity-verify` 41 to 146) | 9b117157e (main) / 976f31067 (hotfix): points kept per process by exactly what `challengePointJson` reads (verifier pin, config digest, the challenge's domain, semantics, height, world root); the verifier sealed at first use. Warm unmoved `credit` 56 -> 16 ms. A moved head still pays two verifier processes (~80 to 290 ms): the Lean continuity functions need a long-lived loop (a Host op or the codec loop), which is a Host image change | moved-head case open |
| 29 | `credit` without `--account` (`credit::my_account`) | resolved every workspace reference through `workspace::reference` to find the one account; a shared name (`ROOM/NAME`) resolves by a signed discovery | the member's own account is never a room's binding | 5 signed reads before the balance read: 164 ms at 3,600 records | the default account is chosen from the address book only (`local_reference`); `--account` still names any | 37a2dc2c6: 164 -> 7 ms |
| 29b | every submit (op 2) -> `CredentialAuthorityServed.decodeServedFrom` | decided the served directory's `(rows.map Prod.fst).Nodup` with the pairwise `List.Nodup` instance: every pair of big-number row ids compared, per write | the loaded twins already compile to one hashed pass | 64% of the Store Host's CPU across `say`s; op 2 151 ms at 3,600 records (21 at ~60) | `CompiledListOps.nodupNat` (one hashed pass); `decodeServedFrom_eq` keeps its statement through `nodupNat_iff` | 37a2dc2c6: op 2 151 -> 36.5 ms; `say` 178 -> 89; `doc new` 986 -> 769 |
| 30 | past reads (op 5 `at`) | read, MAC-checked and decoded a kept checkpoint and replayed to h, then materialized the whole authority trie at h, per read | a cell's bytes at h are its last write at or below h; the grant needs a few epochs and revocations | 0.6 to 1.5 s per read; `doc history` 1.9 to 30 s | `Loaded.pastBytes` (the last write, off the held log) and `grantStandingIn` on the authority cell's bytes there; the kept-checkpoint path deleted | 1fca8363b: 12 to 35 ms per read; `doc history g1512` 4.5 s -> 90 ms, `cdoc1` (35 writes) 30 s -> 1.2 s. Remaining: one round trip per write of the document (a history view answered in one request is the retained form) |
| 31 | `tail` (`chat::Held::stream` -> op 5 `tail` view -> `streamPayload`) | each shown entry's payload: a scan of the whole accepted log from its OLDEST record (`Image.accepted` is `acceptedRev.reverse`, rebuilt per entry), then a decode of the entry's whole signed command | the log has a transaction index (`Loaded.txs`) and the newest entries sit at the head of `acceptedRev`; the payload is fixed when the record lands | the window holding the newest entries 55 to 60 ms per read at 3,600 records; the other windows 17 to 37 ms (the command decodes) | round 2: `streamPayloadIn` reads through the index from the held end (`intentOf_eq`, `streamPayloadIn_eq`: the same payload); `sinceViewIn` takes the records above `after` from the held end (`sinceViewIn_eq`). Remaining: the payload kept by delta at append (a payload index in `Loaded`) | round 2 (Host 3742acf93cd7): that window 55 to 60 -> 3.3 ms; the rest open |
| 32 | a member's own provider admitting the record the member just wrote | the catch-up thread (row 19) polls the head every 100 ms; a command issued sooner admits the previous write inline, at the provider's per-record cost (which carried row 29b's quadratic check until the provider is rebuilt with it) | the resident wrote that record itself a moment ago | 10 to 30 ms on the first consent frame of back-to-back writes | the provider rebuilt with 29b (round 2 ships it); the resident could catch up right after its own submit instead of at the next poll | the provider was rebuilt with 29b. Catch-up is now eager: a resident's catch-up thread waits on inotify for the head marker's rename (`HeadWatch::wait`) and admits a record as it lands, not at the next 100 ms poll. w13 (~3,980 records, load ~5), 15 `say` and 15 `topic`: consent on the command path 34.6 to 9.0 ms (`say`) and 36.1 to 11.8 ms (`topic`); with row 36, `say` wall 102.9 to 77.4 ms |
| 33 | `room members` (op 5 `who`: `holders`, `grantsOf`, `members` over `Finset.biUnion` of capability ids) | rebuilds the room's holder and grant sets from the authority store per read | they change only when a grant does | 21 to 28 ms at 7 members | an index kept with the authority cell (as row 27's issued index) | open |
| 34 | a birth (`doc new`, `room new`, `story new`) | op 1 (prepare) 90 to 170 ms and op 2 (the birth's submit) ~300 ms, plus 284 to 604 ms of consent CPU across residents | | `doc new` 769 ms after round 1 | not yet profiled at this height after 29b | open |
| 35 | `jworld-scratch.sh down` (dregg-infra) | leaves every member's line resident running (they end only when their socket or Store goes) | `down` stops the world | 10 to 18 survivors per world, each a warm `mini` | `down` should stop the line residents by their pid files (`sessions/*/.call-slots/*.pid`) | noted (infra's) |
| 36 | every validation of a next state: each submit (op 2, `validateServedFrom`) and each record a provider admits (`validateLoadedFrom`) | re-decides whole-state facts on the new state: every recorded policy's source looked up and its record digest checked (`policiesSourced`), every cell's law, the directory and authority reloads | the invariants held for the prior state and a record writes a handful of cells | demo Store copy, nothing new: 21.6 ms (served) and 15.8 ms (loaded) per validation; ~half of op 2's 44 ms and most of a provider's 35 ms per `say` | step 1 (338280802): the record digest is hashed off the cell's cached bytes. Step 2 (lane/perf-client-moved): the write set comes as evidence (`Served.Moved`, from `Served.advance_moved`, carried by `Received.appended`; `LoadedMoved.extend` for a provider's walk). `validateServedStep` and `validateLoadedStep` run the cell law on the written cells only, and inherit the sourcing verdict unless the step wrote the authority cell or a cell that held a policy source (`policiesSourced_inherit`); `_eq` theorems tie both to `validateServed` and `validateLoaded` | step 2: `policySourcedAt` is 0 samples of op 2 (13.6% before). What remains of the served validation is the directory: `loadServedDirectoryFrom` still lists, compares and rebuilds every row (O(cells), ~12% of op 2's samples). It goes when the directory is held as a persistent map and updated at the written rows. Open |
| 37 | op 2's index rows (`DurableReceiverIO.withIndexRows`, `indexRows`, `DurableHistoryStore.byTx`/`spent`, the reader footprint) | each append reads every changed key's 48-level path and siblings of the authenticated index back from SQLite through the Store helper, then writes the new rows | the Host could hold the index trie it maintains and update it by delta | 14% of the Store Host's CPU across `say`s | `Compiler/DurableNodeCache.lean`: the serving Store Host holds the node rows of the height it last appended, as written or read (absent rows included). An installed append moves the cache by the rows it wrote, and a read at that height asks the Store only for misses. Untrusted: every row is verified against the authenticated roots | the SQLite reads are gone on a hit (da318a3e7). This commit: the serving Host also holds the index trie's rows decoded, by bit prefix, at one height (`DurableNodeCache.Decoded`, `Transport.heldIndexRows`/`holdIndexRows`); `receiveServed` hands over the rows its append wrote, and `withIndexRows` the rows it read; an index answer at that height walks them with no prefix list, row key or decode, and falls back to the Store read when they do not verify (untrusted, as before). The node cache's `history` no longer copies its whole map per request with a miss (a `get` kept it shared; now `modifyGet`). Then (round 2): the light open hands the holder the whole trie (`DurableReceiverIO.preloadIndex`, a breadth-first walk, one Store read per level, only for a transport whose holder asks, `preloadsIndex`), so a fresh Host's footprint reads no longer miss: `indexRowsRead` is 0 samples of op 2 after a restart (11.5% before), and op 1 p50 7 to 5-6 ms on w13. What remains in op 2 is the trie work itself (`IndexRows.insert`/`set`, `lookupRows`, `AuthTrie.verify`, ~24%), the record and tag encodes (~24%), the controller's admission (~24%), `Served.advance` (~13%) and `SessionIndex.dedup` (~11%). Open |
| 38 | the due checkpoint (`receiveServed` -> `DurableCheckpointCodec.sealAt`, every 64th append) | encodes the whole served state (`StoreCodec.entries` over every cell) and MACs it, inside a member's write | the state differs from the last checkpoint in the cells 64 records wrote | one ~140 ms op 2 every 64 appends at ~3,980 records (23.5% of a 20-`say` profile), growing with the cell count | a checkpoint body made of the held per-cell digests, or sealed off the member's path after the answer | this commit: the seal is deferred past the reply (`DurableServed.afterReply`, run by `serveSession` after each frame; at most one pending, and a caller with no serving loop runs it at its next `receiveServed`). The writing member's op 2 no longer pays it (w13, the write at 4,416: op 2 37 ms, where 348 to 450 ms before). Not on a task: a dedicated task marks the whole served state and World multi-threaded, measured as a 1,003 ms op 2 at the first seal. Round 2: the seal encodes the body once, not twice (`DurableCheckpointCodec.sealedBytesAt`, `sealedBytesAt_eq` by `rfl`: the MAC hashed one encode and the frame carried another); the request after a seal waited 354 to 540 ms, now 207 ms (w13, load ~7). Remaining: that 207 ms, growing with the state. About half of one encode is the fold's World system store (`StoreCodec.entries`, `addressKey`, the journal grows by a row per record, so it grows with HEIGHT), the rest the cells. The retained fix: each cell's `(digest, bytes)` entry and each system-store entry encoded at install and held in encode order, so a seal is a concatenation and a MAC. That needs the system store's entry order (`FiniteDependentMapCachedOrdering`) held as a sorted map of encoded entries beside the World. Open |
| 39 | the flatness bench's growth (`doc append` to one document, builder `flatness-submit`) | each append decodes the written cells in full for the World track (`DurableReceiverIO.advanceWorldIntent` -> `TurnOfIntent.ofCells`/`deltaOf`, `DeployedBridge.decodeCell`) and re-encodes them, and the document cell grows by every paragraph | the write changed one paragraph | ~13% + ~10% of the Store Host's samples at op 60 to 100 of a fresh world; submit wall 37 -> 70 ms over 100 appends in the paired runs (base and this lane alike) | the World track's delta from the record's written cells and their roots, not from decoding the cells, or a document as a trie of paragraphs (host-execution's layer) | open (host-execution) |
| 40 | occasional ~0.5 to 3 s Host reads and consent frames on w13 | traced (perf on the Store Host and a provider, aligned to the census rows, hbox:/home/hbox/pool/pcp/pp3, pp4): (a) ~450 to 520 ms on the first op after the write that crosses a multiple of 64: the deferred seal (`runAfterReply` -> `sealedBytesAt`, row 38); (b) 1.3 to 2.7 s on any op, with a ~1.4 s consent frame in the same command: the scratch world's certifier appends certify records, and each goes through the FULL shape on the serving Host: `Host.sessionFull` -> `NativeHostSession.materialize` catches the held full image up over every record since the last full op (`extendStored` -> `Loaded.replay`; ~77% of it was `PresenceIndex.put` on association lists, the rest `WorldTrack.advance` and `AuthTrie.Trie.build`), then `certifySubmitLoaded` (`loadDeploymentAt`, `CellState.materialize`) ~0.7 to 1 s; every member's provider then admits the certify record (~1.4 s) | the certify and the catch-up block the single-threaded session, so a member op queued behind them waits | 6 to 7 commands in 150 at load ~10 | (a) perf-host's retained seal (ph-A: 18 ms); (b) row 41 removes the association lists; what remains is the full-shape certify path: port certify to the light opening (KN2 ratchet, host-execution) | (a) on perf-host's branch; (b) traced, open (KN2) |
| 41 | the presence index (`PresenceIndex.Index`, held in every `Loaded`: a provider's admission, the Host's full image, every full open's `ofRecords`) | `lastSeen` and `touched` were association lists: `put` scanned every cell (and cell x subject pair) ever written, non-tail-recursive, per written cell of every record | the index is a map | ~20% of a provider's per-record admission at ~4,500 records (~5 ms), quadratic in an open, 77% of the Host's certify catch-up (row 40) | two `SparseMap`s (one tree step per written cell); `get_putAll`, `lastSeen_exact`, `touched_exact`, `index_monotone` keep their statements; `whoSeen` reads `touched.keys` | on main (Host image change, next re-genesis; nothing stored) |
| 42 | the provider's directory per admitted record (`validateLoadedStep` -> `loadDirectoryFrom`) | listed every cell's bytes (`Loaded.cells`), compared each and rebuilt the whole `DirectoryImage` per record | row 36's served directory is held as data; the loaded one was not | ~25% of a provider's admission | `LoadedDirectory` holds `HeldImages` (moved from `CredentialAuthorityServed`); `loadDirectoryStep` decodes only the written cells (`loadDirectoryStep_eq`); `loadDirectory_directory` ties the held directory to `DirectoryImage.decode` of every row (the old definition); `loadDirectoryFrom_eq`, `load_eq`, `unique` unchanged in shape | on main |
| 43 | a provider's refresh (`refreshExtended`, `extendSuffixAppended`, `Anchor.ofOpened`) | `image.accepted.length` and `accepted.drop count` reversed the whole journal per refresh and per anchor | the height is `rootLog.size`; the new records sit at the head of `acceptedRev` | ~8% of an admission | `Loaded.height` (O(1)) and `Loaded.suffixFrom` (`suffixFrom_eq`); provider routes parsed once per process, not per frame | on main |
| 44 | the consent resident's anchor (`mini_sdk::consent` `catch_up`, `serve_connection`) | after every admitted record AND every member frame: a second 229 round trip and an anchor file replace, made under the lock every member frame waits on | the anchor is a resume point: a crash leaves an older one and the next provider admits a longer suffix | 1 to 2 frames and a file replace per record on the command path | the catch-up keeps the 229 it already asked for and writes the anchor at most once a second (`ANCHOR_RETAIN_EVERY`), with the provider released; a member frame asks for no anchor | on main |

Web pages on this world (staging binaries, member-1, warm, four GETs): `/`, `/doc`, `/story`, `/room`,
`/apps` 2 to 7 ms; `/receipts` 11 to 13 ms; `/keys` 60 to 75 ms (two key-status Host calls);
anonymous `GET /` 5 to 8 ms. `POST /doc/new` 4.3 to 5.5 s is `doc new` itself (4.2 to 4.6 s through
the shell at the same load): Host 2.2 s and consent 1.1 s of CPU, two records. Nothing in the web
path adds to it.

## Measured, before and after (hbox:/ci/pc/w, load 12 to 33)

| change | before | after |
|---|---|---|
| rows 41 to 44 (w13, height ~5,880, load ~7; perf-host's ph-A Host both sides; 30 `say` + 30 `topic`, cpA against cpB) | first consent frame p50 29.7 ms (p90 39.8); consent per command 35.5 ms; provider CPU ~53 ms per command; `say` wall p50 80.8 | 0.5 ms (p90 14.2); 3.5 ms; ~15 ms; 60.6 (op2 30 ms that run, after the Store restart); cold provider start 23 s at height 5,877 |
| dafd69ac1 guard hoist (fresh worlds, batch 4 b9450147f against batch 6 74e1cfa10, load ~18) | member-2's consent catching up member-1's two `doc new` (4 records): 1155 ms CPU | 555 ms; batch 6's `doc new` itself: Host 739 to 542 ms, the author's consent 576 to 388 ms, wall 3.8 to 1.0 s (all of batch 6, not this change alone) |
| 60b0dbf20 digest kept by file identity | `tail -n 5` client CPU 176 ms (wall 337) | 26 ms (wall 294) |
| 86428a2f1 no idle exit | member idle 11 min, then `credit`: provider restart from its anchor, 3.2 s (consent 2.4 s CPU) | resident kept; the same `credit` pays only the catch-up of the ~40 records written meanwhile |
| ae39dfeb4 one resident directory (single tenancy), 1 member | 1 provider, 1 codec, 233 MB PSS (code pages counted once) | same |
| shared provider, 117 further records (says) | 67.2 MB anon | 66.1 MB anon: no per-record growth |
| ae39dfeb4, 5 members (4 hosted + sponsor) | 5 providers, 5 codecs, 582 MB PSS; each member's first command after a restart 2.4 to 4.4 s | 2 providers, 2 codecs, 311 MB PSS; members 2 to 4 first command 77 to 109 ms (the provider was already warm) |

Memory method: `smaps_rollup` Pss and Private over the resident processes (`consent-resident`,
`codec-resident`, the provider, the codec Host) of this world (`/ci/pc/mem.sh`).

## Row 19, before and after (hbox, base ae74dca4ec2d on /ci/pc/w9 against its overlay cand-pc1 on /ci/pc/w10)

| member-1's `credit`, ms wall (consent CPU) | base | catch-up (237 build; 236 build: 11 and 12 ms after 10 and 30) |
|---|---|---|
| warm, nothing written since | 8 (2) | 7 (3) |
| right after member-2 wrote 10 records | 93 (76) | 9 (1) |
| right after member-2 wrote 30 records | 228 (219) | 8 (1) |
| 1 s after member-2 wrote 30 more | 256 (246) | 9 (1) |

The admission CPU is unchanged; it is spent as records land instead of inside the next command.
Idle, the catch-up threads cost ~2 ms of CPU per second across a world's six residents (a stat
every 100 ms each). A cold provider on the demo Store copy finishes its first admission in 10.6 s and then answers a
catch-up with nothing new in 0 ms: the cold start now happens when the resident starts, not when a member asks.

At height ~1,560 on the overlay world (1,500 `say` records written by members 2 to 4, catch-up
live): `credit` 12 to 13 ms (Store Host 5 ms CPU, consent 2), `say` 79 to 100 ms (Store Host
60 ms CPU against 21 ms at height ~60; consent 147 ms CPU summed over every member's resident,
each admitting the same record: row 21). Against 10 ms, what remains on a warm read is the Store
Host's per-op work growing with height (2 to 5 ms for `credit`'s three ops), the client's process
start and workspace load (~4 ms) and the wrapper; on a write, the Store Host's op 2 (hot-path's).

## A `doc new`, call by call (MINI_TRACE, batch-6 world hbox:/ci/pc/w6, load ~24)

Two writes (the birth, then the document): 12 Host calls, 26 codec frames, 10 consent frames.

| height | Host | op1 plan (birth, doc) ms | op2 submit (birth, doc) ms | own birth catch-up (consent) | codec frames | another member's catch-up of both |
|---|---|---|---|---|---|---|
| 250 | 1.07 s | 264, 39 | 414, 299 | 347 ms | 19 ms | 417 ms |
| 520 | 1.34 s | 344, 43 | 609, 283 | 372 ms | 19 ms | 434 ms |

Batch 7 (acc7cfa03, fresh world hbox:/ci/pc/w7, load ~18):

| height | Host | op1 plan (birth, doc) ms | op2 submit (birth, doc) ms | own birth catch-up | another member's catch-up of both |
|---|---|---|---|---|---|
| 0 | 487 ms | 85, 14 | 298, 58 | 147 ms | 166 ms |
| 250 | 384 ms | 100, 14 | 180, 64 | 132 ms | 171 ms |
| 520 | 663 ms | 161, 16 | 314, 139 | 142 ms | 239 ms |

Against batch 6 at the same heights: Host 1.07 to 0.38 s at 250 and 1.34 to 0.66 s at 520; a member's own
birth catch-up 347 to 132 ms; another member's catch-up of the two records 417 to 171 ms; a `say` record in
catch-up 36 to 17.6 ms (60 in 1,058 ms). What still grows from 250 to 520: the birth's op1 (100 to 161) and op2
(180 to 314), the document's op2 (64 to 139), and another member's catch-up (171 to 239 ms).

The codec frames cost 19 ms in all, so batching them is not worth a protocol change. Consent per record is
flat with height. The birth's Host op1/op2 grows (+30%/+47% over 270 heights): sent to hot-path. On batch 4 at
height ~500 the same own-birth catch-up was 1,289 ms and op2 1.7 s per write. The member's provider still
re-derives and re-executes its own just-admitted birth (~350 ms); its plan consent ran the planner, not the
executor, so there is no execution to reuse byte for byte, and sharing would mean carrying the planner's
prepared kernel values into the deriver. Decided after batch 7 (its authority-leg fix lands in that walk).

Batch 8 (dc61016cb, fresh world hbox:/ci/pc/w8, against batch 7 acc7cfa03 on /ci/pc/w7, interleaved, load ~20):
`doc new` wall 476 against 614 ms (Host 254 against 346 ms, consent 160 against 219 ms CPU); `credit` 17 ms and
`doc show` 20 ms warm. A batch-8 provider's `doc new` profile: the walk 36% (re-deriving the birth 24%, its own World
advance 7.9%: row 16), the replay of the same records from the Store 10.7%, the authority snapshot (`authStateOfFast`
-> `rootCached`) 10%, the author's plan check 15%.

A warm read verb (`credit`, staging `mini`, batch-7 world): 10 ms wall direct, of which ~4 ms is the process start
and workspace load and the rest three Host round trips (the key commitment re-check, the challenge, the signed view)
plus one codec and one consent frame. The client's own syscalls total ~2.7 ms. Under the deployed wrapper the
same verb measured 23 to 27 ms (its extra processes; row 10).

## Where a verb's client time goes now (batch-6 world, `doc new`, `strace -c -w`)

Of ~0.9 s of client syscall time, 93% is waiting on the Host and consent sockets (poll 565 ms, recvfrom 280 ms).
Every filesystem call together is ~20 ms. The attempt's own files (staged temp, link, unlink; ~30 for the two
writes) are ~3 ms, and each mkdir takes 30 to 80 us. So an attempt is not merged into one file: the saving is
~3 ms, and merging would rewrite the custody format and its crash ordering, which a dozen readers depend on.

The shell path's floor is the ssh handshake: `help` takes 181 to 216 ms over a fresh connection, 15 to 16 ms over a
multiplexed one, and 122 ms with classical curve25519 key exchange instead of OpenSSH 9.7's post-quantum default.
FRIENDS.md shows the ControlMaster lines (bf1c9ccf3). The server's key exchange is ember's decision and infra's sshd.

Consent catch-up of `say` records (batch-6 provider, 60 records in 2.15 s, ~36 ms each): the World pin
re-encode is 27% (batch 7, row 9), the second Store read 11.7% (batch 8, row 12), the Store helper's reply 12.5%,
decoding records 9.4%, and the kernel walk ~20% (the DRC authority leg is 9%, hot-path's).

## Landed

Batch 1 (f883af161, staging merged in; staging d24b3e761, batch 6): rows 1, 2, 4, 8 (single tenancy).
Follow-up 59dd7ded4 (staging db074a736, batch 6): a resident also ends when the Store its settings name
(`storageRoot`) is removed (the explorer's world-down finding); `chargeWith`'s docstring names its caller's duty.
Batch 2 (5415aecf7, staging 227451d8c, batch 7): row 9.
Batch 3 (b34173dad, with f95edc7bf; staging 8ca47d577, batch 7): row 10.
Batch 4 (a36d8bdfa with 394039fb1): row 8 under split tenancy (opt-in: units from infra).
Batch 9 (997905c0b): rows 14, 15. Batch 10 (staging): rows 16, 17, 18. 7b20a1379 + 7d809f349 (main): row 19 (catch-up threads in `mini`'s residents
and the delegated worker, through frame 236; no Lean or protocol change, so it ships with `mini` alone).
37a2dc2c6 (main): rows 29 and 29b (Host image change: ships with the re-genesis). The census round 2
commit (main): row 31's window (Host image change). 7f80be316 (main): the grain controller's typed
close of a prompt witness its allowance outlived (`reconcile prompt-witness`, `prompt_witness_close`),
the demo lobby controller's 40-hour checkpoint hold.

Client syscalls per verb, for the record: a warm ssh `say` is 2,365 syscalls for the whole client tree
(wrapper included). The explorer's 12,031 on batch 5 counted the residents that `strace -f` followed for
~600 s. Client filesystem syscalls of one `doc new` (member-1, 474 attempts, 101 namespace reservations; `strace -f`
of the wrapper and `mini`, residents already warm):

| client | statx | openat | all traced fs calls | what scaled with history |
|---|---|---|---|---|
| batch 6 `mini` (b7) | 1,063 | 523 | 2,515 | `refuse_rerun` stat'ed every attempt's intent copy; `participant_namespace::used_ids` read every reservation record (50 opens), on every reservation and dry-run probe |
| aa24acaf8 attempt index | 569 | 531 | 2,035 | the reservation records |
| c4ef61d37 namespace ID index, settings by identity; c9f64c275 workspace by identity | 505 | 447 | ~2,550 (reads and closes included) | nothing |

What remains is constant per verb, not per record: ~300 `fstat` of descriptors the custody-checked reads
open (each retained file read is open, fstat, read, close), 58 identity `statx` of the Host image (one per
Host or codec frame), and the attempt's own files (each written through `mini_sdk::durable::staged`: temp,
write, link, unlink). `workspace.json` is opened 2 times instead of 11, the consent and codec settings once
per identity instead of twice per frame. Remaining small client items: the attempt's `config.json` re-read once per Host call (36 opens per
`say`), ~490 `statx` from the private-directory checks per load.
