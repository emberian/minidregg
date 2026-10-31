# PERF-CLIENT

The member's side of the Host: the `mini` client (shell, workspace, chat), the consent provider
and its residents, and the web body. A present-state table, rewritten whole. Lane `lane/perf-client`
(worktree `/Users/ember/dev/minidregg-lanes/perf-client`, hbox pool tree `t8`, scratch world and
tools under `hbox:/ci/pc`). Neighbours: the exorcist owns the Host's read ops, the fsync removal and
the web shell-child pool; hot-path owns submit, propose, FORMAT, the consent snapshot start, the
`Patch.run`/`setAll` chain and `DeclaredResourceController`'s guards.

## How it is measured

`hbox:/ci/pc/w` is a scratch world (`jworld-scratch.sh up`, five members, candidate b9450147f =
batch 4 for the Host, the consent provider and the codec). `/ci/pc/pcm.py WORLD MEMBER MINI REPS
LINE...` runs a shell line the way the forced ssh command does (the world's `mini-shell-ssh`, a
chosen `mini`) and reports wall time and the CPU each role spent (client, private Host, Store
helper, consent provider, codec, relay), summed over every thread (`/proc/PID/task/*/schedstat`;
the first version read only the main thread and showed the Lean Host at 0). `/ci/pc/pcweb.sh`
times the web gateway, helper and body. hbox ran at load 12 to 33 throughout: wall numbers are
inflated, CPU numbers much less.

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
| 9b | `Compiler/WorldCompact.compactEvery` | rebuilds every cell's store and the cell map every 32 heights | only cells written since the last compaction changed | O(World) per 32 records (2% of hot-path's story profile, growing) | not sliced: "written since the last compaction" spans 32 turns that `WorldTrack.advance` does not carry (a constructor change through every proof), and re-treeing each turn's cells per height costs a hot cell O(cell) per record. The real fix is a `Store` whose update is a tree insert behind `@[csimp]` (no compaction, no post-store chains) | hot-path, after its row 11 |
| 10 | the member ssh wrapper (`deploy/shell/mini-shell-ssh`, and dregg-infra's deployed copy) | `#!/usr/bin/env bash` probes PATH (8 to 11 failed execve per command), `readlink`/`dirname`/`dirname`/`basename` for MINI_CANDIDATE_SHA, and under split tenancy `sha256sum` of the 194 MB consent provider and the config per command (`mini-web-spawn` per body start) | the digests change once per ship; the client knows its own path | 12 of 15 execve of an ssh `say`; ~176 ms CPU per command where `consent/peer.sock` exists | the candidate's wrapper carries every deployed feature in two processes (bash, mini), files read with builtin `read`; the pins come from a ship-rendered `HOME/consent/peer.pins` (hashing only without it); the client derives its candidate id (f95edc7bf) | b34173dad; infra installs it from batch 7 and renders `peer.pins` in ship.sh |
| 12 | consent provider per member connection (`serve`: frame 233 `recheckHeld`, then `refresh` -> `extendFrom`) | two Store reads per command: the tag at `height`, then the entries from `height + 1` | the resident sends 233 and the command back to back under one lock: one read from `height` serves both | one Store helper round trip per command | 233 answers at once and the re-check is owed: the next frame makes it on its own admitting read (`refreshHeld`: `ConsentAnchor.checkHeld` on the first entry, `DurableReceiverIO.extendStored` on the rest) or, if it admits nothing, as a read of its own (`recheckOrEnd`); `checkHeld` is now the one judgement `recheckHeld` applies | 5517f6f57 + d7e252590, lane-check running |
| 13 | a birth's authority leg (`ResourceBirthPolicyController.rawLeg .authority` -> `ResourceBirthAuthority.request` -> Theory's generic `authState`) | rebuilds the authority projection per leg built: revoked and parent sets each a `Finset.biUnion` over `DFinsupp.support` (quadratic dedups over the whole authority store) | the snapshot holds that projection (`authStateExact`), built once through hot-path's fast `@[csimp]` | 12.8% of a batch-6 consent catch-up of births; the Host builds the same legs | the leg asks `factoryRequest` at `oldAuthority prepared`, as the other legs do; `requestExact` proved from `authStateExact` | ff9ebd756, lane-check running |
| 11 | world bring-up (`jworld-scratch.sh up`, dregg-infra) | 219 s for a five-member scratch world | | every measurement world and journey pays it | for whoever owns world bring-up | noted |

Web pages on this world (staging binaries, member-1, warm, four GETs): `/`, `/doc`, `/story`, `/room`,
`/apps` 2 to 7 ms; `/receipts` 11 to 13 ms; `/keys` 60 to 75 ms (two key-status Host calls);
anonymous `GET /` 5 to 8 ms. `POST /doc/new` 4.3 to 5.5 s is `doc new` itself (4.2 to 4.6 s through
the shell at the same load): Host 2.2 s and consent 1.1 s of CPU, two records. Nothing in the web
path adds to it.

## Measured, before and after (hbox:/ci/pc/w, load 12 to 33)

| change | before | after |
|---|---|---|
| dafd69ac1 guard hoist (fresh worlds, batch 4 b9450147f against batch 6 74e1cfa10, load ~18) | member-2's consent catching up member-1's two `doc new` (4 records): 1155 ms CPU | 555 ms; batch 6's `doc new` itself: Host 739 to 542 ms, the author's consent 576 to 388 ms, wall 3.8 to 1.0 s (all of batch 6, not this change alone) |
| 60b0dbf20 digest kept by file identity | `tail -n 5` client CPU 176 ms (wall 337) | 26 ms (wall 294) |
| 86428a2f1 no idle exit | member idle 11 min, then `credit`: provider restart from its anchor, 3.2 s (consent 2.4 s CPU) | resident kept; the same `credit` pays only the catch-up of the ~40 records written meanwhile |
| ae39dfeb4 one resident directory (single tenancy), 1 member | 1 provider, 1 codec, 233 MB PSS (code pages counted once) | same |
| shared provider, 117 further records (says) | 67.2 MB anon | 66.1 MB anon: no per-record growth |
| ae39dfeb4, 5 members (4 hosted + sponsor) | 5 providers, 5 codecs, 582 MB PSS; each member's first command after a restart 2.4 to 4.4 s | 2 providers, 2 codecs, 311 MB PSS; members 2 to 4 first command 77 to 109 ms (the provider was already warm) |

Memory method: `smaps_rollup` Pss and Private over the resident processes (`consent-resident`,
`codec-resident`, the provider, the codec Host) of this world (`/ci/pc/mem.sh`).

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
