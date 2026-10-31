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
| 1 | every receiver's `readGuards` (`ResourceBirthReceiver`, `ResourceBirthController`, fleet turn, clock tick, certify, pay, capability, ... 21 files) | the filter lambda evaluates `writes prepared` once **per guard**: every post cell rebuilt and canonically encoded per guard, the authority cell's post patch included | the written ids are one list | a birth (`doc new`, two records) costs a member's consent provider 0.5 to 1.1 s of CPU; 56% of the provider's catch-up profile is the birth walk, 36% of it this filter; the Host runs the same receivers | ids bound once before the filter; the authority write encodes its post once; the birth intent's charge reads the writes and guards the intent already holds (`chargeWith`) | dafd69ac1: lane-check green on all 21 files; awaits a Host/consent build for the number |
| 2 | `main.rs` `host_image_sha256` | SHA-256 of the 182 MB Host image once per process unless a loaded workspace pinned it; chat reads, bend, activity, clock, job and checkpoint read `workspace.json` raw and never pin | a digest of an unchanged file | chat `tail -n 5`: 170 of 186 ms of client CPU | the digest is kept by file identity in the owner-private resident directory | 60b0dbf20: `tail` client CPU 176 to 26 ms |
| 3 | consent provider cold start (`Host/ClientConsentCore.verifyInitial`) | a new provider opens the Store (`loadChained`: `openState`, `foldRecords`, `World.admit`) and walks every record above the Store base or its retained anchor | a resumed provider needs the anchor's state, not the history below it | member-3, no anchor, height ~165: 6.1 s (walk 39%, the Store open 23%); with a one-record-old anchor 2.3 s. (`checkpointEvery: null` in the deployed config is read as 64 everywhere: not a cause.) | the walk: rows 1 and 9; the open: hot-path (its row 11, the FORMAT batch) | split |
| 4 | `mini_sdk::consent` resident idle exit (600 s) | consent and codec residents ended after ten idle minutes and the next command paid row 3 | the member comes back; a web session lasts a day idle | 2 to 61 s on the first command after ten minutes away | no idle exit: a resident ends with its world, its child, or a superseded binding (another file at its executable path, other bytes at its settings path), and outlives the attempt whose settings copy started it; `serve-controller-consent` the same, and it polls its listener instead of sleeping 20 ms per accept | 86428a2f1, 1e37efc44: 11 min idle then `credit`: the resident stayed (catch-up of the records written meanwhile only) |
| 5 | consent catch-up (`refresh` -> `ConsentAnchor.Basis.extendAppended` -> `NativeHostReplay.walkSuffix`, plus `DurableReceiverIO.extendFrom`) | every member's provider re-executes every record since it last looked | independent verification is the design (ember's question pending) | ~150 ms per record at load 25 (11 records, 1.73 s): walk 46% (DRC authority legs 21%, capability evidence 18%, issuerCheck 14.5%: hot-path), `extendFrom` -> `WorldTrack.advance` -> `World.admit` -> `pinFails` -> `DeployedBridge.cellRoot` 16% (row 9) | rows 1 and 9, hot-path's DRC and issuer work | open |
| 6 | `workspace::recheck_commitment` | one Host key-status round trip per `mini` process, before any verb | a verb process per ssh command makes "once per process" once per command | a missing-reference `doc show` still spends 30 ms of Host CPU at load 30 (op 144, 4 to 5 ms idle) | open (a security check; the Host op is the exorcist's) | open |
| 7 | `shell.rs` `history` (web `/receipts`, `history all`) | reads every retained attempt directory per page | a page shows the newest few | O(attempts): 11 to 13 ms at ~40 attempts here, 45 to 68 ms at ~700 (explorer) | an attempt index, newest first | open |
| 8 | resident footprint | each member's consent provider and codec Host do byte-identical work (one Store, one pinned config, one image) | one verifier and one codec per box serve them all | single tenancy, per member ~87 MB PSS (provider 56 to 90 MB private, flat over 117 records; codec 12 MB private); split tenancy, per member a 2.5 MB worker + a 91 MB provider child running a pinned memfd COPY of the 194 MB image (its code pages not shared) + the member's codec | single tenancy: one resident directory (`/etc/mini/session-residents`, dev `residents`); split tenancy (ember's ruling 2026-10-31): `serve-controller-consent --resident-dir` relays each member connection to ONE operator consent resident (fresh connection per member connection: the Store re-check per command kept), and `mini serve-codec` is one codec for every member account (`/etc/mini/session-codec`; clients check the greeting's image and config digests) | ae39dfeb4 single: 5 members 582 to 311 MB PSS. a36d8bdfa + 394039fb1 split: worker 2.0 MB PSS and no provider per member; infra renders the units with batch 7, then a forge measurement |
| 9 | `Kernel.World` `World.admit` -> `pinCheck` -> `pinFails` -> `DeployedBridge.cellRoot` (in `WorldTrack.advance`) | re-encodes the World's own copy of every pinned cell (a fresh value after each write, its byte cache cold) to compare its root, per record | the executed snapshot already holds those cells' canonical bytes | 16% of a warm catch-up; the Host's append runs the same advance | pins judged from the snapshot's bytes (`snapPinFails`, proved equal at a represented World); `World.admitPinned` with `admit_eq_admitPinned` (rfl) | 5415aecf7: lane-check green; awaits a Host/consent build for the number |
| 9b | `Compiler/WorldCompact.compactEvery` | rebuilds every cell's store and the cell map every 32 heights | only cells written since the last compaction changed | O(World) per 32 records (2% of hot-path's story profile, growing) | a World map without closure chains (each update O(log n)), or compaction of the cells written since the last one | open |
| 10 | the member ssh wrapper (`deploy/shell/mini-shell-ssh`, and dregg-infra's deployed copy) | `#!/usr/bin/env bash` probes PATH (8 to 11 failed execve per command), `readlink`/`dirname`/`dirname`/`basename` for MINI_CANDIDATE_SHA, and under split tenancy `sha256sum` of the 194 MB consent provider and the config per command (`mini-web-spawn` per body start) | the digests change once per ship; the client knows its own path | 12 of 15 execve of an ssh `say`; ~176 ms CPU per command where `consent/peer.sock` exists | the candidate's wrapper carries every deployed feature in two processes (bash, mini), files read with builtin `read`; the pins come from a ship-rendered `HOME/consent/peer.pins` (hashing only without it); the client derives its candidate id (f95edc7bf) | b34173dad; infra installs it from batch 7 and renders `peer.pins` in ship.sh |
| 11 | world bring-up (`jworld-scratch.sh up`, dregg-infra) | 219 s for a five-member scratch world | | every measurement world and journey pays it | for whoever owns world bring-up | noted |

Web pages on this world (staging binaries, member-1, warm, four GETs): `/`, `/doc`, `/story`, `/room`,
`/apps` 2 to 7 ms; `/receipts` 11 to 13 ms; `/keys` 60 to 75 ms (two key-status Host calls);
anonymous `GET /` 5 to 8 ms. `POST /doc/new` 4.3 to 5.5 s is `doc new` itself (4.2 to 4.6 s through
the shell at the same load): Host 2.2 s and consent 1.1 s of CPU, two records. Nothing in the web
path adds to it.

## Measured, before and after (hbox:/ci/pc/w, load 12 to 33)

| change | before | after |
|---|---|---|
| 60b0dbf20 digest kept by file identity | `tail -n 5` client CPU 176 ms (wall 337) | 26 ms (wall 294) |
| 86428a2f1 no idle exit | member idle 11 min, then `credit`: provider restart from its anchor, 3.2 s (consent 2.4 s CPU) | resident kept; the same `credit` pays only the catch-up of the ~40 records written meanwhile |
| ae39dfeb4 one resident directory (single tenancy), 1 member | 1 provider, 1 codec, 233 MB PSS (code pages counted once) | same |
| shared provider, 117 further records (says) | 67.2 MB anon | 66.1 MB anon: no per-record growth |
| ae39dfeb4, 5 members (4 hosted + sponsor) | 5 providers, 5 codecs, 582 MB PSS; each member's first command after a restart 2.4 to 4.4 s | 2 providers, 2 codecs, 311 MB PSS; members 2 to 4 first command 77 to 109 ms (the provider was already warm) |

Memory method: `smaps_rollup` Pss and Private over the resident processes (`consent-resident`,
`codec-resident`, the provider, the codec Host) of this world (`/ci/pc/mem.sh`).

## Landed

Batch 1 (f883af161, staging merged in; staging d24b3e761, batch 6): rows 1, 2, 4, 8 (single tenancy).
Follow-up 59dd7ded4 (staging db074a736, batch 6): a resident also ends when the Store its settings name
(`storageRoot`) is removed (the explorer's world-down finding); `chargeWith`'s docstring names its caller's duty.
Batch 2 (5415aecf7, staging 227451d8c, batch 7): row 9.
Batch 3 (b34173dad, with f95edc7bf; staging 8ca47d577, batch 7): row 10.
Batch 4 (a36d8bdfa with 394039fb1): row 8 under split tenancy (opt-in: units from infra).

Client syscalls per verb, for the record: a warm ssh `say` is 2,365 syscalls for the whole client tree
(wrapper included). The explorer's 12,031 on batch 5 counted the residents that `strace -f` followed for
~600 s. Remaining small client items: the attempt's `config.json` re-read once per Host call (36 opens per
`say`), ~490 `statx` from the private-directory checks per load.
