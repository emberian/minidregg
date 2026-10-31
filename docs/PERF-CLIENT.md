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
| 8 | resident footprint | each member's resident consent provider and codec Host do byte-identical work (one binding for every hosted member of a box) | one verifier per box serves them all | per member ~87 MB PSS (provider 56 to 90 MB private, growing with history; codec 12 MB); code pages (~150 MB) are shared once per box | single tenancy: one resident directory per box (`/etc/mini/session-residents`, dev config `residents`); split tenancy (the demo) HELD for ember's ruling on who verifies for a member | ae39dfeb4: 5 members 582 to 311 MB PSS, 5 to 2 providers (the sponsor's config is another binding) |
| 9 | `Kernel.World` `World.admit` -> `pinCheck` -> `pinFails` -> `DeployedBridge.cellRoot`; `WorldCompact.compactEvery` | re-encodes a cell to compare its root on every record; compacts every cell of the World every 32 heights | the executed snapshot already holds each cell's root | 16% of a warm catch-up; compaction O(World) ~2% of hot-path's story profile and growing | next | next |
| 10 | split tenancy: `mini-shell-ssh` (dregg-infra) and `mini-web-spawn` `delegated_consent_env` | `sha256sum` of the 194 MB consent provider and the config per ssh command / per body start | the worker already holds both digests | 176 ms per ssh command where `consent/peer.sock` exists | infra's wrapper | open |
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
| ae39dfeb4, 5 members (4 hosted + sponsor) | 5 providers, 5 codecs, 582 MB PSS; each member's first command after a restart 2.4 to 4.4 s | 2 providers, 2 codecs, 311 MB PSS; members 2 to 4 first command 77 to 109 ms (the provider was already warm) |

Memory method: `smaps_rollup` Pss and Private over the resident processes (`consent-resident`,
`codec-resident`, the provider, the codec Host) of this world (`/ci/pc/mem.sh`).

## Landed

Batch 1 (lane/perf-client 4a962d506, staging merged in): rows 1, 2, 4, 8 (single tenancy).
