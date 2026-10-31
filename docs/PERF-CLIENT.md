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
| 1 | every receiver's `readGuards` (`ResourceBirthReceiver`, `ResourceBirthController`, fleet turn, clock tick, certify, pay, capability, ... 20 files) | the filter lambda evaluates `writes prepared` once **per guard**: every post cell rebuilt and canonically encoded per guard, the authority cell's post patch included | the written ids are one list | a birth (`doc new`, two records) costs a member's consent provider 0.5 to 1.1 s of CPU; 56% of the provider's catch-up profile is the birth walk, 36% of it this filter; the Host runs the same receivers | ids bound once before the filter; the authority write encodes its post once; the birth intent's charge reads the writes and guards the intent already holds (`chargeWith`) | dafd69ac1, lane-check running |
| 2 | `main.rs` `host_image_sha256` | SHA-256 of the 182 MB Host image once per process unless a loaded workspace pinned it; chat reads, bend, activity, clock, job and checkpoint read `workspace.json` raw and never pin | a digest of an unchanged file | chat `tail -n 5`: 170 of 186 ms of client CPU | the digest is kept by file identity in the owner-private resident directory | 60b0dbf20: `tail` client CPU 176 to 26 ms |
| 3 | consent provider cold start (`Host/ClientConsentCore.verifyInitial`) | a provider started after its resident idled out opens the Store and resumes from its retained anchor, which replays every record from the Store's base (`loadChained`, `cutAbove`): the deployed config has `checkpointEvery: null`, so the base is genesis | a resumed provider needs the anchor's state, not the history below it | member-2 at height 160: 2.27 s (consent 2.1 s CPU) with an anchor one record old; 8.1 s (7.3 s) with no anchor; explorer: 19 to 61 s at height 620 | hot-path's snapshot start (option A); this lane keeps the per-record cost down (row 1) | hot-path |
| 4 | `mini_sdk::consent::RESIDENT_IDLE_S` = 600 | consent and codec residents end after ten idle minutes, and the next command pays row 3 | the member comes back; a web session lasts a day idle | 2 to 61 s on the first command after ten minutes away; 159 MB (consent) + 84 MB (codec) RSS per member while resident | open: tie a resident's lifetime to the member's session, or make row 3 cheap enough that idling out costs nothing | open |
| 5 | consent catch-up (`refresh` -> `ConsentAnchor.Basis.extendAppended` -> `NativeHostReplay.walkSuffix`) | every member's provider re-executes every record since it last looked | independent verification is the design (ember's question pending) | per record it is the executor's cost: row 1 for births, hot-path's `Patch.run` chain and DRC guards for the rest | rows 1 and hot-path's | after row 1: re-measure |
| 6 | `workspace::recheck_commitment` | one Host key-status round trip per `mini` process, before any verb | a verb process per ssh command makes "once per process" once per command | a missing-reference `doc show` still spends 30 ms of Host CPU at load 30 (op 144, 4 to 5 ms idle) | open (a security check; the Host op is the exorcist's) | open |
| 7 | `shell.rs` `history` (web `/receipts`, `history all`) | reads every retained attempt directory per page | a page shows the newest few | O(attempts): 11 to 13 ms at ~40 attempts here, 45 to 68 ms at ~700 (explorer) | an attempt index, newest first | open |
| 8 | split tenancy: `mini-shell-ssh` (dregg-infra) and `mini-web-spawn` `delegated_consent_env` | `sha256sum` of the 194 MB consent provider and the config per ssh command / per body start | the worker already holds both digests | 176 ms per ssh command where `consent/peer.sock` exists | not on this world (no peer.sock); infra's wrapper | open |

Web pages on this world (staging binaries, member-1, warm, four GETs): `/`, `/doc`, `/story`, `/room`,
`/apps` 2 to 7 ms; `/receipts` 11 to 13 ms; `/keys` 60 to 75 ms (two key-status Host calls);
anonymous `GET /` 5 to 8 ms. `POST /doc/new` 4.3 to 5.5 s is `doc new` itself (4.2 to 4.6 s through
the shell at the same load): Host 2.2 s and consent 1.1 s of CPU, two records. Nothing in the web
path adds to it.

## Landed

None yet.
