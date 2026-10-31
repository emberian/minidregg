# App and grain paths: where the time goes (present state)

Present-state table, rewritten whole. Lane `lane/perf-apps`. Measured on hbox (load 11 to 14, about 100
other sessions, so every wall number is inflated; the CPU and the call counts are not) on standing worlds
from `scripts/spk-platform/world-up.sh`, driven by `apps-e2e.sh` (the real `mini apps install`) and
`featured-qualify.sh` (create, install, share, start, enrol, page), with a bpftrace exec/fork/exit trace of
every process the world started (`hbox:/home/hbox/lanes/perf-apps/proc.bt`, tree by `tree.py`).
Ember's bar: nothing on an NVMe machine should take substantially over 1 ms.

## The install, end to end (EtherCalc, 37 MB SPK, batch 5 `1c151fce4`)

| step | where | wall | what it is |
|---|---|---|---|
| member turn: tool reserve, app birth, six delegation proposals, request cell | client `mini apps install` | about 10 s | about 10 Host writes at about 1 s each (hot-path's) |
| stage and qualify the package | `spk-host grain install` | 7.9 s | copy, a full SPK verify, launch-descriptor authoring |
| INSTALL BEGIN plan (op66) | Host | **8.6 s** | one Host call; history walk below the checkpoint (hot-path, row 4 slice 2) |
| claim (op68/69/26) | Host | 0.8 s | |
| publish the image and re-check it | broker ingest + `spk-host` | 9.6 s | materialize (a verify plus extraction), then the installed image verified again, twice |
| INSTALL completion (op70/71/38) | Host | 2.3 s | |
| the owner's route: session birth, three signed reads, share issue | apps worker | 17.5 s | 13 `mini` processes plus 2 one-shot Host helper processes |
| `spk-host grain route` | spk-host | 3.7 s | about 3 s of it a full SPK re-verify |
| each START, before the first Host call | resident | 4.5 to 5.5 s | about 3 s CPU re-verifying the whole SPK in the new process |

## Findings, ranked by what a person waits for

| # | finding | measured cost | state |
|---|---|---|---|
| 1 | Every wake of an installed image (`verify_installed_spk`) re-verifies the whole SPK: copy to a temp file, xz-decode it to a second temp file, SHA-512, ed25519, parse the archive. It runs at install (about 3 times), at the route bind, at every START and STOP. | 2.7 to 4.3 s per call for EtherCalc (37 MB; 2.4 s CPU); more for Etherpad (64 MB) and Davros | batch 1: 0.02 s |
| 2 | The apps worker binds the owner's route through 13 `mini` subprocesses and 2 one-shot `minidregg-host` helper processes (`grain-share-issue-*` ran `HOST CONFIG author` and `inspect outcome` as processes). | 17.5 s wall; 0.3 s per helper process | helper processes fixed on the lane; in-process worker steps are next |
| 3 | op66, the lifecycle BEGIN plan, takes 8.6 s on a fresh world (a history walk from genesis when a share/grant/reserve record sits below the checkpoint) | 8.6 s per INSTALL and per START | hot-path's (row 4 slice 2) |
| 4 | Agent typed-tool custody (`agent_reserve`, `agent_payer`, `agent_lifetime_grant`) runs every author/inspect/signatures as a `minidregg-host` process | 5 to 8 processes per operation, 60 to 300 ms each | fixed on the lane |
| 5 | `grain start` polled the resident's completion every 500 ms and spawned `systemctl --user show` per poll | up to 0.5 s added latency; 10 to 750 ms per poll | batch 1: inotify wake, the unit read at most every 500 ms |
| 6 | Each grain HTTP request is a durable Mini turn (PLAN, ASSEMBLE, SUBMIT, and inspections); the resident dispatches one request at a time | not yet measured on a running grain (START was red until 40efdcff9) | next measurement |
| 7 | `apps_worker` read the whole quarantined SPK into memory and hashed it on every install attempt and retry | about 0.1 s per 37 MB, the SPK's size in memory | batch 1: streamed, kept per file identity |

Already done before this lane, on batch 5: no fsync anywhere (exorcist); the hosting delegation's
rounds run in-process, not as `mini workspace --action app-lifecycle` subprocesses (exorcist); spk-host's
`author`/`inspect`/`signatures` go to the Host session instead of a process per call (about 1 ms each,
`tool-timing ... session=1` in the resident journal).

## Batch 1: before and after (EtherCalc, batch 5 plus 40efdcff9, same box, back to back)

| measure | before | after |
|---|---|---|
| one wake's image verification (`spk-host inspect-installed`, three runs) | 2.81 to 3.43 s (2.2 to 2.5 s CPU) | 0.02 to 0.03 s |
| `spk-host grain install` (worker phase 2) | 39.5 s | 17.7 s |
| `spk-host grain route` | 2.2 s | under 0.5 s |
| `spk-host grain start` (to the resident's refusal, see the reds) | 8.9 s | 7.1 s |
| worker install phase (request received to installed) | 40 s | 18 s |

START still ends red on member-namespace ids (route socket path over SUN_LEN; enrollment lookup
"agent reserve custody lacks confirmation"): app-reds has both, so the first page and the per-request
path are measured after its fix.

## What batch 1 changes

- **The image's verified identity is retained at publication.** `materialize` writes
  `verified-identity.json` (0444, the manifest's custody) with the publishing parse's result: raw length
  and SHA-256, the signed manifest digest, the signed bridge and data config bytes. A wake re-hashes
  `package.spk` with SHA-256 (about 25 ms for 37 MB) and must match that record and the image's own name;
  signature verification is a function of those bytes, so the record is that verification's result for
  them. An image published before the record existed is re-verified as before. Test:
  `retained_verified_identity_equals_reverification_and_binds_the_bytes` (the record's identity equals a
  fresh re-verification field for field; a one-byte rewrite of `package.spk` at the same length is
  refused; a 0644 record is refused).
- **`grain start` wakes on its journal and route directories** (inotify), reading the unit's state at
  most every 500 ms instead of sleeping 500 ms between checks.
- **The worker's package digest** is streamed from the opened descriptor and kept per file identity.
- **Source custody pure verbs go through the codec session.** `share_issue::source_process` and
  `agent_reserve::source` answer `author`, `inspect` and `signatures` through
  `client_consent::pure_source` (this process's codec session, the frame every other client verb
  already uses), never through the operator socket, as before.
</content>
</invoke>

## Batch 2 (in progress on `lane/perf-apps`)

- **The apps worker's client commands run in two resident `mini client-resident` processes**
  (`native/resource-client/src/client_resident.rs`), not a `mini` process per command: the channel is a
  socketpair handed over as stdin (moved off fd 0, which becomes /dev/null), each request a JSON argv,
  each reply the exit code plus stdout and stderr from `capture::argv` on the resident's one thread. One
  resident is pinned to the public socket (`query`, `submit`, `current-session-intent`), one serves the
  commands that name the operator socket themselves (share issue, session enrollment). A lost reply is
  an error, never re-sent; the next command starts a fresh resident.
- **`transport::host_image_sha256` keeps one digest per file identity** (device, inode, length,
  mtime, ctime; checked on the path and the opened descriptor, before and after hashing). The 180 MB
  Host image was hashed about 0.1 s per pin check, several times per custody operation (agent_payer
  four times per paid dispatch).

## Continuation (for whoever picks this lane up)

State: batch 1 (`23738a4ce`) is merged on staging as `cfe5c24d5` and rides batch 6. Batch 2 above is
committed on `lane/perf-apps`, checked on the Mac (cargo check, filtered tests), not yet measured.

Next steps, in order:
1. Measure batch 2 on hbox: build `mini` (and spk-host) from `lane/perf-apps` into
   `/home/hbox/lanes/perf-apps/target`, copy into `ownB`, run `up.sh B ownB` (worlds live in `/ci/pa-*`,
   never `/tank` or `/home`), then `run.sh eB B e2e <app id>` against a baseline `run.sh eA A e2e`. Compare
   with `cmp.sh eB B` (install phase, start phase, resident boots, spk-host durations from the bpftrace
   process tree) and the worker's `route-*` stdout files. The before number is the route bind at
   17.5 s in 13 `mini` processes.
2. When app-reds lands the START fixes (route socket path over SUN_LEN for 20-digit app ids; enrollment
   lookup "agent reserve custody lacks confirmation"), measure the first page and per-request latency:
   time repeated authenticated GETs over the route socket (`curl --unix-socket .../http.sock -w
   %{time_total}`), and split a request in the resident journal (`tool-timing` lines plus the attempt
   directory's file times: PLAN, ASSEMBLE, SUBMIT, inspect committed).
3. Open items from the table: the per-request Host round trips (four Host calls per GET, served one at a
   time by the resident and by the operator socket's single Host thread, hot-path's for the Host side);
   the client's member turn at install (about 10 Host writes, hot-path's).

Tools on hbox (`/home/hbox/lanes/perf-apps`): `up.sh WORLD OWN_BIN`, `run.sh NAME WORLD fq|e2e ARGS`,
`trace-start.sh NAME` (bpftrace exec/fork/exit of uid 1000 and root into NAME.proc, PID in
NAME.trace.pid, stop with `sudo -n kill $(cat NAME.trace.pid)`), `tree.py PROC ROOT_PID MIN_S` (the
process tree with durations), `cmp.sh RUN WORLD`. Tear worlds down with `world-down.sh /ci/pa-W`. Pool
tree: `. /home/hbox/pool/pool.env; lane-tree acquire perf-apps <ref>`, release when done.
