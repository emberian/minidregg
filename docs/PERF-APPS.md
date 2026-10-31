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
| 1 | Every wake of an installed image (`verify_installed_spk`) re-verifies the whole SPK: copy to a temp file, xz-decode it to a second temp file, SHA-512, ed25519, parse the archive. It runs at install (about 3 times), at the route bind, at every START and STOP. | 2.7 to 4.3 s per call for EtherCalc (37 MB; 2.4 s CPU); more for Etherpad (64 MB) and Davros | fixed on the lane (below) |
| 2 | The apps worker binds the owner's route through 13 `mini` subprocesses and 2 one-shot `minidregg-host` helper processes (`grain-share-issue-*` ran `HOST CONFIG author` and `inspect outcome` as processes). | 17.5 s wall; 0.3 s per helper process | helper processes fixed on the lane; in-process worker steps are next |
| 3 | op66, the lifecycle BEGIN plan, takes 8.6 s on a fresh world (a history walk from genesis when a share/grant/reserve record sits below the checkpoint) | 8.6 s per INSTALL and per START | hot-path's (row 4 slice 2) |
| 4 | Agent typed-tool custody (`agent_reserve`, `agent_payer`, `agent_lifetime_grant`) runs every author/inspect/signatures as a `minidregg-host` process | 5 to 8 processes per operation, 60 to 300 ms each | fixed on the lane |
| 5 | `grain start` polls the resident's completion every 500 ms and spawns `systemctl --user show` per poll | up to 0.5 s added latency; 10 to 750 ms per poll | open |
| 6 | Each grain HTTP request is a durable Mini turn (PLAN, ASSEMBLE, SUBMIT, and inspections); the resident dispatches one request at a time | not yet measured on a running grain (START was red until 40efdcff9) | next measurement |
| 7 | `apps_worker` re-hashes the whole quarantined SPK on every install attempt and retry | about 0.1 s per 37 MB | small; open |

Already done before this lane, on batch 5: no fsync anywhere (exorcist); the hosting delegation's
rounds run in-process, not as `mini workspace --action app-lifecycle` subprocesses (exorcist); spk-host's
`author`/`inspect`/`signatures` go to the Host session instead of a process per call (about 1 ms each,
`tool-timing ... session=1` in the resident journal).

## Landed on the lane (before/after pending the measured run)

- **The image's verified identity is retained at publication.** `materialize` writes
  `verified-identity.json` (0444, the manifest's custody) with the publishing parse's result: raw length
  and SHA-256, the signed manifest digest, the signed bridge and data config bytes. A wake re-hashes
  `package.spk` with SHA-256 (about 25 ms for 37 MB) and must match that record and the image's own name;
  signature verification is a function of those bytes, so the record is that verification's result for
  them. An image published before the record existed is re-verified as before. Test:
  `retained_verified_identity_equals_reverification_and_binds_the_bytes` (the record's identity equals a
  fresh re-verification field for field; a one-byte rewrite of `package.spk` at the same length is
  refused; a 0644 record is refused).
- **Source custody pure verbs go through the codec session.** `share_issue::source_process` and
  `agent_reserve::source` answer `author`, `inspect` and `signatures` through
  `client_consent::pure_source` (this process's codec session, the frame every other client verb
  already uses), never through the operator socket, as before.
</content>
</invoke>
