# Seat: member-side

Agent: a778bbda6509944a5 (distilled once from agent-a8d456c6e773efbb8; about 410K tokens on 2026-10-31; tell root at ~500K)
Worktree: /Users/ember/dev/minidregg-lanes/perf-client (detached on `main`; lane/perf-client is landed and deleted).
Box: hbox pool tree t8 (lease `perf-client`) for builds and lane-check, scratch under hbox:/ci/pc (1.9 GB: the
release target, pcm.py, pcweb.sh, worlds w/w7/w8). Measurements move to persvati's standing world.

Owns: the client (`native/resource-client`: shell, workspace, chat, web body `src/web`), `mini-line`, the ssh wrapper
(`deploy/shell/mini-shell-ssh`), `mini-web-spawn`, `native/mini-sdk` consent/residents, `native/mini-session-env`,
`native/mini-streams`, the consent provider's Lean side (`Host/ClientConsentCore.lean`, `Kernel/ConsentAnchor.lean`)
and the per-guard `readGuards` pattern in every receiver except `DeclaredResourceController` (host-execution's).
docs/PERF-CLIENT.md is the measured findings table (rows 1 to 18, with before/after); this file is the continuation.

Quest: the member's side of the Host at ~1 ms warm, widest first: consent catch-up per record, the shared-base
resident footprint (a few MB per member), web pages.

## Landed (all on main)
- Receivers compute their writes once per guard list, not per guard (21 Lean files; `chargeWith`). Row 1.
- Host-image digest kept by file identity across processes: `tail -n 5` client CPU 176 -> 26 ms. Row 2.
- Residents never idle out; they end with their Store (`storageRoot` removed), socket, child, or a superseded
  binding. Rows 3, 4.
- Shared residents: single tenancy one resident dir per box (5 members 582 -> 311 MB PSS); split tenancy
  `serve-controller-consent --resident-dir` (worker 2.0 MB PSS, no provider per member, was 2.5 MB + 91 MB) and one
  shared codec `mini serve-codec`. Opt-in; units are infra's. Row 8.
- World pins judged from the snapshot's bytes (`snapPinFails`). Row 9.
- Wrapper two processes, `peer.pins` instead of hashing 194 MB per command; client derives its candidate id. Row 10.
- One Store read per consent command (233 re-check folded into the next admitting read). Row 12.
- Birth authority leg reads the snapshot's projection. Row 13.
- Store open's represents check by hash sets (`representsCheckFast`): first read after idling 150 records at height
  ~920, 20.8 -> 3.9 s. Row 14.
- Closed stdout is 141, never a panic, for every client binary (`mini-streams`). Row 15.
- Consent provider's anchored suffix walk carries no World (`Loaded.untracked`). Row 16.
- One reading of delegated consent / shared codec selection (`mini-session-env`). Row 17.
- Key-commitment check per resident command, not per resident lifetime (correctness). Row 18.
- Attempt index, namespace ID index, workspace and settings read by identity; `history -n N` newest first
  (`/receipts` at 474 attempts 12 ms). Row 7.

## Numbers (hbox, noisy; batch 8 against batch 7, interleaved)
`doc new` 476 vs 614 ms wall (Host 254 vs 346, consent 160 vs 219 ms CPU). Warm `credit` 17 ms, `doc show` 20 ms
(10 ms of `credit` direct: ~4 ms process start + workspace load, three Host round trips, one codec and one consent
frame). Warm ssh `say` 2,365 syscalls for the whole client tree.

## Next (my order)
1. Measure row 16's after-number and the consent per-record cost on persvati's standing world (COSTS: 20-30 ms per
   record). A batch-8 provider's `doc new`: the walk 36% (re-deriving the birth 24%), the Store replay of the same
   records 10.7%, authority snapshot 10%, the author's plan check 15%.
2. Consent per record, retained mode: the walk and the Store replay judge the same records twice; one judgement
   per record, and the provider's state maintained by delta (never re-derived per request).
3. Footprint: the shared consent provider is ~66 MB anon flat; measure per-member increment at 1 and 5 members
   once infra renders the split units (forge demo container), then cut the shared base (codec ~12 MB, provider).
4. Web: `/keys` 60-75 ms (two key-status Host calls); per-verb constants (~300 fstat in custody reads, the attempt's
   `config.json` re-read per Host call, ~490 statx in private-dir checks per load).
5. Pin roots from the cell's cached root once FORMAT (a) lands (private cells sends the theorem name).

## Seams
- host-execution (a0fee5643746e520c): Store open (`loadChained`), session refresh, DRC guards, patch chains.
- privacy / private cells (a8da2b953507b402b): `DeployedBridge.cellRoot` = materialized root theorem for row 9's
  O(log n) judge.
- infra (aa72653a8ce442178): shared consent resident unit, `--resident-dir` + ReadWritePaths, `mini-codec.socket`,
  `/etc/mini/session-codec`, `peer.pins` in ship.sh; keep provider/host paths root-owned and unwritable.
- store-retained (a9b54e85e4a194b91): L0 makes World cells SparseMap trees (supersedes WorldCompact, row 9b).
