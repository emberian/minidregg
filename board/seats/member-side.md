# Seat: member-side

Agent: vacant. The last holder, a778bbda6509944a5 (distilled once from agent-a8d456c6e773efbb8), stopped at ~480K
tokens on 2026-10-31. A fresh seat starts from this file plus docs/PERF-CLIENT.md, with `cv show a778bbda6509944a5`
for detail.
Worktree: /Users/ember/dev/minidregg-lanes/perf-client, detached on `main`, clean. There is no lane branch:
lane/perf-client was landed and deleted.
Box: hbox pool tree t8, leased as `perf-client`, at main ed875b89 with a warm .lake (renew or release it). Scratch is
hbox:/ci/pc (1.9 GB; hbox / is at 42 GB free, near its 40 GB early-warning line): the release cargo target
(`target`), `pcm.py` (wall plus CPU by role per shell line; `pcm.py WORLD MEMBER MINI REPS LINE...`), `pcweb*.sh`
(web timing), `fold.sh` (perf to folded stacks), `native-loop`, `up3.sh CANDIDATE NAME PORT` (jworld 5-member
scratch world), and the profiles `dn8.folded` (batch-8 provider, `doc new`). Live world: hbox:/ci/pc/w8
(candidate dc61016cbbac, port 22900; PID files in w8/pid, residents under each session's
`.mini/consent-anchors` and w8/a). Built, never measured: candidates/43f5e676214e under
/home/hbox/pool/lanes/perf-client/ (main ed875b89 host+consent overlaid on integ dc61016cb). A world on it fails at
`enroll plan member-4` (members 1 to 3 enrol, then no workspaces); I stopped that world (w9) by its PID files and
removed it.
Measurements move to persvati's standing world once build-loop has one up (board/seats/build-loop.md).

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
- Consent's Store-side target carries no World (ed875b899): the refresh extends `old.1.untracked`. For a provider
  the World advance never refused anything (a refused turn only loses the track), and it was 9.6% of a `doc new`
  catch-up (236 of 2,466 samples, hbox batch-8 profile). With row 16 (the walk's World, ~8%) a provider's catch-up
  no longer derives or admits any World turn. Lane-check green. Row 19.
- Attempt index, namespace ID index, workspace and settings read by identity; `history -n N` newest first
  (`/receipts` at 474 attempts 12 ms). Row 7.

## Numbers
- hbox, noisy; batch 8 against batch 7, interleaved: `doc new` 476 vs 614 ms wall (Host 254 vs 346 ms, consent
  160 vs 219 ms CPU). Warm `credit` 17 ms, `doc show` 20 ms. Of `credit`'s 10 ms when run directly: ~4 ms process start
  plus workspace load, three Host round trips, one codec frame, one consent frame. Warm ssh `say` makes 2,365
  syscalls across the whole client tree.
- w8 today (dc61016 Host and consent, member-1, `doc new`, three runs): wall 2,107 / 800 / 869 ms; consent
  1,041 / 241 / 253 ms CPU (the first run caught up after idle); Host 483 to 556 ms.
- Row 19 (ed875b899): an estimate from the profile only. The removed `WorldTrack.advance` under `extendStored` was
  236 of 2,466 samples (9.6%) of a batch-8 provider's `doc new`. There is no end-to-end after-number yet (see Next 1).

## Next (in order)
1. Rows 16 and 19's after-number. Bring up a world on a main-built candidate: a base whose clients and codec match
   main's Host. The overlay of main's host+consent on dc61016 fails at enrolment. Either use a fresh integ or
   builder candidate of main, or persvati's standing world. Then interleave `doc new` against w8 (or main^) with
   pcm.py, and profile the provider (`perf record -g --call-graph dwarf -p PROVIDER`, `fold.sh`). Expect no
   `WorldTrack` frames under `refreshExtended`.
2. Consent per record, retained mode. The walk re-derives each record, and that is the design (independent
   verification). What it spends is O(authority cell): a birth projects the authority (`Snapshot.ofCell`) about five
   times (pre cell in `preparePreAuthority`, post cell in `CandidateLawResolution.validateRecords`, again in
   `validateLoadedFrom` and in the member's own plan check `checkIntentPlan` -> `prepareDraft`), and encodes post
   cells (`LifecycleImage.bytes`, ~5%). The way out is a maintained projection carried in the provider's opened
   state and advanced per record, plus FORMAT (a)'s trie roots. Design it with host-execution, privacy and
   store-retained, who own those cells and the codec; per-record cost is the COSTS row (20 to 30 ms).
3. The map codec's decode-time sortedness check re-encodes keys on every comparison (`PackedCell.decodePayload` ->
   `IsChain` -> `encodeViaWriter`, 3.6%). Hand it to store-retained, or take it with their yes.
4. Footprint. The shared consent provider is ~66 MB anon and flat. Measure the per-member increment at 1 and 5
   members once infra renders the split units (forge demo container, batch 7 or later), then cut the shared base
   (codec ~12 MB, provider).
5. Web: `/keys` 60 to 75 ms is the Host's key-status op, not the page. Per-verb constants: ~300 fstat in custody reads,
   the attempt's `config.json` re-read per Host call, ~490 statx in private-dir checks per load (each well under 1 ms).
6. Pin roots from the cell's cached root once FORMAT (a) lands. Private cells sends the theorem relating
   `DeployedBridge.cellRoot` to the materialized root (`rootExact` / `materializer_rootOf`).

## Seams
- host-execution (a0fee5643746e520c): the Store open (`loadChained`), the session refresh, the DRC guards, patch
  chains, the authority projection on the Host's served path (`ServedAuthority`).
- read-path (ad74bb6d4410b48f3): takes the consent provider's start (`verifyInitial`, `resume`) off the full Store
  open onto `DurableServed.openHead`. I told it nothing of mine is in flight in ClientConsentCore/ConsentAnchor;
  keep one Store read per command (5517f6f57) and no World on the walk.
- privacy / private cells (a8da2b953507b402b): the `DeployedBridge.cellRoot` = materialized root theorem, for row 9's
  O(log n) judge.
- store-retained (a9b54e85e4a194b91): L0 makes the World's cells SparseMap trees (supersedes WorldCompact, row 9b); it
  ports `allSupport` itself; the map codec's sortedness check. Told: the provider needs no sealed World (only the
  Host's open does).
- infra (aa72653a8ce442178): shared consent resident unit, `--resident-dir` + ReadWritePaths, `mini-codec.socket`,
  `/etc/mini/session-codec`, `peer.pins` in ship.sh; provider and Host paths stay root-owned and unwritable, and
  `/var/lib/mini/consent-shared` is 0700 under the operator. Rendered with batch 7 or later on the forge demo container.
