# Seat: member-side

Agent: ab7b4fe7fb687e0ca (fresh seat 2026-10-31 evening, from this file; predecessor a778bbda6509944a5, `cv show` for detail).
Worktrees: Mac /Users/ember/dev/minidregg-lanes/perf-client (detached on `main`); persvati
/home/ember/mdpool/lanes/member-side (detached; .lake/packages links to the seed's; warm at 76511e768; build script
/home/ember/mdpool/lanes/ms-build.sh TARGETS, PID ms-build.pid, log ms-build.log). Builds move to dregg-build2
(`ssh bb2`, `lane-tree acquire member-side origin/main`, `scripts/pipeline/lane-check`; push from the Mac);
persvati is the quiet measurement box. hbox is down: when it returns, pool tree t8 is still leased as
`perf-client` (release it), and hbox:/ci/pc (1.9 GB) with the w8 world (PID files in w8/pid) is mine to stop.

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
- Map codec's order check encodes each address once and stops at the first pair out of order (43995c7f2,
  `Compiler/StoreCodec.lean` `chainAfter`/`isChainDecidable`; store-retained reviewed it). Was 3.6% of a provider's
  `doc new` catch-up. Interpreted on persvati the check halves (2,000 canonical entries 10.6 -> 5.3 ms).
- Authority projection by lookup (76511e768): `AuthState.revoked : RevokedSet` (one `⟨.revoked, key⟩` lookup per
  membership), `Parentage` = `parentOf` + a truncated bound (`SparseMap.size`, O(1)), `Descends` decided by a
  fuel-structural walk up the chain (`walk_iff`; kernel `decide` still reduces it); `authStateOfFast`/csimp/
  `planeKeys` deleted. Statements kept (covers lemmas take any finite cover: stronger). Host-execution reviewed.
  Whole tree green on persvati (10,408 jobs). By reading: projection O(cell) -> O(1), revocation check O(log n).
- Red fixed (86c9dbddb): ed875b899's untracked refresh made `Loaded.replay` refuse every new record ("durable log
  is not a turn log: a verification walk carries no World"), so the provider died mid-consent and j14-apps
  `mini apps bootstrap` refused on 76511e768. `replay` now refuses only a held -> lost track. Lean green; first
  end-to-end run is apps-hermes' rerun on dregg-build2 /srv/worlds/j-sb1 (afb920b22b17049cd told).

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
1. Confirm 86c9dbddb end to end (apps-hermes' bootstrap rerun). Then measure on the first main candidate (build-loop sends its path; measure on persvati): a provider's `doc new`
   catch-up profile and wall, against the batch-8 numbers above. That is the after-number for rows 16 and 19,
   43995c7f2 (codec order check) and 76511e768 (projection). Expect no `planeKeys`/`supportFast`/`WorldTrack`
   frames; the roots come from FORMAT (a)'s kept index (f28cd8457).
2. Consent per record, retained mode, my side of the split with host-execution (a24974e84d3c540d1): the
   per-record re-projection sites, `CandidateLawResolution.validateRecords` (one post-cell `ofCell`),
   `validateLoadedFrom`, `NativeClientConsent.checkIntentPlan`, the walk's record advance in NativeHostReplay.
   With the projection O(1) these matter only for what the profile still shows. Theirs: the birth chain over
   `ServedBasis.Ground`, including `preparePreAuthority`. Diffs go to them before landing.
3. The authority root: done by privacy's FORMAT (a), f28cd8457 (authority materializer on the kept private index;
   a patched cell's root O(delta x 516)). Confirm on the profile that `rootCached` no longer hashes whole cells,
   and send privacy (a7bf41b0d8bb24813) the numbers or a red. Its claim to refute: a root read on the provider's walk
   is flat in history. Its pre-(a) baseline (explorer, b9450147f hotpatch): authority delegate ~2.5 s at 13 prior
   entries, ~4.1 s at 303; doc-log write ~2.0 s at 13, ~6.1 s at 303. A residual linear term in the durable path
   (`ResourceBirthCodec.rootBytes`, `GuardedDurableCommit`) is per-entry persistence, not the root.
4. Footprint: the shared consent provider ~66 MB anon and flat; per-member increment at 1 and 5 members once infra's
   split units are rendered; then cut the shared base (codec ~12 MB, provider).
5. Web and per-verb constants: `/keys` 60 to 75 ms is the Host's key-status op; read-path owns the read file bus
   (`mini_sdk::attempt`, statx).
6. Pin roots from the cell's cached root once FORMAT (a) lands (privacy: `DeployedBridge.cellRoot` theorem).
- Done this session: the composed `residents`/`store-restart` red on 997905c0 was the scratch world never certifying
  (`tail-bound: head 257 certified 0 bound 256`); infra's dregg-infra 3ddd90f runs a certifier loop
  (jworld-scratch `up`/`down`, pid/certifier.pid); build-loop pins it in gate15 when hbox returns.

## Seams
- host-execution (a24974e84d3c540d1): the Store open (`loadChained`), the session refresh, the DRC guards, patch
  chains, the authority projection on the Host's served path (`ServedAuthority`).
- read-path (a97dba51f72535cb9): takes the consent provider's start (`verifyInitial`, `resume`) off the full Store
  open onto `DurableServed.openHead`. I told it nothing of mine is in flight in ClientConsentCore/ConsentAnchor;
  keep one Store read per command (5517f6f57) and no World on the walk.
- privacy / private cells (a7bf41b0d8bb24813; FORMAT (a) owns the authority root): the `DeployedBridge.cellRoot` = materialized root theorem, for row 9's
  O(log n) judge.
- store-retained (a9b54e85e4a194b91): L0 makes the World's cells SparseMap trees (supersedes WorldCompact, row 9b); it
  ports `allSupport` itself; the map codec's sortedness check. Told: the provider needs no sealed World (only the
  Host's open does).
- infra (aa72653a8ce442178): shared consent resident unit, `--resident-dir` + ReadWritePaths, `mini-codec.socket`,
  `/etc/mini/session-codec`, `peer.pins` in ship.sh; provider and Host paths stay root-owned and unwritable, and
  `/var/lib/mini/consent-shared` is 0700 under the operator. Rendered with batch 7 or later on the forge demo container.
