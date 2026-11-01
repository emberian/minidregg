# Seat: member-side

Agent: vacant (handoff 2026-11-01 ~02:45Z). Last holder ab7b4fe7fb687e0ca, before it a778bbda6509944a5; `cv show <id>`
gives either transcript. Editing passes to another agent; this file is the whole continuation.

## What this seat owns
- The client, `native/resource-client` (`mini`: the shell verbs, workspace, chat, the web body `src/web`), and
  `mini-line`, the ssh forced command.
- The ssh wrapper (`deploy/shell/mini-shell-ssh`) and `mini-web-spawn`.
- `native/mini-sdk`'s consent and residents, `native/mini-session-env` and `native/mini-streams`.
- The consent provider's Lean side, `Host/ClientConsentCore.lean` and `Kernel/ConsentAnchor.lean`.
- The per-guard `readGuards` pattern in every receiver except `DeclaredResourceController` (host-execution's).
- The composed-gate adapter `native/resource-client/composed-scenario.py` (its residents phase).

The measured-findings table is docs/PERF-CLIENT.md (rows 1 to 19). The rules are board/README.md, board/RULINGS.md,
CLAUDE.md and ATLAS.md §6; ~/swarm (README.md, RULES.md, MACHINES.md) describes the boxes.

Quest: the member's side of the Host at about 1 ms of warm work per action, widest costs first, never slower as
history grows (law 17); members share one base, a few MB per member session.

## Landed on main this session (2026-10-31 to 11-01; whole tree green on persvati for each Lean change)
- 43995c7f2 (+ pin 4e76674a2): `Compiler/StoreCodec.lean`. The map payload's order check encodes each address
  once and stops at the first pair out of order (`chainAfter`, `isChainDecidable`). It was 3.6% of a consent catch-up
  and is half as costly interpreted.
- 76511e768: the authority projection is built from closures only.
  - `AuthState.revoked : RevokedSet`, membership by one `⟨.revoked, key⟩` lookup.
  - `Parentage` = `parentOf` plus a `Trunc` bound (`SparseMap.size`, O(1)), so `ext` is on `parentOf` alone.
  - `Descends` is decided by a fuel-structural walk (`walk_iff`); kernel `decide` still reduces it.
  - `authStateOfFast` deleted. No statement weakened: the cover lemmas take any finite cover.
- 86c9dbddb, red fix: `Loaded.replay` refused every record of an untracked walk (ed875b899's consent refresh),
  so every provider died at the first new record ("durable log is not a turn log: a verification walk carries no
  World"; enrolment and bootstrap failed on 76511e768). It now refuses only held -> lost. Confirmed on overlay
  93b31c1c33d6: read-path's persvati reproducer passes, and a 5-member world enrols and bootstraps.
- 22cac1ee0: one Host reply check for the custody flows (`agent_reserve::host_reply(frame, op, what)`) names every
  outcome (no record, never forwarded, undecided). The grain share recovery test now drives the codec session.
- 467e698ef: named Host op constants in a client test; `scripts/host-operations.py check` had stopped every
  `lane-build.sh host`.
- a014ff501: a verification walk's authority load follows the held trie. `Patch.diff`/`run_diff` are in
  Theory/Store.lean; `Materialized.relativeTo` is in Theory/CellState.lean. `loadDeploymentFromAt` takes the decoded
  cell relative to the held one when the bytes moved. Store-retained and privacy reviewed it.
- Unchanged from earlier holders: rows 1 to 19 of docs/PERF-CLIENT.md (receivers' writes once per guard list,
  host-image digest by file identity, residents that never idle out, shared and split-tenancy residents, one Store
  read per consent command, representsCheckFast, closed stdout 141, no World on the provider's walk, ed875b899).
- No wip branches. Nothing is unfinished or uncommitted; the Mac worktree is clean at main.

## Numbers (persvati, the quiet box; pcm.py, member-1 `doc new`, blocks of 10, medians, ms)
| world | block 1 | block 6 | note |
|---|---|---|---|
| base 4b750eb67 | 255 / 101 / 110 | 398 / 198 / 173 | wall / Host / consent |
| overlay e0cd5307229b (main 467e698ef host+consent on 4b750eb67, carries a014ff501) | 219 / 94 / 95 | 276 / 139 / 104 | consent near flat |
| interleaved base vs store-retained's held 4f60d20e9ef7 | Host 85 vs 93 | Host 123 vs 148 | held slower; cause found by store-retained (double bind, fixed on its wip 4ca511c70) |

- `minidregg-host CONFIG store-bench` at height 177, with a 25 KB authority cell: `loadDeployment` from bytes 42 ms
  against 2.5 ms held and unchanged. `credit` takes 11 ms wall.
- Host growth with births (about 94 to 139 ms over 60 `doc new`, even with a014ff501) belongs to host-execution and
  store-retained. Host-execution measured 500 says growing only 24 to 40 ms, so the Host's growth is per birth.

## Next, in order
1. Composed `residents` red (owners member-side and infra), the gate on hbox at d5e858b2:
   `REFUSED timeout: managed fixture provider`, in `PHASE provider`, after `prepoll-filler: 129 native rows in
   20.5s`. Evidence is in hbox:/ci/c-d5e858/composed/state/evidence/0124-residents/adapter.err. The earlier
   tail-bound refusal is fixed (dregg-infra 3ddd90f certifier). Read the provider phase in composed-scenario.py and
   the managed fixture provider's logs before guessing.
2. Law 17 on the consent walk. `Loaded.replay` binds each record with `IntentRecord.bind?` (`rootBytes post =
   exactPost`), which for the authority cell may be a whole private-trie build per record (store-retained's
   finding). Profile one provider block first (perf note under Boxes). The law-17 form: the walk carries each
   record's own write patch as data beside the Prop admission in `Derived`, so it never decodes or diffs a whole
   cell, and `Patch.diff` stays the bytes-only fallback. Diffs go to host-execution (NativeHostReplay is theirs).
3. A one-pass merge in `Patch.diff` over both sorted `toList`s (store-retained's note), only if a profile shows it.
4. Footprint: the shared consent provider is about 66 MB anon and flat. Measure the per-member increment at 1 and 5
   members on infra's split units, then cut the shared base (codec about 12 MB, provider).
5. Web: `/keys` takes 60 to 75 ms, all of it the Host's key-status op. Read-path owns the read file bus.

## Seams (current agent ids)
- host-execution (a559316c0cc2b4b14): NativeHostReplay, the walk's `Derived`, the birth chain, the Host open and
  sessions. Agreed split: the walk's per-record projection sites are this seat's, `preparePreAuthority` theirs.
- store-retained (a9b54e85e4a194b91): SparseMap/Store (`Patch.diff` lives there), the held served state
  (wip/retained-held).
- privacy (a7bf41b0d8bb24813): CellState carried and `relativeTo`'s neighbour, FORMAT (a) (f28cd8457), the
  authority root.
- read-path (a31482e50a323ff17): the client's read path and op 5. Its c4a1e4cf4 in workspace.rs was reviewed and
  approved here.
- apps-hermes (a990f9e07566fd55c): custody flows in resource-client (agent_reserve, lifetime_v3).
- infra (a5bc08dce78e7405e): jworld-scratch (dregg-infra), the consent resident units.
- build-loop (a4141abe7297fdc4b): the builder, pools and `world-reap`.

## Boxes, as left
- No pool tree is held (hbox t8 and bb2 t1 are released). dregg-build2 is obend's now. hbox / had about 41 GB
  free. hbox:/ci/pc (1.9 GB, a predecessor's scratch) is left for ember to decide.
- persvati, /home/ember/mdpool/lanes:
  - `member-side`: my Lean worktree, with its own 7.3 GB package copy.
  - `msl`: LANE_DIR of `msl-build.sh` (host, consent, overlay on a base).
  - `cand`: candidates 4b750eb67, 93b31c1c33d6, d5c4b3cf2a41 (withdrawn), 4f60d20e9ef7.
  - `pcm.py`, `fold.sh`, `world-reap`.
- persvati worlds: none of mine is up. rf, sb, sr, sa, tb and tr are down (tb and tr by world-reap, logged in
  rpw/winddown.log; sr's two orphans by SIGTERM, logged in rpw/sr.orphans.log). Worlds rpw/xb and rpw/xn, started
  from /home/ember/mdpool/lanes/srp, are not mine (likely store-retained's) and are left up.
- Measuring on persvati: bring a world up with `/home/ember/mdpool/rp/up.sh CANDIDATE RUN_DIR PORT`. Run
  `python3 /home/ember/mdpool/lanes/pcm.py WORLD member-1 MINI 10 "doc new x{t}{i}"`, where MINI is
  WORLD/root/var/lib/mini/candidate/current/bin/clients/x86_64-unknown-linux-gnu/mini. Stop the world with
  `scripts/pipeline/world-reap ROOT`.
- perf on persvati: `sudo -n` works. The serving Host runs from a deleted memfd (comm `7`); copy the binary into a
  symfs dir as `memfd:mini-pinned-image (deleted)` and pass `--symfs`. Only flat profiles work, since DWARF stacks
  do not unwind through Lean frames. Stop perf by its PID file.
- A full umbrella at 16 Lean threads OOMs the 24 G swarm cap on persvati; use 8 threads.
