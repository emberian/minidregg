# Seat: store-retained (handoff, 2026-11-01 wind-down)

Status: **idle; handed off.** Last agent a9b54e85e4a194b91 (formerly a13f0c9ab4513b2d7); its transcript is
readable with `cv show a9b54e85e4a194b91` / `cv show a13f0c9ab4513b2d7`. A new agent starts here, then reads
`docs/RETAINED-MODE.md` (design: diagnosis, abstraction, node inventory §3, order §4, L0 §5, generation §6, lint §7,
continuation §8).

Owns: the leaf layer and retained mode. `Theory/Retained.lean` (a maintained answer equals recomputation after
any admitted run and across checkpoint/restore; chain rule; generic red-green memo node), `Theory/SparseMap.lean`
(persistent extensional tree map over injective `List Nat` key codes: get/set/ext, support with no dedup,
filterKeys, map, ofFinset, toDFinsupp/ofDFinsupp spec views), `Theory/DeriveStoreKey.lean` (`deriving StoreKey`),
`Theory/Store.lean`'s representation, the World's `Cells`, `Compiler/DurableServed.lean`'s served state.

Quest: derived values maintained by delta, never recomputed per request; the widest costs first (law 17 and
ember's ~1 ms of warm Host work per action).

## Landed on main
- `675a80745` Theory/Retained.lean (statement, proofs, witnesses; astra rounds 1-2; integrator audits closed).
- `62aa5fcf8`, `05bffae27` Theory/SparseMap.lean, transport lemmas to the DFinsupp view.
- **`802ba8c69` L0**: `Store L` and World's `Cells R` are SparseMap trees (every lookup and set O(log n));
  `Compiler/WorldCompact.lean` and `compactEvery` deleted; `deriving StoreKey` on every layout's keys; StoreCodec
  builds by `set` and reads the tree's support; the cached-support twins collapsed. Whole tree green (10404 jobs).
- `49cf4f2d2` **R1**: op 5 authorizes from the challenge op 4 planned over the same light opening.
- `bdfa9428c`, `c3a28038a` **R6(i)**: after an ordinary birth the session keeps the post-birth authority cell with
  its built index, so the next load skips the private-trie rebuild (other writers still decode from bytes).
- `f937f2b38` `mini serve` writes the serving Host's PID beside the socket (`mini.host.pid`).
- Docs: `1d4ff4efb`, `03c8af2c0`, `f53c9e07e` docs/RETAINED-MODE.md.

## Numbers
- **L0** (grow2r on hbox, 8 sequential `story new`, Host CPU from /proc, base 997905c0b vs its L0 Host overlay):
  Host CPU per story 590 → 1200 ms (s1 → s8) before, 500 → 700 ms after; slope +610 → +200 ms. At story 8
  `DFinsupp.update`/`Function.update` (49 % inclusive) gone, `SparseMap.set` 1.1 %. hbox is shared: CPU seconds,
  not wall.
- **Held served state** (persvati, quiet box, load ~1): see the WIP section below.

## WIP (not landed; do not merge as is)
**`origin/wip/retained-held` = `4ca511c70`** (main merged at 70f61182d; DurableServed elaborates green on hbox t4,
`lane-check`, 0 errors) and **`origin/wip/retained-held-measure` = `6fe9124dd`** (the same fix alone on
`d6468ecaf`, for an A/B against base 4b750eb67; overlay `7ed32ce04576`, on hbox
`/home/hbox/pool/lanes/retained/candidates/` and persvati `/home/ember/mdpool/lanes/cand/`).

What it is: `DurableServed.Served` keeps `Held`, one `SparseMap CellId (bytes × root)` plus the allowance as a
`ChargeTuple`, advanced per record (`Held.install_agrees`, `replayed_agrees`, `replay_rootsBound`, `ofState_agrees`,
`ofSnapshot_agrees`, `bare_viewAt_ofLoaded`), in place of a `DataSnapshot` whose `canonicalBytes`/`roots`/`available`
were a closure per installed record.

Defects found and their state:
1. *Fixed* (first overlay d5c4b3cf2a41, withdrawn): `flatCharge`'s lets floated back into its match arms, so each
   lane read re-walked the history (story 3: 852 s of Host CPU). The allowance is now a `ChargeTuple`.
2. *Fixed in 4ca511c70*: **double binding**. `extendVerified`'s `replay` binds each record (`IntentRecord.bind?`
   checks `rootBytes write.canonicalPostBytes = write.exactPost`; on the authority cell `rootBytes` is a whole
   private-trie build), and `Held.replayed` bound every record again. Now `Held.installRecord` takes the roots'
   binding as a proof and `Held.replayed` threads `RootsBound` from the accepting replay: nothing is re-hashed.
   persvati before the fix (member-side's interleaved blocks, then my alternating per-op schedstat of the serving
   Host): held 202 ms vs base 159 ms per `doc new`, growing faster. After: keccak level with base.
3. **Open: the residual runaway.** Fresh pair on persvati (xb = base 4b750eb67, xn = 7ed32ce04576), equal heights,
   `MINIDREGG_HOST_TRACE=1`, 20 alternating rounds: op 2 (the write) median 61.5 ms base vs 76.5 ms held, and held
   grows faster (first half 58 → 62 base, 67.5 → 77.5 held). Earlier blocks looked level (op 2 47 vs 46 ms at a
   lower height); serving-CPU medians are confounded by periodic ops 170/172 (73–184 ms each, certify-shaped),
   so compare request ops from the trace, not totals. **Diagnosis so far** (hbox DWARF stacks, 60 + 10 `doc new`
   per candidate, `/home/hbox/pool/t4-retained/gd{b,n}.inc.raw`): the held build spends +6–7 points inclusive in
   `Host.sessionAdopt` → `CredentialAuthorityDomain.Snapshot.ofCell` → `CellState.materialize` /
   `Materialized.rootCached` → `AuthTrie.Trie.build`/`mkBranch` (`PrivateCellRoot.deployedDig` 4.8 → 11.6 %), i.e.
   it rebuilds the authority cell's private trie on adopt where the base reuses the held cell. Likely cause: R6(i)'s
   reuse and `cellsLawfulServedFrom` rely on `bytesBEq`'s pointer-equality fast path ("an unchanged cell's bytes in
   the next image are the very object of the prior image's"), and the bytes the held state hands to
   `loadDeploymentFrom`/adopt are no longer that object (or the held authority cell is not threaded through the
   held state's adopt path). Next step: in `Host/Main.lean` `sessionAdopt` and
   `CredentialAuthorityDomainReceiver.loadDeploymentFrom`, check which bytes are compared and make the held
   state return the prior image's object for an unchanged cell (or carry the held `Materialized` cell with the
   `Held` entry), then re-run the persvati traced pair. **Land only on a persvati result that is not slower.**

## Next (in order, after the WIP)
1. Finish the held served state (above), then the session refresh (`NativeHostSession.refresh` still grows after L0).
2. Authority nodes: a maintained digest → capability-address index beside the authority cell (`issuerCheck` scans
   the support and hashes every capability, twice per evidence via `domainPortal`); the rest of R6(i) (the other
   writers pass `none`).
3. Tree order = wire order for StoreCodec (drop encode's sort).
4. R3 planner/deriver prepared write (perf-client's design, docs/PERF-CLIENT.md); I4/I5 Fn and carry scans;
   export/backup; client refs index; the lint (RETAINED-MODE §7).

## Seams
- host-execution (a24974e84d3c540d1, delegate he-births ac49ca4075452034f): owns the World fold frames
  (`foldRecords` → `World.admit` → `pinCheck` → `DeployedBridge.cellRoot`), `Ground.authorityWrite`'s cellRoot,
  `StoreCodec.encode`, and `Opening.world` as a WorldTrack (type and the `worldAfter` line in `receiveServed`).
  store-retained's lines in `receiveServed` are `served.advance`, `checkpointState` and the `rootsEq` rewrite.
  he-births landed cb38b5612 (rebase the WIP onto it).
- privacy (a3f7fce75cd3e4e49 / a7bf41b0d8bb24813): narrowed views on `SparseMap.filterKeys`; R6(i) is its seam.
- member-side (ab7b4fe7fb687e0ca): measured the held pair; its consent walk replays through the same root check
  and may rebuild the authority trie once per record (its next profile).

## Box state (2026-11-01 ~02:30Z)
- hbox: pool tree t4 **released** (lane-tree saved its uncommitted state to
  `/home/hbox/pool/saved/t4-retained-20261101T022834Z.patch`). `/home/hbox/pool/t4-retained/` holds logs, scripts
  (`grow2r.sh`, `gdoc.sh`, `world-reap`), world dirs (all stopped) and `kills.log`. world-reap stopped 51
  processes by PID file. **Two left UNNAMED (no PID file, not stopped, reported to root):** 1189092 `mini
  codec-resident` and its child 1189093 `minidregg-host`, under `t4-retained/gdbg` (candidate d39611974c22).
  Candidates in `/home/hbox/pool/lanes/retained/candidates/`: d5c4b3cf2a41 (withdrawn), 4f60d20e9ef7 (double-bind
  defect), d39611974c22 (L0 era), 7ed32ce04576 (bind-once fix alone).
- persvati: worlds rpw/xb and rpw/xn **stopped** by world-reap (21 each, 0 unnamed). Scripts and outputs in
  `/home/ember/mdpool/lanes/srp/` (`alt2.py` = alternating per-op serving-Host schedstat; `prof4.sh` flat perf;
  perf data deleted). perf on persvati cannot unwind the memfd Host (flat profiles only, with a symfs copy named
  `memfd:mini-pinned-image (deleted)`); hbox's perf unwinds it with `--call-graph dwarf -p`.
- Mac: worktrees /Users/ember/dev/minidregg-lanes/retained (branch `retained-held-measure`; `retained-held` =
  4ca511c70) and /Users/ember/dev/minidregg-lanes/store-retained (detached main, board edits).
