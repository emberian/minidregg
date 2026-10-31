# Seat: privacy

Agent: a7bf41b0d8bb24813 (distilled from a3f7fce75cd3e4e49, retired; earlier: a8da2b953507b402b. Transcripts:
`cv show agent-a3f7fce75cd3e4e49`, `cv show agent-a8da2b953507b402b`).
Owns: private cells: `Compiler/PrivateCellRoot.lean`, `Compiler/PrivateCellIndex.lean`, `Kernel/PrivateCell*.lean`
(View, Scope, Receiver, Materializer, Opening), `Kernel/BlindedCellHiding.lean`, `Kernel/ReceiptEventHiding.lean`,
`Theory/PrivateCellTrie.lean`, `Theory/AuthTrieErase.lean`, `Theory/AuthTrieReveal.lean`, `Theory/CellStateAux.lean`
(the carried structure in `Theory/CellState.lean`), `Theory/FiniteTapeGap.lean`, `Theory/OracleGame.lean`, `Compiler/AirKeccak.lean`, `Compiler/AirCshake.lean`,
`docs/RATCHET-LOG-DESIGN.md`.
Quest: blinded cells (content, declared kinds) on a private authenticated map with O(log n) writes and bounded reads,
hidden by a fresh outer mask per version and a zero-knowledge complete selective opening; the unblinded growing kinds
on the same trie root (FORMAT (a)). Never trade hiding for speed.

## Worktrees and boxes
- Mac: `/Users/ember/dev/minidregg-lanes/privacy` (branch `seat/privacy`, tracks `main`; commit by path, `git pull
  --rebase origin main`, `git push origin HEAD:main`).
- Builds: dregg-build2 (`ssh bb2`), pool tree t4 leased to `privacy` (`lane-tree acquire privacy origin/main`;
  release with `lane-tree release privacy`). Its origin is a mirror that can lag GitHub: after a push, check the
  tree has the commit, or rsync the changed files. Logs and PID files in `~/privacy-logs/` (`lcN.sh`, `bN.sh`).
  Whole tree: `SWARM_MEM_MAX=28G swarm-build lake build Theory Kernel Compiler Assurance Minidregg Host`. On bb2 six
  Mathlib replays fail with "permission denied" (read-only shared packages; build-loop told); every project module
  still builds. hbox t1 (lease `private-cells`) and persvati `/home/ember/mdpool/lanes/privacy` exist but are idle.
- Reviews: codex astra as peer via the native binary (the Homebrew node `codex` is broken):
  `/opt/homebrew/lib/node_modules/@openai/codex/node_modules/@openai/codex-darwin-arm64/vendor/aarch64-apple-darwin/bin/codex
  exec -m gpt-6-astra -s read-only -C <worktree> "<prompt>"`, nohup with a PID file in the scratchpad.

## State (main cf368e4fb)
- cf368e4fb, private root format v2: inner digests are cSHAKE256 outputs (`Inner`, 32 bytes) framed as their bytes.
  The node bytes are fixed per variant (empty 1, branch 65, leaf 98; `pathNodeBytes_length`), and `outerInput` is
  the context and mask as framed lists, then 32 inner bytes. This corrects 21cbfc7de, whose `digestStream` framing
  (33 or 34 bytes by value) leaked digest magnitude. Tags NODE/v2 and OUTER/v2 put this in a second root-format
  epoch (build-loop re-records once from main's tip). The framed custody decode (`framedDecode`, `custodyBytes`:
  identity, version, exactly 32 secret octets; `PublicShape`) is for blinded kinds at epoch (b); `natDecode`'s
  mask grows with the secret and stays only in the receiver's ideal-setting instance. `framed_outerBytes`: an
  accepted witness's outer input is a public frame, then 64 private octets.
- 6b104c63c, aaec61fce, 81afc7026: the circuit substrate. `Compiler/AirKeccak.lean` (round and permutation, per
  transition, sound, complete, unique), `Compiler/AirCshake.lean` (cSHAKE256 at a public length; the prefix blocks
  absorbed into the public `midstate`), `Compiler/AirKeccakCensus.lean` (#guard: 12480 gates per round after
  `EmitShare.cse`, 1600 AND; one permutation per node hash).
- 4038d3693: `Shaped` in `OpeningRel`. f28cd8457: FORMAT (a) (event log and authority cell on the private root).
- f9fcaa25b: `Kernel/PrivateCellOpening.lean` (the fixed relation), `Theory/OracleGame.lean` (costed ROM systems).
- Earlier (predecessor): receipt hiding, trie erase as a heap program, scoped reveals, the Store adapter, the
  receiver (`KeptCell`, custody PRF hop, `hiding_of_hybrids` with zk, rom, identical open).

## Next, in order
Substrate (astra round 17): the built Air rung over `ZMod 2` (add' = XOR, mul' = AND, each constraint zero-checked
alone), flattened by `AirFlatten`, emitted by `Emit`, shared by `EmitShare.cse` (`cse_emit_accepts_iff`). The parked
AND/XOR network in ResearchWip (`ObliviousNetwork`, `BendProofKeccak`) keeps its Bend consumers; rescue by a proved
lowering into Air only where useful, never as a second compiler for the opening.
1. Done: the Keccak permutation, cSHAKE at a public length with the public midstate, and the build-checked census
   (above). A bounded-length variant only if a private hash input turns out variable (none does now).
2. Done: the custody size contract (cf368e4fb). Owed at epoch (b): blinded kinds' blinding space as bytes with
   `framedDecode`, and the receiver's setting moved to it.
3. The opening system per public shape (capacities per prefix; private stopping depth, occupancy and node tags):
   node hash inputs are variant-sized (empty 1 byte, branch 65, leaf 98), so private variants need selection or
   bounded-length hashing; the public view's content digests may be verifier preprocessing if their binding to
   the encoded view is proved. `Witness.reveals` is a function: serialize the selected prefixes and prove
   reconstruction preserves `OpeningRel`. Sound and complete against `OpeningRel` through the codec.
4. The ZKBoo seam (round 17 item 3): an evaluator derived from the emitted SSA whose outputs are the residuals,
   every zero check preserved; deterministic gate evaluation, uniqueness only for retained outputs after CSE.
   `OracleGame.System` picks circuits by statement bit length: shape-indexed instances or one padded circuit.
5. The backend: MPC-in-the-head over that circuit as an OracleGame `System` (straight-line extraction from the
   logged commitment preimages, one stateful simulator).
6. The receiver adapter (round 15 items 7, 8), then `zk` of `hiding_of_hybrids`; epoch (b).
7. The binding reduction for the private root (equal roots → equal stores ∨ a named collision).
8. FORMAT (a)'s timing: member-side (ab7b4fe7fb687e0ca) measures the authority cell. Baseline b9450147f:
   doc-log write ~2.0 s at 13 prior entries, ~4.0 s at 103, ~6.1 s at 303; delegate ~2.5 s at 13, ~4.1 s at 303.

## Seams
- store-retained (a9b54e85e4a194b91): L0's Store (landed 802ba8c69); narrowed views are `SparseMap.filterKeys`.
- member-side (ab7b4fe7fb687e0ca): told the authority root is the kept trie since f28cd8457 (a patched cell's root
  in O(delta · 516) walks); it rewords `AuthState.revoked`/`Parentage.support` in Theory/TypedAuthorization.
- build-loop (a6c58cb72b0764dbb): seam 1 on main (f2002e589); named codec tags in `Compiler/PersistedCodecTags/Core.lean`,
  census-only tags (all four PRIVATE-CELL tags) in `Compiler/PersistedCodecTags.lean`; never add an import of the
  census. Told of the epoch (fixtures re-record) and the bb2 Mathlib permission failures.
- host-execution (a24974e84d3c540d1) measured 14% of `doc new` in rebuilding the authority trie. Cause:
  `CredentialAuthorityDomainReceiver.loadDeploymentAt` decodes the cell from bytes per load, and each fresh
  `Materialized` builds its index on its first root read; patches already carry it. Routed to store-retained
  (session holds the forced cell). Nothing to change in PrivateCellRoot or CellState.
- hot-path (no seat row now): per-entry persistence; the durable path still hashes whole lifecycle bytes
  (`ResourceBirthCodec.rootBytes`, `GuardedDurableCommit`): FORMAT (a) does not remove that linear work.
- perf-client (a8d456c6e773efbb8): the theorem relating `DeployedBridge.cellRoot` to the cell's `rootCache`.
- explorer: retired (a3e5d6dbcd68e616c → a8f1f44390a8e457d, stopped by ember). FORMAT (a)'s timing: member-side
  measures the authority cell in its next consent profile (baseline sent).
- /ci/pc on hbox is not this seat's (unknown owner; not removed).
