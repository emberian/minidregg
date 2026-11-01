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
- Builds: hbox's pool (dregg-build2 now belongs to obend; t4 there is released, its copy of main saved in
  /srv/pool/saved). `ssh hbox`, `t=$(lane-tree acquire privacy origin/main); cd $t`, rsync edited files in,
  `scripts/pipeline/lane-check FILE...` under swarm-build; `lane-tree release privacy` when done. Build scripts
  `exec` the build so the PID file names it. Measure on persvati.
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
3. The opening system per public shape, as an Air system over bits (backend-independent). Astra round 18 checklist:
   `0 ≤ d ≤ |p|` with the stop depth private (a public stop depth leaks hidden occupancy); occupancy and the
   early terminal's membership under `p.take d` and its filtered answer under `p`; full-depth distinct paths and
   exact binding to the public view (whose class subtree root the verifier computes natively); selection among
   the constant empty digest, a leaf hash and the public subtree root without exposing the variant; canonical
   packing of the 516-bit path; the outer hash over its public frame (one or more permutations by alignment).
   Serialize the selected reveals and prove reconstruction preserves `OpeningRel`. Cost: a field-scoped prefix pads
   to `|p| = 260` node hashes, about 10M AND. Root-preserving savings first: `.code` and `.annotations` reader
   prefixes reduced to their 3-bit family (prove the scope equivalence), redundant prefixes normalized, one
   multiproof climb for shared ancestors.
4. The backend (decided, round 18): a SUCCINCT zero-knowledge argument, not MPC-in-the-head. ZKBoo/KKW stay a
   reference backend only (proof size linear in AND: hundreds of MB here). The repo's committed/FRI/sumcheck stack
   is not yet a private argument (`CommittedTerminalFiatShamir` hashes the full word into the statement, `W = Unit`),
   and it is odd-characteristic: the Air system over `ZMod 2` needs a proved Boolean lowering (bitness, AND `xy`, XOR
   `x + y - 2xy`) or a binary-field protocol. Needed: a hiding polynomial commitment, ZK sumcheck, authenticated
   queries, terminal linkage, composed straight-line extraction and a bounded simulator, instantiated in
   `Theory/OracleGame.lean`'s contract with full domain separation and one shared oracle. This is cross-layer:
   coordinate with the committed-terminal stack's owner before building.
5. The receiver adapter (round 15 items 7, 8), then `zk` of `hiding_of_hybrids`; epoch (b) (blinded kinds' blinding
   space as bytes with `framedDecode`).
6. Path compression (optional, round 18 item 1): Patricia nodes over full-width hashed parameters keep collision
   resistance and lower typical depth, but a public cap needs completeness under adversarial insertions and
   changes roots (a new root-format version, never a reinterpretation of NODE/v2).
7. The binding reduction for the private root (equal roots → equal stores ∨ a named collision).
8. FORMAT (a)'s timing, measured by member-side on persvati (world at 27f85e89, which includes f28cd8457):
   the claim fails as deployed. Over about 80 `doc new` writes, consent CPU per write goes 118 → 240 ms and Host CPU
   174 → 540 ms, with `AuthTrie.strip` (whole-trie build) and keccak on top. Cause: cells are decoded from bytes per
   write and rebuilt by `keptBuild`; O(delta·516) holds only for cells patched from a held, forced pre-cell.
   Fixes: member-side's a014ff501 (reviewed) adds `Materialized.relativeTo held decoded` to `Theory/CellState.lean`
   (the held cell's index moved by `Carried.run` over `Patch.diff`; `relativeTo_eq`), used by `loadDeploymentFromAt`
   on a walk, so hashing is O(changed · 516); decode and diff stay O(cell). Measured by member-side on persvati
   (fresh worlds, 60 `doc new` in blocks of 10): consent CPU per write 110 → 108 → 131 → (533) → 227 → 173 ms on
   base 4b750eb67, and 95 → 91 → 111 → 188 → 110 → 104 ms with a014ff501, close to flat. Host CPU still grows,
   94 → 139 ms with it. Still open: the Host's writers
   adopt the held post-cell as the birth path does (store-retained, bdfa9428c); or the index is persisted beside
   the bytes (hot-path). Re-measure against the baseline once they land: b9450147f doc-log write ~2.0 s at 13
   prior entries, ~6.1 s at 303.

## Seams
- store-retained (a9b54e85e4a194b91): L0's Store (landed 802ba8c69); narrowed views are `SparseMap.filterKeys`.
- member-side (ab7b4fe7fb687e0ca): told the authority root is the kept trie since f28cd8457 (a patched cell's root
  in O(delta · 516) walks); it rewords `AuthState.revoked`/`Parentage.support` in Theory/TypedAuthorization.
- build-loop (a6c58cb72b0764dbb): seam 1 on main (f2002e589); named codec tags in `Compiler/PersistedCodecTags/Core.lean`,
  census-only tags (all four PRIVATE-CELL tags) in `Compiler/PersistedCodecTags.lean`; never add an import of the
  census. Told of the epoch (fixtures re-record) and the bb2 Mathlib permission failures.
- host-execution (a24974e84d3c540d1) measured 14% of `doc new` in rebuilding the authority trie. Cause:
  `CredentialAuthorityDomainReceiver.loadDeploymentAt` decodes the cell from bytes per load, and each fresh
  `Materialized` builds its index on its first root read; patches already carry it. Fixed by store-retained
  (bdfa9428c, c3a28038a: the session holds the light birth's validated post-cell, and
  `loadServedAuthorityHeld` takes it when the served bytes are its bytes). Writers other than the ordinary birth
  still re-decode; host-execution measures the 14% on the next candidate.
- hot-path (no seat row now): per-entry persistence; the durable path still hashes whole lifecycle bytes
  (`ResourceBirthCodec.rootBytes`, `GuardedDurableCommit`): FORMAT (a) does not remove that linear work.
- perf-client (a8d456c6e773efbb8): the theorem relating `DeployedBridge.cellRoot` to the cell's `rootCache`.
- explorer: retired (a3e5d6dbcd68e616c → a8f1f44390a8e457d, stopped by ember). FORMAT (a)'s timing: member-side
  measures the authority cell in its next consent profile (baseline sent).
- /ci/pc on hbox is not this seat's (unknown owner; not removed).
