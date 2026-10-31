# Seat: privacy

Agent: a7bf41b0d8bb24813 (distilled from a3f7fce75cd3e4e49, retired; earlier: a8da2b953507b402b. Transcripts:
`cv show agent-a3f7fce75cd3e4e49`, `cv show agent-a8da2b953507b402b`).
Owns: private cells: `Compiler/PrivateCellRoot.lean`, `Compiler/PrivateCellIndex.lean`, `Kernel/PrivateCell*.lean`
(View, Scope, Receiver, Materializer, Opening), `Kernel/BlindedCellHiding.lean`, `Kernel/ReceiptEventHiding.lean`,
`Theory/PrivateCellTrie.lean`, `Theory/AuthTrieErase.lean`, `Theory/AuthTrieReveal.lean`, `Theory/CellStateAux.lean`
(the carried structure in `Theory/CellState.lean`), `Theory/FiniteTapeGap.lean`, `Theory/OracleGame.lean`,
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

## State (main 4038d3693)
- f28cd8457 FORMAT (a): `HyperdocumentCell.eventMaterializer` and `CredentialAuthorityCell.materializer` are
  `PrivateCellRoot.materializer _ (untagged _)`; `CanonicalCellRegistry` `saltedWire?`/`privateWire?`/
  `wire_salted_or_private`/`materializer_of_privateWire`/`privateWire_rootOf`; narrowed openings over salted wires
  only (`private_root_recomputes`); four census tags DREGG/PRIVATE-CELL/{ADDRESS,NODE,OUTER,CONTENT}/v1: a
  root-format epoch, fixtures re-record by the builder. Consumers repaired: `authorityRootBytes`, `fullRoot`, the
  weld's event root. Whole tree built on bb2 (all project modules). The WIP tag is deleted.
- 21cbfc7de fixed-size leaves: `deployedDig W T = pathDig ∘ nodeImage`; a leaf hashes 0, its 516-bit path packed to
  65 bytes, and `contentDigest` (cSHAKE256 under CONTENT/v1 over framed address bytes and value bytes): 98 bytes.
  The trie stays keyed by address (astra round 16). `DigestCollision`/`deployedDig_collision`;
  `PrivateCellTrie.tree_image` (naturality); the opening's witness reveals the path-keyed image (`imageEntries`,
  `innerRoot_image`), so every sibling, key and value is fixed-size; `openingRel_exact` has address, node, content
  and outer alternatives; `honest_rel` complete with distinct paths.
- f9fcaa25b: `Kernel/PrivateCellOpening.lean` (the fixed relation) and `Theory/OracleGame.lean` (costed ROM proof
  systems: OCircuit prover/verifier/simulator/extractor with sizes, query-bounded adversaries, KnowledgeSound,
  ZeroKnowledge, Sized; Echo satisfiable; reveal_refuted, acceptAll_refuted).
- Earlier (predecessor): receipt hiding, trie erase as a heap program, scoped reveals, the Store adapter, the
  receiver (`KeptCell`, custody PRF hop, `hiding_of_hybrids` with zk, rom, identical open), the private root.

## Next, in order
1. The circuit pinned (astra round 15 item 2). Done: the bounded shape (`Shaped` in `OpeningRel`, 4038d3693;
   `AuthTrieReveal.walkReveal_short_stop`). Owed: the opening's `OracleGame.Codec` (statement bits: root, cell,
   version, scope, the view's framed entries; witness bits: mask, inner digest, per prefix siblings padded to the
   prefix length with private selectors, one optional terminal (path, digest), the members under the prefix), and
   an `EmittedCircuit` per public width: an AirFlatten gate list over ZMod 2 WITH its acceptance output wire
   (`flatten_constraint_iff`; conjoin checks, never sum residuals over F2), sound (acceptance → `OpeningRel` of the
   decoded witness), complete (`OpeningRel` → the encoded witness accepts), gate count bounded by the width; strict
   canonical order of the answered entries.
2. The Keccak/cSHAKE gadget (statement first: acceptance equals `Sp800185Cshake256.hash` on the deployed framing).
3. The backend: MPC-in-the-head over the linearized circuit as an OracleGame `System`, straight-line extraction from
   the logged commitment preimages (round 15 item 6).
4. The receiver adapter (round 15 items 7, 8), then `zk` of `hiding_of_hybrids` discharged; epoch (b): content and
   declared kinds onto the private root.
5. The binding reduction for the private root (equal roots → equal stores ∨ a named collision), owed since round 13.
6. FORMAT (a)'s timing: member-side (ab7b4fe7fb687e0ca) measures the authority cell. Baseline b9450147f:
   doc-log write ~2.0 s at 13 prior entries, ~4.0 s at 103, ~6.1 s at 303; delegate ~2.5 s at 13, ~4.1 s at 303.

## Seams
- store-retained (a9b54e85e4a194b91): L0's Store (landed 802ba8c69); narrowed views are `SparseMap.filterKeys`.
- member-side (ab7b4fe7fb687e0ca): told the authority root is the kept trie since f28cd8457 (a patched cell's root
  in O(delta · 516) walks); it rewords `AuthState.revoked`/`Parentage.support` in Theory/TypedAuthorization.
- build-loop (a6c58cb72b0764dbb): seam 1 on main (f2002e589); named codec tags in `Compiler/PersistedCodecTags/Core.lean`,
  census-only tags (all four PRIVATE-CELL tags) in `Compiler/PersistedCodecTags.lean`; never add an import of the
  census. Told of the epoch (fixtures re-record) and the bb2 Mathlib permission failures.
- hot-path (no seat row now): per-entry persistence; the durable path still hashes whole lifecycle bytes
  (`ResourceBirthCodec.rootBytes`, `GuardedDurableCommit`): FORMAT (a) does not remove that linear work.
- perf-client (a8d456c6e773efbb8): the theorem relating `DeployedBridge.cellRoot` to the cell's `rootCache`.
- explorer: retired (a3e5d6dbcd68e616c → a8f1f44390a8e457d, stopped by ember). FORMAT (a)'s timing: member-side
  measures the authority cell in its next consent profile (baseline sent).
- /ci/pc on hbox is not this seat's (unknown owner; not removed).
