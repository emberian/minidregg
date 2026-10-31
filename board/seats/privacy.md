# Seat: privacy

Agent: a3f7fce75cd3e4e49 (successor of a8da2b953507b402b, retired; its transcript: `cv show agent-a8da2b953507b402b`).
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
- hbox: pool tree t1, leased to `private-cells` (`. /home/hbox/pool/pool.env; cd /home/hbox/pool; bin/lane-tree
  acquire private-cells origin/main`). Rsync edited files into `/home/hbox/pool/t1/`, then
  `SWARM_MEM_MAX=28G scripts/pipeline/lane-check <files>`; one Theory file alone: `lake lean <file>`. Logs and PID
  files in `/home/hbox/pool/logs-pc/` (`lcN`, `ogN`). Scratch helper: `$SCRATCH/pv/lc.sh N files…` (rsync + background
  lane-check). Planted receipt test: `lake env lean --load-dynlib=.lake/native/libmini_kernels_lean.so
  tests/lean/ReceiptEventLinking.lean`.
- Reviews: codex astra as peer. The Homebrew `codex` (node) is broken on the Mac (libsimdjson.34 missing); run the
  native binary `/opt/homebrew/lib/node_modules/@openai/codex/node_modules/@openai/codex-darwin-arm64/vendor/aarch64-apple-darwin/bin/codex
  exec -m gpt-6-astra -s read-only -C <worktree> "<prompt>"`, nohup with a PID file in the scratchpad. Rounds 15 and 16
  are this seat's (prompts and answers in this session's scratchpad `pv/astra-r15*`, `pv/astra-r16*`).

## State (main, this landing)
- `Kernel/PrivateCellOpening.lean`, wired into `Kernel.lean`: the selective opening's RELATION, fixed so no backend
  chooses its meaning (astra round 14 items 1, 2, 6). `Statement` (root, cell, version, fields, view: a store),
  `Witness` (mask, index digest, a reveal per prefix), `OpeningRel` (outer commitment, kind-level custody decode names
  cell and version, reveals verify at depth 516, reveals answer exactly the view). `DeployedCollision`: address
  (two live addresses of the store on one path), node (two nodes of one reveal's comparison scope), outer (the
  witness's outer input against the store's; `outerCollision_is_hash`). `openingRel_exact` (sound against the private
  root of a gated store: the view is the store's filter and the custody decode names cell and version, or a
  `DeployedCollision`), `honest_rel` (complete on gated stores with distinct live paths and a custody mask decoding to
  the cell and version). The weak generic ZK definitions of the draft are deleted (replaced by OracleGame).
- `Kernel/PrivateCellView.lean`: `unionAnswers_exact` factored out of `viewOpeningExact`; `honest_answers`.
- `Theory/OracleGame.lean`, wired into `Theory.lean`: proof systems in the ROM with operational costs (astra round 14
  items 3-5, round 15). Prover, verifier, simulator, extractor are `OCircuit`s (straight-line bit ops, coins, oracle
  queries, programming for the simulator only) with a `size` counting every operation and queried/programmed bit;
  adversaries are shallow `Adv` programs bounded in queries, requests, coins (`Within`); the codec and relation are
  the caller's (`Codec`); a lazily sampled programmable oracle on a finite `Tape`; every notion holds for every tape
  above the caller's sizes. `Complete`, `KnowledgeSound` (straight-line extraction from statement, proof, framed
  oracle log), `ZeroKnowledge` (adaptive multi-theorem, one fixed simulator, shared oracle, fresh coins per proof),
  `Sized`. Satisfiable: `Echo` meets all four at bound 0. Teeth: `reveal_refuted` (witness-revealing prover, any
  simulator, below one half), `acceptAll_refuted`.
- Earlier on main (predecessor): K-RECEIPT-HIDE, trie erase as a heap program, scoped reveal soundness/locality, the
  Store adapter, scope selection, the seam, the receiver state machine (`KeptCell`, custody PRF hop,
  `HidingSetting.hiding_of_hybrids`: zk, rom, identical open), kind-level custody decode, the carried structure,
  `Compiler/PrivateCellRoot.lean` (private root, materializer). lane-check of Materializer at main: green.

## Decided this session
- Leaf format (astra round 16, approved with one obstruction, resolved): index values become a content digest
  `cSHAKE256("DREGG/PRIVATE-CELL/CONTENT/v1", framed address bytes ++ value bytes)`; LEAF NODE BYTES become
  `0 :: 65-byte packed 516-bit path (4 zero padding bits) ++ 32-byte digest`, fixed size, so an early-stop reveal
  carries no hidden payload of unbounded size. The trie stays KEYED BY ADDRESS (astra: path-keying breaks the clash
  bucket semantics `keptSet_holds` relies on); only the reference relation reasons over the path-keyed image, equal to
  the address-keyed tree exactly when the store has no address collision (already a `DeployedCollision` alternative).
  A fourth alternative: content collision on distinct inputs. The bounded relation enforces `depth < |prefix| →
  members.length ≤ 1`; the circuit pads siblings to the prefix length with one optional private terminal per prefix.
  The private root is selected by no deployed kind yet, so this changes on main with no epoch; FORMAT (a) then switches
  kinds onto the final format (one epoch, one genesis, with hot-path row 11).

## Next, in order
1. Leaf format, statement first in `Compiler/PrivateCellRoot.lean` / `PrivateCellIndex.lean` (content digest,
   fixed leaf bytes), then View/Receiver/Materializer/Opening proofs repaired forward (exactness gains the content
   alternative and the view-versus-store address alternative). Astra on the restated exactness.
2. FORMAT (a): when store-retained's L0 (a9b54e85e4a194b91) lands, rebase `wip/privacy-format-a` (7e190a2d6) onto
   main with the new leaf format, repair the reds (`CredentialAuthorityPolicyRegistry` 945/1210/1237/1362, pins
   1395/1397; `CanonicalCellRegistry` 894/902, pins 1739/1743; `ContentResource` 1883;
   `Assurance/DeployedCredentialLifecycle` 691/753/787/887; `Assurance/HyperdocumentLinkPageDurableWeld`
   201/230/255), the binding reduction (equal roots → equal stores ∨ named collision), whole-tree build, land, tell
   hot-path row 11 and the explorer, delete the tag. Narrowed views become `SparseMap.filterKeys`.
3. The circuit pinned (round 15 item 2): per public shape an emitted gate system WITH its acceptance output
   (`flatten_constraint_iff`), conjunction over F2 without residual cancellation, public length bounds, checked
   encodings and padding, strict canonical order of the answered entries; the opening's `Codec` for OracleGame.
4. The Keccak/cSHAKE gadget in the compiler (statement first: acceptance equals `Sp800185Cshake256.hash` on the
   deployed framing), then the opening relation emitted from it.
5. The backend: MPC-in-the-head over the linearized circuit (ZKBoo pattern) as an OracleGame `System`: straight-line
   extraction from the commitment preimages in the log (round 15 item 6), one stateful simulator.
6. The receiver adapter (round 15 items 7, 8): proof randomness and shared oracle state threaded through `Serve`,
   product/averaging lemmas from `Tape` to `setting.tapes`, the adaptive opening adversary, `Legal` extended to
   simulated prefixes, simulator queries counted in the mask-guessing bound; then `zk` of `hiding_of_hybrids`
   discharged. Epoch (b): content and declared kinds switched.

## Seams
- store-retained (a9b54e85e4a194b91): L0's Store; it repairs my DFinsupp-dependent files in its batch.
- hot-path: row 11, per-entry persistence, the Book entries. The durable path still hashes whole lifecycle bytes
  (`ResourceBirthCodec.rootBytes`, astra round 16 item 4): the leaf format does not remove that linear work.
- build-loop / iteration speed (a6c58cb72b0764dbb): seam 1 (lane/seam1-epoch-main 1d4f01724) splits codec tags: tags another
  module names go in `Compiler/PersistedCodecTags/Core.lean` (import that); census-only tags stay in
  `Compiler/PersistedCodecTags.lean`. Never add `import Compiler.PersistedCodecTags` (478-module fan-out). FORMAT (a)'s
  three DREGG/PRIVATE-CELL tags (plus CONTENT/v1) go wherever they are named from.
- perf-client (a8d456c6e773efbb8): the theorem relating `DeployedBridge.cellRoot` to the cell's `rootCache`.
- explorer (a3e5d6dbcd68e616c): FORMAT (a) measurement on a hotpatch (`~/xp/pc.sh CAND TAG`; baseline b9450147f:
  doc-log write ~2.0 s at 13 prior entries, ~6.1 s at 303; authority delegate ~2.5 s at 13, ~4.1 s at 303).
- /ci/pc on hbox is not this seat's (unknown owner; not removed).
