# Seat: privacy (handoff)

Last agent: a7bf41b0d8bb24813, wound down 2026-10-31 (ember handed editing to another agent). Earlier agents:
a3f7fce75cd3e4e49, a8da2b953507b402b. Read any of them with `cv show agent-<id>`, and one tool result with
`cv cat agent-<id> <tool_use_id>`. Nothing is running, no pool tree is leased, and no wip branch exists: everything
written is on main.

## What this seat owns
Private cells: blinded cells hidden from narrowed readers, with a proof that an attacker cannot tell two worlds apart
within a stated probability bound. Every per-write cost stays O(log n). Never trade hiding for speed.
- Root and index: `Compiler/PrivateCellRoot.lean`, `Compiler/PrivateCellIndex.lean`.
- The kernel: `Kernel/PrivateCellView.lean`, `PrivateCellScope.lean`, `PrivateCellReceiver.lean`,
  `PrivateCellMaterializer.lean`, `PrivateCellOpening.lean`, `Kernel/BlindedCellHiding.lean`,
  `Kernel/ReceiptEventHiding.lean`.
- Theory: `Theory/PrivateCellTrie.lean`, `AuthTrieErase.lean`, `AuthTrieReveal.lean`, `CellStateAux.lean` (and the
  carried structure in `Theory/CellState.lean`), `FiniteTapeGap.lean`, `OracleGame.lean`.
- The circuit: `Compiler/AirKeccak.lean`, `Compiler/AirCshake.lean`, `Compiler/AirKeccakCensus.lean`.
- `docs/RATCHET-LOG-DESIGN.md`.

## Landed on main (newest first)
- cf368e4fb, private root format v2. Inner digests are cSHAKE256 outputs (`Inner` = `Sp800185Cshake256.Output`, 32
  bytes) framed as their raw bytes.
  - Node bytes are fixed per variant: empty 1, branch 65, leaf 98 (`pathNodeBytes_length`). `outerInput` is the
    context and mask as framed lists, then the 32 inner bytes (`outerInput_injective`).
  - It corrects 21cbfc7de, whose `digestStream` framing ran 33 or 34 bytes by value and so leaked digest magnitude.
  - Tags DREGG/PRIVATE-CELL/NODE/v2 and OUTER/v2 make it the second root-format epoch after FORMAT (a). Build-loop
    re-records fixtures once from main's tip.
  - The framed custody decode in `Kernel/PrivateCellReceiver.lean` is cell identity, version, then exactly 32 secret
    octets (`framedDecode`, `custodyBytes`, `framedDecode_iff`, `framed_length`, `PublicShape`; teeth:
    `passThrough_not_publicShape`). Blinded kinds take it at epoch (b). `natDecode`'s mask grows with the secret, so it
    stays only in the receiver's ideal-setting instance.
  - `PrivateCellOpening.framed_outerBytes`: an accepted witness's outer input is a public frame of (cell, version),
    then 64 private octets.
- 6b104c63c, the public midstate. Blocks wholly inside the customization prefix are absorbed once from public data
  (`skip`, `midstate`, `padded_midstate`).
  - `Compiler/AirKeccakCensus.lean` checks the costs on every build by `#guard`. One round after `EmitShare.cse` is
    12,480 gates: 1,600 AND, 10,880 XOR, 1,600 zero checks (56,000 gates before CSE). A permutation is 38,400 AND.
  - Under the node customization `skip = 1`, so every node hash (input up to 135 bytes) is one permutation.
- aaec61fce, cSHAKE256 at a PUBLIC customization and input length as an Air system over `ZMod 2`
  (`Compiler/AirCshake.lean`).
  - Input bytes are 8 private wires each. Per block there is an XOR row, then `permSystem`.
  - `sponge_sound` and `cshake_sound`: the last row's first 256 bits are `cshake256Bytes cust input`.
  - `sponge_complete`: the canonical `spongeAsg` accepts on an injective layout disjoint from the input wires.
- 81afc7026, Keccak-f[1600] as an Air system over `ZMod 2` (`Compiler/AirKeccak.lean`).
  - `roundB_spec` agrees with the spec's `round`, and `round_accepts` holds as an iff.
  - `perm_accepts` holds per transition. `perm_sound`, `perm_complete` (via `traceAsg`) and `perm_trace_unique` follow.
  - Teeth: `round_refuses_flip`.
- 4038d3693, `Shaped` is now a conjunct of `OpeningRel`: an early-stop reveal carries at most one member
  (`AuthTrieReveal.walkReveal_short_stop`, `revealFor_shaped`).
- f28cd8457, FORMAT (a): the event log (`HyperdocumentCell.eventMaterializer`) and the authority cell
  (`CredentialAuthorityCell.materializer`) are rooted by `PrivateCellRoot.materializer` at the untagged paths.
- 21cbfc7de, path-keyed node image and content digest (`deployedDig = pathDig ∘ nodeImage`, `tree_image`). Its size
  claim is corrected by cf368e4fb.
- f9fcaa25b, the opening's fixed relation and its proof-system contract.
  - `Kernel/PrivateCellOpening.lean` holds `OpeningRel`. `openingRel_exact` is sound up to a named collision (address,
    node, content or outer), and `honest_rel` is complete.
  - `Theory/OracleGame.lean` holds ROM proof systems with operational costs: oracle-circuit prover, verifier, simulator
    and extractor; `KnowledgeSound` (straight-line); adaptive multi-theorem `ZeroKnowledge`; `Sized`.
- Earlier (predecessor): receipt hiding, trie erase as a heap program, scoped reveals, the Store adapter, and the
  receiver (`KeptCell`, the custody PRF hop, `hiding_of_hybrids` with premises zk, rom and identical open).

## Next steps, in order
The substrate (astra round 17) is the built Air rung over `ZMod 2`: `add'` is XOR, `mul'` is AND, and each constraint
is zero-checked alone. It is flattened by `AirFlatten`, emitted by `Emit`, and shared by `EmitShare.cse`
(`cse_emit_accepts_iff`). The parked AND/XOR network in ResearchWip (`ObliviousNetwork`, `BendProofKeccak`) keeps its
Bend consumers. It is never a second compiler for the opening.
1. **Circuit costs.** Done for the hash (census above). Owed: the opening circuit's own census once it exists, and the
   lowered cost on whichever backend is chosen (item 4).
2. **Custody bound.** Done (cf368e4fb). Owed at epoch (b): blinded kinds' blinding space as bytes with `framedDecode`,
   and the receiver's setting moved to it.
3. **The opening circuit**, per public shape, as an Air system over bits. Not started; no partial code exists.
   - Astra round 18's checklist:
     - `0 ≤ d ≤ |p|` with the stop depth PRIVATE. A public stop depth leaks hidden occupancy.
     - Occupancy, the early terminal's membership under `p.take d`, and its filtered answer under `p`.
     - Full-depth distinct paths, and exact binding to the public view. The verifier computes the opened class's
       subtree root natively from the view.
     - Selection among the constant empty digest, a leaf hash and the public subtree root, without exposing which.
     - Canonical packing of the 516-bit path.
     - The outer hash over `outerFrame` ++ 64 private octets (`framed_outerBytes`).
     - Serialize the selected reveals, and prove reconstruction preserves `OpeningRel`.
   - Cost: a field-scoped prefix pads to `|p| = 260` node hashes, about 10M AND.
   - Root-preserving savings to take first:
     - Reduce the `.code` and `.annotations` reader prefixes to their 3-bit family (prove the scope equivalence).
     - Normalize redundant prefixes.
     - Climb shared ancestors once (a multiproof).
4. **Evaluator and backend.**
   - The ZKBoo evaluator, derived from the emitted SSA, with outputs that are the residuals and every zero check kept,
     remains the reference backend, as does MPC-in-the-head (ZKBoo/KKW) over it.
   - Astra round 18 decided they are not the production backend: their proof size is linear in ANDs, hundreds of MB at
     this size. Production needs a SUCCINCT zero-knowledge argument.
   - The repo's committed/FRI/sumcheck stack is not yet a private argument: `CommittedTerminalFiatShamir` hashes the
     full word into the statement and has `W = Unit`. It is also odd-characteristic, so the `ZMod 2` system needs a
     proved Boolean lowering (bitness, AND `xy`, XOR `x + y − 2xy`) or a binary-field protocol.
   - Needed:
     - A hiding polynomial commitment, ZK sumcheck, authenticated queries and terminal linkage.
     - Composed straight-line extraction and a bounded simulator, instantiated in `OracleGame`'s contract with full
       domain separation and one shared oracle.
   - Cross-layer: agree with the committed-terminal stack's owner before building.
5. **Receiver adapter** (astra round 15, items 7 and 8).
   - Thread proof randomness and shared oracle state through `Serve`.
   - Product/averaging lemmas from `Tape` to `setting.tapes`.
   - The adaptive opening adversary, and `Legal` extended to simulated prefixes.
   - Simulator queries counted in the mask-guessing bound.
   - Then discharge `zk` of `hiding_of_hybrids`, and run epoch (b): content and declared kinds onto the private root.
6. **Binding**: the private root's reduction, equal roots → equal stores ∨ a named collision (owed since round 13).
7. **Optional, path compression** (round 18 item 1).
   - Patricia nodes over full-width hashed parameters keep collision resistance and lower typical depth.
   - A public cap needs completeness under adversarial insertions.
   - It changes roots: a new root-format version, never a reinterpretation of NODE/v2.

## FORMAT (a) performance (measured by member-side on persvati)
- Before the fixes, per-write cost grew with history: about 80 `doc new` took consent CPU 118 → 240 ms and Host CPU
  174 → 540 ms. The cause was cells decoded from bytes per write and rebuilt by `keptBuild`. O(delta·516) holds only
  for a cell patched from a held, forced pre-cell.
- Fixed for the consent walk by member-side's a014ff501 (reviewed by this seat). `Materialized.relativeTo held decoded`
  moves the held cell's index by `Carried.run` over `Patch.diff`. Consent then measured 95 → 91 → 111 → 188 → 110 → 104
  ms over 60 writes, close to flat. Decode and diff stay O(cell).
- Store-retained fixed the birth path (bdfa9428c, c3a28038a: `loadServedAuthorityHeld`).
- Still open: Host CPU grows 94 → 139 ms. Its `doc new` writer probably re-decodes the event-log cell; that is with
  store-retained. The other route, persisting the index beside the bytes, is hot-path's.
- Baseline before FORMAT (a), at b9450147f: doc-log write ~2.0 s at 13 prior entries, ~6.1 s at 303.

## Astra review state
Codex astra is the peer reviewer: `codex exec -m gpt-6-astra -s read-only -C <worktree> "<prompt>"`. On the Mac the
Homebrew `codex` (node) is broken (libsimdjson.34 missing); use the native binary at
`/opt/homebrew/lib/node_modules/@openai/codex/node_modules/@openai/codex-darwin-arm64/vendor/aarch64-apple-darwin/bin/codex`.
The prompts and answers for rounds 15–18 sit in the session scratchpad
`/private/tmp/claude-501/-Users-ember-dev-minidregg/01a192eb-6b7b-70ef-8cad-095d745dabe5/scratchpad/pv/astra-r1{5,6,7,8}.{txt,out}`,
and in agent a3f7fce75cd3e4e49's and a7bf41b0d8bb24813's transcripts.
- Round 14: the opening draft admitted degenerate backends. Replaced by f9fcaa25b.
- Round 15: the OracleGame shape; the receiver adapter items (7, 8).
- Round 16: fixed-size committed payloads; the trie stays keyed by address.
- Round 17: the Air substrate; per-transition permutation theorem; the custody size gap.
- Round 18: keep the root relation; the stop depth stays private; a succinct ZK backend; the Boolean lowering is
  needed for an odd-characteristic stack; the circuit checklist in item 3.
Item 3's design has not been reviewed beyond round 18's checklist.

## Boxes
- Mac worktree: `/Users/ember/dev/minidregg-lanes/privacy`, branch `seat/privacy`, clean and equal to main. Commit by
  path, then `git pull --rebase origin main` and `git push origin HEAD:main`.
- Builds run on hbox's pool: `ssh hbox`, `. /home/hbox/pool/pool.env`,
  `t=$(lane-tree acquire privacy origin/main); cd $t`, rsync edited files in, and
  `SWARM_MEM_MAX=28G scripts/pipeline/lane-check FILE...`; `lane-tree release privacy` when done. Measure on persvati.
  `exec` the build inside the script, so the PID file names the build process itself.
- dregg-build2 now belongs to obend. Its t4 is released, with the saved diff in `/srv/pool/saved`.
- hbox t1, leased as `private-cells`, is released; its stale `PrivateCellRoot` copy is in
  `/home/hbox/pool/saved/t1-private-cells-20261101T022127Z.patch`, superseded by cf368e4fb.
- No process of this seat is running on any box.
- Idle: persvati worktree `/home/ember/mdpool/lanes/privacy`.
- Not this seat's: `/ci/pc` on hbox (owner unknown, not removed).

## Seams
- store-retained (a9b54e85e4a194b91): L0's Store (802ba8c69, `SparseMap.filterKeys` for narrowed views); the held
  authority cell (bdfa9428c); the Host writers' held cells (open).
- member-side (ab7b4fe7fb687e0ca): the consent walk (`relativeTo`, a014ff501); the authority root is the kept trie.
- build-loop (a6c58cb72b0764dbb): codec tags. The PRIVATE-CELL tags are census-only, in
  `Compiler/PersistedCodecTags.lean`. Never add an import of the census. Fixture re-records happen at epochs.
- host-execution (a24974e84d3c540d1) and he-births (ac49ca4075452034f): the turn-of-intent epoch touches nothing here.
- hot-path (no seat row): per-entry persistence. The durable path still hashes whole lifecycle bytes
  (`ResourceBirthCodec.rootBytes`, `GuardedDurableCommit`).
- perf-client (a8d456c6e773efbb8): the theorem relating `DeployedBridge.cellRoot` to the cell's `rootCache`.
