# Seat: privacy

Agent: a8da2b953507b402b (about 470K tokens after five distills; a fresh seat takes over from this file).
Owns: private cells: `Compiler/PrivateCellRoot.lean`, `Compiler/PrivateCellIndex.lean`, `Kernel/PrivateCell*.lean`
(View, Scope, Receiver, Materializer, Opening), `Kernel/BlindedCellHiding.lean`, `Kernel/ReceiptEventHiding.lean`,
`Theory/PrivateCellTrie.lean`, `Theory/AuthTrieErase.lean`, `Theory/AuthTrieReveal.lean`, `Theory/CellStateAux.lean`
(the carried structure in `Theory/CellState.lean`), `Theory/FiniteTapeGap.lean`, `docs/RATCHET-LOG-DESIGN.md`.
Quest: blinded cells (content, declared kinds) on a private authenticated map with O(log n) writes and bounded reads,
hidden by a fresh outer mask per version and a zero-knowledge complete selective opening; and the unblinded
growing kinds on the same trie root now (FORMAT (a)). Never trade hiding for speed.

## Worktrees and boxes
- Mac: `/Users/ember/dev/minidregg-lanes/privacy` (branch `seat/privacy`, tracks `main`; commit by path, `git pull
  --rebase origin main`, `git push origin HEAD:main`). The old lane branch `lane/private-cells` is deleted.
- hbox: pool tree t1, leased to `private-cells` (`. /home/hbox/pool/pool.env; cd /home/hbox/pool; bin/lane-tree
  acquire private-cells origin/main`). Rsync edited files into `/home/hbox/pool/t1/`, then
  `SWARM_MEM_MAX=28G scripts/pipeline/lane-check <files>` (rebuilds stale imports, then elaborates). Logs and PID
  files in `/home/hbox/pool/logs-pc/`. Whole tree when a shared interface moves: `SWARM_MEM_MAX=28G swarm-build lake
  build Theory Kernel Compiler Minidregg Host` (not Assurance; add it when touching roots it pins). The planted receipt
  test: `lake env lean --load-dynlib=.lake/native/libmini_kernels_lean.so tests/lean/ReceiptEventLinking.lean`.
- Reviews: codex astra as peer, `codex exec -m gpt-6-astra -s read-only -C <worktree> "<prompt>"`, nohup with a PID
  file in the scratchpad. Keystone statements also go to the integrator (aec6914709d96f496) for a sub-Opus audit.

## State (main 36c717bd9 and before)
- On main: K-RECEIPT-HIDE (receipt event ids hash the signed ingress; `DeclaredReceiptHiding`); the trie erase as a
  heap program (`erase_cost` 7L+3), scoped reveal soundness and locality, `classRevealComplete`; the Store adapter
  (`indexExact`, `indexBindsData`); scope selection (`scopeSelectsVisible_checked`, `addressFits`); the seam
  (`viewOpeningExact_deployed`, witness); the receiver state machine (`KeptCell`, `accept_composite`, custody PRF
  hop `receiver_prf_hop[_view]`, `HidingSetting.hiding_of_hybrids`: zk, rom, identical stay open); kind-level context
  `kindCtx` (round 18), kind-level `CustodyDecode` with `cross_cell`, `custodyBytes_disjoint`, `declared_cross_cell`,
  `secretBytes_injective`; the carried structure (`Materialized.carried`, a Thunk; `ValidatedPatch.apply` moves it by
  `Carried.run`).
- 36c717bd9: `Compiler/PrivateCellRoot.lean` (private root, `Kept`/`aux`, `materializer`, `materializer_rootOf`,
  `rootAvailable`, `set_index`, generic over a wire and a `KeyTag`); the Kernel twins deleted (receiver and seam
  instantiate it at `kindTag`); `Kernel/PrivateCellOpening.lean` landed UNWIRED as a draft (not in `Kernel.lean`).
  lane-check of PrivateCellMaterializer and PrivateCellOpening was launched in t1 (`logs-pc/lc1.log`); read it first.

## FORMAT (a): eventHistory and authority onto the private root
Root's ruling: only the unblinded kinds that grow with history switch now; resourceBook and policySource are
one-address cells (the Book's entry redesign is hot-path's `Theory/CanonicalResourceBookEntries`, which then selects
`PrivateCellRoot.materializer bookWire (untagged _)`); content and declared kinds keep the salted ratchet until the
ZK opening (epoch (b)).
- The switch is tag `wip/privacy-format-a` (7e190a2d6), whole-tree RED: `eventMaterializer` and
  `CredentialAuthorityCell.materializer` := `PrivateCellRoot.materializer _ (untagged _)`; `CanonicalCellRegistry`
  `saltedWire?`/`privateWire?`/`wire_salted_or_private`/`materializer_of_privateWire`/`privateWire_rootOf`
  (`materializer_of_wire` now over `saltedWire?`); observation `openingView` over `saltedWire?` and
  `private_root_recomputes`; three `DREGG/PRIVATE-CELL/*` tags in `PersistedCodecTags` (move them into seam 1's layout).
- Reds to repair (consumers that pinned the salted roots): `Compiler/CredentialAuthorityPolicyRegistry` 945
  (`authorityRootBytes`), 1210, 1237, 1362, pins 1395/1397; `Compiler/CanonicalCellRegistry` 894/902, pins 1739/1743;
  `Kernel/ContentResource` 1883; `Assurance/DeployedCredentialLifecycle` 691/753/787/887 and pins;
  `Assurance/HyperdocumentLinkPageDurableWeld` 201/230/255 and pins.
- Rebase onto store-retained's L0 (a9b54e85e4a194b91, `lane/retained-l0`) when it lands: narrowed views become
  `SparseMap.filterKeys`; `PrivateCellRoot.maskOf_set_blind`/`index_set_blind` (`simp [Store.set,
  Function.update_of_ne]`) and the receiver's `DFinsupp.filter` lemmas (~1274-1330) need its lemmas.
- Owed (astra round 13): a binding reduction for the private root (equal roots → equal stores ∨ scoped outer/node
  collision ∨ live-address path collision; from `AuthTrie.Cache.root_lastVal_eq`, `indexExact`,
  `nodeBytesWith_injective`). Whole-cell bytes are still hashed on the durable path (`ServedBasis` 512 →
  `CredentialAuthorityDomainReceiver.cellRoot` → `ResourceBirthCodec.rootBytes`; `GuardedDurableCommit` 168): hot-path's
  per-entry persistence. perf-client (a8d456c6e773efbb8) wants the theorem relating `DeployedBridge.cellRoot` to the
  cell's `rootCache` (O(log n) pin judge) once (a) lands.
- Pairing: one epoch and one fresh genesis with hot-path's row 11, after iteration speed's seam 1; the fixtures
  re-record from the batch candidate (builder's rerecord stage).
- Measurement: explorer's driver `~/xp/pc.sh CAND TAG` on hbox. Baseline b9450147f: doc-log write ~2.0 s at 13
  prior entries, ~4.0 s at 103, ~6.1 s at 303; authority delegate ~2.5 s at 13, ~3.1 s at 103, ~4.1 s at 303.

## The ZK selective opening (epoch (b)'s prerequisite)
`Kernel/PrivateCellOpening.lean` (draft, unwired): `ProofSystem`, `Adversary`, `runReal`/`runSim`, `Complete`,
`SoundUpTo`, `MultiTheoremZK`; `Statement`, `projection` (index entries of the Visible filter), `EmittedOpening`
(sound against a gated store's private root, complete with witness size ≤ c₀ + c₁ (k + s + 1) 516),
`SelectiveOpening`, `selectiveOpening_exact`; poles `Ideal.complete/sound/zk`, teeth `reveal_refuted` (proved,
`count_disjoint`). Astra round 14 found, all open, in this order:
1. `ScopedCollision` lacks the scoped `AddressCollision` alternative of `viewOpeningExact` (paths may collide).
2. `scopeOf` is chosen by the implementation: derive the scope from the comparison (statement, authenticated store
   paths, the witness's decoded hash inputs) with membership and size bounds.
3. `bad`, `budgeted`, `tapes` are chosen by the implementation (`bad := True`, `budgeted := False` trivialize it):
   fix the adversary class outside, require meaningful distinguishers and positive tapes, price `bad`; add
   extraction or a direct collision reduction.
4. `MultiTheoremZK` has no simulator cost: a unique-witness relation lets an unbounded simulator recover the
   witness. Charge simulator runtime/oracle queries; model the joint oracle and stateful simulation for Fiat-Shamir;
   fresh coins per proof, not one tape plus an index.
5. The cost field proves nothing operational (`witSize := 0`): pin `accepts` to an emitted constraint system and the
   size to its encoding; bound witness construction, gates, proving and verifying; charge answer bytes.
6. Bind the version: an authenticated `(cell, version) → root` lookup or public metadata checked against the
   witness's custody decode.
Astra's design recommendation, adopted as the plan: keep cSHAKE256 and grow the compiler an exact Keccak/cSHAKE
gadget (framing, customization, padding) over `Compiler/Air` (`AirHash` has no deployed parameters or sponge);
backend by MPC-in-the-head over the linearized AIR (ZKBoo pattern) with an adaptive multi-theorem ROM transform;
masked Tower256 FRI would need simulation of every opening. Fixed depth 516 makes a bounded read's circuit size
independent of the store.

## Next, in order
1. Read `logs-pc/lc1.log`; fix forward if red.
2. Revise `Kernel/PrivateCellOpening.lean` for astra round 14 items 1-6, wire it into `Kernel.lean`, astra again,
   then send the statement with its ATLAS fields to the integrator for audit before proof work.
3. The Keccak/cSHAKE gadget in the compiler (statement first: the gadget's acceptance equals
   `Sp800185Cshake256.hash` on the deployed framing), then the opening relation emitted from it.
4. FORMAT (a): when L0 lands, rebase `wip/privacy-format-a`, repair the reds, the binding reduction, whole-tree build,
   land on main, tell hot-path row 11 and the explorer (measurement), delete the tag.
5. Epoch (b): the MPC-in-the-head backend, the receiver's custody op in the cell patch, the registry custody decode
   (`CanonicalCellRegistry.custodyDecode kind`), content and declared kinds switched, flatness-submit.

## Seams
- store-retained (a9b54e85e4a194b91): L0's Store; it repairs my DFinsupp-dependent files in its batch.
- hot-path (a8e4317c9e1574ca5 / ac53c05fe796e4294): row 11, per-entry persistence, the Book entries.
- perf-client (a8d456c6e773efbb8): the cellRoot ↔ rootCache theorem.
- explorer (a3e5d6dbcd68e616c): FORMAT (a) measurement on a hotpatch.
- integrator (aec6914709d96f496): statement audits.
- /ci/pc on hbox is not this seat's (unknown owner; not removed).
