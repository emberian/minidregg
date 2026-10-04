# WEBSITE-CORRECTIONS: website/*.html audited against minidregg main 5216e02f

Audited: `website/index.html`, `why.html`, `architecture.html`, `maturity.html`, `laws.html`, `website/README.md`, `website/css/site.css` (the css carries no claims; its only `::before`/`::after` rules are layout resets).
Ground truth: this repository at main 5216e02f (all evidence paths below are relative to the repository root). Entry points read: `README.md` (Honest state table), `docs/OBJECTIVE-BEND.md`, `PROJECT.md`, `docs/README.md`, `lakefile.toml`, `Minidregg.lean`, `Deployed.lean`, `Selvage.lean`, `docs/SELVAGE-COMPLETE.md`, `docs/PROOF-SYSTEM-SURVEY.md`, `docs/PROVER-PLAN.md`, `GOAL.md`, `ATLAS.md`, `CLAUDE.md`, `AGENTS.md`, plus the Lean/Rust sources named per entry.
Method: every site sentence was compared to those files and to the source modules they name. Counts are lexical (`find ... -name '*.lean' | xargs cat | wc -l`, `grep -c`), not semantic, and include comments and docstrings. No builds, no network, nothing run beyond grep/find/wc/sed.
Tags: READ = I read the cited source and it says this. INFERRED = follows from sources I read but no single line states it. (RUN is not used.)
Policy applied: a claim is listed as wrong if main contradicts it, OR if it states a state of the world that README.md's Honest state table grades lower (README grades by evidence class: authored, compiled, executed, integrated, deployed). Where main's own older documents (`PROJECT.md`, `docs/PROVER-PLAN.md`) disagree with the source, the source wins (README.md, "Where the design records live"), and the entry cites the source.
Line numbers are the site file's line numbers.

Review note (lane S12-DOCS-TRUTH): this list was produced by a read-only audit pass and then spot-checked by the lane against main: `Loom/` and `docs/LOOM-RECOMPOSITION.md` and `docs/decisions/D-0004-why-loom.md` do not exist while `Selvage/`, `docs/SELVAGE-RECOMPOSITION.md` and `docs/decisions/D-0004-why-selvage.md` do; `Kernel/DeclaredHyperedge.lean` does not exist; the Lean line count (516,811 over 1,651 files outside `.lake`, `vendor/`, `scratch/`, `world/`, `examples/`) was reproduced. The site files themselves are unchanged. Applying a replacement is a separate edit (cv 01a104f3-e35e).

Headline findings:
1. The proof system is called **Selvage** on main, not Loom. There is no `Loom/` directory, no `docs/LOOM-RECOMPOSITION.md`, no `docs/decisions/D-0004-why-loom.md` (the file is `D-0004-why-selvage.md`).
2. The product is **Mini**: README.md line 1 is "# Mini". The repo and the host binary (`minidregg-host`) keep the name minidregg. The site never mentions Objective Bend, Nock, SPK, Hermes, the agreement mesh or the deos/docuverse world.
3. "Proof-native" is no longer defensible as a headline: `README.md` (Selvage section) says "No world admission uses a proof today; admission is checked by re-execution", and `Deployed.lean` lines 9-11 say the same and leave Selvage out of the deployed umbrella.
4. Three concrete caveats on the site have since changed: the "uninhabitable deployed schemas" vacuity is closed (2026-08-11); `Kernel.DeclaredHyperedge` is deleted; the durable-settlement "no torn record, no fsync" residual is partly obsolete.
5. The clause-406 card claims D and B; the site's own legend and `docs/PROVER-PLAN.md` do not support either.

---

## index.html

**IDX-1** (lines 6, 9, 17, 191; also 37, 130) Name of the product.
- Quote: `<title>minidregg — proof-native semantic computer</title>`; `minidregg is a Lean-owned kernel for authorized state change`.
- Main: README.md line 1 is "# Mini" and line 3 "A programmable shared world for people and agents." "Mini is the construction home of the next Dregg" (README.md lines 5-6). `AGENTS.md` line 1: "Working on Mini". The repo/package name stays minidregg (`lakefile.toml` line 1 `name = "minidregg"`; `Host.Main` is `minidregg-host`). Tag: READ.
- Replacement: "Mini is a programmable shared world for people and agents, built in Lean with a Rust physical boundary, and its repository is emberian/minidregg."

**IDX-2** (lines 6, 34-35) "proof-native".
- Quote: `minidregg — proof-native semantic computer`; `A proof-native semantic computer.`
- Main: README.md "Selvage" section: "No world admission uses a proof today; admission is checked by re-execution." `Deployed.lean` lines 9-11: "Mini admits by re-execution, not by proof (decision 10-01), so no deployed module needs [Selvage]." README.md Honest state row "Oblivious and zk execution of Objective Bend": "authored, conditional". (`CLAUDE.md` line 5 still says "The proof-native semantic computer", so the phrase survives only in a session-rules file.) Tag: READ.
- Replacement: "Mini is a Lean-owned semantic kernel that admits changes by re-execution; Selvage, its proof-system research layer, is not on the admission path today."

**IDX-3** (lines 36-39) Lede.
- Quote: `typed requests, multi-cell hyperedges, heterogeneous proofs, and causal documents that agents and humans can actually inspect.`
- Main: README.md lines 15-27 (design paragraph): "Every change is a proposal that the Lean kernel admits or refuses against current capabilities, laws, exact read roots and funding"; proofs appear only in "Selvage, the proof-system research layer". "Heterogeneous proofs" is a Selvage research goal (`docs/decisions/D-0004-why-selvage.md`), not a feature of the admitted path. Tag: READ.
- Replacement: "Mini is a Lean-owned kernel that admits or refuses each proposed change against current capabilities, laws, exact read roots and funding, and keeps a durable outcome for every admitted change."

**IDX-4** (lines 7, 9, 75-79) Loom.
- Quote: `Lean-owned semantic kernel · Loom proof fabric · Hyperdocuments`; card "Loom — Heterogeneous proof fabric: binary fields, prime fields, lookup/RAM, FHE rings, privacy, and history meet at checked joints."
- Main: the proof system is Selvage: `Selvage.lean` header "Selvage — the proof system"; `lakefile.toml` "Selvage/ — the proof system"; `docs/decisions/D-0004-why-selvage.md` line 1 "Selvage as heterogeneous proof-assurance fabric"; README.md "Selvage is Mini's proof-system research and construction layer: hash-based, small-field machinery for proximity testing, sumcheck, transcript compilation, accumulation and verifiable history". "Meet at checked joints" overstates: `docs/SELVAGE-COMPLETE.md` lines 5-6: "not one deployed succinct ZK proof system". Tag: READ.
- Replacement: "Selvage is the proof-system research layer: hash-based, small-field machinery for proximity testing, sumcheck, transcript compilation, accumulation and verifiable history, with explicit security assumptions and bounds."

**IDX-5** (lines 50, 93-94) Native boundary slogan.
- Quote: `Lean owns meaning. Native code returns bytes or fails.`
- Main: true of the Selvage/prover boundary (`prover/src/lib.rs` lines 1-6), but README.md lines 19-24 describe a much wider Rust side: "clients, signing and custody, storage, transport and hosted-service adapters", under `native/` (about 25 crates and sources), which "decides nothing semantic". Tag: READ.
- Replacement: "Lean owns semantics and admission; Rust owns the physical boundary (clients, signing and custody, storage, transport and hosted-service adapters) and decides nothing semantic."

**IDX-6** (lines 61-63, 154-163) The S/A/P/D/B maturity scheme as the site-wide labelling.
- Quote: `Each pillar advances through explicit maturity boundaries (S → A → P → D → B).`; `Every substantial claim is labeled by the strongest boundary actually closed: S A P D B`.
- Main: S/A/P/D/B is the proof-system grading (`PROJECT.md` "Maturity boundaries", `docs/PROVER-PLAN.md` "Maturity labels", `docs/SELVAGE-COMPLETE.md` "Boundary legend"). README.md's Honest state table grades every world component by evidence class: authored, compiled, executed, integrated, deployed. Tag: READ.
- Replacement: "Mini grades each component as authored, compiled, executed, integrated or deployed in the README Honest state table, and grades proof-system claims separately on the S, A, P, D, B boundaries of PROJECT.md."

**IDX-7** (lines 82-88) Hyperdocuments card.
- Quote: `Proof-native causal medium: typed content, transclusion, backlinks, offline branches, explicit conflicts, versioned history.`
- Main: README.md "What lives here": "Shared documents with transclusion, history, marks and protected fragments", and the Honest state row "Native Host, shell, documents, journey J0–J8" is graded deployed on the public node. Offline-branch merge with conflict records is S/A only: `PROJECT.md` "Hyperdocuments" residuals include "one real offline merge UI" (Ordered frontier item 6); the merge semantics are in `Kernel/HyperdocumentMerge.lean` lines 1-12. "Proof-native" has no basis (see IDX-2). Tag: READ (documents row mapping to Hyperdocument modules is INFERRED).
- Replacement: "Documents carry transclusion, history, marks and protected fragments and run on the public node's 2026-10-01 candidate; offline-branch merge with explicit conflict records is formalized in Lean (Kernel/HyperdocumentMerge.lean) but has no merge UI yet."

**IDX-8** (lines 100-123) "What you should be able to ask".
- Quote: `Can I hand a compact proof of this history to another device?`; agent list `Branch offline and merge without erasing provenance`, `Invoke sealed computation without disclosure authority`.
- Main: `PROJECT.md` "Outcome first" states these as "The finished system should let a user ask", i.e. targets. No compact history proof is produced: admission is by re-execution (README.md Selvage section) and the Selvage history checkpoint is "no succinct deployed checkpoint" (`docs/PROVER-PLAN.md` controller table, "semantic history" row). README.md: "None of these [private execution paths] executes a member's program privately today." Tag: READ.
- Replacement: "PROJECT.md lists these as the questions the finished system should answer; today no compact history proof is produced, and no private execution path runs a member's program privately."

**IDX-9** (lines 127-134, 128) "The derived path is the only path" read as a present-tense state.
- Quote: `The derived path is the only path.` / `Here, nothing lands beside what it supersedes.`
- Main: this is a design law (`ATLAS.md` section 1, `CLAUDE.md` first law), not a measured state. The tree still has `Effects/Placeholder.lean` standing in for the open registry (`Effects.lean` line 3 "the REMAINING registry carve"), hand-written Assurance files (`ATLAS.md` lines 274-275: "as of 2026-09-30 every Assurance/ file is hand-written and nothing is generated"), and hand-written Rust mirrors of Lean checks that `prover/src/sumcheck.rs` and `prover/src/rank1.rs` label "UNVERIFIED COMPUTE". Tag: READ.
- Replacement: "The derived path is Mini's design rule (ATLAS.md section 1); the tree still contains hand-written Assurance files and unverified Rust mirrors of Lean checks that are labeled as such."

**IDX-10** (lines 167-172) Status of the project.
- Quote: `Frontier research, not a product. This is a frontier research stack.`
- Main: README.md Honest state: "Native Host, shell, documents, journey J0–J8 | deployed | public node runs the 2026-10-01 candidate; no outside member enrolled yet"; rooms/invitations integrated; SPK hosted apps integrated. Only the proof-system layer (Selvage) and private/oblivious execution are research. Tag: READ.
- Replacement: "Mini has a native Host deployed on a public node (2026-10-01 candidate, no outside member enrolled yet), while Selvage and private execution remain research."

**IDX-11** (lines 168-171) Stale vacuity caveat.
- Quote: `some deployed schemas are still uninhabitable.`
- Main: closed 2026-08-11. `CellState.FieldStore` is a canonical dependent finite map; `Theory.DeployedMaterializerWitness` and `Kernel.DeployedMaterializerWitness` exhibit materializers and cells for all four deployed schemas (`PROJECT.md` "Resolved caveat (2026-08-11)", lines 219-226; `GOAL.md` lines 442-466 "THE MATERIALIZER FINDING — CLOSED 2026-08-11"; `Theory/MaterializerCardinality.lean` lines 1-12). Tag: READ.
- Replacement: "The 2026-08 materializer vacuity (a total-function field carrier with no materializer) was closed on 2026-08-11 by a finite-map carrier, with the old carrier kept as a regression tooth in Theory/MaterializerCardinality.lean."

**IDX-12** (lines 33-46, whole page) Language and product names missing.
- Main: README.md "Objective Bend is Mini's only Bend language"; docs/README.md line 5: "Objective Bend is its central authored language"; Core4 is the live core, BendTT the retiring Gen-1 core (README.md Honest state, Layout rows). The page names none of Objective Bend, Core4, Nock, SPK, Hermes, deos/docuverse, agreement mesh. Tag: READ.
- Replacement: "Objective Bend, a lazy open-recursion language over first-class partial specifications with Core4 as its core, is Mini's only Bend language and its central authored language."

Checked and consistent: "Sixteen design laws" (`ATLAS.md` section 6 has 16); "Statement-first. Keystones enter as propositions with satisfiability, teeth, and premise-inhabitation" (`ATLAS.md` law 2, `CLAUDE.md`); four pillar one-liners for the semantic kernel and compiler boundary (`PROJECT.md` "Hard invariants").

---

## why.html

**WHY-1** (lines 57-59) Size budget.
- Quote: `minidregg budget | ≤10% (~290K) | analysis says we need far less`.
- Main: `ATLAS.md` line 14 sets the budget and line 287 projects "Rough total: 100–150K lines". Current tree, lexical `wc -l`: about 516,811 lines of Lean (excluding `.lake`, `vendor/`, `scratch/`, `world/`, `examples/`; 517,483 with them) across about 1,660 files, plus 283,938 lines of Rust under `native/` and `prover/` (487 files). By directory: Theory 213 files / 85,054 lines; Kernel 498 / 151,682; Compiler 382 / 94,557; Selvage 152 / 78,011; Assurance 157 / 58,964; Host 131 / 35,164; Pred 10 / 4,403; Effects 2 / 436; Verify 16 / 1,660. Tag: READ (counts by grep/wc; lexical, include comments).
- Replacement: "ATLAS.md set a budget of 10% of breadstuffs (about 290K lines) and projected 100 to 150K, and the tree now holds about 517K lines of Lean and 284K lines of Rust by a lexical line count."

**WHY-2** (lines 162-173, 175-181) "Why Loom".
- Quote: `Why Loom (not one universal field)`; `Loom owns the joints: roots-before-challenges control, explicit failure events and error budgets, ...`; `if Loom's joins do not remove duplication ... we replace it.`
- Main: `docs/decisions/D-0004-why-selvage.md` lines 1-12: "Keep Selvage as the proof-theoretic composition and assurance layer"; its "falsifiable" status is accurate. The older `docs/SELVAGE-RECOMPOSITION.md` line 1 still carries the title "LOOM" but states "Working name Selvage". Tag: READ.
- Replacement: "Selvage owns the typed joints between native dialects: roots-before-challenges transcript causality, exact security and error regimes, checked common-opening relations, native-failure non-authority, and proof-carrying history attribution (docs/decisions/D-0004-why-selvage.md)."

**WHY-3** (lines 186-191) Further reading path.
- Quote: `<code>docs/decisions/D-0004-why-loom.md</code> — Loom decision record`.
- Main: file does not exist; it is `docs/decisions/D-0004-why-selvage.md`. Tag: READ (ls).
- Replacement: "docs/decisions/D-0004-why-selvage.md is the decision record for keeping Selvage as the proof-assurance layer."

Checked and consistent: `ATLAS.md` section 0 figures reproduced exactly (see "unverifiable" for breadstuffs-side numbers); "Four substances", "One Pred algebra, four polarities", "Spine in five words" match `ATLAS.md` section 2; `PROJECT.md` and `docs/PROOF-SYSTEM-SURVEY.md` ("the backend decision") exist and match their descriptions.

---

## architecture.html

**ARCH-1** (line 7) Meta description.
- Quote: `How minidregg is carved: Theory, Kernel, Loom, Hyperdocuments, Compiler, and the narrow waist`.
- Main: `Minidregg.lean` line 15 `import Selvage -- the proof system`; no `Loom` library in `lakefile.toml`. Tag: READ.
- Replacement: "How the repository is carved: Theory, Kernel, Pred, Effects, Compiler, Selvage, Assurance, Host and prover, with one canonical semantic event as the narrow waist."

**ARCH-2** (line 58) Diagram node.
- Quote: `physical handler       Loom proof/checkpoint`.
- Main: `PROJECT.md` "Target composition" has the same diagram with "Selvage proof/checkpoint". Tag: READ.
- Replacement: "In the target composition the causal receipt and history feed a Selvage proof or checkpoint."

**ARCH-3** (lines 120-123) Repo carve row `Loom/`.
- Quote: `Loom/ | Proof fabric: FRI regimes, sumcheck, proximity, light client shapes, ZK games, sponge/ROM.`
- Main: no `Loom/`; the directory is `Selvage/` (152 Lean files, 78,011 lines; `Selvage/LightClient*.lean`, `Selvage/Sumcheck.lean`, `Selvage/Additive*`, `Selvage/BaseFold*`). It may import only Mathlib, Theory and Selvage (`scripts/check-import-boundary.sh` lines 4-13). README.md Layout: "`Selvage/` | proof-system research". Tag: READ.
- Replacement: "Selvage/ is the proof-system research library (proximity testing, sumcheck, accumulation, light-client and zero-knowledge games, sponge/ROM), and it imports only Mathlib, Theory and Selvage."

**ARCH-4** (line 155) Pillar badge.
- Quote: `<div class="num">LOOM</div>`.
- Main: see ARCH-3. Tag: READ.
- Replacement: "SELVAGE: heterogeneous dialects, owned joints."

**ARCH-5** (lines 100-103) `Theory/` row.
- Quote: `Candidate-independent core: verify/find seam, cameras, verbs, governed dynamics.`
- Main: `Theory/Knowledge.lean` is the verify/find seam (`Theory.lean` line 8) and `Theory/AdversarySchema.lean` is `GovernedDynamics`. There are no camera modules in Theory/ (`grep -rli camera Theory Kernel` finds only a comment in `Theory/ReactiveReceipt.lean` line 134 and the word in `AdversarySchema.lean`), and the three verbs `create`/`gwrite`/`move` live in `Kernel/Verbs.lean` and `Kernel/State.lean`/`Turn.lean`, not Theory. Theory also holds Objective Bend Core4 (`Theory/ObjectiveBend*.lean`), Nock, the store and cell-state model (README.md Layout row). Tag: READ.
- Replacement: "Theory/ holds the candidate-independent semantics, including the verify/find seam (Theory/Knowledge.lean), GovernedDynamics, the typed store and cell state, and Objective Bend Core4, and it imports only Mathlib and Theory."

**ARCH-6** (lines 112-115) `Effects/` row.
- Quote: `Open effect-spec surface from which executor equality, descriptors, and teeth are derived.`
- Main: `Effects/` has two files (436 lines): `EffectSpec.lean`, which derives term, executor and descriptor for one declaration (`moveEffect`), and `Placeholder.lean`, the "carve marker" for the open registry (`Effects.lean` lines 4-5 and `Effects/EffectSpec.lean` lines 1-30). Teeth/witnesses exist for that one effect only. Tag: READ.
- Replacement: "Effects/ contains the EffectSpec derivation engine with one derived declaration (the kernel move effect) and a placeholder for the open handler registry that is still to be built."

**ARCH-7** (lines 128-131) `prover/` row.
- Quote: `Opaque fallible native compute + generated dispatch glue. Authors nothing semantic.`
- Main: broadly right, but `prover/src/lib.rs` lines 1-6 describe "the one protocol-shaped resident ... `sumcheck` ... an unverified mirror", and `prover/src/rank1.rs` mirrors `Selvage/Rank1GradientCheck.lean`; `prover/generated/evm_stage0_add_aux.rs` is generated gate-row data (work 9103). Tag: READ.
- Replacement: "prover/ is unverified native compute (field, transform, hash and MLE kernels, a sumcheck engine and a rank-1 gradient check mirrored from Lean and tied to it only by conformance vectors) plus Lean-generated artifact dispatch, and it holds no semantic authority."

**ARCH-8** (lines 94-132, table) Trees missing from the carve.
- Main: README.md "Layout" also lists `Host/` (the native receiving process; `lakefile.toml` `minidregg-host`), `Verify/`, `native/` (the Rust `mini` client, SPK host, grain runtime, stores, agreement crypto, private backend, FHE, Discord, pay watcher), `protocol/`, `scripts/`, `deploy/`, `testing/`, `tests/`, `examples/`, `world/`, `vendor/bend/`, `website/`. Tag: READ.
- Replacement: "Besides the semantic libraries, the repository holds Host/ (the native receiving process), Verify/, native/ (Rust clients, SPK host, grain runtime, stores and agreement crypto), protocol/, deploy/ and scripts/."

**ARCH-9** (lines 176-181) Stale caveat.
- Quote: `Current caveat: some document cells are still uninhabitable at deployed schemas (infinite total-function logical state).`
- Main: closed 2026-08-11; same evidence as IDX-11 (`PROJECT.md` lines 219-226, `GOAL.md` lines 442-466, `Theory/MaterializerCardinality.lean` lines 1-12). Tag: READ.
- Replacement: "The former total-function field carrier, which left document cells without a materializer, was replaced by a finite-map carrier on 2026-08-11; the witness codecs are existence codecs and the roots are non-cryptographic, so concrete versioned codecs and root pins are still owed (PROJECT.md)."

**ARCH-10** (line 268) Design-doc path.
- Quote: `<code>docs/LOOM-RECOMPOSITION.md</code> — proof system + obligation ledger`.
- Main: file is `docs/SELVAGE-RECOMPOSITION.md` (its H1 still reads "LOOM", line 1). `CLAUDE.md` line 9 names it with the same description. Tag: READ.
- Replacement: "docs/SELVAGE-RECOMPOSITION.md is the proof-system design and obligation ledger."

Checked and consistent: hard invariant paragraph (lines 78-83) equals `PROJECT.md` invariants 1-4; hyperdocument merge sentence (lines 168-173: singleton writes, multi-source becomes `ConflictRecord`, ambiguous base absent) matches `Kernel/HyperdocumentMerge.lean` lines 1-12 and `Kernel/HyperdocumentMergeAncestry.lean` (`ambiguous_plan_base_absent`, line 75); the clause-406 sentence (line 189) matches `docs/SELVAGE-COMPLETE.md` and `Compiler/ComposableDeploymentManifest.lean` lines 17-19, 242-285; the other five doc links exist (`docs/HYPEREDGE-DESIGN.md`, `docs/KERNEL-NECESSITY.md`, `docs/PROOF-SYSTEM-SURVEY.md`, `docs/decisions/`); the `Kernel/`, `Pred/`, `Compiler/`, `Assurance/` rows are consistent with README.md Layout.

---

## maturity.html

**MAT-1** (lines 82-86, 287-290) Provenance of the page.
- Quote: `Condensed from the repository README. For the full residual text, read README.md and the evidence ledger in GOAL.md.`; `Snapshot prose tracks the repo README as of site authoring.`
- Main: README.md was rewritten (Mini, Honest state table, 2026-10-03 evidence). It no longer contains this residual text; per-artifact evidence is in `docs/evidence/` ("update it there rather than copying counts into introductions", README.md line 83); the proof-system residuals live in `docs/PROVER-PLAN.md` and `docs/SELVAGE-COMPLETE.md`; `GOAL.md` line 1 says the top block is the live trail and the ledger below "is not present-tense status". Tag: READ.
- Replacement: "Current status is the Honest state table in README.md and the dated records under docs/evidence/; proof-system boundaries are tracked in docs/PROVER-PLAN.md and docs/SELVAGE-COMPLETE.md, and this page predates the Selvage rename."

**MAT-2** (lines 96-98) `DeclaredHyperedge`.
- Quote: `DeclaredHyperedge composes a flat, balanced multi-cell turn.`
- Main: `Kernel/DeclaredHyperedge.lean` does not exist; "The legacy integer-field carrier (`Kernel.DeclaredHyperedge`) and its adapter certificate are deleted; this is the only joint carrier over one cell" (`Kernel/TypedCellHyperedge.lean` lines 20-21); `Kernel.lean` line 26 repeats it; `Assurance/TypedCellHyperedgeReceipt.lean` line 20 "replaces `Assurance.DeclaredHyperedgeReceipt`". The live carriers are `Kernel.TypedCellHyperedge` and `Kernel.MultiCellHyperedge`. (`PROJECT.md` "Flat hyperedges" still names `Kernel.DeclaredHyperedge`; the source wins.) Tag: READ.
- Replacement: "Kernel.TypedCellHyperedge and Kernel.MultiCellHyperedge compose accepted effects into a flat, balanced, jointly re-validated turn; the earlier Kernel.DeclaredHyperedge carrier is deleted."

**MAT-3** (lines 107-121) Durable settlement.
- Quote: `device model only — no fsync, torn record, page cache, or liveness claimed.`
- Main: `Kernel/FramedWalRefinement.lean` lines 1-17 (imported in `Kernel.lean` line 48) models checksummed frames, torn final segments, fail-closed recovery and an abstract sync barrier; the deployed Host persists to a SQLite store with KMAC-tagged log and checkpoints (`docs/DURABLE-STORE.md`, "Files" table). Still unproved: POSIX `fsync`/filesystem semantics, replication, liveness (`FramedWalRefinement.lean` lines 11-16). Tag: READ.
- Replacement: "Kernel.DurableWalHandler models a staged, committed and compacting log, Kernel.FramedWalRefinement adds checksummed frames, torn tails and an abstract sync barrier, and the Host stores to a SQLite store (docs/DURABLE-STORE.md), while real fsync semantics, replication and liveness remain unproved."

**MAT-4** (lines 133-141) Vacuity caveat.
- Quote: `Vacuity caveat: at some deployed schemas, LogicalState is a total function over an infinite address space, so no materializer can inject it into List UInt8.`
- Main: closed; the old carrier survives only as a regression model in `Theory/MaterializerCardinality.lean` ("The deleted total carrier"). `grep -rl LogicalState --include=*.lean` returns only that file. Evidence as IDX-11. Tag: READ.
- Replacement: "The total-function LogicalState carrier that had no materializer was deleted on 2026-08-11 and survives only as a regression tooth in Theory/MaterializerCardinality.lean."

**MAT-5** (lines 123-132) Hyperdocuments badge row S, A.
- Main: README.md Honest state grades "documents" deployed on the public node; the S/A badges understate the shipped document path while offline merge stays S/A (`PROJECT.md` "Hyperdocuments", "Landed **S/A** construction"). Tag: READ for README row; mapping to the Kernel/Hyperdocument* modules INFERRED.
- Replacement: "Shared documents are graded deployed in README.md on the public node's 2026-10-01 candidate, and offline-branch merge with conflict records is graded S and A in PROJECT.md."

**MAT-6** (lines 161-178) Tower256 additive FRI "S A P*".
- Quote: `Exact Tower/Fan–Paar coordinates, cSHAKE framing, Merkle schedule, coherent openings and folds. Accepted bytes select the literal challenge/query coin;`
- Main: the page describes the legacy binding-closed controller whose `MerklePcs` carrier is proved EMPTY at every positive height (`Assurance/Tower256MerkleCardinalityCore.lean`, `merklePcs_empty_of_positive`); `docs/SELVAGE-COMPLETE.md` lines 113-120 say `Tower256AdditiveFriControllerAdmission` and `Tower256AdditiveFriActualReduction` were retracted and deleted (2026-09-30) and the live path is `Tower256AdditiveFriRawAdmission`/`Tower256AdditiveFriCanonicalExecutionGame` over `RawMerklePcs`; line 111: "This closes **A**, not deployed **P**". (`PROJECT.md` line 337 records the same deletion for the history-checkpoint module.) Tag: READ.
- Replacement: "Tower256 additive FRI has a Lean-owned bytes-or-error controller (A) and a conditional P shape over RawMerklePcs, because the earlier binding-closed MerklePcs carrier was proved empty at every positive height and its admission modules were deleted on 2026-09-30."

**MAT-7** (lines 197-215) Clause 406 card carries badge D.
- Quote: `S A D B ... Compiler & native authority (narrow path) ... Clause 406: authenticated artifact / native work / controller / deployment join.`
- Main: the site's own legend (lines 67-69) defines D as "joined and used by a real consumer". No consumer uses it: `PROJECT.md` "Consumer migration" lists the required D demonstrations as unmet; `Deployed.lean` lines 9-11 leaves Selvage and the proof-system Assurance out of the deployed umbrella; README.md: "No world admission uses a proof today". `docs/PROVER-PLAN.md` line 62 says "work 9102 deployed through exact artifact/controller/native-catalog join", which is a manifest join (`Compiler/ComposableDeploymentManifest.lean` lines 285-339), not use. Tag: READ.
- Replacement: "Clause 406 is a narrow authenticated artifact, controller and native-work loop that exists in the research umbrella, and no world admission uses it because Mini admits by re-execution."

**MAT-8** (lines 197-203, 208) Same card carries badge B.
- Quote: `Dispatch microbenchmarks exist.` under badges S A D B.
- Main: `docs/PROVER-PLAN.md` line 62 gives B = "none" for the clause-406 row; the recorded benchmark (source `54295c6`, evidence `4d1f290`) measures generated dispatch for work 9101, the Tower256 dot product in base V1 (`docs/SELVAGE-COMPLETE.md`, "Performance boundary — B, narrow"; `PROJECT.md` "Performance and evidence discipline"). Tag: READ.
- Replacement: "The only recorded benchmark measures generated dispatch for work 9101 (Tower256 dot product), with dispatch-to-direct ratios of 0.985 to 1.040 on hbox, and says nothing about clause 406."

**MAT-9** (lines 228-231) Count of controller seams.
- Quote: `Five concrete controller seams exist: arithmetic clause 406, Tower256 additive FRI, extension-only lookup 404, Ext6 gate proof, and sealed note spend`.
- Main: `docs/PROVER-PLAN.md` "Lean-owned controller table" (lines 59-69) has seven rows (adds BFV 901 and semantic history); `Compiler/EvmStage0NativeDeployment.lean` (lines 1-30) adds clause 407, work 9103 (EVM Stage 0 u256 add) with `prover/generated/evm_stage0_add_aux.rs`. No document on main says "five". Tag: READ.
- Replacement: "docs/PROVER-PLAN.md tabulates seven controller or join rows (clause 406, Tower256 additive FRI, lookup 404, Ext6 gate proof, BFV 901, sealed note spend, semantic history), and Compiler/EvmStage0NativeDeployment.lean adds clause 407 for EVM Stage 0."

**MAT-10** (lines 223-227) Native source scope.
- Quote: `Current native source is limited to fallible arithmetic, transform, hash, and MLE/lookup candidate compute plus generated artifact/dispatch data.`
- Main: `prover/src/lib.rs` also exports `sumcheck` ("the one protocol-shaped resident") and `rank1`, and generated gate-row data for work 9103. Tag: READ.
- Replacement: "Current prover/ source is unverified arithmetic, transform, hash, MLE and lookup kernels, a Lean-mirrored sumcheck engine and rank-1 gradient check tied to Lean by conformance vectors, and generated artifact and dispatch data."

**MAT-11** (lines 247-285) Consumers table.
- Quote: `Drex / FHEgg / Dark Bazaar`, `DeOS / agent platform`, `token authorization`, `Grains`, `DreggNet control plane`.
- Main: these names occur only in `PROJECT.md` "Consumer migration" (and DreggNet in `docs/KERNEL-TWIN-AUDIT.md`); README.md and docs/README.md name the live consumers: native Host, shell and documents, rooms, Studio, SPK hosted apps, Hermes residents, the agreement mesh, Discord entrance, payments. Tag: READ (grep over README.md, docs/README.md, HANDOFF.md, AGENTS.md).
- Replacement: "Mini's current consumers are the native Host, shell and documents, rooms, Studio, SPK hosted apps, Hermes residents and the agreement mesh, graded in the README Honest state table, and none of them admits by proof."

Checked and consistent: legend rows (lines 51-75) against `PROJECT.md` "Maturity boundaries"; `AcceptedCellEffect` retains authorization token, effects digest and pre-root (`Theory/AcceptedCellEffect.lean` lines 174-199); clause 404 gated out of base V1 (`docs/SELVAGE-COMPLETE.md` line 152); "proof-suite ID still 0" (`Assurance/NoteSpendCoreAcceptedCellEffect.lean` line 81); "base V1 still has zero clauses" and the add-1 zero-witness description of 406 (`PROJECT.md` "Honest deployment registry"); "Former parallel prover/verifier paths ... were deleted" (`docs/PROVER-PLAN.md` "Deleted authority islands").

---

## laws.html

**LAW-1** (lines 113-119) Law 7 as present-tense status.
- Quote: `The claims ledger is generated and unparkable.`
- Main: the law text matches `ATLAS.md` law 7 (line 210), but `ATLAS.md` lines 271-275 record that generation is "PLANNED, not built: as of 2026-09-30 every Assurance/ file is hand-written and nothing is generated". `lakefile.toml` "Assurance/ ... Hand-written; axiom pins are `#guard_msgs in #print axioms` lines beside each theorem, not generated." Tag: READ.
- Replacement: "Law 7 is a design law; ATLAS.md records that as of 2026-09-30 every Assurance/ file is hand-written and the generated claims ledger is planned, not built."

**LAW-2** (lines 31, 191-195) Law 14 attribution.
- Quote: label `ATLAS §6`; law 14 body `State covered scope in the same sentence as the claim. Proven parameters only — zero conjectures on the label.`
- Main: `ATLAS.md` lines 232-234 law 14 reads "Quote the pessimistic number of a pair ... State covered scope in the same sentence as the claim"; the sentence "Proven parameters only — zero conjectures on the label" is in `CLAUDE.md` (fourth law), not ATLAS §6. Tag: READ.
- Replacement: "Law 14 in ATLAS.md section 6 is 'Quote the pessimistic number of a pair' with covered scope stated in the same sentence, and CLAUDE.md adds 'proven parameters only, zero conjectures on the label'."

Checked and consistent: all sixteen law titles and bodies match `ATLAS.md` section 6 lines 185-240 (sixteen is the count there and in `CLAUDE.md` line 7); law 11's "One added word moved reach" condenses the `25/76 → 76/76` of `ATLAS.md` line 223; the footer pointer to `ATLAS.md` and `CLAUDE.md` is valid (both exist).

---

## website/README.md

**WREADME-1** (lines 36-38) Synchronization rule.
- Quote: `Keep maturity claims synchronized with the root README.md / GOAL.md.`
- Main: README.md says dated evidence lives in `docs/evidence/` and per-component status in its Honest state table; `GOAL.md` is a 1,314-line history whose live block is its top (GOAL.md line 1). Tag: READ.
- Replacement: "Keep maturity claims synchronized with the Honest state table in the root README.md, the dated records under docs/evidence/, and, for proof-system rows, docs/PROVER-PLAN.md."

Checked and consistent: the page table (five pages exist), "sixteen ATLAS design laws", `.github/workflows/pages.yml` exists and triggers on `website/**` pushes to main.

---

## Unverifiable from main

| Site claim | Where | What would verify it |
|---|---|---|
| breadstuffs `~2.89M LOC`, `1.82M Rust · 913K Lean · ~160K TS/JS` | why.html lines 53-54 | Reproduced verbatim from `ATLAS.md` line 13 (compiled 2026-08-06 from `~/dev/breadstuffs`). A `tokei`/`cloc` run over the breadstuffs checkout at that date. breadstuffs is not in this tree. |
| `semantic core (prior) ~25K`; `irreducible kernel (audit) 800–1,200` | why.html lines 63, 69 | `ATLAS.md` lines 18, 23 only ("per the kernel-lane audit"); the audit itself is not in this tree (`docs/KERNEL-TWIN-AUDIT.md` is a different document). Needs the breadstuffs kernel-lane audit notes. |
| eDSL/VCG "used once", toolkit "proved once; almost never adopted", "Kernel minimality theorems ... Never executed" | why.html lines 86-101 | `ATLAS.md` lines 36-55 (63 apps, 3 of 63 adopt the toolkit, etc.). Needs breadstuffs source. |
| "Our own development fleet is the first user." and the helm description (rooms as cells, posts as signed turns, premises as attested claims, review verdicts and land-receipts as receipts on chain) | index.html lines 177-185 | Text is copied from `CLAUDE.md` "North star", which states it as a target. README.md does not mention helm or a first user. Closest evidence: `docs/FLEET-SURFACE.md` and `docs/evidence/2026-09-30-fleet-surface/` (the `mini fleet` client: join, send, transfer, receipt lookup, event topics). Verify with ember or helm usage logs. Suggested sentence: "docs/FLEET-SURFACE.md describes the `mini fleet` operations (join, send, transfer, receipt lookup, event topics) that an agent fleet uses on Mini, with a measured run in docs/evidence/2026-09-30-fleet-surface/." |
| Law 2 "CI-gated beside the axiom pin" (declaration-level satisfiable + teeth + premise-inhabitation); Law 6 "CI reachability gate" | laws.html lines 59-60, 105 | `scripts/local-gates.sh` header lists `hyp-ledger` (no VACUOUS/INCONSISTENT/TOOTHLESS row), `hygiene` (no bare `#print axioms`), `exports` (every `@[export]` called from `native/`), `host-closure`. These cover parts of both laws; I did not establish that every keystone has a satisfiable+teeth+premise-inhabitation gate. Verify by reading `scripts/check-hypothesis-ledger.sh` against `ATLAS.md` law 2. |
| External links: https://github.com/emberian/minidregg, https://ember.software, GitHub Pages deployment | index.html lines 26, 44, 191-193 | Network (no network allowed). `.github/workflows/pages.yml` exists and deploys `website/` on push to main. |
| Reactive-promise sentence ("late-advice codecs, wake from verified history, retain observed pre-root and replay nullifier") and "Note-spend path has a bytes/error controller with roots-before-challenge control" | maturity.html lines 149-154 | Match `PROJECT.md` "Reactive lifecycle and tools" (lines 201-206) and the note-spend paragraph; I did not read the underlying `Theory/Reactive*.lean` or `Assurance/NoteSpendProofControllerAdmission.lean` theorem statements. Read those statements. |
| "Hyperdocuments ... stable ranges, annotations" and "Ancestry-backed accepted merge retains the selected base" | architecture.html lines 166-174 | Consistent with `PROJECT.md` "Hyperdocuments"; only `Kernel/HyperdocumentMerge*.lean` headers were read. Read `Kernel/HyperdocumentMergePublication.lean` statements. |

---

## Names to replace globally

| Old (site) | New (main) | Evidence |
|---|---|---|
| Loom | Selvage | `Selvage.lean`; `lakefile.toml` "Selvage/ — the proof system"; `docs/decisions/D-0004-why-selvage.md`; `PROJECT.md` "Target composition" |
| `Loom/` (directory) | `Selvage/` | `ls Selvage` (152 files); `ls Loom` fails |
| `docs/LOOM-RECOMPOSITION.md` | `docs/SELVAGE-RECOMPOSITION.md` | file exists; `CLAUDE.md` line 9 |
| `docs/decisions/D-0004-why-loom.md` | `docs/decisions/D-0004-why-selvage.md` | file exists |
| minidregg (as product name in prose) | Mini (repo, package and host binary remain minidregg / `minidregg-host`) | `README.md` line 1; `AGENTS.md` line 1; `lakefile.toml` |
| proof-native semantic computer | programmable shared world for people and agents | `README.md` lines 3-11 (CLAUDE.md line 5 retains the old phrase) |
| `DeclaredHyperedge` | `Kernel.TypedCellHyperedge` / `Kernel.MultiCellHyperedge` | `Kernel/TypedCellHyperedge.lean` lines 20-21; `Kernel.lean` line 26 |
| "Hyperdocuments", "Compiler boundary" as pillar names | keep, but add Objective Bend (Core4, `Theory/ObjectiveBend*.lean`) as Mini's authored language; BendTT is the retiring Gen-1 core | `README.md` Objective Bend section and Honest state rows |
| S / A / P / D / B as the site-wide label set | authored / compiled / executed / integrated / deployed for components; S/A/P/D/B only for Selvage rows | `README.md` "Honest state"; `PROJECT.md` "Maturity boundaries" |
| "Plonky3" | not named on the site; no change needed | `docs/SELVAGE-VS-PLONKY3.md` is a historical brief (its header says so) |
| "Core4", "Objective Bend", "BendTT", "Nock" | not named on the site; add per IDX-12 | `README.md` |
