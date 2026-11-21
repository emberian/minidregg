# minidregg: index and survey

Written 2026-11-11 at `main` = `c492c4dd3` (last commit 2026-11-09), the day the public demo was shut down.
This is a catalogue of what is in the repository, how the parts relate, which experiments were under way,
what was never finished, what finishing each would take, and what finishing would teach.

**How it was made, and what to trust.** The source was read first: the eight per-library root files
(`Kernel.lean`, `Theory.lean`, `Compiler.lean`, `Selvage.lean`, `Assurance.lean`, `Host.lean`, `Pred.lean`,
`Effects.lean`), whose per-import comments are a hand-written catalogue; the headers and statements of the
load-bearing modules; the import graph (computed over all 1,741 tracked `.lean` files); `git` history and
branches; the board. Prose documents were used as pointers and checked against what they name. Where this
file quotes a number, a command produced it. Where a claim comes from an earlier review and was not
re-derived, it says "per" and names the review. Session transcripts (through `cv`) supplied what ember
said the project was for; those are cited as `session#message`.

Status words used throughout:

| word | meaning |
|---|---|
| **served** | on the path the demo box ran (the `minidregg-host` executable, the client, the deployed crates) |
| **rooted** | in the default Lean build (`Minidregg.lean`'s closure) but not on the served path |
| **qualified** | built only by its own library or executable (`ObjectiveProofs`, `SimplexQualification`, `Verify`, an exe) |
| **WIP-only** | reachable only from `ResearchWip.lean`, the opt-in target whose header says it "may fail" |
| **orphan** | reached by no Lean root, no script, no unit |
| **branch** | not on `main` |
| **moved** | its live development continues in another repository |

---

## 1. What this repository is

### 1.1 Three missions, in order

1. **August: a proof-native computer at a tenth of the size.** The founding brief (b54b6026#3, 2026-08-06)
   was a formal-first rebuild of `~/dev/breadstuffs` in at most 10% of its lines, with nothing
   hand-written: every constraint system, executor arm and codec derived from one declaration by
   compilers. `ATLAS.md` is that brief's map: the diagnosis of breadstuffs ("built and proved every piece
   of the derivation machine, demonstrated each at n=1, and wired almost none of them into the load
   path"), seventeen design laws, and a carve of about 100-150K lines. The same week ember decided the
   project would own its proof system. That became Loom, renamed Selvage.
2. **September: semantics first.** On 2026-09-19 ember chose to run the system's semantics before its
   proofs were complete ("we want to be offering and running the semantics of the system before the full
   starks & assurances are complete", cx-01a0b0ed#6380) and to rebuild what a hosted, multi-user,
   agent-inhabited "shellserver" needs directly in this tree. On 2026-10-01 the ruling followed: Mini
   admits by re-execution, never by proof. From then on the proof system was research with no consumer in
   admission, and the product was a world host: documents, grants, money, programs, Sandstorm
   applications and agent residents behind one Lean admission function.
3. **Late October to November: a public demo, then stock-taking.** From 2026-10-26 the work was a
   temporary public deployment (`demo.dregg.online`), to answer by use the questions the design had
   raised. Its join page opened to strangers on 2026-11-03 and the box was stopped on 2026-11-11 (§6). Meanwhile the
   ideas began leaving for their own repositories: the language to `~/dev/obend`, the oracle to
   `~/dev/o7vn`, the transport to `fn`/`fn2`, and (on 2026-11-11) Selvage, copied with its history into
   `~/dev/zkml-research` (`dev` at `b950c991`).

The founding laws in `CLAUDE.md` describe mission 1. The code is mostly mission 2. Reading the tree as a
failed mission 1 is a misreading: ember's own account (01a1ae2a#4793) is that the ambition grew past the
original mission "semi-intentionally", to explore the design consequences of a world that is admitted in
Lean and re-executed rather than proved.

### 1.2 The thesis the served system embodies

One shared world. Every change is a signed request. One Lean function family admits or refuses it. An
admitted request yields a new world root and a receipt; a refusal names the clause of the law that refused
it, and `can --any` computes a request that law would admit; a request whose reply was lost stays
undecided and is retried byte for byte, so its effect happens once. A program or an agent can propose a
write but cannot admit one. Rust moves bytes, holds keys, runs sandboxes and renders pages; it is meant to
decide nothing. (Per the 10-26 crate review it does decide some things; §8.3.)

### 1.3 Sizes

Tracked files, excluding `docs/evidence`:

| kind | files | lines |
|---|--:|--:|
| Lean | 1,729 | 660,513 |
| Rust | 567 | 354,043 |
| shell | 491 | 72,269 |
| Python | 301 | 60,719 |
| Markdown | 495 | 82,046 |
| Objective Bend (`.obend`) | 137 | 9,304 |
| JSON | 925 | 131,429 |

The founding budget was about 290K lines in total. 8,543 commits, 2026-08-07 to 2026-11-09, in bursts:
08-07 to 08-14 (the proof-system burst), 09-17 to 10-08 (the build-out), 10-14 to 10-17 (integration),
10-26 to 11-09 (the demo; 1,477 commits on 10-27 alone). 20,527 `theorem`/`lemma` headers. No `sorry`,
`axiom` or `opaque` declaration anywhere in the Lean; unfinished work is carried as named hypotheses,
`Prop`s stated but not proved, and bracketed residual tags in comments (§7.4).

---

## 2. The tree at a glance

| path | files | first .. last commit | what it is | status |
|---|--:|---|---|---|
| `Theory/` | 201 | 08-07 .. 11-06 | abstract machinery that may import only Mathlib and itself: the store and guarded patch, authenticated maps and tries, the cell model, Objective Bend's calculus, Nock, channels, binary towers, plus research algebra | 134 modules in the served closure; 20 WIP-only |
| `Pred/` | 10 | 08-07 .. 10-30 | the predicate algebra laws are written in | served |
| `Effects/` | 15 | 08-07 .. 10-31 | the effect derivation engine | rooted; one consumer (§5.2) |
| `Kernel/` | 591 | 08-07 .. 11-08 | admission: four generations of kernel (§3.4) and every receiver | mostly rooted and served; the exceptions are in §3.9 |
| `Compiler/` | 346 | 08-07 .. 11-08 | mostly codecs; also the Objective Bend front end, the law-to-constraint compiler, the proof-system controllers | 264 rooted, 66 WIP-only |
| `Selvage/` | 162 | 08-13 .. 11-06 | the proof system | rooted, not served; copied to zkml-research |
| `Assurance/` | 148 | 08-07 .. 11-06 | cross-layer theorems; hand-written | rooted; 24 modules in `Deployed.lean` |
| `Host/` | 127 | 09-18 .. 11-08 | the `minidregg-host` executable and its JSON, inspection and authoring surfaces | served |
| `TokenCensus/`, `AxiomCensus*.lean`, `CensusChecks.lean` | 8 | 10-06 .. 11-08 | build-time censuses: private constructors minted only at home, axiom footprints | qualified |
| `Verify/`, `Fixtures/` | 20 | 10-03 .. 11-04 | Simplex harnesses; recorded native runs replayed in Lean | qualified; 2 orphans |
| `protocol/` | 5 | 10-02 .. 11-06 | the registry of Host operation bytes (199 entries) and the hosted-conversation protocol; generators emit Lean and Rust from them | served |
| `native/` | 1,825 | 08-11 .. 11-09 | 26 Rust crates and 2 non-Cargo units (§3.10) | 20 shipped, the rest research or orphan |
| `prover/` | 49 | 08-08 .. 11-06 | native arithmetic kernels and the Tower256 FRI prover; nothing depends on the crate | island |
| `deploy/` | 212 | 09-26 .. 11-09 | candidate packager, units and installers for the demo box, the world migration tool | served, with the rest of the box in `~/dev/dregg-infra` |
| `scripts/` | 573 | 08-07 .. 11-08 | the builder loop, gates and checks, generators, one-off recoveries | about 15 files live; about 95 referenced by nothing (§8.2) |
| `apps/` | 294 | 10-28 .. 11-01 | 22 Sandstorm package recipes and 43 typed app-interface declarations | served |
| `world/`, `examples/`, `tests/`, `testing/` | 198 | 10-02 .. 11-05 | Objective Bend programs and cohorts, front-end tests, composed-gate fixtures | gated in CI; several unreferenced (§3.12) |
| `website/` | 11 | 08-10 .. 10-30 | the project site, plain HTML | published by `pages.yml` |
| `bridges/arklib-ud/` | 7 | 11-05 .. 11-06 | an opt-in Lake package that discharges a Selvage premise from ArkLib | built by nothing |
| `board/` | 14 | 10-31 .. 11-09 | how work was coordinated from 10-31: rulings, reds, one file per owned seat | current to 11-09 at best |
| `docs/` | 5,298 | 08-07 .. 11-08 | 161 documents, 4,934 evidence files (33 MB; 299 of 342 dated directories are from 09-26 and 09-27), 79 review files, 68 screenshots | mixed; §3.13 |
| `.spw/`, `spk-notes/`, `scratch/`, `files.txt`, `SOURCE-INBOX.jsonl`, `EVENTS-DESIGN.txt`, `SUMS-DESIGN.txt` | 44 | 10-01 .. 10-29 | leftovers (§3.14) | orphan or cited once |

Top-level Lean roots: `Minidregg.lean` (the default build: every library plus about 40 modules no
library root imported), `Deployed.lean` (the served system without the proof-system research; no module
in its closure imports Selvage), `ResearchWip.lean` (generated by `scripts/lean-build-surfaces.py` as
"every library module no other target reaches": 131 modules), `ObjectiveProofs.lean` (Objective Bend
metatheory), `SimplexQualification.lean` (agreement-engine safety).

---

## 3. Catalogue

### 3.1 `Theory/` (200 modules, 97.5K lines)

The import boundary (Mathlib, Lean core and Theory only) is enforced by `scripts/check-import-boundary.sh`. The
directory is not the "candidate-independent core of 3-5K lines" the atlas carved. Of the atlas's listed
contents only the verify/find seam (`Theory/Knowledge.lean`) and the epistemic frame
(`Theory/EpistemicConsensus.lean`) exist; `AmpClosed`, the games, `nuF` and `GovernedDynamics` as a core
shape were never brought over. What is there, by cluster:

| cluster | files / lines | what | status |
|---|---|---|---|
| `ObjectiveBend*` | 46 / 27.5K | Core4: types, open recursion (`Step`), typing, the demand machine, data, capacity, checkpoint codec, and their metatheory (`ObjectiveBendDemandAdequacy` alone is 5,385 lines) | definitions served; proofs qualified (`ObjectiveProofs`) |
| Store and cells: `Store`, `StoreNormalize`, `SparseMap`, `CellState*`, `CellSlot`, `PlanBinding`, `Retained` | about 12 | the one typed sparse store with ROM/RAM/append-only disciplines and guarded patches; the retained-mode abstraction | served |
| Authenticated structures: `AuthMap`, `AuthTrie*`, `LogAccumulator`, `PrivateCellTrie` | about 9 | sparse Merkle map, compressed trie with range reveals and a kept cache, Merkle mountain range; soundness "up to a named collision" | served |
| Authority: `TypedAuthorization*`, `Credential*`, `KeyPreRotation`, `Renounce`, `RoomAuthorization`, `AuthorizationDeclaration` | about 12 | request-indexed authority, capability lineage, revocation, pre-rotation | served |
| Resources: `CanonicalResourceKernel`, `CanonicalResourceBookEntries`, `Conservation*`, `ResourceCost` | 6 | the Book: one solvency rule with floors; conservation as a homomorphism; multi-lane charges | served |
| The August "semantic machine": `AcceptedCellEffect*`, `CanonicalTransition`, `EffectDeclaration`, `DeclaredTurn`, `DeclaredActionLowering`, `Reactive*`, `GuardedAdvice`, `IndexedProgram`, `PrivacyProfile`, `DisclosureDeclaration`, `PrivateComputationDeclaration`, and the `*Witness` anti-vacuity files | about 25 | typed effect families, reactive receipts, sealed private computation as a shape | rooted; the served path uses little of it directly |
| Hyperdocuments: `Hyperdocument*`, `StableRanges`, `CausalVersion*` | 8 | document identity, operations, interface negotiation, causal DAG and ancestry | rooted; partly served through the content cell |
| Evaluators: `Noun`, `Nock`, `NockCost*`, `Eval` | 5 | Nock 4K with jam/cue, a syntactic step bound, shared run outcomes | served (ops 131-137) |
| `Channel*` | 6 | constant-rate broadcast cells, schedule, lease | rooted; the relay was deleted (§5.22) |
| Hashing: `Sp800185Cshake256*`, `HashBytes`, `CollisionFloor`, `StreamCodec` | 7 | cSHAKE256 spec, fast path, `@[extern]` seam to `native/mini-kernels`, NIST vectors; the prefix codec nucleus | served |
| Distributed theory: `Confluence`, `ViewMerge`, `Finality`, `LaceMerge`, `RevocationConsensus`, `EpistemicConsensus` | 6 | I-confluence, the four-tier finality ladder, replica merge, why revocation needs consensus | rooted, no consumer (§5.19) |
| Algebra for proofs: `BinaryTower*`, `AdditiveNTT*`, `ExtensionBasis`, `Bignum`, `CrossModulus`, `CompressedLinearEquation`, `IntegerFingerprint`, `Cyclotomic*`, `ExceptionalSetLocalRing` | about 16 | GF(2) towers with Fan-Paar arithmetic, additive NTT, ring-switching packing, lattice challenge sets | rooted |
| zkML and EVM: `ZkmlTensorOps`, `ZkmlMatmulSum`, `EvmFragment`, `EvmResidual` | 4 | tensor-op vocabulary; a five-opcode EVM fragment with a refusing decompiler | rooted |
| BFV: `Bfv*` | 8 / 3.2K | exact decryption of folded ciphertexts, noise, smudging | WIP-only (§5.10) |
| Ports from breadstuffs: `Disputation`, `OptimisticAdjudication`, `ResearchRegime`, `Transferability`, `AdversarySchema`, `BendMasking*`, `BendQuotient*`, `BoundedNockMachine` | 12 | | WIP-only |

### 3.2 `Pred/` (10 modules, 4.9K lines): served

One predicate AST with no function payloads (`Pred/Core.lean`), a decidable evaluator, the failing leaf
a refusal names (`Leaf`), a hash-equality commitment leaf (`HashEq*`), bounded quantifiers lowered to the
same AST, a satisfiability decider that returns a witness or a negative-cycle certificate and never
"unknown" on translated laws (`Satisfiable*`; this is what `can --any` runs), the coordination dial
(`CoordinationDial`: a computed verdict of whether a law is coordination-free), and `Frame` (a law reads
only its slots). Named residuals in `Pred.lean`: `[PRED-relational-view]`, `[PRED-disclosure-dial]`,
`[DIAL-pn]`, `[DIAL-declared-merge]`, `[DIAL-price]`. The `witnessed` leaf (a claim discharged outside
the cell) is refused by the compiler at every depth; deleting the constructor is open (`docs/ZK.md`, D1).

### 3.3 `Effects/` and `Kernel/EffectsRevival/` (22 modules, 4.1K lines): rooted, one consumer

`Effects/EffectSpec.lean` is the August engine: one declaration derives a term, an executor and a
descriptor, with their agreement free by initiality. Its only declaration is `moveEffect` over the first
kernel's `move` (`Kernel/MoveEffect.lean`). `Effects/Placeholder.lean` still marks the remaining carve
(`[EFFECT-registry]`). The October revival (`Effects/Revival/Engine*.lean`, `docs/EFFECTS-REVIVAL.md`)
widened the declaration to the deployed store and added a registry and dispatcher. Its keystones over the
deployed controller live in `Kernel/EffectsRevival/`; §5.2 says which are proved. `Effects/Revival/Hosted*`
(conversation, lifecycle, DAV, schema) are generated from `protocol/hosted-conversation.json` for the app
layer; their statement and proof files are WIP-only.

### 3.4 `Kernel/` (591 modules, 241K lines)

Four kernels sit in this directory. Little was deleted when the next one arrived: the first kernel's
gate and camera, and the second's legacy `DeclaredHyperedge` carrier (per `docs/KERNEL-TWIN-AUDIT.md`).

| generation | dates | modules to read first | what it is | status |
|---|---|---|---|---|
| **A. The atlas kernel** | 08-07 .. 09-05 | `State`, `Verbs`, `Turn`, `TurnLimit`, `TurnBalancedLimit`, `Receipt`, `PrivateTurn`, `HyperedgeTier`, `HyperedgeKnowledge`, `FinalityGate`, `FinalityLiveness`, `MoveEffect` | three verbs over an integer ledger; the turn as a wide pullback (N2a, N2b); the finality gate as a decider | rooted; consumed by `MoveEffect` and `Assurance/ReceiptClaim` only |
| **B. The semantic machine** | 08-09 .. 08-14 | `TypedCellHyperedge`, `MultiCellHyperedge`, `DurableCommitProtocol`, `DurableDataIntent`, `GuardedDurableCommit`, `DurableWalHandler`, `FramedWalRefinement`, `ReplicatedSettlementFinality`, `AuthenticatedSettlementFinality`, `IrreversibleEffectSettlement`, `Hyperdocument*`, `Reactive*`, `CanonicalEscrowMarket`, `ProviderExecutionLease` | typed accepted effects over canonical cells, joined as flat hyperedges; a fail-closed durable settlement model with a WAL device model; hyperdocument publication and merge | rooted. `DurableDataIntent.execute` is the function the Host still runs |
| **C. The World** | 09-30 .. 11-08 | `World` (3,183 lines), `TurnCensus`, `TurnOfIntent`, `HostRefinesWorldCore`, `DeployedBridge`, `WorldRoot`, `WorldRootCache`, `TurnLog`, `DurableCheckpoint`, `DurableView`, `NativeHost*` (29 files, 22.5K), `Receiving`, `ReceivingLaw` | the data-model cutover: a world is a finite map of cells plus a system cell; a turn is one guarded patch per written cell; `World.admit` is the one transition; history is a fold | the model is rooted; the Host is proved to refine it (§5.1) |
| **D. The Objective kernel** | 10-04 .. 11-06 | `ObjectiveActivity` (6,713 lines), `ObjectiveCall`, `ObjectiveSend`, `Inbox`, `ObjectRecord`, `ObjectLaw`, `ObjectiveActivityUpgrade`, `Seat*`, `CertifiedClearing`, `ObjectiveTariff` | Objective Bend activities persisted between turns, synchronous calls, asynchronous sends, objects with laws and governed upgrade, seats and invitations | served (session ops 210-219) |

Around those, the receivers: one cluster per product surface, each a signed operation family with its
admission, receiver, lookup and proofs.

| cluster | files / lines | surface |
|---|---|---|
| `Application*` | 138 Kernel + 46 Host / 36.9K | Sandstorm grains: birth, lifecycle (BEGIN, claim, completion, retry, failed-start recovery, STOP), dispatch, agent lifetime grants, share issue, session enrollment, permissions. 61 files carry `V2`/`V3`/`V4`/`Legacy`/`Historical` in their names (12.3K lines) beside their predecessors: old records must still be read |
| `Native*` | 32 / 22.5K | the Host session, replay and re-admission on open, genesis, the served state and the light opening, thin consent |
| `Resource*`, `Declared*`, `Content*`, `Stream*` | about 27 / 21K | the one signed resource invocation receiver (`DeclaredResourceController`), births, observation, the content cell and its element tree, per-author streams |
| `Pay*`, `Purse*`, `Job*`, `Provider*`, `RealmWell*` | about 35 / 19K | observed Solana payments mint Book credit; self-enrollment by payment; purse refill; job escrow and bond; provider route tariffs; realm wells |
| `Fn*` | 44 / 9.4K | the consumer side of the fn transport: evidence, operation, frontier, archive, selective release, reply publication |
| `GenericSimplex*`, `Joint*`, `NativeJointAgreement` | about 50 / 10K | the agreement engine and joint decisions (§5.18) |
| `Capability*`, `Policy*`, `Participant*`, `Subject*`, `Room*`, `Platform*`, `Clock*`, `System*`, `Domain*` | about 40 | revocation and renounce, policy install, key enrollment and rotation, rooms and the birth gate, the platform, clock and system cells, channel epochs |
| `PrivateCell*`, `BlindedCellHiding`, `ReceiptEventHiding`, `NarrowedViewHidingWitness`, `PrivateRoom*` | about 12 / 5K | blinded cells and private rooms (§5.12) |
| `Nock*`, `Door`, `Run`, `Job`, `Evaluator` | about 10 | programs refereed by re-execution (§5.15) |
| `LawView`, `LawHistory`, `StoryLaw`, `SealedMarket`, `AppsRequest` | 5 | laws that are theorems about templates under `native/resource-client/templates/` |
| `Contracts/*` | 7 | the SDK's contract surface (identities, cuts, snapshot, futures, intents) |
| `FleetTurn*` | 2 | the agent-fleet surface (§5.31) |

### 3.5 `Compiler/` (346 modules, 115K lines)

The name dates from August. In practice the directory holds anything that turns one representation into
another. By kind (the first split was measured in session 01a1ae2a on 11-11):

| kind | about | what | status |
|---|---|---|---|
| Wire and storage codecs | 50K | `StoreCodec`, `Durable*` (log, checkpoint, index, history reader, served state), `CredentialAuthority*`, `HyperdocumentCell`, `StreamCell`, `PersistedCodecTags` (640 persisted identities), `RefusalReason`, `PlanFootprintCodec`, the `FnWire*` grammar interpreter, `Blake3`, `Sp800185Kmac256` | served. Round-trip theorems. These were the `List UInt8` paths the bytes-repr work was converting to `ByteArray` |
| Objective Bend front end | 8.6K | parse, elaborate, Core4 term, proof-producing checker, publication | served (18 of 24 modules) |
| Law to constraints | about 8K | `PredCompile` (laws to constraint systems, with an iff), `Air*` (the arithmetization DSL, flattening, range, bignum, hash, Keccak, cSHAKE, membership), `Emit*` (descriptor, CSE pass, serializer), `NoteSpend`, `AdmissionAir`, the recursive-verifier gadgets (`SumcheckVerifierAir`, `FriQueryVerifierAir`, `FiatShamirAir`, `MerkleBindAir`) | rooted; no prover consumes the output (§5.3) |
| Proof-system controllers | about 15K | `Tower256*` (22 files), `CommittedTerminal*` (6), `Ext6GateProof*`, `Gate*Ext6`, `*ReceiptClause`, `SemanticController`, `TranscriptController`, `AuthenticatedColumn*`, `ComposableDeploymentManifest`, `NativeGlueGen` | rooted, not served (§5.5, §5.6) |
| Agreement | 2.7K | `GenericSimplex*` (IO, codec, source anchor, controller, native, participant, serve) | part served closure, part qualified |
| Bend proofs | about 1.8K | `Bend*` (24 files): committed run, trace, IR2, cSHAKE and Keccak networks | WIP-only (§5.14) |
| Oblivious circuits | 1.7K | `Oblivious*` (15), `BoundedNock*` | WIP-only except two reached by an exe (§5.11) |
| Portable continuation | 1.0K | `Portable*` (9) | WIP-only (§5.24) |
| Private backend boundary | | `PrivateBackendBoundary*`, `JointBackendPartyCodec`, `PrivateWorldIR`, `PrivateSuccessorCustodyCodec` | exe-only or WIP |
| BFV, zkML, EVM | about 5K | `Bfv*` (6), `Zkml*`, `Evm*`, `DescriptorEval` | rooted |
| N4 | 0.6K | `DistributiveLaw` | rooted by one import in `Minidregg.lean` |

`Compiler/Placeholder.lean` still describes the unbuilt spine: "one signature algebra; `fold_unique` as
the single induction ... derived canonical codec with a generic round-trip theorem". The codecs that
exist are written one by one on `Theory/StreamCodec`.

### 3.6 `Selvage/` (162 modules, 80.5K lines): rooted, not served, copied out

The proof system: WHIR-shaped, sumcheck-centred, hash-based accumulation. Whole in the default build, and
absent from `Deployed.lean`. `Assurance/SelvageV0Manifest.lean` is a build-checked table of contents with a
residual ledger. Families: proximity (`ProximityGapUD*`, `PolishchukSpielman*`, `JohnsonRegime`,
`HalfThreshold*`, `RateRegimeSelector`), sumcheck and MLE (9 files), the accumulator and its soundness and
extraction (`Acc*`, 12 files), the light client (5), zero knowledge (`ZK*`, `Zk*`, `ConstrainedMask*`,
`RbrZeroKnowledge`), Fiat-Shamir and the oracle log (`FiatShamir`, `OracleLog*`, 14 files), BaseFold
(23 files, 11.9K), sponge indifferentiability (21 files, 6.5K), additive (binary-field) FRI (`Additive*`,
`CharTwoWall`), lookups (`BinaryLookup`, `LogupStar`, `LogupIndexLink`, `DecomposableTable`,
`MultisetFingerprint`), commitment and binding games (`Commitment`, `AuthMapCommitment`, `BinaryMerkle`,
`Binding*`, `CollisionResistanceROM`), composition (`HeteroComposition*`, `Ligerito*`), and the November
audit files (`Audit*`, 8 files; §5.36). §5.4 has the results and the stops.

### 3.7 `Assurance/` (148 modules, 61K lines)

The atlas planned this directory as generated ledgers. Every file is hand-written. Three populations:

- **About the served kernel** (roughly 40 modules; 24 are in `Deployed.lean`): `StoryLaw`,
  `StoryHistory`, `SheetLaw`, `ItemLaw`, credential lifecycle and delegation audits, `CapabilityRevocationAudit`,
  `RenounceAudit`, `KeyPreRotationAudit`, `CanonicalResourceBookInvariantAudit`, `NativeObservationAudit`,
  `NativeProviderHistoryAdmission`, `EvaluatorAudit`.
- **The August end-to-end slices over generation B** (about 40): `Hyperdocument*` (link publication,
  reopen, framed recovery, local file and SQLite stores, query deployment, two-parent merge),
  `Reactive*`, `GrainFork*`, `DreggNetProviderConsumer`, semantic history accumulators.
- **Proof-system apexes** (about 60): `SelvageV0*`, `ErrorBudget*`, `MixedFieldBudget`, `PowGrinding`,
  `TwoRegimeQueryBudget`, `AirSumcheck*`, `Tower256*`, `Ext6GateProof*`, `RawHistory*`,
  `ProofCompositionGame`, `Bfv*` (7), `Zkml*` (10), `NoteSpend*`, `SpartanR1CS`,
  `TwistMemoryFingerprintJoin`, `Unlearning*`, `ReleaseGateRouting`.

### 3.8 `Host/` (127 modules, 43.6K lines): served

`Host/Main.lean` (10,757 lines) is the executable: it dispatches 197 active operation bytes
(`protocol/host-operations.json`) to their receivers. `Host/Json.lean` (6,058) is the JSON surface. The
rest are per-family authoring, inspection and operator modules, the consent executables
(`ClientConsentCore`, `ClientConsentSession`, the specialized session), and tools: `WorldSim` (the seeded
simulation of Host against a follower), `TurnLogFollower`, benches (`WorldFoldBench`, `WorldRootBench`,
`Kn2StoreBench`, `CodecBench`, `CshakeBench`), `NockEval`, `CarryVerifierMain`.

### 3.9 Lean files outside the default build

- **Reached by nothing (9):** `Host/BendCommitmentIR2Emit`, `Host/BendTraceIR2Emit`,
  `Host/ObjectiveBendFrontEndMain` (run by hand from `scripts/check-objective-frontend.sh`),
  `Host/ObjectiveStudioPublication`, `Host/PortableContinuationProbe`, `Host/SourceAgreementReader`
  (351 lines, still documented), `Kernel/Contracts/IntentVectors` (its output is the SDK's golden file),
  `Verify/GenericSimplexNativeHarness`, `Verify/BendCommittedIR2Emit`.
- **WIP-only (131):** Kernel and Host 34 (room key release 6, portable continuation 5, joint 3, native
  current-key 4, `GenericSimplexReconfig`, `ObjectiveActivityEffect`, `DefaultLaw`,
  `AgreementEvidenceRegime`, others); Compiler 66; Theory 20; Assurance 10; Verify 1.
- **Reached only by `Deployed.lean`/`AxiomCensus` (11):** the application lifecycle V4 receivers and
  lookups and failed-start recovery. `Deployed.lean:50` says `Minidregg` roots them; it does not, so the
  token census never scans them.
- **Reached only by `SimplexQualification` (26):** the agreement engine's safety proofs.

### 3.10 `native/`

Shipped (in `deploy/candidate/package.py` `RUST_ROLES`):

| crate | Rust lines | what | notes |
|---|--:|---|---|
| `resource-client` | 132.5K | the `mini` command, the ssh shell, the server-rendered web body, the apps worker, pay, fleet, bend, chat, key adoption; plus 129 journey scripts (28.5K lines) and 132 templates (laws, the MUD realm) | 127+ commands in one binary. The typed verb grammar (`shell_grammar.rs`, 75 entries) coexists with hand-written verb rows it has not replaced. Per the 10-26 review about 41K of its lines were the deployed demo |
| `grain-runtime` | 64.5K | the Hermes agent controller: supervisor per member grain, MCP broker, provider gateway, room resident, concierge | `main.rs` is 21.6K lines |
| `spk-host` | 63.5K | custody and sandbox launch for Sandstorm grains, the HTTP custodian, broker, volume helper, hosted conversations | Agent API v3 is in the tree, parked (`#[allow(dead_code)]`, "ruling R7") |
| `mini-sdk` | 13.3K | consent-gated signing and the custody record that keeps each attempt's exact retry; app-interface declarations and their executor | checked against a Lean-built codec library (`lean-codec/build.sh`) |
| `discord-entrance` | 8.0K | the Discord gateway, the join door and its processor, the mirror | |
| `mini-keys` | 6.4K | the key broker: the one process that holds provider keys | |
| `pay-watcher` | 3.8K | the Solana observation tick (698 JSON fixtures) | |
| `hyperdocument-link-sqlite-store` | 4.0K | the Host's durable byte store | misnamed: it is the Store helper |
| `mini-web`, `mini-web-spawn` | 4.7K | the browser gateway and the per-member session helper | |
| `spk-rpc`, `spk-package-stream`, `signed-api-path`, `compatible-upgrade-custody`, `mini-streams`, `mini-session-env`, `mini-kernels`, `credential-signature-verifier`, `launch-gate` | about 6K | libraries and small tools. `mini-kernels` is the Rust behind Lean's six `@[extern]` seams (cSHAKE256, KMAC256, Ed25519, SSHSIG) | |
| `inference-scheduler` | 4.1K | fair-share placement of shared homelab inference | packaged; nothing starts it |

Not shipped:

| unit | lines | what | status |
|---|--:|---|---|
| `private-backend` | 25.8K | an asynchronous BFT MPC stack (§5.11) | own workspace; research |
| `joint-agreement-crypto` | 0.7K | signature, journal and transport helper for the Lean Simplex driver | called only by Lean executables |
| `oracle-appliance` | 1.2K | the fd-3 endpoint for the Oracle7 appliance | held (§5.29) |
| `portable-archive` | 0.3K | "physical-only operator experiment" | orphan |
| `objective-emit` | 0 Rust | a hand C machine for Core4, differential scripts, and the Lean-versus-C diagnosis | not a Cargo package |
| `mini-sdk-ts` | 1.0K TS | a TypeScript twin of the SDK over wasm | no script runs its tests |
| `hermes-test-provider` | 2.3K | a scripted model endpoint for journeys | fixture |
| `hyperdocument-link-store`, `launch-gate` | 0 | an empty directory left by a deleted twin; a manifest pointing at `deploy/grain-host/launch-gate.rs` | |

Cross-language seams: `protocol/host-operations.json` generates `Host/HostOperations.lean` and
`native/host-operations.rs`; `protocol/hosted-conversation.json` generates Lean and Rust;
`native/resource-client/src/bounds.rs` is the only Lean-emitted Rust in the client; `prover/generated/*`
are Lean-emitted; everything else in Rust that mirrors a Lean definition is hand-written and checked, if
at all, by a pinned test.

### 3.11 `prover/` (8.5K lines): island

BabyBear, Ext6, binary towers, additive NTT, MLE kernels, a sumcheck engine mirroring Selvage's
(`sumcheck.rs`, 1,500 lines), and `tower256_fri_prove.rs` (the 11-06 additive-FRI prover, "work 9104").
Lean writes its test vectors by `#eval`; no crate depends on it; Lean has no `@[extern]` into it. Per
the 10-26 review it holds internal twins (MLE evaluation five ways, fold three ways). Two Lean files name
`prover` sources that do not exist (`nextgen_light_client.rs`, `tests/conformance.rs`).

### 3.12 `deploy/`, `scripts/`, tests and worlds

- **`deploy/`**: `candidate/` (the only commit-to-pinned-binaries path; `lane-build.sh` is the builder's
  stage runner), `spk-host/`, `grain-host/`, `hermes/` (`demo/install-hermes`), `market/`, `door/`,
  `pay/`, `shell/`, `discord/`, `web-frontend/`, `demo-seed/`, `migrate/` (the world migration, §5.38),
  `oracle/` (63 files, 11K lines of packaging with no unit; held), `fn/`, `clock/`, `policy/`. The units
  that ran the Store, keys, consent, certifier and Hermes on the box are in `~/dev/dregg-infra`, as is the
  gate's edge tree.
- **`scripts/`, live:** `pipeline/builder` (the unattended loop on hbox), `integ-build`, `gate` (rows:
  tour, composed, enrol, j14-apps, flatness), `sweep`, `world-reap`, `lane-tree`, `lane-check`,
  `native-loop`, `hot-swap`, `umbrella-tree`; `host-operations.py`, `hosted-conversation.py`,
  `lean-build-surfaces.py`; `build-native-host.sh`, `build-mini-kernels.sh`; the `check-*` gates that
  `local-gates.sh` runs.
- **`world/`**: 28 Objective Bend programs in 16 directories (ballot, bounty, collective, commons, drex,
  dues, market, play, station, story, workshop, activity, call, send, seats, automatafl).
  `scripts/check-world-cohorts.sh` runs the cohort files in the effect-free preview. `activity/Tally`,
  `call/Calls`, `send/Sends` and `seats/Broker` run natively through the acceptance scripts. Five station
  and workshop programs and all of `automatafl/` are referenced by nothing outside their cohort or docs.
- **`tests/objective-bend-source/`** (97 files): parser, elaborator and preview tests, including the
  `ltuo/` probes against Faré's text. `tests/lean/` (3 adversary files) and
  `tests/consent/test_proxy_adversary.py` are run by nothing.
- **Journeys** are not here: `native/resource-client/journey.sh` and `journey.d/`.

### 3.13 `docs/`

`docs/README.md` indexes 84 of the 160 other top-level documents; it omits every fn, oracle and
`*-STATE` file. The documents fall into:

- **Present-state descriptions rewritten against the code** (they mark each section shipped, changed or
  design, and are the most reliable prose): `SURPASS`, `COMPUTE`, `MUD`, `CHANNELS`, `DATAMODEL`, `PLACE`,
  `ZK`, `OBJECTIVE-BEND*`, `WORLD-MIGRATION`, `RETAINED-MODE`, `DURABLE-STORE`, `PAY`, `SEATS`,
  `EFFECTS-REVIVAL`, `GENERIC-SIMPLEX-NATIVE`, `DISTRIBUTED-DESIGN`.
- **Lists of owed work:** `ROWS-OWED` (146 rows, 91 not green, as of 10-28), `PERF-BACKLOG-2026-10-28`
  (10 ranked items and about 1,360 unverified reader findings), `BACKLOG-2026-10-27` (72 open),
  `HOT-PATH-STATE` (the newest, 11-08), `PERF-CLIENT`, `KERNEL-TWIN-AUDIT`, `SELVAGE-COMPLETE`,
  `TOWER256-FRI-PROVER-WORK`, `PROVER-PLAN`, the 21 `*-STATE.md` lane notebooks.
- **The plan and its reviews:** `DEMO-PREFIX-2026-10-26` (its Phase 3 table C1-C9 is the best single list
  of large intended work; §9), `DEMO-EXPERIENCE-2026-10-27`, `COORDINATION-2026-10-27` (superseded in
  part by `board/README.md`), and `docs/review/` (79 files). The whole-tree reads there are
  `2026-10-26-history/HISTORY.md` (what happened to 10-26, from transcripts),
  `2026-10-26-triage/{LEAN,RUST}-TRIAGE.md` (measured delete, rescue and repair lists),
  `2026-10-26-native-crates/` (every crate read whole; `SYNTHESIS.md`), `2026-10-26-deploy/`.
- **Founding and August design:** `ATLAS.md`, `PROJECT.md`, `PROOF-ENG-DESIGN.md`,
  `CROSS_REPO_CONTRACTS.md`, `HYPEREDGE-DESIGN`, `KERNEL-NECESSITY`, `N2-*`, `N4-*`,
  `PROOF-SYSTEM-SURVEY`, `SELVAGE-RECOMPOSITION`, `decisions/` (D-0001, 0002, 0004, 0005, 0006).
  `PROJECT.md` describes generation B and is otherwise unrevised.
- **Evidence** (`docs/evidence/`): run records; nothing dated after 10-28.

### 3.14 Leftovers

`files.txt` (a 19-line file list from a 10-03 snapshot commit), `SOURCE-INBOX.jsonl` (ten rows naming
source archives on hbox whose adoption was never finished; four name files that never landed),
`EVENTS-DESIGN.txt` and `SUMS-DESIGN.txt` (10-04 Objective Bend lane notes, each cited once), `.spw/`
(a one-day snapshot of an external tool's map and audits), `spk-notes/` (per-app porting notes),
`scratch/` (four files; `CordKeyCollision.lean` is an unproved input to a Nock question), and the empty
untracked directory `native/hyperdocument-link-store`.

### 3.15 Branches and worktrees

`main` equals `origin/main`. `origin/green` (the last commit the builder found fully green) is
`980d80c5d` of 11-08, 56 commits behind. 80 of 352 local branches hold commits not on `main`; 29 remote
branches do; 275 worktrees are registered. The branches that carry substance not on `main`:

| branch | commits ahead | what |
|---|--:|---|
| `wip/iter-speed-modules` | 16 | the Lean module-system port: 794 files, +16.2K/−2.4K (§5.33) |
| `lane/arklib-sr-bridge` | 8 | Selvage's state-restoration keystone derived from ArkLib's (§5.8); finished, waiting on a merge decision |
| `lane/pcdsystem`, `lane/costmodel` | 4, 2 | DAG proof-carrying data; the cost model as a Lean function (§5.37); their lanes were cut off mid-work on 11-07, so both are partial |
| `lane/accel-tower256-gpu`, `lane/redesign-native-openings` | 4, 4 | the Tower256 prover on a GPU (§5.5); complete, never merged |
| `lane/mma-exact` | 3 | exact integer accumulation on tensor cores (§5.36); complete as statements; its measurement went against the idea |
| `lane/perf-client-moved`, `lane/perf-client-census`, `lane/perf-client-hotfix` | 13, 4, 7 | client and consent performance; some landed by other paths |
| `wip/retained-held`, `retained-held-measure` | 6, 6 | the held served state; its seat says it measured slower than base and must not merge as is |
| `origin/wip/he-enrol` | 2 | Store index family 2 and dispatch on the light opening; never compiled |
| `lane/wave-*`, `lane/wave3-*` (9 branches) | 1-4 each | three waves of Gemini lanes, 11-01 to 11-02: world overhaul, assurance de-twin, host on the light opening, receipt inclusion and a laws workbench, seat verbs and a clearing solver. Their content reached `main` through the `perf-client` lane (`e4796e5f7`, 11-04); only the refs are unmerged |
| `lane/oracle-v7-qualification`, `codex/oracle-*` | 23 | Oracle7 qualification; held |
| `lane/hermes-live` | 24 | Hermes resident fixes from 10-27 |
| `hotfix/stop-fence-on-980d`, `origin/hotfix/consent-count-on-980d` | 13, 18 | hotfixes cut from `green` for the box |

---

## 4. How the parts relate

### 4.1 The served path, end to end

```
member key ──► mini (resource-client) ──► consent provider (Lean exe: Host.ClientConsentSession)
                   │                          checks what the key is about to sign against the
                   │                          member's own replay of the world
                   ▼
            signed frame, kept in the custody record before it travels (mini-sdk)
                   ▼
   minidregg-host (Host.Main) ── op byte ──► receiver family (Kernel.*Receiver)
                   │     signature first (credential-signature-verifier / mini-kernels)
                   │     authority: capability lineage in the authority cell
                   │     law: Kernel.ReceivingLaw judges every written cell by its own law (Pred.eval)
                   │     charge: exact, per lane
                   ▼
      DurableCheckpoint.prepare ► DurableDataIntent.execute ► append   (generation B's executor)
                   │                                   proved to refine World.step (generation C)
                   ▼
      Store helper (hyperdocument-link-sqlite-store): log, checkpoints, index tries
                   ▼
      receipt + world root (cSHAKE256 trie over cell roots) ──► client; `why`, `can --any`, exact retry
```

Applications and agents enter the same path as members. A Sandstorm grain's requests go through
`spk-host` to the `Application*` receivers. A Hermes resident runs under `grain-runtime`, holds no key, and
writes through grants a member gave it, paying from a purse on the Book. An Objective Bend program runs
inside the Host as an activity: the kernel re-runs the Lean front end on the stored package, runs the
demand machine under a declared envelope, and commits the Plan it yields as one turn.

### 4.2 Lean dependencies

`scripts/check-import-boundary.sh` gives each library a row of what it may import. `Theory` imports only
itself; `Selvage` only Theory (11 files of it); `Effects` and `Pred` only Theory. `Kernel` and `Compiler`
are allowed to import each other and do: 157 Kernel files import `Compiler.*` and 48 Compiler files
import `Kernel.*`, so the two are one layer in practice. `Host` sits on both. `Assurance` imports
everything. The hubs by importer count are `Kernel.NativeHost` (48),
`Kernel.NativeHostReplay` (42), `Kernel.ContentResource` (26), `Kernel.DeclaredResourceController` (25),
`Kernel.DurableDataIntent` (23). The Host executable's closure was 787 modules and 330K lines on 10-26
(per `LEAN-TRIAGE.md`); nanodregg's charter set 150 as its ceiling in reaction.

Concrete imports everywhere are why builds were slow: a pin regeneration rebuilt about 486 modules, a
deep Theory edit 631 in 39 minutes (ember, 10-28: "there are HUGELY DIFFERENT WAYS we should have been
structuring this code from the beginning"). The one seam cut since (codec tags behind a private import,
`f2002e589`) took a census-tag edit from 365 modules to 4.

### 4.3 What depends on the proof system

Nothing served. `Deployed.lean` excludes Selvage. The served closure still carried 12 Selvage modules on
10-26 through one import chain (`Sp800185Cshake256` → `Tower256CshakeMerkleController`); `Deployed.lean`'s
header says that chain was since cut. The 10-26 triage measured an upward-closed research set of 227
modules and 110K lines (Selvage 140, Assurance 57, Compiler 29) that no executable and no qualification
library touches.

### 4.4 Sibling repositories

| repository | relation to this tree |
|---|---|
| `~/dev/breadstuffs` (GitHub `dregg`) | the first system, 2.9M lines. The atlas's file references point into it. Several Theory files are ports. "Waits there to be either resumed or truly-composted" (7c10f132#2156) |
| `~/dev/nanodregg` | the single-writer rebuild founded 10-16 when a cut in place was judged too risky; twelve laws, each "a response to a measured minidregg failure". Wound down 10-27 ("we have little to learn from continuing to work on it") |
| `~/dev/obend` | Objective Bend extracted on 10-29 from delvetalk, nanodregg and this tree; typeclasses and Lean modules from the first day because of this tree's build times. Larger than what remains here |
| `~/dev/zkml-research` | zkML and verifiable-FHE research since 08-12; holds Selvage's copy (`selvage/`, 260 commits of history) since 11-11; `Assurance/CostModel` on its branch here cites its `docs/COST-MODEL.md` and `LEAF-PROVER-DECISION.md` |
| `~/dev/degg-research` | MPC and homomorphic encryption for coordination; the planned home of `native/private-backend` (not moved) |
| `~/dev/o7vn` | veri7vn / Oracle7. The appliance was built against this tree in October, then separated ("mini is someone else's job", cx-01a14da6#35910) |
| `~/dev/fn` | the NNTP transport, adopted 09-26 as a semi-untrusted carrier; its consumer side is 44 Kernel files here; out of the demo; its successor is fn2 |
| `~/dev/dregg-infra` | the box: units, installers, the gate's edge tree, the walk that ships a candidate |
| `~/dev/delvetalk2` | the Objective Bend MUD town that shipped about 17 editions in October from the same edge box |
| `~/dev/redregg` (private) | the notes repository: reviews, retrospectives and plans that this tree's documents cite |

---

## 5. The experiments

Each entry: the question, how far it got (the strongest result present, with its real scope), where it
stopped, what closing it needs in dependency order, and what closing it would teach. No estimate of
effort is given anywhere.

### 5.1 One transition: is the Host the World?

- **Question.** Can the function a writer runs be the function the theorems are about?
- **Got to.** `Kernel/World.lean` is complete as a model: `World.admit`, replay exactness, journal
  exactness, ROM immutability after birth, checkpoint soundness. `TurnCensus` decides that all 48
  admission constructors' shapes are admitted by `World.admit` and their negations refused by name.
  `HostRefinesWorldCore.deployed_refines_step` and `host_trace_represents_fold` prove the present Host
  (`DurableDataIntent.execute` plus the append and checkpoint rebase) refines `World.step` on the turn
  `Turn.ofIntent` derives, over every schedule including crashes. `Host/WorldSim.lean` runs both sides
  from seeds and from retained Stores. The append path refuses an intent whose charge is not its derived
  turn's.
- **Stopped at.** Stage 1. `host_submit_is_step` is written in `HostRefinesWorldCore.lean` as a statement
  and not proved. `World.admit` has no caller on the Host path (only `WorldSim` and `TurnLogFollower`).
  The header lists what the representation still leaves model-side: the journal holds only the id's
  presence (G-JOURNAL), the parent plane is a twin of the system cell's rows (G-PARENT, T7), capability
  and key epoch are not in `DataIntent` (G-AUTH), the window translation is owed per receiver.
- **To finish.** Prove the receipt half (`Loaded.worldRoot = WorldRoot.rootOf`); persist turns, not post
  images (the turn log exists: `TurnLog`, `DeployedTurnCompact`); run `World.admit` in gate mode on the
  receive path, refusing on disagreement (plan item C1); then make `Loaded` a `World` and delete the
  consumed-set and parent-plane twins.
- **Would teach.** Whether the two-state-machine arrangement (a model and an implementation joined by a
  refinement proof) can collapse to one without losing the Host's speed, and what the refusing-path gap
  actually costs. This is the project's thesis stated as a theorem; it is the one place where finishing
  changes what every other kernel theorem is about.

### 5.2 The derived path: effects from declarations

- **Question.** Can a kernel effect be one declaration from which its executor, codec and receiver arms
  are derived, with the hand arm deleted?
- **Got to.** The engine and its completeness keystone are proved (`Effects/Revival/EngineProofs`). Over
  the deployed controller: `ContentComplete` (every one of the fifteen content actions writes only its
  declared fields), `PrepareFactors contentSpec` (the deployed per-target preparation is the content
  handler's dispatch followed by payload-blind checks), `HostTeeth`, the commuting-append statements,
  and the two refusal levels of an activity's yield are proved. `docs/EFFECTS-REVIVAL.md` §1 counts what
  one hand-written payload kind costs today: 49 arms in 11 Lean files.
- **Stopped at.** `HostKeystone` is "known false today, by clause" (`Kernel/EffectsRevival/Statements.lean`
  §7): unknown payload tags refuse as `malformed` instead of by name, and code 1 is still served by the
  hand arm. Eight of nine payload codes are `hostLegacy`. The second substrate (the Book's posting
  algebra, for transfers) is named and not built. `Kernel/ObjectiveActivityEffect.lean`, the most recent
  hand-written effect, is WIP-only.
- **To finish.** The migration commit: route the payload decoder through the registry and delete the
  content arms of `computeTarget` and `targetPatch`, making `HostKeystone` true. Then one declaration per
  remaining payload code. Then the posting substrate and the activity's transfer and commit effects.
  Then generate the persisted-codec rows and receiver arms from declarations.
- **Would teach.** The measured ratio between a declared effect and a hand-written one on a kernel that
  serves real traffic, which is the founding law's claim. Ember's ruling (10-27): "hand-written kernel
  changes aren't really acceptable after all".

### 5.3 Law to constraints

- **Question.** Can the constraint system that proves a law held be compiled from the law?
- **Got to.** `Compiler/PredCompile` compiles a `Pred` to a constraint system with sound and complete
  witness lowering. `Air`, `AirFlatten` and `Emit` take nested expressions to a degree-2 gate system and
  a serialized descriptor with `emit_accepts_iff`. `NoteSpend` composes range, hash and membership
  gadgets into a shielded spend with `noteSpend_binds`. `AdmissionAir` derives the first kernel's gated
  admission. Four gadgets of a recursive verifier exist.
- **Stopped at.** No prover takes the output; admission re-executes the law. `PredCompile` names explicit
  residuals for order, oracle and quantified atoms. The gadgets target the first kernel and BabyBear;
  the served kernel hashes with cSHAKE256 (`AirKeccak` and `AirCshake` are the bridge, built for private
  cells).
- **To finish.** Choose the backend (§5.5 or §5.6), emit a served law through it, and bind the policy
  term in the statement, not the decision bit (law 12).
- **Would teach.** What a proof of "this law admitted this write" costs at the served hash and field,
  which decides whether proofs at admission (`docs/ZK.md` Part 1) are ever worth turning on.

### 5.4 Selvage

- **Question.** Can the project own a transparent, recursion-capable proof system whose soundness is
  mechanized with an inhabited floor?
- **Got to.** `selvage_zk_argument` (`Selvage/ZkRbrGame.lean:318`): knowledge soundness and zero
  knowledge of the accumulator chain, with Fiat-Shamir at `(t + k)·ε`, modulo three named assumptions
  (the sponge realizes the oracle, collision resistance, the proximity gap at macroscopic distance) and
  two named seams. `Assurance/ErrorBudget`: 55 proven bits at BabyBear⁴, code length 2²⁰, rate 1/2, unique
  decoding, grinding-dominated; `ErrorBudget120` prices a 137-bit configuration. `Assurance/SelvageV0`:
  sound, knowledge-sound and binding as reductions to an exhibited collision. A discipline of
  refutations: the unfixed Polishchuk-Spielman floor is refuted over every field with three elements;
  `MerklePcs` is proved empty at every positive height (six Assurance modules quantified over it were
  deleted 09-30); the multiplicative folding data is proved empty in characteristic two.
- **Stopped at.** `Assurance/SelvageV0Manifest.lean` §13: the sub-unique-decoding seam
  (`[ZK-RBR-extract]` lemma A), the BCS packaging (`[ACC-rbr-bcs]`), the list-decoding regime, adaptive
  tree query strategies for the grinding bound, the deployed query schedule. `OracleLogProgram` and
  `OracleLogLinked` record that the deployed-ZK adaptive bound is settled negatively as first stated.
  `docs/SELVAGE-COMPLETE.md` lists seven steps "before a defensible whole", ending with deployment and a
  benchmark against alternatives under the kill criteria of `D-0004`. Ember (11-01): without the right
  framework for probabilistic arguments, "the arguments will never actually close".
- **To finish.** In the zkml-research copy: a lakefile (it still imports `Theory.*` by this tree's
  names); then the manifest's residuals; then one proved configuration run end to end with a prover.
- **Would teach.** Whether a hash-based proof system can be carried to a deployed parameter set with
  every probability term on one ledger, and what the proven (not conjectured) bit count costs in proof
  size and time.

### 5.5 Tower256: a binary-field prover that runs

- **Question.** Can binary semantics (hashes, automata, memory) be proved over GF(2²⁵⁶) with cheap native
  work and Lean as the only acceptor?
- **Got to.** The newest proof work in the tree (11-05, 11-06). `Tower256SuccinctCheck.check_iff` (the
  checker as a `Bool`, exact against the acceptance relation), `checkBytes_iff` over a receipt codec,
  `Tower256FriNativeDeployment.acceptResponse_iff` (a native reply has authority only through the Lean
  check), a compiled honest prover at any size (`lake exe tower256-prover-run`), and a Rust kernel pinned
  byte for byte to it. `Tower256ContentCert.named_or_collision`: a content-bound automaton certificate at
  full disclosure. On branches: a CUDA port whose receipts are byte-identical to the CPU prover's, at
  17, 67 and 298 ms per proof for sizes 18, 20 and 22 on a T4, 34 to 36 times that box's CPU
  (78fef112#2985).
- **Stopped at.** `Tower256ContentCert`'s header: "no AIR layer exists yet". `docs/TOWER256-FRI-PROVER-WORK.md`
  §3: one column only, no zerocheck or lookup argument, the DFA relation not arithmetized. The lane's own
  note: the cases that run have zero folding rounds, so the challenge, seed and fold checks have no
  accepting test. The cSHAKE transport and the collision price are explicit premises. Only the executable builds the prover; the
  11-11 stock-taking session found `Tower256SuccinctCheck` red on the builder for a missing native symbol.
- **To finish.** Multi-column batching; the zerocheck and lookup arguments over the binary field
  (`Selvage/BinaryLookup`, `LogupStar` are the pieces); the trace AIR for the automaton; then a private
  receipt; merge the GPU branches.
- **Would teach.** Measured cost per Keccak permutation and per table lookup in a binary-field system
  with a Lean-checked verifier, against the BabyBear route.

### 5.6 The BabyBear/Ext6 gate proof and its three generations

- **Question.** Can a descriptor emitted by §5.3 be checked by a sumcheck-based verifier controlled from
  Lean?
- **Got to.** `CommittedTerminalCompose.gateProof_sound` (accepted implies the descriptor holds, or a
  priced event); a computable controller with an honest prover and tamper refusals
  (`CommittedTerminalController`); a Fiat-Shamir instance under the tree's own keystone; a compiled
  Stage-0 demo. `Ext6GateProof*` is the earlier noncomputable version, with eight security events left
  as supplied evidence.
- **Stopped at.** Three versions of one verifier sit side by side; the controller's header says why it
  was built beside its predecessor. The polynomial commitment, subfield proof, proximity and final
  low-degree test are premises.
- **To finish.** Keep the lane-carrier version; discharge the commitment with §5.4's BaseFold or §5.5's
  FRI; delete the other two.
- **Would teach.** Little that §5.5 would not. Its value is as the consumer that would make §5.3's
  output mean something.

### 5.7 Sponge indifferentiability

- **Question.** Can the "the sponge is a random oracle" assumption be reduced to an ideal permutation?
- **Got to.** 21 files: the run invariant, the capacity budget, an off-bad classifier with a
  `q(2q+2)/|Cap|` price, prefix programming with exact failure classification. One refutation: external
  query count is not a valid primitive-work budget for multi-block constructions.
- **Stopped at.** Several hops "remain explicit" (`Selvage.lean` lines 104-123); the eager/deferred
  coupling is a named construction.
- **Would teach.** Whether the floor of §5.4 can shrink from three assumptions to two.

### 5.8 Proximity gaps and the ArkLib bridge

- **Got to.** The gap proved for distances below `(1−ρ)/3`, then to the full unique-decoding radius
  `(1−ρ)/2` at `l = 2` (`ProximityGapUDTight`); the Johnson list-size bound for every linear code; a one-halving route
  past Johnson. `bridges/arklib-ud` imports ArkLib's BCIKS20 correlated agreement to discharge Selvage's
  premise, up to the Johnson radius on `main`. Branch `lane/arklib-sr-bridge` derives Selvage's
  state-restoration keystone from ArkLib's.
- **Stopped at.** Nothing builds the bridge. The founding decision was not to vendor ArkLib (b54b6026#329);
  the bridge reverses it in an opt-in package, after ArkLib's open `sorry`s fell from 292 to 4 and its
  toolchain pin came to match this tree's. The state-restoration branch is finished for finite alphabets
  and waits on a merge decision.
- **Would teach.** How much of Selvage's own tower is now available upstream. The lanes' verdict
  (78fef112#296): import correlated agreement and ring switching, mirror FRI and sumcheck, and Selvage is
  ahead on the round-by-round to Fiat-Shamir compiler, state restoration and accumulation depth.

### 5.9 zkML

- **Got to.** A matmul contraction sumcheck with a succinct checker and three commitment claims wired
  to BaseFold; a correction recorded as a theorem (`matmul_is_not_hadamard`); low-rank updates; a rank-1
  gradient check (`sgd_step_sound`); an MNIST trace reader. `ZkmlLowRankUpdate`'s header states the
  finding: the check removes the n² proof and not the n² commitment.
- **Stopped at.** The commitment cost. Ember (08-13): "so no good ideas for efficient zkml from our
  research...?" The thread moved to zkml-research.

### 5.10 BFV / FHE

- **Got to.** `fold_decrypts_exact` and its deployed instance (15 orders per bucket), no-wrap bounds,
  smudging with a leak witness (all WIP-only, dated 10-03/04). In the default build: all 384 exact
  integer equations of a batch checked from opaque native buffers (`Assurance/Bfv*`).
- **Stopped at.** `Theory/BfvLifetime` records that its native consumer (`native/fhe-bend`) was deleted
  on 10-04 and the next one "must re-bind these constants". `BfvProofControllerAdmission` proves that
  with zero suite pins "semantic admission is currently impossible rather than faked".

### 5.11 Private computation: the MPC backend and oblivious circuits

- **Question.** Can a private program run among several parties with the world seeing only sealed
  commitments?
- **Got to.** `native/private-backend` (25.8K lines Rust): private send, verifiable secret sharing with
  identification, an agreement stack, triple generation checked through reconstruction, crash WALs,
  recipient-key custody tied to a Host readback. Lean: the sealed-cell shape
  (`Assurance/MpcSealedCellExecution`), the oblivious circuit IR, a bounded Nock machine with a first
  refinement tranche.
- **Stopped at.** `CONSTRUCTION.txt`: "The native deployment join remains OPEN"; variable-time field
  arithmetic; no simulator; no holder-private output or resharing. `BoundedNockRefinement`: "initial
  refinement tranche, not the still-required all-opcode ... simulation". The live shell had a
  `private-compute` verb over an in-process demo.
- **To finish.** Recipient-sealed channels joined to the Host; the simulator; the remaining opcodes'
  refinement; then move the crate to degg-research as planned.
- **Would teach.** Whether "computation is sealed by default and disclosure is a separate authorized
  effect" (the invariant in `PROJECT.md`) survives contact with a real multi-party protocol.

### 5.12 Private cells

- **Question.** Can a cell be readable in part, with a proof that a reader cannot distinguish two worlds
  that agree on what it may see?
- **Got to.** Blinded cells with a per-write ratchet, served. The private index as a kept trie with one
  walk per write. `Kernel/BlindedCellHiding`: the hiding game as exact finite counting, with the hybrid
  arithmetic proved for every instantiation. `Compiler/AirKeccak`, `AirCshake`, `AirKeccakCensus`: the
  hash as a constraint system with published costs (1,600 ANDs per round after sharing).
- **Stopped at.** `board/seats/privacy.md`: the opening circuit is "Not started; no partial code
  exists"; a field-scoped prefix costs about 10M ANDs; the reference backend (MPC-in-the-head) gives
  proofs of hundreds of MB, so production needs a succinct zero-knowledge argument, which the tree's
  FRI and sumcheck stack is not yet (`W = Unit`, odd characteristic). The zero-knowledge and
  root-replacement hybrids are named open premises. Binding of the private root is owed.
- **To finish.** The opening relation as an Air system over bits; the receiver adapter (proof randomness
  and oracle state through `Serve`); binding; then a backend, which is §5.5.
- **Would teach.** The first real consumer for the proof system inside the served world, with a known
  circuit size. This is where the semantics-first world and the proof research would meet.

### 5.13 Objective Bend

- **Question.** Can the world's programs be written in a language of lazy open recursion over partial
  specifications (after Faré), checked and run by Lean, with authority supplied by the world and not the
  language?
- **Got to.** Core4 with `mix` and `fix`, a proof-producing checker, a call-by-need demand machine with
  one effect (yield); adequacy and completeness against the reference semantics (`ObjectiveProofs`); the
  front end in Lean with `decode_json`; activities persisted between turns with resume-with-view,
  consume-once and conservation theorems; calls, sends, inboxes, governed upgrade; seats; `bend publish`
  and `bend run` on the demo; a tutorial re-run by a gate.
- **Stopped at.** Most `world/` programs run only in the effect-free preview. Effects beyond the yield's
  Plan are hand-written (§5.2). The compiled Lean machine was measured 500 to 2,900 times slower than a
  hand C machine, for two quadratic reasons diagnosed in `native/objective-emit/fastmachine/DIAGNOSIS.md`;
  the C machine's refinement is "NOT proved". `world/automatafl` (the game expressed from a 2,988-byte
  language capsule and compared against a Rust oracle) is run by nothing.
- **Moved.** `~/dev/obend` since 10-29.
- **To finish here.** Decide whether this tree consumes obend or keeps its own Core4; if the latter, the
  fast machine as the differential reference and the retirement of `runtime.c` (plan C7).
- **Would teach.** Whether world programs written against laws compose in practice, which the demo did
  not get far enough to show.

### 5.14 Proofs of Objective Bend runs

- **Got to.** `Compiler/BendCommittedRunSound.direct_forces_both_success` and the trace constraint
  system; Keccak and cSHAKE as AND/XOR networks; masking theory. All WIP-only, dated 10-03.
- **Stopped at.** The 10-01 ruling. `docs/ZK.md` Part 2 says link by link what a verified proof of a run
  would establish today.

### 5.15 Programs refereed by re-execution: Nock, evaluators, jobs

- **Got to.** Nock 4K with a sound and complete fueled evaluator exported to C; a syntactic cost bound
  with loop summaries; an evaluator registry (`Compiler/Evaluator`, registry `[nock]`); `Kernel/Run`
  (`checkRun_sound`); doors; a job as a cell whose law is a `Pred` with escrow, bond and slashing on the
  Book. Served as ops 131-137 and the `job` verb.
- **Stopped at.** `docs/COMPUTE.md` §1: the operator can drop truth turns until the window closes, and
  "nothing yet" bounds it; certification is the operator's word. Ember (10-01): "we DEFINITELY do not
  need to be stuck with nock".
- **Would teach.** With a second evaluator registered (Core4 is the candidate), whether the registry is
  the right seam between the kernel and languages.

### 5.16 Laws as products: the story, the MUD

- **Got to.** A sealed story whose table is the law on every player's cell
  (`sealed_story_scene_monotone`, `sealed_story_never_relawed`), served as the demo's built-in tale. The
  MUD's sheet and item laws as written in templates, with theorems over any accepted history
  (`no_dupe_unique`, deaths monotone), and the Tidewrack realm as data.
- **Stopped at.** The MUD never ran as a game; `docs/MUD.md` marks combat resolution and markets as
  design. `StoryHistory` names residuals R1-R3.

### 5.17 Seats and certified clearing

- **Got to.** Offer safety on every reallocation, an exit no clause can forbid, conservation
  (`Kernel/Seat`); a batch auction cleared by an untrusted solver and admitted only with a certificate of
  ε-optimality (`Kernel/CertifiedClearing`). Served as ops 215-219. Branch
  `lane/wave3-surface-solvers` adds a clearing solver in the client.
- **Would teach.** Whether "untrusted solver, certified result" generalizes beyond one auction form.

### 5.18 Agreement: Generic Simplex

- **Question.** Can a domain's log be agreed by a committee with the engine written and proved in Lean?
- **Got to.** Safety proofs (`SimplexQualification`: 26 modules); a native driver with ML-DSA-65
  certificates, a durable journal and transferable commit evidence; harness executables that reproduce a
  timed stall and reopen 100,000-entry journals.
- **Stopped at.** No liveness proof (ember, 10-31: "it needs to prove progress and not just safety").
  Reconfiguration and the transferable witness are WIP-only. The demo had one operator. An outside pull
  request (#18, a prepared catch-up jump) is open with its first question unanswered.
- **To finish.** Liveness under partial synchrony for the timer as modified; reconfiguration that
  preserves liabilities; then a second operator.
- **Would teach.** What "genuinely multi-party domains" cost the kernel: the world model assumes one
  writer per world.

### 5.19 Ordering and independence

- **Got to.** I-confluence with a guard classifier; views merged as colimits and the overdraft pair
  with no colimit; a four-tier finality ladder with no downgrade; the coordination dial as a function
  from a law to a verdict; revocation needs consensus and issuance does not; the finality gate as a
  decider.
- **Stopped at.** `docs/DISTRIBUTED-DESIGN.md`: the lace, the liveness carrier and the derived finalizer
  are not built; no `Distributed` library exists. Nothing served consults a tier.

### 5.20 The kernel's necessity theorems

- **Got to.** N2a/N2b (the turn's cone data is a wide-pullback limit; conservation is its equalizer);
  N3 and its converse (opaque payloads forbid a faithful second reading); N4 (`Compiler/DistributiveLaw`:
  adequacy and congruence, with the finding that naturality does not force fail-closedness).
- **Stopped at.** `[N4-home]`, `[N4-hyperedge-instance]`, `[N4-gsos]`. Per the twin audit no theorem of
  `Kernel/Turn` is ever applied to a later kernel's hyperedge: "the bridge is decorative".

### 5.21 Hyperdocuments

- **Got to.** Generation B's widest slice: typed operations, causal versions with proof-relevant
  ancestry, conservative merge that keeps conflicts, transclusion references with backlinks, stable
  ranges, and Assurance slices from publication through crash recovery to a SQLite store. The served
  system has documents, links, embedded live ranges and a link index (`Kernel/LinkIndex`,
  `Kernel/ContentResource`).
- **Stopped at.** `PROJECT.md`: the complete operation grammar, conflict resolution policies, rights and
  views, checkpoints and garbage collection. The served content cell and generation B's hyperdocument
  model are different carriers.
- **Moved.** Ember (8f470963#1) reframed these as "specific attempts to try and get the more general
  capacity" that obend is after.

### 5.22 Traffic privacy

- **Got to.** Stack 1: constant-rate channels as a Lean model with theorems and a kernel epoch record
  (served as journey step KCH on a fresh Store). Stack 2: a post-quantum mailbox and a guarded cohort TCP
  adapter in the client (4.4K lines), with a two-host run recorded.
- **Stopped at.** Stack 1's relay and client were deleted on 10-26. Stack 2 is "research line ... outside
  the public candidate"; "No independent-host deployment ... or privacy proof exists". The unified
  design ember described on 10-01 (constant rate, erasure-coded, onion-routed, and reaching agreement on
  an order) was never built.

### 5.23 The fn transport

- **Got to.** 44 Kernel files for the consumer side; a wire-grammar interpreter proved to round-trip,
  pinned to fn's vendored grammar and 1,028 vectors; selective release; an archive publisher.
- **Stopped at.** Out of the demo by ruling. `protocol/fn/images.json` has no checker. fn continued as
  fn2.

### 5.24 Portable continuation

- **Got to.** Manifest, home-transfer admission and receiver, archive IO (all WIP-only), and
  `native/portable-archive`.
- **Stopped at.** `docs/PORTABLE-CONTINUATION.md`: "No whole-home transfer has run."

### 5.25 Private rooms and room key release

- **Got to.** A wrapping law for room keys and member grants that read only their own wraps (served).
  Room key release (six modules) is WIP-only; `jpriv1.sh` says "AUTHORED, NOT YET RUN against a real
  Host".

### 5.26 PAY

- **Got to.** Observed Solana transfers mint Book credit under an audit identity; enrollment by payment;
  a subscriber tier; a watcher; served on mainnet.
- **Stopped at.** The watcher refused about one observation in fourteen on a clock-view race (memory
  note, 11-04). `pay-watcher/README.md` contradicts itself about the per-index cursor. Ember's open
  design idea: verify a payment posted after local records are purged.

### 5.27 Applications: Sandstorm grains with typed interfaces

- **Question.** Can ordinary web applications become world citizens that agents drive through typed
  tools beneath the HTML?
- **Got to.** Any Sandstorm package installs on its own origin; 22 recipes built here; WebDAV, CalDAV and
  git; 33 interface declarations that generate tools and are interpreted by one executor for calls and
  for qualification; a hosted-conversation protocol generated into Lean and Rust.
- **Stopped at.** The demo's seed carried three apps (EtherCalc, Etherpad, reveal.js) against a target
  of two to three dozen. The `apps-hermes` seat file (11-01) has Scrumblr qualifying and WBO and
  Hummingbird not; all three qualified later that day under the Gemini session. About 1.0 s of
  Host turns and 1.2 s of controller time per hosted operation; app creation to first page about 26 s.
  A grain's own state lives in its volume on the box and never enters the world root.
  `docs/APP-INTERFACE-2026-10-28.md`: "Hermes attachment/catalogue wiring, the composed real-agent turn,
  and Lean validation of the receiving extension remain open." Two browsers on one grain was refused.
  The 184-file `Application*` stratum keeps every past record version alive.
- **To finish.** A candidate carrying the last fixes and the two qualify runs; the controller-side cost;
  the real-agent turn; then the strata consolidation at a re-genesis (plan C3).
- **Would teach.** Ember's hypothesis of a "hybrid web2/web3 system": whether agents acting through
  declared interfaces on live app data is a product.

### 5.28 Agent residents and their economy

- **Got to.** A resident in a room under a member's grant, with a purse, per-member caps, provider
  routes with tariffs, and prompts that survive a controller restart.
- **Stopped at.** Ember on the live box (11-06): "the lobby bot...posting every minute...yikes". The
  lobby resident held one provider attempt needing "manual reconciliation" with no operator verb. Per the
  crate review the economy is Rust-invented and one upstream timeout could wedge a purse. The
  inference scheduler is never started. Plan C6 (the grain economy in Lean) is unstarted.
- **Would teach.** The demo's second tangible moment ("an agent is a member") at a quality where a
  stranger could judge it.

### 5.29 The Oracle appliance

- **Got to.** A Rust appliance, grant factory, Hermes tool routes and 11K lines of packaging and
  acceptance scripts; qualification branches.
- **Stopped at.** Held 10-31; the six SQLite members exceed the package format's member limit
  (`spk_packable: false`). Continues in `~/dev/o7vn`.

### 5.30 Never slower over time: retained mode, the light opening, bytes

- **Question.** Can every operation cost what it changes, with derived values maintained and not
  recomputed?
- **Got to.** `Theory/Retained` (maintained equals recomputation, proved once); the light opening that
  serves ported operations without replaying history (`Kernel/NativeHostLight`, `Compiler/DurableServed`);
  World legs that carry only changed ops; the kept world-root trie; packed record bodies (consent cold
  start 42 s to 30 s and 2.9 GB to 1.7 GB at 3,777 records); the host build stage from 2,476 s to
  1,005 s; a round of the builder in 468 s.
- **Stopped at.** `docs/HOT-PATH-STATE.md` lists 18 remaining accumulated-size costs. The deployed cell
  commitment is a flat hash whose preimage is `44 + 32·entries` bytes, so a one-entry change is O(entries).
  Cold first read and restart are the full Store open, O(height), until the Host session and replay are
  retyped over the light opening (KN2 stage 2b) and the consent provider ported after it. The held
  served state measured slower than base. STOP still walks. `ByteArray` conversion: about 226
  occurrences in 89 files remain for post images. Flatness ratios at the last measurement were 3 to 5
  against a bound of 2.
- **To finish.** KN2 2b; the consent port; `canonicalPostBytes` packed; persistent indexes for the
  listed terms; the per-cell commitment as a tree.
- **Would teach.** Whether a Lean-executed kernel reaches the 10 ms bar ember set (11-06) at demo scale,
  or whether the representation choices of generation B cap it.

### 5.31 The fleet surface

- **Got to.** `Kernel/FleetTurn`: join, send, transfer, receipt lookup and event topics for an agent
  fleet, as one receiver, with a journey and a measured run (09-30).
- **Stopped at.** `docs/FLEET-MIGRATION.md` describes moving helm onto it; helm was retired for this
  project on 09-04. `CLAUDE.md` still names it the north star.

### 5.32 Assurance tooling

- **Got to.** `#assert_axioms` pins beside theorems (4,257 on 10-26, per the triage); `TokenCensus` (374 private
  constructors each minted only at home, with a planted forgery caught for every one); a hypothesis
  ledger; the persisted-codec census.
  One of the 11-01 Gemini lanes wired the kernel-facing Assurance modules into `Deployed.lean` (2 modules
  to 24), the only work that moved theorems onto the served closure after September.
- **Stopped at.** Ember (10-28): "I don't want to /pin anything/ ... The code just is and does what it
  is." The census tail became the longest part of the umbrella build (`TokenCensus` 31 minutes on the
  Mac; unprofiled). 18 or 23 open defect rows, depending on which document is read.

### 5.33 The Lean module-system port

- **Got to.** Branch `wip/iter-speed-modules`: 794 files converted, with rules learned per wave. Parts
  landed (`module`, `public import`, `@[expose]` appear across `main`).
- **Stopped at.** 16 commits unmerged since 10-27.
- **Would teach.** How much rebuild fan-out the module system removes on a tree this entangled.

### 5.34 Durable and replicated settlement models

- **Got to.** A WAL device model whose recovery fold tracks the settlement model, with compaction
  invisible to recovery; framed records with torn tails; quorum-certificate finality with authenticated
  votes; irreversible external effects in three classes.
- **Stopped at.** `PROJECT.md`: "That handler is a device MODEL." Ember (10-31) removed fsync everywhere:
  "The network boundary is NOT meant to imply permanence"; the threat model trusts the storage device.
  No class-2 or class-3 target and no production class-1 target exists.

### 5.35 EVM Stage 0

- **Got to.** A five-opcode fragment checked against a real EVM's vectors; an untrusted refusing
  decompiler; the u256-add descriptor registered as native work 9103.
- **Stopped at.** Stage 0.

### 5.36 The November audit and unlearning files

From 11-05 to 11-07 a separate programme on verifiable training and inference ran from session 78fef112
(working directory `~/dev/aidev`, 131 sub-agents). Its register of 19 numbered initiatives is
`~/dev/whatember/INITIATIVES.md`. Most of its work is in breadstuffs and zkml-research. Eight initiatives
put Lean or native code here: the Tower256 leaf prover (2; §5.5), one dark-learning theorem (3), iteration
speed (7), the audit theorem (8), tensor-core exactness (14), the ArkLib bridge (15; §5.8), unlearning
certificates (16), and accelerator readiness (17).

- **Why here.** A lane of that programme chose this tree, not ember (78fef112#451): the root hash was
  already ruled to be cSHAKE256; Keccak is about 51 times cheaper to prove in a binary field; "Lean owns
  acceptance and native code is opaque" was already this tree's rule; breadstuffs had been frozen since
  10-01; ArkLib sits on this tree's toolchain pin.
- **Got to.** Commit-then-audit sampling against a fully adaptive adversary (`Selvage/AuditSampling`:
  detection probability per round; expected corrupt rounds before the first alarm at most `1/q`; and the
  statement that sampling amortizes the checker and never the ledger), instantiated over two checkers
  (`AuditFlashProve`, and `AuditExact` over a bit-exact integer recompute of a 20B-parameter model) with
  the decision rules exported to C. Exact deletion certificates and an SGD deletion bound
  (`Assurance/Unlearning*`). Expected injected displacement before the first alarm (`AuditDisplacement`).
  On branch `lane/mma-exact`, exact integer accumulation on tensor cores; the measurement said the route
  loses on a T4.
- **Stopped at.** The session's last message is 11-07 19:16Z with 22 lanes still marked running after a
  burst of network drops; it was not resumed. Ember's redirections inside it are a judgment on method:
  "we learned ~nothing from this that we couldn't have just Known, analytically" (#2364). A dig of her
  directives found that what gets built is "runs, censuses and measured demos" and what does not is
  "generators, calculi, proof-repair tools and analytic bounds" (#2989).
- **Relation to this tree.** These files use Selvage's finite-probability vocabulary and have no consumer
  here. They went to zkml-research with the Selvage copy; the `Assurance/Unlearning*` files did not.

### 5.37 DAG proof-carrying data and the cost model (branches)

`Selvage/DagPcd` (branch `lane/pcdsystem`): knowledge soundness of accumulation over an arbitrary DAG with
error `(t + N)·ε`, per node and depth-free, with a concrete scheme and a diamond run under `#guard`.
`Assurance/CostModel` (branch `lane/costmodel`): proof-system cost as a total function of the knobs, with
security drawn from the tree's proved walls and a proven 100-bit configuration. Both come from the
programme of §5.36, opened as "analytic" lanes on 11-07 an hour before that session went quiet, so both
are partial. Neither is merged, and neither went across in the Selvage copy.

### 5.38 Carrying a world across a re-genesis

- **Got to.** `deploy/migrate/world-migrate`: capture through each member's own signed reads, rebuild on a
  new genesis so that "only hashes, heights and ids change", verify; walked on the demo box including one
  app grain with its volume (11-09).
- **Stopped at.** Two re-geneses before the grain carry existed stranded members' app writes in retired
  volumes. There is no in-place format migration: a Store is pinned to its Host image.
- **Would teach.** A general answer to "the format changed" that is not a migration tool per format.

### 5.39 Consent, custody and exact retry

- **Got to.** The client keeps the exact bytes before they travel; an undecided attempt is looked up or
  retried byte for byte; a Lean consent provider derives what a key may sign; thin consent
  (`opened_display_is_commit`); post-quantum signatures.
- **Stopped at.** Per the crate review, about 15 hand-rolled custody machines beside `mini_sdk::custody`
  and no Lean concept of "this retained call can never be admitted" (plan C7). Hosted keys lived on the
  box. The consent provider held 1.65 GB at 3,777 records.

### 5.40 Smaller surfaces

Discord entrance (bot and door served; interactions never verified end to end). Web front end (every
shell verb a form derived from the command grammar, 203 leaves). Confinement (nspawn, Landlock,
user-namespaced custodian; Stage B of the gate container reverted; plan C9, self-confinement in place of
bwrap, unstarted). Credentials (delegation lineage, pre-rotation, revocation, renounce: served, with
audits in `Deployed.lean`). Reproducible builds (26 outputs reproduced byte for byte on a second box,
10-27).

---

## 6. State at the stop

- **The demo.** Three rehearsals shipped between 10-27 and 10-31 (two on a Hetzner box, one in an nspawn
  container on `dregg-forge`), none fully green on the box. The first walk with no reds was on 11-01,
  under a Gemini session that had taken over the tree that morning; that world became the public demo.
  `/join` opened on 11-03 with a free route and a mainnet pay route. Two strangers signed up: one
  enrolled and never logged in, one was refused twice during an outage and did not return. The only fee
  paid was ember's own. "So nobody outside the team has done anything inside the system yet"
  (01a1ae2a#1217). On 11-04 the Store restart-looped for about 16 hours: binaries had been hot-copied
  into the pinned candidate, and the Store's own tamper check refused them at the next restart. There
  were re-geneses on 11-05 and after; a backup on 11-09 left the site half down for its last two days.
  The container was stopped and disabled on the evening of 11-11; its image remains on the box for a log
  audit.
- **What the demo answered.** Operational questions, mostly: a checkpoint that must quiesce a resident
  can strand the box; a resident posting on a timer is unbounded Store growth while opens replay the log;
  a scripted walk misses what a browser hits (an explorer agent found 20 bugs the walk had not); a
  performance fix measured on a fresh world does not hold at the live world's height.
- **The builder.** Dead from 11-01 to 11-05 on a key denial, then rebuilt. `board/REDS.md` (11-09):
  every stage after the first "did not run" for six rounds;
  `green` is 56 commits behind `main`. `scripts/local-gates.sh` (27 gates) runs only in GitHub CI, which
  per the 10-03 audit had never been green; two of its gates are red by construction (a glob over a
  directory that no longer holds shell tests; three test modules in no row).
- **The seats** (`board/seats/*.md`). Wound down 11-01 except `build-loop` (11-06) and `bytes-repr`
  (11-08). Each file is a continuation: `host-execution` (nine ordered steps; a branch never compiled),
  `store-retained` (the held served state), `read-path` (measurements never run), `member-side` (the
  composed `residents` red; the consent walk), `privacy` (§5.12), `apps-hermes` (§5.27), `infra`
  (confinement Stage B; root-unit review not started), `explorer` (a stub: `board/COSTS.md` is four
  lines).
- **Costs at the last ruling** (`board/RULINGS.md`): app create to first page about 26 s; `story new`
  10 to 15 s; birth submit about 600 ms and growing with height; certify about 6 s per tail; restart plus
  first read about 5 s.

---

## 7. What was never built

### 7.1 From the atlas carve

`Distributed/` (blocklace, strand, the exported finality gate, CapTP, migration): no library.
`Apps/` (factories and a verification toolkit; apps as declarations with inherited contracts): the app
layer is 184 hand-written receiver files instead. `Deos/` (surface-as-capability, membrane
non-amplification, confinement as the deterministic-replay fragment, affordance algebra): absent.
`Assurance/` as generated ledgers: hand-written. `Effects/` as the registry from which the weld,
descriptor and witness generator are derived: §5.2. The games, authority closure with amplification
(`AmpClosed`), the final coalgebra `nuF`, the interchain adapter, graduated descriptor passes: absent.

### 7.2 From the plan's Phase 3 (`docs/DEMO-PREFIX-2026-10-26.md`)

C1 `World.admit` in gate mode (§5.1). C2 the research move (done for Selvage as a copy on 11-11;
`private-backend` not moved; nothing removed here). C3 strata consolidation. C4 emit the remaining laws
and tables from Lean and delete each Rust twin. C5 one wire (partly: named op constants are generated).
C6 the grain economy in Lean. C7 the never-admissible witness, private rooms owned by Lean, receipts with
inclusion, `runtime.c` retired. C8 performance beyond the bar (§5.30). C9 self-confinement.

### 7.3 Statements with no proof

`host_submit_is_step`; `HostKeystone`; the opening circuit's relation and the hiding game's two open
hybrids; the fast-forward open's remaining proofs (`Compiler/DurableFastForwardSpec` is "stated before
proof"); the per-member request rate ("stated and proved but not yet wired in", `Kernel/SubjectRate`);
`Theory/PrivateCellTrie` ("statements the compressed trie owes").

### 7.4 Named residuals in root files

`Kernel.lean`: `[FINALITY-GATE-authenticated]`, `-liveness`, `-rust`, `-receipt-seam`; `[TIER-of-cell]`,
`[TIER-gate]`; `[HYPEREDGE-operational]`; `[LIVENESS-gst]`, `[LIVENESS-authenticated]`;
`[PRIVATE-TURN-kernel]`, `-crypto`, `-exec`. `Pred.lean`: §3.2. `Minidregg.lean`: `[N4-*]`.
`Effects.lean`: `[EFFECT-registry]`. `Selvage.lean` and `Assurance.lean` carry about 140 tagged lines
between them (`[PROXGAP-*]`, `[BASEFOLD-*]`, `[ACC-*]`, `[ZK-RBR-*]`, `[BUDGET-compose]`,
`[BUDGET-PoW-compose]`, `[SPARTAN-*]`, `[TWIST-FP-BIND]`, `[MATMUL-pcs]`, `[COMMIT-CR]`, `[FS-ROM]`).

---

## 8. Twins and dead weight

### 8.1 Twins (two things doing one job, both kept)

- Kernel generations A and B (the twin audit's verdict: "twins, not layers"), and B's settlement
  executor beside C's `World.admit`.
- The deployed consumed set and the system cell's `spent`; the authority cell's parent plane and the
  system cell's `parent` rows.
- 61 version-suffixed application and pay files beside their predecessors.
- `computeTarget` and `targetPatch` (one computes a post, the other recomputes the patch whose replay is
  that post).
- Three gate-proof verifiers (§5.6); the Lean cSHAKE256 and its Rust kernel (by design, pinned by
  vectors); `prover/`'s internal duplicates.
- In Rust, per the crate review: about 15 custody machines, three dispatch generations in grain-runtime,
  nine lifecycle skeletons in spk-host, four copies of Lean's HTTP header allowlist. The shell's typed
  grammar beside its hand-written verb rows.
- `mini-sdk` and `mini-sdk-ts`.

### 8.2 Referenced by nothing

About 95 scripts (`scripts/burst/*` for boxes that are gone; the pre-board pipeline: `landing.sh`,
`merge-gate-checks.sh`, `journey-runner`, `journey-rows`, `box-wait`, which `CLAUDE.md` and `AGENTS.md`
still name; `oracle-u3-*`; `probe-*.lean`; `kern/*`; the `r3` recoveries; `remote-check.sh`), and about
59 more referenced only by documents. The nine orphan Lean files of §3.9. `native/portable-archive`,
`bridges/arklib-ud`, `world/automatafl`, `tests/lean/`, `examples/.../RunImportedReview.lean`,
`testing/agreement-carrier-scenario.py`. The leftovers of §3.14. 275 registered worktrees, 272 local
branches with nothing `main` lacks, and 351 tags (almost all `archive/lane/*`).

### 8.3 Where Rust decides

Per `docs/review/2026-10-26-native-crates/SYNTHESIS.md` §B (not re-derived): Rust and operator JSON
author the content of every law the shell installs; grain-runtime's economy; pay-watcher's notion of what
counts as a payment; mini-keys' grant caps; the inference scheduler's whole policy; the Discord roster's
identity binding. No fail-open authority path was found in any crate.

---

## 9. Finishing out

Six lines of work, each in dependency order. They are independent of each other except where noted.

1. **Make the thesis a theorem (§5.1).** Receipt half of `host_submit_is_step` → `World.admit` in gate
   mode on the receive path → the Host's state is a `World` → delete the two state twins. Everything in
   §5.30 that retypes the Host session touches the same code, so do them as one design.
2. **Make the founding law true once (§5.2).** The content migration commit → the other payload codes →
   the posting substrate → generated codec rows and arms. This is also the only route by which the
   `Application*` strata stop growing by hand.
3. **Give the proof research a consumer (§5.12, then §5.5, §5.3).** The private-cell opening relation as
   a bit-level constraint system → its binding and the receiver adapter → Tower256 with batching,
   zerocheck and lookup → the opening proved. Selvage's own residuals (§5.4) proceed in zkml-research and
   do not block this.
4. **Reach the cost bar (§5.30).** KN2 2b → consent on the light opening → packed post images →
   persistent indexes → a tree commitment per cell. The last changes roots, so it rides a re-genesis,
   which needs §5.38.
5. **Consolidate at a re-genesis (plan C3, §8.1).** One application lifecycle, one pay enrollment, one
   dispatch generation; delete generation A's unused parts and generation B's unreached carriers after
   re-pointing `MoveEffect` and `ReceiptClaim`.
6. **Finish the product surfaces that carry a hypothesis (§5.27, §5.28).** The real-agent turn on a typed
   app interface; the grain economy stated in Lean.

Deletion that needs no design: §8.2.

What each line would teach is stated per experiment in §5. Across them, three questions stand out as
answerable only by finishing, and not answered anywhere else in ember's repositories:

- Does a Lean-admitted, re-executed world stay fast enough to use when its Host state is the model
  itself (lines 1 and 4)?
- What does one declared effect cost against one hand-written effect on a kernel with real traffic
  (line 2)?
- What does a zero-knowledge selective opening of a real cell cost with a Lean-checked verifier
  (line 3)?

---

## 10. Where the documents and the source disagree

| document says | source says |
|---|---|
| `CLAUDE.md`: "≤10% of its LOC: everything derived ... nothing hand-written" | 660K Lean and 354K Rust; the served write path is hand-written receivers (§5.2) |
| `CLAUDE.md`: boxes `dregg-build`, `dregg-demo`; lanes on `lane/<name>` branches | those boxes are gone; from 10-31 seats commit to `main` (`board/README.md`) |
| `HANDOFF.md`, `README.md`, `COORDINATION`: "sixteen design laws" | `ATLAS.md` §6 has seventeen |
| `HANDOFF.md` links `docs/INTEGRATOR-STATE.md` | deleted 10-31; `board/` is mentioned by none of `HANDOFF.md`, `README.md`, `AGENTS.md` |
| `Kernel.lean` header: "The conservation ALGEBRA of the three verbs ... The admission gate ... is `DeclaredHyperedge.Declaration.authorizationCheck`" | that carrier was deleted; the file imports four kernels |
| `Deployed.lean:50`: "modules `Minidregg` roots beside the per-directory roots" | 11 of them are reached only from `Deployed.lean` |
| `Assurance/SelvageV0Manifest.lean`: "NO PROVER" | a compiled Tower256 prover and its Rust kernel exist |
| `Compiler/Air.lean`, `Assurance/PrivateTurn.lean`: the private-turn arithmetization is "not yet built" | `Compiler/NoteSpend.lean` closes it |
| `Selvage/Rbr.lean:447-454`: TODO statement fields | `Selvage/Depth.lean` proves the repaired form |
| `Theory/ResearchRegime.lean` names `Theory/RegimeTypedEvidence.lean`; two Compiler files name `prover` sources | none of the three exists |
| `docs/STATUS.md`: "rehearsal #2 is still the build serving" (10-28) | several later builds shipped; the box is down |
| `docs/README.md` | indexes 84 of 160 documents |
| `board/seats/build-loop.md`: "green is still 83e926874" | `origin/green` is `980d80c5d` |
| `README.md`: "Rust ... makes no admission decisions" | §8.3 |

---

## 11. Where to look next

- **The source catalogue:** the eight library root files, read with their comments.
- **Measured structure:** `docs/review/2026-10-26-triage/LEAN-TRIAGE.md` (reach classes, the research
  split), `docs/KERNEL-TWIN-AUDIT.md` (§0 and §8), `docs/review/2026-10-26-native-crates/SYNTHESIS.md`.
- **History:** `docs/review/2026-10-26-history/HISTORY.md` to 10-26. For 10-26 to 11-11, the transcripts:
  `cv show 698fc87d` (the demo sprint), `01a192eb` (the board era), `01a1ae2a` (the live demo and the
  stock-taking; `4a6f3c64` is the same conversation before pruning), `78fef112` (the November research
  programme); the Antigravity conversation `ca74e7a0` (11-01 to 11-04) is not indexed by `cv` and is read
  from `~/.gemini/antigravity-cli/brain/`. Many of the sessions that wrote the September
  and October Lean ran with `~/dev/breadstuffs` as their working directory.
- **Continuations:** `board/seats/*.md`.
- **The plan that was current:** `docs/DEMO-PREFIX-2026-10-26.md` §3.
