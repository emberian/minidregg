/-
# Assurance — the apex bridge + generated ledger machinery (ATLAS §7).

The only lawful home for cross-boundary apex theorems: `Assurance/` is
unrestricted, so a kernel object (a receipt word) may meet a proof-system
object (the code + claim) here — nowhere else.
-/
import Assurance.Placeholder  -- carve marker: pins, keystone audit, carrier registry, Bound/Forced
import Assurance.ReceiptClaim  -- OB-3: the receipt Q as a native accumulated claim (the kill-checkpoint)
import Assurance.SemanticReceiptRelation  -- clean-sheet ReceiptDelta quadratic language → native Loom AccClaim fold
import Assurance.SemanticTurnReceipt  -- exact typed request/auth/effects/disclosure wrapper → SemanticReceiptRelation
import Assurance.DeclaredTurnReceipt  -- DeclaredTurn.execute derives the exact commit/reject receipt core and history claim; callers cannot supply post/touched/auth semantics
import Assurance.DeclaredHyperedgeReceipt  -- flat jointly authorized turns derive one canonical commit/reject history core without choosing a synthetic primary leg
import Assurance.DeclaredHyperedgeHistoryBinding  -- context plus the complete ordered request/effect/presentation-root family occupies the joint receipt header; hash collisions stay explicit
import Assurance.BinaryTowerHeaderCodec  -- the fixed 32-byte joint header packs injectively into sixteen GF(2^256) cells through GF(2^16), avoiding characteristic-two Nat-cast collapse
import Assurance.SemanticReceiptRuntimeCodec  -- exact fixed key-major word/residual layout ↔ formal receipt relation; no native semantics is asserted
import Assurance.SemanticHistoryAccumulator  -- manifest-admitted commit/reject receipts fold only from a verified predecessor head; WARP/PCS recommitment stays explicit proof data
import Assurance.SemanticHistoryFamily  -- request-shape-neutral, proof-relevant entry semantics fold singular turns and joint objects through Loom's one AccClaim
import Assurance.SemanticHistoryFamilyInstances  -- exact singular-turn and complete flat-hyperedge instances; no synthetic primary request
import Assurance.AcceptedCellEffectHistory  -- accepted canonical cell effects derive their exact bounded core and enter the same request-shape-neutral verified history family without a legacy turn wrapper
import Assurance.ScopedAcceptedCellEffectHistory  -- finite declared-footprint openings retain typed roots and exact lookup/frame laws without enumerating an infinite deployed schema
import Assurance.HistoryProjectionCardinalityTooth  -- proves why the old global finite-field projection cannot encode a root-separated infinite materialized-cell stream
import Assurance.ReactiveLifecycleHistory  -- weak-hole Promise/Notify/React/Finalize/Expire/Break over authenticated history entries; finalization is an accepted cell effect/typed hyperedge leg and physical CAS remains explicit
import Assurance.GrainForkSettlement  -- causally linked fork heads settle through one schema-polymorphic typed hyperedge while unresolved conflicts and capability liveness stay proof-relevant
import Assurance.GrainForkScopedSettlement  -- finite declared field focus replaces impossible whole-infinite-schema enumeration while retaining exact roots, frames, and receipt bindings
import Assurance.SemanticHistoryStraightlinePcs  -- WARP-shaped prefix/fold-root schedule plus explicit straightline erasure extraction and KS/CR/ROM error ledger; not yet a full WARP protocol
import Assurance.SemanticAdditiveFriCheckpoint  -- canonical zero-padding joins the exact semantic history word/root to additive FRI; KS-good extraction recovers the authoritative head
import Assurance.SemanticHistoryWARPAdditiveJoin  -- link roots precede fold challenges, post-challenge fold roots commit exact words, and the terminal root is the additive-FRI initial root
import Assurance.SemanticHistoryBcsClaimProjection  -- exact carrier reindex transports semantic AccClaims and folds into the existing unshifted BCS reduction
import Assurance.SemanticHistoryBcsGame  -- retained history derives the exact unshifted BCS schedule; ideal mathematics and common-coin PCS/CR/ROM evidence stay separate
import Assurance.SemanticHistoryTower256CheckpointGame  -- one coin/ledger and exact root schedule join retained-history BCS evidence to the concrete Tower256 additive checkpoint
import Assurance.Tower256MerkleBindingCardinality  -- the old positive-height binding-closed checkpoint carrier is formally impossible, so deployment must retain raw collision events
import Assurance.SameCoinGameProduct  -- exact nonempty product-coin pullbacks compose raw additive, Ext6, note, and BFV ledgers without pretending they share a deployed ROM
import Assurance.HistoryHeadInhabitation  -- ANTI-VACUITY: the first constructed `VerifiedHistoryHead`, with a real fold round, at closed built parameters — until this, every retained-history theorem quantified over a type nothing in the tree inhabited
import Assurance.SemanticHistoryTower256DeployedBcs  -- the literal retained-history Fiat--Shamir failure event has its native MCA bound; concrete same-coin PCS/CR/ROM classification remains explicit
import Assurance.SemanticHistoryPcsEventRealization  -- intrinsic retained-history MCA/PCS extraction failure is charged to `historyPcs` alone, and is proved minimal: the CR/ROM disjuncts cannot secretly discharge it
import Assurance.RawHistoryBcsOpenings  -- the retained-history carrier BEFORE binding: submitted roots/columns kept as-is over an executable `OpeningScheme`, root-preimage attribution separated out, and the equivocation branch exhibited inhabited rather than refuted
import Assurance.RawHistoryCollisionBridge  -- that retained equivocation IS the landed `BindingFailure`, and at the concrete cSHAKE Merkle scheme it extracts an exact framed collision; the power-of-two coordinate embedding is the named residual
import Assurance.RawSemanticHistoryCheckpointGame  -- constructible nonempty same-coin history/additive checkpoint game retains attribution, proximity, extracted collision, and oracle-transport failures
import Assurance.Tower256AdditiveFriCanonicalExecutionGame  -- actual raw receipt execution yields the exact ideal coin or a priced collision/transport event on one ledger
import Assurance.ProofCompositionGame  -- one prefix-typed shared-oracle schedule and one tagged PCS/CR/ROM/FRI/OracleLog/ZK failure ledger; the union bound is over an actual common coin space
import Assurance.ExtensibleProofCompositionGame  -- disjoint finite ledger extensions preserve every old event/price and add Ext6's eight failures on the same coin without tag reuse
import Assurance.Tower256LogupControllerAdmission  -- exact verified Tower256 LogUp control admitted only with the canonical codec, real Merkle binding, and one common-game PCS/CR/ROM coin
import Assurance.Tower256AdditiveFriControllerAdmission  -- byte-checked Tower256 additive-FRI control enters one explicit same-coin failure ledger
import Assurance.Tower256AdditiveFriRawAdmission  -- the same-coin cover CONSTRUCTED rather than assumed: ideal additive proximity, an accepted receipt carrying a path-specific `ExtractedCollision`, and one transcript-distribution residual
import Assurance.Tower256AdditiveFriActualReduction  -- accepted controller bytes derive the real Loom challenge/query event and UD price, leaving only exact ROM transport and pre-assumed position binding
import Assurance.Ext6GateProofControllerAdmission  -- Ext6 gate control concludes descriptor semantics only outside named PCS/subfield/LDT/CR/ROM failures
import Assurance.Ext6GateProofDeploymentAdmission  -- reflected Ext6 deployment is separated from its exact eight-event semantic security residual
import Assurance.HyperdocumentHistoryAdmission  -- exact head membership, indexed finality, post-only openings, and accepted LinkRecord containment
import Assurance.HyperdocumentAgentOperation  -- one composed user/agent link-or-annotation slice: negotiate, promise, notify, react, then the sole accepted effect at Finalize drives publication, invalidation, receipt/history, and the conditional durable plan
import Assurance.HyperdocumentGuardedDurable  -- the actual published operation becomes exact content/event payload writes guarded by the current authority root
import Assurance.HyperdocumentLinkPublicationWitness  -- a concrete genesis-to-link child is accepted and atomically publishes content plus its causal event
import Assurance.HyperdocumentLinkReopenWitness  -- the published link occupies an exact post opening and reopens through the canonical content query
import Assurance.HyperdocumentTwoParentHistoryWitness  -- the concrete two-parent conflict survives at an exact verified-history coordinate
import Assurance.HyperdocumentMergeDurableFinalityWitness  -- the merged conflict survives guarded WAL recovery and an intersecting-quorum finalization witness
import Assurance.HyperdocumentDurableInstallation  -- that slice's durable half with the handler premise DISCHARGED by the constructed WAL device: atomicity, marker installation, crash-before, and idempotent retry no longer quantify over a hypothetical correct store
import Assurance.TransclusionBacklinkHistory  -- typed durable references, exact source/history/opening identity, authenticated forward welds, and coverage-relative complete backlinks
import Assurance.SemanticHistoryRecursiveAir  -- stateless public history heads bind into the shared-wire recursive verifier AIR while soundness/KS/ZK/SE remain distinct evidence
import Assurance.AuthenticatedColumnHistoryBridge  -- openings retained by one accepted authenticated-column trace become the identical binding BCS messages and exact semantic WARP link stream
import Assurance.PrivateComputationReceiptClause  -- ZK/MPC/FHE completions become manifest-bound receipt disclosures only through exact authorization, named same-opening bridges, evidence, and VerifiedRelease
import Assurance.BfvPrivateComputationJoin  -- the encrypted-RNS/FHE evidence lane instantiates the private receipt with one BFV token and all 384 exact integer equations; suite/privacy/knowledge remain unassigned
import Assurance.BfvNativeBufferAdmission  -- fallible opaque BFV buffers are checked by Lean row descriptors/link constraints before the 384-row token and private receipt can exist
import Assurance.BfvAcceptedCellEffect  -- checked all-row BFV admission fills typed private completion, then constructs a sealed canonical accepted effect and common history claim; release remains independent
import Assurance.BfvProofControllerAdmission  -- the BFV384 deployment boundary stated honestly: zero-pinned statements provably cannot bind a suite, so semantic admission is currently impossible rather than faked
import Assurance.BfvSuiteMigrationBoundary  -- zero-to-nonzero suite migration changes canonical bytes or exposes an exact framed collision; control-only suites cannot fake semantic closure
import Assurance.NoteSpendCoreAcceptedCellEffect  -- the note-spend AIR enters the release-free computation core as one sealed authorized canonical effect; hiding/PoK/PCS/CR/ROM remain explicit
import Assurance.NoteSpendProofControllerAdmission  -- canonical proof control admits the sealed note-spend relation only outside separately priced PCS/PoK/CR/ROM failures; hiding is not inferred
import Assurance.ReactiveDurableSettlement  -- accepted reactive content, terminal state, and outbox settle in one retry-safe payload intent with explicit liveness ceilings
import Assurance.HyperdocumentReactiveCarrierWitness  -- concrete deployed create/history/controller values inhabit the reactive carrier and its durable terminal settlement
import Assurance.LoomV0  -- the v0 CAPSTONE: sound + knowledge-sound + bound + decided, one bundle
import Assurance.LoomV0Manifest  -- the machine-checked table of contents: re-exports the whole proved tower
import Assurance.PrivateReceipt  -- can a turn carry a PRIVATE input? the hiding checkpoint (verdict: yes at the opening layer; [OB-4-hiding-rbr] the full ZK)
import Assurance.PrivateTurn  -- the private-witness TURN model (Lean-authored): public claim binds, private witness hides; [PRIVATE-TURN-air] the Lean constraint system (not the Rust AIR)
import Assurance.AirSumcheck  -- [AIR-sumcheck]: the flattened gate system's linear face retired by Loom's proven sumcheck; [AIR-sumcheck-quadratic] the mul-gate MLE encoding
import Assurance.AirSumcheckQuadratic  -- [AIR-sumcheck-quadratic] CLOSED: the mul-gate face retired at d = 2 (quadHonest), full gate-system soundness; [AIR-quadratic-selectors] the oracle-side table linearization
import Assurance.ErrorBudget  -- the product-coordinate SOUNDNESS ERROR BUDGET: soundnessError (grinding + sumcheck + CR + proximity, union bound) composed via soundnessError_bound; deployedBudget = 55 bits at BabyBear⁴ (in (2^{-56}, 2^{-55}], grinding-dominated); [BUDGET-compose] is the required shared-oracle rendering before this is an end-to-end deployment number
import Assurance.ErrorBudget120  -- the 120-bit path, priced exactly: BabyBear^6 challenge field + 20 PoW bits gives a resource-budget error in (2^-138, 2^-137]; both levers load-bearing; [BUDGET-PoW-compose] is the honest nonce-protocol bridge
import Assurance.MixedFieldBudget  -- exact runtime field split: base gate/sumcheck + Ext4 FRI is only 16 priced bits; Ext6 gate/sumcheck alone leaves 75; all algebraic draws at Ext6 recover 137
import Assurance.PowGrinding  -- [BUDGET-PoW-compose] counting core: exact 2^-bits nonce density and a leave-one-out adaptive work*epsilon/2^bits ideal-coordinate bound; deployed shared-ROM/domain-separation compilation remains explicit
