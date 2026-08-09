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
import Assurance.SemanticReceiptRuntimeCodec  -- exact fixed key-major word/residual layout ↔ formal receipt relation; no native semantics is asserted
import Assurance.SemanticHistoryAccumulator  -- manifest-admitted commit/reject receipts fold only from a verified predecessor head; WARP/PCS recommitment stays explicit proof data
import Assurance.SemanticHistoryStraightlinePcs  -- WARP-shaped prefix/fold-root schedule plus explicit straightline erasure extraction and KS/CR/ROM error ledger; not yet a full WARP protocol
import Assurance.SemanticAdditiveFriCheckpoint  -- canonical zero-padding joins the exact semantic history word/root to additive FRI; KS-good extraction recovers the authoritative head
import Assurance.SemanticHistoryWARPAdditiveJoin  -- link roots precede fold challenges, post-challenge fold roots commit exact words, and the terminal root is the additive-FRI initial root
import Assurance.ProofCompositionGame  -- one prefix-typed shared-oracle schedule and one tagged PCS/CR/ROM/FRI/OracleLog/ZK failure ledger; the union bound is over an actual common coin space
import Assurance.AuthenticatedColumnHistoryBridge  -- openings retained by one accepted authenticated-column trace become the identical binding BCS messages and exact semantic WARP link stream
import Assurance.PrivateComputationReceiptClause  -- ZK/MPC/FHE completions become manifest-bound receipt disclosures only through exact authorization, named same-opening bridges, evidence, and VerifiedRelease
import Assurance.BfvPrivateComputationJoin  -- the encrypted-RNS/FHE evidence lane instantiates the private receipt with one BFV token and all 384 exact integer equations; suite/privacy/knowledge remain unassigned
import Assurance.BfvNativeBufferAdmission  -- fallible opaque BFV buffers are checked by Lean row descriptors/link constraints before the 384-row token and private receipt can exist
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
