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
import Assurance.SemanticReceiptRuntimeCodec  -- exact fixed key-major word/residual layout ↔ formal receipt relation; no native semantics is asserted
import Assurance.SemanticHistoryAccumulator  -- manifest-admitted commit/reject receipts fold only from a verified predecessor head; WARP/PCS recommitment stays explicit proof data
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
