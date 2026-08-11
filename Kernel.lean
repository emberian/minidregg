/-
# Kernel — the 3 verbs over the product camera (ATLAS §7).

The conservation ALGEBRA of all three verbs is landed: move (State) ·
create/gwrite (Verbs) — plain state functions + conservation/frame theorems.
The executor tier (Gate) is the kernel MODEL of the 4-leg admission gate:
Verb = admission × footprint, fail-closed admit, gate soundness
(fail-closed/conserves/frame), the first Kernel @[export]. Its footprint-Fpu
refinement and the AIR arithmetization (Compiler lane) are named residuals.
-/
import Kernel.Camera  -- the four-substance product resource algebra (the camera tier)
import Kernel.State   -- the minimal kernel state: accounts + bal + caps + one UKey map; Σ-conservation
import Kernel.Turn    -- the turn as a wide pullback (hyperedge): cone + balance, legs_agree, the binding tooth
import Kernel.TurnLimit  -- N2a: the hyperedge cone data IS a wide-pullback limit (Types.isLimit), keystones
import Kernel.TurnBalancedLimit  -- N2b: conservation as the balance equalizer over N2a's limit; the conserving turn is universal
import Kernel.DeclaredHyperedge  -- computable flat N-incidence turns jointly authorize, balance, compose, and commit one canonical post; this is the call-forest replacement carrier
import Kernel.DeclaredHyperedgeCost  -- declaration-static bounds and exact Lean-owned flat-turn charges; funding failure is state/budget atomic and machine overflow cannot wrap
import Kernel.DeclaredHyperedgeWitness  -- concrete two-leg commitment and exact TypedCellHyperedge migration certificate close the carrier without reviving a second runtime
import Kernel.TypedCellHyperedge  -- schema-polymorphic joint accepted effects over typed fields/resources, one validated post, and an explicit resource law
import Kernel.MultiCellHyperedge  -- genuinely heterogeneous incidence-indexed cells joined by one flat apex/receipt binding and resource equation
import Kernel.TypedCellHyperedgeWitness  -- ANTI-VACUITY: a built same-cell `Commit`, giving the landed `no_commit_of_nonzero_resource` something to be a negative ABOUT, plus the matching `no_commit_of_wrong_apex`
import Kernel.MultiCellHyperedgeWitness  -- ANTI-VACUITY: a built two-incidence `Commit` — distinct cell ids, distinct accepted legs over distinct pre-cells, aggregate balanced by CANCELLATION; the carrier the durable protocol and the Hyperdocument installation quantify over. Cross-SCHEMA heterogeneity is still untested
import Kernel.SparseAuthenticatedState  -- typed sparse ROM/RAM/append-only namespaces, fresh allocation, exact trace footprints/roots/bus rows
import Kernel.HyperdocumentEventLog  -- final causal events occupy a separate append-only sparse cell with an exact canonical CellState adapter
import Kernel.DeployedMaterializerWitness  -- the append-only event-log schema has an actual materializer/cell and an exact shared sparse/canonical empty root
import Kernel.HyperdocumentVersionEffects  -- accepted content effects derive final causal records and append them through a separately authorized sparse log effect
import Kernel.EventLogMaterializerLimit  -- regression-only reconstruction of the deleted total event-log carrier and its counting obstruction
import Kernel.HyperdocumentPublication  -- the exact accepted content and event-log legs form one two-cell MultiCellHyperedge commit with an explicit physical boundary
import Kernel.HyperdocumentMerge  -- conservative causal joins retain exact parent values and explicit conflicts instead of erasing them
import Kernel.HyperdocumentMergePublication  -- merge content and its append-only causal event publish as one heterogeneous two-cell commit
import Kernel.HyperdocumentMergeAncestry  -- proof-relevant lowest/ambiguous/unavailable base decisions survive exact merge acceptance and atomic publication
import Kernel.HyperdocumentTwoParentWitness  -- a built base-to-two-siblings merge retains both provenances as one conflict, publishes content+event, and rejects stale authority
import Kernel.DurableCommitProtocol  -- fail-closed multi-root/nullifier/budget/history settlement model; physical storage refinement remains explicit
import Kernel.DurableDataIntent  -- stable payload-bearing writes and read guards refine root settlement without assuming hash injectivity or physical durability
import Kernel.GuardedDurableCommit  -- Hyperdocument content/event writes carry exact bytes while the canonical authority cell participates as a stale-detecting read guard
import Kernel.CanonicalPolicyRegistry  -- committed policy records resolve to exact payloads and remain guarded through durable settlement; signatures and physical atomicity stay explicit
import Kernel.AdmissionPrologue  -- fee and nonce settle before the body, so rejection preserves replay protection and charge without leaking a body post-state
import Kernel.DurableWalHandler  -- the first inhabitant of that refinement: a staged/committed/compacting write-ahead log whose recovery fold tracks the model exactly; a device MODEL, with no fsync, torn write, codec, replication, or liveness claim
import Kernel.FramedWalRefinement  -- versioned/checksummed frames, torn tails, crash repair, and sync refine the abstract WAL while real OS/device semantics remain a premise
import Kernel.ReplicatedSettlementFinality  -- intersecting quorum certificates make finalized logs comparable; availability and network liveness remain separate hypotheses
import Kernel.IrreversibleEffectSettlement  -- external actions settle as commit/refuse/compensate/quarantine with exact receipts; compensation and physical restoration remain distinct
import Kernel.CanonicalResourceEffect  -- canonical transfer/mint/burn/fee/lease operations derive the sole accepted effect and patch-bound hyperedge resource law
import Kernel.AuthorizedResourceCharge  -- authority binds the exact ten-lane codec/tariff charge and its payload-bearing durable settlement
import Kernel.ReactiveTerminalCell  -- finalize/cancel/expire/break race for one canonical terminal cell and atomic outbox intent
import Kernel.ProviderExecutionLease  -- prepaid provider work, irreversible start, terminal settlement, retries, races, and separately authorized refunds
import Kernel.CanonicalEscrowMarket  -- authorized deposit/fill/cancel/expire/refund orders conserve resources, settle fees atomically, and reject replay or fill/close races
import Kernel.Receipt    -- the receipt word Q: uproj faithfulness + the frame as a receipt fact (OB-3's kernel side)
import Kernel.Verbs   -- create + gwrite: the remaining conservation-algebra verbs, conservation (honest side-conditions) + frames + the receipt bridge
import Kernel.PrivateTurn  -- the private-witness turn: the hyperedge at carrier Pub × Priv; publicView blind to the witness ([PRIVATE-TURN-kernel])
import Kernel.Gate    -- the gated executor MODEL: Verb = admission × footprint, the 4-leg fail-closed gateOK, admit + soundness (fail-closed/conserves/frame/no-TOCTOU), @[export minidregg_gate_ok]
