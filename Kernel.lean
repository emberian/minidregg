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
import Kernel.HyperdocumentIndexSync  -- bounded persistent backlink/range rows advance from exact causal deltas with replay and cursor-staleness semantics
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
import Kernel.CredentialSignedEnvelopeController  -- versioned key-directory and authority-root checks admit only an exact externally verified credential envelope
import Kernel.AdmissionPrologue  -- fee and nonce settle before the body, so rejection preserves replay protection and charge without leaking a body post-state
import Kernel.DurableWalHandler  -- the first inhabitant of that refinement: a staged/committed/compacting write-ahead log whose recovery fold tracks the model exactly; a device MODEL, with no fsync, torn write, codec, replication, or liveness claim
import Kernel.FramedWalRefinement  -- versioned/checksummed frames, torn tails, crash repair, and sync refine the abstract WAL while real OS/device semantics remain a premise
import Kernel.ReplicatedSettlementFinality  -- intersecting quorum certificates make finalized logs comparable; availability and network liveness remain separate hypotheses
import Kernel.AuthenticatedSettlementFinality  -- authority roots, key epochs, policy addresses, and revocation bind quorum votes while EUF remains an explicit bad event
import Kernel.IrreversibleEffectSettlement  -- external actions settle as commit/refuse/compensate/quarantine with exact receipts; compensation and physical restoration remain distinct
import Kernel.CanonicalResourceEffect  -- canonical transfer/mint/burn/fee/lease operations derive the sole accepted effect and patch-bound hyperedge resource law
import Kernel.AuthorizedResourceCharge  -- authority binds the exact ten-lane codec/tariff charge and its payload-bearing durable settlement
import Kernel.ReactiveTerminalCell  -- finalize/cancel/expire/break race for one canonical terminal cell and atomic outbox intent
import Kernel.OutboxDelivery  -- stable terminal/outbox identity, receiver replay, and authenticated acknowledgements without invented transport liveness
import Kernel.ProviderExecutionLease  -- prepaid provider work, irreversible start, terminal settlement, retries, races, and separately authorized refunds
import Kernel.CanonicalEscrowMarket  -- authorized deposit/fill/cancel/expire/refund orders conserve resources, settle fees atomically, and reject replay or fill/close races
import Kernel.PrivateEscrowSettlement  -- sealed computation and separately authorized declassification stage exact escrow release, terminal, and outbox effects
import Kernel.QuotaGcSettlement  -- root-bound reachability, lease expiry, quotas, and guarded atomic compaction make deletion an admitted settlement rather than a host guess
import Kernel.DeclaredActionExecution  -- accepted create/write/move batches become a typed hyperedge and payload-bearing durable intent with exact resources and charge
import Kernel.Receipt    -- the receipt word Q: uproj faithfulness + the frame as a receipt fact (OB-3's kernel side)
import Kernel.Verbs   -- create + gwrite: the remaining conservation-algebra verbs, conservation (honest side-conditions) + frames + the receipt bridge
import Kernel.PrivateTurn  -- the private-witness turn: the hyperedge at carrier Pub × Priv; publicView blind to the witness ([PRIVATE-TURN-kernel])
import Kernel.Gate    -- the gated executor MODEL: Verb = admission × footprint, the 4-leg fail-closed gateOK, admit + soundness (fail-closed/conserves/frame/no-TOCTOU), @[export minidregg_gate_ok]
import Kernel.FinalityGate  -- ATLAS §3 item 11, the finality gate as a DECIDER over ReplicatedSettlementFinality: `check` is a bare && of positive checks, check_eq_true_iff the unfolding lemma, a true verdict CONSTRUCTS the Finalized certificate (certificate / check_sound / check_complete / check_eq_true_iff_exists_finalized) so checked_logs_comparable and checked_no_conflict are inherited, never re-proved; fail-closed teeth attributable per leg; closed Fin 3 instance decided; @[export minidregg_finality_check]. Residuals [FINALITY-GATE-authenticated] [FINALITY-GATE-liveness] [FINALITY-GATE-rust] [FINALITY-GATE-receipt-seam]
import Kernel.HyperedgeTier  -- Law 2 on the ONE turn model: commitTier tierOf := Finset.univ.sup over the incidences, leg_le_commitTier, commitTier_eq_causal_iff (coordination-free iff EVERY written cell is tier 1), hyperedge_commit_at_join (+ leg canonicity from the one apex); Law 1 ⟂ Law 2 on the shared conservation aggregate (conservedAtTier := Σ halfEdge = 0, conservation_tier_independent := rfl, the Σ = 1 cone refused at every tier). On Kernel.Turn only — no KernelState. Residuals [TIER-of-cell] [TIER-gate]
import Kernel.HyperedgeKnowledge  -- the epistemic reading of legs_agree: in the observation frame the apex H.tid is DISTRIBUTED KNOWLEDGE among the honest legs for ANY hyperedge and ANY faulty set (agreement_is_distributed_knowledge; distKnows_apex_iff_honest_agree the iff), and a fork — two honest legs reading different ids — is the absence of any distributed apex (fork_has_no_distributed_apex; splitTuple_no_hyperedge). Residual [HYPEREDGE-operational]
import Kernel.FinalityLiveness  -- liveness as ONE carrier: PostGSTProgress bundles the replicated layer's three premises (available quorum, fair delivery, responsive replicas) as a realizer slot; progress reuses finalized_of_available_fair_responsive and the decider accepts it (checked_of_progress); the constitution's sentence as two theorems kept apart — cannot_forge (no liveness premise anywhere) and no_progress_without_quorum (IsEmpty PostGSTProgress); closed Fin 3 realizer built, dead quorum system / partition / never-delivering schedule each refuted at its own leg. Residuals [LIVENESS-gst] [LIVENESS-authenticated]
import Kernel.NativeHost
import Kernel.NativeHostSession
import Kernel.NativeReserveContinuity
import Kernel.NativeHostGenesis
import Kernel.FnEvidence
import Kernel.FnConsumerOperation
import Kernel.FnConsumerOperationProofs
import Kernel.FnConsumerProgress
import Kernel.FnPortableSource
import Kernel.FnReplyConsumption
import Kernel.FnOriginOutbox
import Kernel.FnReplyPublication
import Kernel.FnReplySource
import Kernel.ContentResource
import Kernel.ContentResourceAudit
import Kernel.AgentGrain
import Kernel.AgentGrainAudit
import Kernel.CapabilityRevocationReceiver
import Kernel.ResourceTransactionAudit
