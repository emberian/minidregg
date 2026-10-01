/-
# Kernel — the turn carriers and their settlement models (ATLAS §7).

The conservation ALGEBRA of the three verbs over a `ℤ` ledger: move (State) ·
create/gwrite (Verbs) — plain state functions + conservation/frame theorems.
The admission gate a committed turn passes is
`DeclaredHyperedge.Declaration.authorizationCheck`, consulted by
`DeclaredHyperedge.execute`.
-/
import Kernel.RealmWellReceiver  -- K-WELL: realm wells mint and burn under the well law; the audit identity per realm asset
import Kernel.PayObservationProofs  -- PAY P3: observed payments mint Book credit; the audit identity, the transfer nullifier, the clock
import Kernel.PayEnrolProofs  -- PAY P3b-2: one enrollment-index payment is one turn over authority, factory, Book and pay cell
import Kernel.PayEnrolDecision  -- PAY P3b-1: the self-enrollment memo, its refusals, and the enrol/renew/journal decision
import Kernel.PurseRefillProofs  -- PAY P6: a Book burn funds an AgentGrain purse in one joint turn; ledger identity; purse never mints
import Kernel.State   -- the minimal kernel state: accounts + bal + caps + one UKey map; Σ-conservation
import Kernel.Turn    -- the turn as a wide pullback (hyperedge): cone + balance, legs_agree, the binding tooth
import Kernel.TurnLimit  -- N2a: the hyperedge cone data IS a wide-pullback limit (Types.isLimit), keystones
import Kernel.TurnBalancedLimit  -- N2b: conservation as the balance equalizer over N2a's limit; the conserving turn is universal
import Kernel.TypedCellHyperedge  -- the one flat joint carrier (D-0002): accepted effects over one Store cell, one re-validated joint patch, one post, an explicit resource law; the legacy DeclaredHyperedge carrier is deleted
import Kernel.MultiCellHyperedge  -- genuinely heterogeneous incidence-indexed cells joined by one flat apex/receipt binding and resource equation
import Kernel.TypedCellHyperedgeWitness  -- ANTI-VACUITY: a built same-cell `Commit`, giving the landed `no_commit_of_nonzero_resource` something to be a negative ABOUT, plus `no_commit_of_wrong_apex` and `repeated_write_refused` (joint re-validation)
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
import Kernel.Receipt    -- the receipt word Q: uproj faithfulness + the frame as a receipt fact (OB-3's kernel side)
import Kernel.Verbs   -- create + gwrite: the remaining conservation-algebra verbs, conservation (honest side-conditions) + frames + the receipt bridge
import Kernel.PrivateTurn  -- the private-witness turn: the hyperedge at carrier Pub × Priv; publicView blind to the witness ([PRIVATE-TURN-kernel])
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
import Kernel.ContentElementTree
import Kernel.ContentMarks
import Kernel.AgentGrain
import Kernel.AgentGrainAudit
import Kernel.CapabilityRevocationReceiver
import Kernel.ResourceTransactionAudit
import Kernel.World  -- DATAMODEL §3.3 B2: World (cells + system cell: journal/head/retired), Turn, admit/step, fold, Checkpoint; replay exactness, checkpoint soundness, journal exactness, fail-closed admission, frame, poles
import Kernel.WorldBench  -- B2 exit: compiled 1000-turn fold over the real step (native_decide, pinned)
import Kernel.TurnRecord  -- B2: an AcceptedCellEffect is a Leg (exactPost derived from step); ImplementationRefinement re-indexed by Turn/World, trace_represents_fold (crash recovery = fold of a sublist); model refines, torn install refuted
import Kernel.DurableCheckpoint -- DATAMODEL C2: resume from a materialized checkpoint; honest resume = genesis replay
import Kernel.WorldRoot  -- DATAMODEL §3.2/§3.4 C1: world root = AuthMap two-level root over (slot -> slot root), sparse evaluator = Scheme.root, RootBinding carrier discharging resume_sound, explicit-collision reduction, deployed cSHAKE scheme (256-bit hashed index), cSHAKE History; honest/tampered poles
import Kernel.DocumentHistory  -- K-DOC-HISTORY: doc diff = DocumentHistory.diff over the two doc show line lists (added_iff, removed_iff, changed_iff)
import Kernel.PresenceIndex  -- PLACE K-INDEX: lastSeen (cell, subject) and touched cell as exact folds of the accepted log (lastSeen_exact, touched_exact, index_monotone)
import Kernel.LinkIndex  -- K-DOC-INDEX: links and backlinks as an exact fold of the accepted log (ofRecords_exact, backlinks_sound, backlinks_complete, backlinks_covered)
import Kernel.WorldRootCache -- C2: the world root cached, one path per write; cache = spec root (insertWrite_root, deployedOf_root), stale cache refuted
import Kernel.ApplicationDispatchUpper
import Kernel.ApplicationGrainLaws
import Kernel.ApplicationLifecycleBeginCheck
import Kernel.ApplicationLifecycleClaimPolicyCheck
import Kernel.ApplicationLifecycleClaimReceiver
import Kernel.ApplicationLifecycleClaimVerified
import Kernel.ApplicationShareIssueHistorical
import Kernel.ApplicationSpkProfileProofs
import Kernel.FnSelectedHistoricalStep
import Kernel.FnSelectiveReleaseProofs
import Kernel.NativeHostBookInvariant
import Kernel.StreamResource  -- per-author streams: append leg theorems, author law, rooms (PLACE §2.3/§4.4, K-STREAM)
import Kernel.NockProgramCell -- NOCK K-NOCK-CELL: sampleOf (targets + ABI slots), sampleOf_injective/_deterministic; reads for ops 131-133
import Kernel.NockDoor -- NOCK N11: a NockApp kernel door (poke 23 / peek 22, state at axis 6) refereed by re-execution; door_poke_sound / door_state_stale_refused / door_effects_are_writes / door_peek_pure / door_load_deterministic; ops 135-137
import Kernel.NockRun -- NOCK K-RAN: RunClaim, checkRun (re-execution on the kernel sample), checkRun_sound / no_accepted_of_output_mismatch / steps_equal_oracle; op 134 dryRun
