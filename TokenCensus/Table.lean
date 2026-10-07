/-
# TokenCensus.Table — the census of private constructors

The table `TokenCensus` checks (see `TokenCensus.lean` for the four checks). It is a
Lean module, not a loose text file, so that Lake rebuilds the census whenever a row
changes. One row per private constructor of a package type:

    constructor | home module | kind | layer | note
-/

namespace Minidregg.TokenCensus

/-- The census table, one row per line; `#` starts a comment line. -/
def table : String := "
# Token census: every private constructor of a package type (TokenCensus.lean checks this table).
# Columns:  constructor | home module | kind | layer | note
#   kind   evidence       a theorem`s `only X mints this` story relies on the constructor's privacy
#          encapsulation  the privacy hides a representation; no guarantee rests on who builds it
#   layer  L1 <theorem>   the type carries the proposition it asserts: <theorem> states the guarantee
#                         for EVERY inhabitant, so a forgery must prove it (unforgeable as a theorem)
#          L2             opaque: the guarantee rests on a runtime fact no proof can express (an oracle
#                         or IO verdict) or is not yet stated as a proposition; protected only by
#                         TokenCensus check 1 (no foreign mint) and its per-row plant
# The note records the field census at classification (P proof fields / D data fields) and, where
# reviewed, why the row has its kind and layer.
Minidregg.Assurance.GrainForkScopedSettlement.ScopedCanonicalReceipt.mk | Assurance.GrainForkScopedSettlement | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Assurance.GrainForkSettlement.CanonicalReceipt.mk | Assurance.GrainForkSettlement | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Assurance.ReactiveLifecycleHistory.Broken.mk | Assurance.ReactiveLifecycleHistory | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Assurance.ReactiveLifecycleHistory.Expired.mk | Assurance.ReactiveLifecycleHistory | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Assurance.ReactiveLifecycleHistory.Finalized.mk | Assurance.ReactiveLifecycleHistory | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Assurance.ReactiveLifecycleHistory.Notification.mk | Assurance.ReactiveLifecycleHistory | evidence | L2 | 4 proof / 1 data fields; layer-1 review pending
Minidregg.Assurance.ReactiveLifecycleHistory.Promise.mk | Assurance.ReactiveLifecycleHistory | evidence | L2 | 0 proof / 1 data fields; layer-1 review pending; mints: Promise.open (opening a promise is the model input; no verdict rests on it)
Minidregg.Assurance.ReactiveLifecycleHistory.Reaction.mk | Assurance.ReactiveLifecycleHistory | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Assurance.SemanticHistoryAccumulator.VerifiedHistoryHead.mk | Assurance.SemanticHistoryAccumulator | evidence | L2 | 5 proof / 4 data fields; layer-1 review pending
Minidregg.Assurance.SemanticHistoryBcsGame.HistoryBcsGameSecurity.mk | Assurance.SemanticHistoryBcsGame | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Assurance.SemanticHistoryFamily.VerifiedHistoryHead.mk | Assurance.SemanticHistoryFamily | evidence | L2 | 5 proof / 10 data fields; layer-1 review pending
Minidregg.Assurance.TransclusionBacklinkHistory.AppliedEffect.mk | Assurance.TransclusionBacklinkHistory | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Assurance.TransclusionBacklinkHistory.LinkEvent.mk | Assurance.TransclusionBacklinkHistory | evidence | L2 | 9 proof / 3 data fields; layer-1 review pending
Minidregg.Assurance.TransclusionBacklinkHistory.Observation.mk | Assurance.TransclusionBacklinkHistory | evidence | L2 | 11 proof / 1 data fields; layer-1 review pending
Minidregg.Compiler.CanonicalPolicyAdmission.PolicyStepContext.mk | Compiler.CanonicalPolicyAdmission | evidence | L2 | 0 proof / 5 data fields; layer-1 review pending; mints: PolicyStepContext.ofPreparedTuple (projects a real prepared tuple; review pending: the tuple is not itself a census token)
Minidregg.Compiler.CarriedApplicationProvenance.CarriedIssue.mk | Compiler.CarriedApplicationProvenance | evidence | L2 | 6 proof / 5 data fields; layer-1 review pending
Minidregg.Compiler.CarriedDispatchProvenance.CarriedDispatchIssue.mk | Compiler.CarriedDispatchProvenance | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Compiler.CarriedSegmentIO.AuditedSource.mk | Compiler.CarriedSegmentIO | evidence | L2 | 0 proof / 3 data fields; layer-1 review pending
Minidregg.Compiler.CarriedSegmentIO.Authorized.mk | Compiler.CarriedSegmentIO | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Compiler.CarriedSegmentIO.Prepared.mk | Compiler.CarriedSegmentIO | evidence | L2 | 0 proof / 4 data fields; layer-1 review pending
Minidregg.Compiler.CarriedSegmentIO.PreservedPrefix.mk | Compiler.CarriedSegmentIO | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Compiler.CredentialAuthorityDomainReceiver.Loaded.mk | Compiler.CredentialAuthorityDomainReceiver | evidence | L2 | 5 proof / 1 data fields; layer-1 review pending
Minidregg.Compiler.CredentialAuthorityDomainReceiver.LoadedDirectory.mk | Compiler.CredentialAuthorityDomainReceiver | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Compiler.CredentialAuthorityDomainReceiver.PreparedGrantBatch.mk | Compiler.CredentialAuthorityDomainReceiver | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Compiler.CredentialAuthorityServed.ServedAuthority.mk | Compiler.CredentialAuthorityServed | evidence | L2 | an authority snapshot served from a verified open (kn2-store-open ii); layer-1 review pending
Minidregg.Compiler.CredentialAuthorityServed.ServedDirectory.mk | Compiler.CredentialAuthorityServed | evidence | L2 | a directory served from a verified open (kn2-store-open ii); layer-1 review pending
Minidregg.Compiler.CredentialSignatureAdmission.CheckedSignature.mk | Compiler.CredentialSignatureAdmission | evidence | L2 | 2 proof / 6 data fields; layer-1 review pending
Minidregg.Compiler.CredentialSignatureAdmission.ReceiverSignature.mk | Compiler.CredentialSignatureAdmission | evidence | L2 | a voucher erased to a value a Prepared record can hold; the oracle verdict it carries is a runtime fact
Minidregg.Compiler.DurableHistory.Head.mk | Compiler.DurableHistory | evidence | L2 | a verified history head of an opened Store; a genesis head asserts every nullifier and tx id absent; mints: Head.genesis
Minidregg.Compiler.DurableHistory.RawEntry.mk | Compiler.DurableHistory | encapsulation | L2 | a raw history entry as stored; trusted only after Head.verify checks it at use (kn2-store-open)
Minidregg.Compiler.DurableHistory.RawNode.mk | Compiler.DurableHistory | encapsulation | L2 | a raw accumulator node as stored; trusted only after Head.verify checks it at use (kn2-store-open)
Minidregg.Compiler.DurableHistory.StoreIdentity.mk | Compiler.DurableHistory | evidence | L2 | the identity of an opened Store; minted only by the open (kn2-store-open); mints: StoreIdentity.ofOpen
Minidregg.Compiler.DurableServed.Served.mk | Compiler.DurableServed | evidence | L2 | the served Store open (kn2-store-open ii); layer-1 review pending
Minidregg.Compiler.DurableServed.Start.mk | Compiler.DurableServed | evidence | L2 | the served Store open's start state (kn2-store-open ii); layer-1 review pending
Minidregg.Compiler.GenericSimplexIO.VerifiedCommit.mk | Compiler.GenericSimplexIO | evidence | L2 | 4 proof / 1 data fields; layer-1 review pending
Minidregg.Compiler.GrainResourceBirthAuthority.Prepared.mk | Compiler.GrainResourceBirthAuthority | evidence | L2 | 3 proof / 2 data fields; layer-1 review pending
Minidregg.Compiler.GrainResourceBirthController.PreparedSourceAuthority.mk | Compiler.GrainResourceBirthController | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Compiler.GrainResourceBirthController.PreparedSourceBirth.mk | Compiler.GrainResourceBirthController | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Compiler.NeutralPolicyCarry.Plan.mk | Compiler.NeutralPolicyCarry | evidence | L2 | 0 proof / 5 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveBendCombinedResult.Prepared.mk | Compiler.ObjectiveBendCombinedResult | evidence | L2 | 10 proof / 14 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveBendFrontEnd.Accepted.mk | Compiler.ObjectiveBendFrontEnd | evidence | L2 | 7 proof / 5 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveBendGenericResult.Prepared.mk | Compiler.ObjectiveBendGenericResult | evidence | L2 | 11 proof / 15 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveBendNativePlanData.BoundEffect.mk | Compiler.ObjectiveBendNativePlanData | evidence | L2 | 5 proof / 3 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveBendPublication.Replayed.mk | Compiler.ObjectiveBendPublication | evidence | L2 | 3 proof / 2 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveBendResultAdapter.PreparedResult.mk | Compiler.ObjectiveBendResultAdapter | evidence | L2 | 9 proof / 6 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveBendSourceArtifact.Checked.mk | Compiler.ObjectiveBendSourceArtifact | evidence | L2 | 3 proof / 3 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveNativeScalarBinding.BoundPlan.mk | Compiler.ObjectiveNativeScalarBinding | evidence | L2 | 4 proof / 3 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveNativeScalarBinding.BoundRead.mk | Compiler.ObjectiveNativeScalarBinding | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Compiler.ObjectiveNativeScalarBinding.BoundScalar.mk | Compiler.ObjectiveNativeScalarBinding | evidence | L2 | 8 proof / 3 data fields; layer-1 review pending
Minidregg.Compiler.PayEnrolSignatureIO.Checked.mk | Compiler.PayEnrolSignatureIO | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Compiler.PayEnrolSignatureV2IO.Checked.mk | Compiler.PayEnrolSignatureV2IO | evidence | L2 | 0 proof / 3 data fields; layer-1 review pending
Minidregg.Host.FnSelectiveReleaseFnAck.Selected.mk | Host.FnSelectiveReleaseFnAck | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Host.GrainOriginPreparation.Prepared.mk | Host.GrainOriginPreparation | evidence | L2 | 0 proof / 3 data fields; layer-1 review pending
Minidregg.Host.GrainOriginSource.Rendered.mk | Host.GrainOriginSource | evidence | L2 | 4 proof / 8 data fields; layer-1 review pending
Minidregg.Host.Json.BirthParts.mk | Host.Json | encapsulation | L2 | 0 proof / 4 data fields; JSON parsing helper, no admission rests on it
Minidregg.Host.Json.GrainBirthPeer.mk | Host.Json | encapsulation | L2 | 0 proof / 5 data fields; JSON parsing helper, no admission rests on it
Minidregg.Host.Json.ScanFrame.mk | Host.Json | encapsulation | L2 | 0 proof / 3 data fields; JSON parsing helper, no admission rests on it
Minidregg.Host.RetainedSegmentInspection.ReadonlyOperation.continuity | Host.RetainedSegmentInspection | encapsulation | L2 | closed operation enumeration; no admission rests on who names it
Minidregg.Host.RetainedSegmentInspection.ReadonlyOperation.dispatchLookup | Host.RetainedSegmentInspection | encapsulation | L2 | closed operation enumeration; no admission rests on who names it
Minidregg.Host.RetainedSegmentInspection.ReadonlyOperation.receiptByTransaction | Host.RetainedSegmentInspection | encapsulation | L2 | closed operation enumeration; no admission rests on who names it
Minidregg.Host.SourceAgreementJson.BirthParts.mk | Host.SourceAgreementJson | encapsulation | L2 | 0 proof / 4 data fields; JSON parsing helper, no admission rests on it
Minidregg.Host.SourceAgreementJson.ScanFrame.mk | Host.SourceAgreementJson | encapsulation | L2 | 0 proof / 3 data fields; JSON parsing helper, no admission rests on it
Minidregg.Kernel.ActivitySeatEnd.Joined.mk | Kernel.ActivitySeatEnd | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeDispatchCore.Checked.mk | Kernel.ApplicationAgentLifetimeDispatchCore | evidence | L2 | 6 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeDispatchCurrent.Checked.mk | Kernel.ApplicationAgentLifetimeDispatchCurrent | evidence | L2 | 20 proof / 14 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeDispatchPayer.Checked.mk | Kernel.ApplicationAgentLifetimeDispatchPayer | evidence | L2 | 8 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeDispatchReceiver.Permit.mk | Kernel.ApplicationAgentLifetimeDispatchReceiver | evidence | L2 | 2 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence.mk | Kernel.ApplicationAgentLifetimeDispatchReserveCore | evidence | L2 | 3 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeGrantAdmission.Accepted.mk | Kernel.ApplicationAgentLifetimeGrantAdmission | evidence | L2 | 5 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeGrantAtomicBirth.Checked.mk | Kernel.ApplicationAgentLifetimeGrantAtomicBirth | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeGrantDelegation.Checked.mk | Kernel.ApplicationAgentLifetimeGrantDelegation | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeGrantDelegation.Prepared.mk | Kernel.ApplicationAgentLifetimeGrantDelegation | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationAgentLifetimeGrantSource.Ready.mk | Kernel.ApplicationAgentLifetimeGrantSource | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchAdmission.CheckedCurrentForSourceBytes.mk | Kernel.ApplicationDispatchAdmission | evidence | L2 | 15 proof / 13 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchAdmission.CheckedRead.mk | Kernel.ApplicationDispatchAdmission | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchAgentCore.Checked.mk | Kernel.ApplicationDispatchAgentCore | evidence | L2 | 6 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchAgentPayer.Checked.mk | Kernel.ApplicationDispatchAgentPayer | evidence | L2 | 8 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchAgentReceiver.Committed.mk | Kernel.ApplicationDispatchAgentReceiver | evidence | L2 | 1 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchAgentReceiver.Permit.mk | Kernel.ApplicationDispatchAgentReceiver | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchAgentReserveCore.RawEvidence.mk | Kernel.ApplicationDispatchAgentReserveCore | evidence | L2 | 3 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchAgentReserveCore.ReservedEvidence.mk | Kernel.ApplicationDispatchAgentReserveCore | evidence | L2 | 3 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchHistoricalCore.CheckedCandidate.mk | Kernel.ApplicationDispatchHistoricalCore | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchHistoricalCore.IssuedEvidence.mk | Kernel.ApplicationDispatchHistoricalCore | evidence | L2 | 1 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchReceiver.Committed.mk | Kernel.ApplicationDispatchReceiver | evidence | L2 | 1 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchReceiver.Permit.mk | Kernel.ApplicationDispatchReceiver | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchReceiver.RefusalAtTip.mk | Kernel.ApplicationDispatchReceiver | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationDispatchUpper.Accepted.mk | Kernel.ApplicationDispatchUpper | evidence | L2 | 0 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationFailedCreateRetryEvidence.Conditional.mk | Kernel.ApplicationFailedCreateRetryEvidence | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationFailedStartRecoveryAdmission.Candidate.mk | Kernel.ApplicationFailedStartRecoveryAdmission | evidence | L2 | 12 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationFailedStartRecoveryAdmission.PackageRead.mk | Kernel.ApplicationFailedStartRecoveryAdmission | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationFailedStartRecoveryHistory.Candidate.mk | Kernel.ApplicationFailedStartRecoveryHistory | evidence | L2 | 4 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationFailedStartRecoveryPolicy.Accepted.mk | Kernel.ApplicationFailedStartRecoveryPolicy | evidence | L2 | 3 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationFailedStartRecoveryPolicy.CheckedLeg.mk | Kernel.ApplicationFailedStartRecoveryPolicy | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationFailedStartRecoveryReceiver.Confirmed.mk | Kernel.ApplicationFailedStartRecoveryReceiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationFailedStartRecoveryReport.Checked.mk | Kernel.ApplicationFailedStartRecoveryReport | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationGrainBirth.Ready.mk | Kernel.ApplicationGrainBirth | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationGrainSessionBirth.Ready.mk | Kernel.ApplicationGrainSessionBirth | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationGrainSessionEnrollmentAdmission.Checked.mk | Kernel.ApplicationGrainSessionEnrollmentAdmission | evidence | L2 | 1 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationGrainSessionEnrollmentAdmission.CheckedRead.mk | Kernel.ApplicationGrainSessionEnrollmentAdmission | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationGrainSessionEnrollmentReceiver.Confirmed.mk | Kernel.ApplicationGrainSessionEnrollmentReceiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleBeginV2Admission.Accepted.mk | Kernel.ApplicationLifecycleBeginV2Admission | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleBeginV2Receiver.Confirmed.mk | Kernel.ApplicationLifecycleBeginV2Receiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleBeginV3Admission.Accepted.mk | Kernel.ApplicationLifecycleBeginV3Admission | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleBeginV3Receiver.Confirmed.mk | Kernel.ApplicationLifecycleBeginV3Receiver | evidence | L2 | 1 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleClaimCore.Conditional.mk | Kernel.ApplicationLifecycleClaimCore | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleClaimCurrent.CheckedRead.mk | Kernel.ApplicationLifecycleClaimCurrent | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleClaimHistory.Conditional.mk | Kernel.ApplicationLifecycleClaimHistory | evidence | L2 | 0 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleClaimReceiver.Reservation.mk | Kernel.ApplicationLifecycleClaimReceiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleClaimV2Core.Conditional.mk | Kernel.ApplicationLifecycleClaimV2Core | evidence | L2 | 2 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleClaimV2Receiver.Reservation.mk | Kernel.ApplicationLifecycleClaimV2Receiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleClaimV3Core.Conditional.mk | Kernel.ApplicationLifecycleClaimV3Core | evidence | L2 | 3 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleClaimV3Receiver.Reservation.mk | Kernel.ApplicationLifecycleClaimV3Receiver | evidence | L2 | 1 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleClaimVerified.Admitted.mk | Kernel.ApplicationLifecycleClaimVerified | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionAdmission.Candidate.mk | Kernel.ApplicationLifecycleCompletionAdmission | evidence | L2 | 11 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionAdmission.PackageRead.mk | Kernel.ApplicationLifecycleCompletionAdmission | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionHistory.Candidate.mk | Kernel.ApplicationLifecycleCompletionHistory | evidence | L2 | 4 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionPolicy.Accepted.mk | Kernel.ApplicationLifecycleCompletionPolicy | evidence | L2 | 3 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionPolicy.CheckedLeg.mk | Kernel.ApplicationLifecycleCompletionPolicy | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionReceiver.Confirmed.mk | Kernel.ApplicationLifecycleCompletionReceiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionReport.Checked.mk | Kernel.ApplicationLifecycleCompletionReport | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionV2Admission.Candidate.mk | Kernel.ApplicationLifecycleCompletionV2Admission | evidence | L2 | 12 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionV2Admission.PackageRead.mk | Kernel.ApplicationLifecycleCompletionV2Admission | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionV2History.Candidate.mk | Kernel.ApplicationLifecycleCompletionV2History | evidence | L2 | 4 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionV2Policy.Accepted.mk | Kernel.ApplicationLifecycleCompletionV2Policy | evidence | L2 | 3 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionV2Policy.CheckedLeg.mk | Kernel.ApplicationLifecycleCompletionV2Policy | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionV2Receiver.Confirmed.mk | Kernel.ApplicationLifecycleCompletionV2Receiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCompletionV2Report.Checked.mk | Kernel.ApplicationLifecycleCompletionV2Report | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleCreatedHistory.Candidate.mk | Kernel.ApplicationLifecycleCreatedHistory | evidence | L2 | 13 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryBeginV4Admission.Accepted.mk | Kernel.ApplicationLifecycleRetryBeginV4Admission | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryBeginV4Receiver.Confirmed.mk | Kernel.ApplicationLifecycleRetryBeginV4Receiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Core.Conditional.mk | Kernel.ApplicationLifecycleRetryClaimV4Core | evidence | L2 | 3 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Receiver.Reservation.mk | Kernel.ApplicationLifecycleRetryClaimV4Receiver | evidence | L2 | 1 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4Admission.Candidate.mk | Kernel.ApplicationLifecycleRetryCompletionV4Admission | evidence | L2 | 12 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4Admission.PackageRead.mk | Kernel.ApplicationLifecycleRetryCompletionV4Admission | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4CreatedHistory.Candidate.mk | Kernel.ApplicationLifecycleRetryCompletionV4CreatedHistory | evidence | L2 | 13 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4History.Candidate.mk | Kernel.ApplicationLifecycleRetryCompletionV4History | evidence | L2 | 4 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4Policy.Accepted.mk | Kernel.ApplicationLifecycleRetryCompletionV4Policy | evidence | L2 | 3 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4Policy.CheckedLeg.mk | Kernel.ApplicationLifecycleRetryCompletionV4Policy | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4Receiver.Confirmed.mk | Kernel.ApplicationLifecycleRetryCompletionV4Receiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4Report.Checked.mk | Kernel.ApplicationLifecycleRetryCompletionV4Report | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationRouteAdmission.Attestation.mk | Kernel.ApplicationRouteAdmission | evidence | L2 | 5 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationShareIssueAdmission.Accepted.mk | Kernel.ApplicationShareIssueAdmission | evidence | L2 | 5 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationShareIssueAtomicBirth.Checked.mk | Kernel.ApplicationShareIssueAtomicBirth | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationShareIssueDelegation.Checked.mk | Kernel.ApplicationShareIssueDelegation | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationShareIssueDelegation.Prepared.mk | Kernel.ApplicationShareIssueDelegation | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationShareIssueGrainAdmission.Accepted.mk | Kernel.ApplicationShareIssueGrainAdmission | evidence | L2 | 5 proof / 10 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationShareIssueHistorical.Issued.mk | Kernel.ApplicationShareIssueHistorical | evidence | L2 | 3 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationShareIssueSource.Ready.mk | Kernel.ApplicationShareIssueSource | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ApplicationStreamContinuity.Attestation.mk | Kernel.ApplicationStreamContinuity | evidence | L2 | 6 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.AudienceRosterBinding.Checked.mk | Kernel.AudienceRosterBinding | evidence | L2 | 6 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.AudienceRosterBinding.CheckedBytes.mk | Kernel.AudienceRosterBinding | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.BirthCandidateAdmission.Checked.mk | Kernel.BirthCandidateAdmission | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.BirthExportAdmission.Evaluated.mk | Kernel.BirthExportAdmission | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.BirthExportAdmission.ItemChecked.mk | Kernel.BirthExportAdmission | evidence | L2 | 5 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.BirthExportAdmission.Neutral.mk | Kernel.BirthExportAdmission | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.BirthExportAdmission.NeutralItem.mk | Kernel.BirthExportAdmission | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityDelegationController.Accepted.mk | Kernel.CapabilityDelegationController | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityDelegationController.Prepared.mk | Kernel.CapabilityDelegationController | evidence | L2 | 4 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityDelegationReceiver.AcceptedDelegation.mk | Kernel.CapabilityDelegationReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityDelegationReceiver.DecodedIngress.mk | Kernel.CapabilityDelegationReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityRenounce.Accepted.mk | Kernel.CapabilityRenounce | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityRenounce.AcceptedRenounce.mk | Kernel.CapabilityRenounce | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityRenounce.DecodedIngress.mk | Kernel.CapabilityRenounce | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityRenounce.HolderRefusal.mk | Kernel.CapabilityRenounce | evidence | L2 | 3 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityRenounce.Prepared.mk | Kernel.CapabilityRenounce | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityRevocationController.Accepted.mk | Kernel.CapabilityRevocationController | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityRevocationController.PreparedOn.mk | Kernel.CapabilityRevocationController | evidence | L2 | 3 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityRevocationReceiver.AcceptedRevocation.mk | Kernel.CapabilityRevocationReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CapabilityRevocationReceiver.DecodedIngress.mk | Kernel.CapabilityRevocationReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.CarriedApplicationDispatchReceiver.Committed.mk | Kernel.CarriedApplicationDispatchReceiver | evidence | L2 | 1 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.CarriedApplicationDispatchReceiver.Permit.mk | Kernel.CarriedApplicationDispatchReceiver | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.CarriedApplicationDispatchReceiver.RefusalAtTip.mk | Kernel.CarriedApplicationDispatchReceiver | evidence | L2 | 1 proof / 0 data fields; layer-1 review pending
Minidregg.Kernel.CarriedDispatchAdmission.Admitted.mk | Kernel.CarriedDispatchAdmission | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CarriedSessionEnrollmentAdmission.Admitted.mk | Kernel.CarriedSessionEnrollmentAdmission | evidence | L2 | 3 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CarriedSessionEnrollmentReceiver.Confirmed.mk | Kernel.CarriedSessionEnrollmentReceiver | evidence | L2 | 2 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.CertifyReceiver.Accepted.mk | Kernel.CertifyReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CertifyReceiver.AcceptedCertify.mk | Kernel.CertifyReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.CertifyReceiver.DecodedIngress.mk | Kernel.CertifyReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.CertifyReceiver.Prepared.mk | Kernel.CertifyReceiver | evidence | L2 | 1 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ClockCellDomain.Loaded.mk | Kernel.ClockCellDomain | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ClockTickReceiver.Accepted.mk | Kernel.ClockTickReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ClockTickReceiver.AcceptedTick.mk | Kernel.ClockTickReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ClockTickReceiver.DecodedIngress.mk | Kernel.ClockTickReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ClockTickReceiver.Prepared.mk | Kernel.ClockTickReceiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.ConfidentialAudienceAdmission.Checked.mk | Kernel.ConfidentialAudienceAdmission | evidence | L2 | 6 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ContentResource.PreparedCell.mk | Kernel.ContentResource | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.DeclaredResourceController.AcceptedInvocation.mk | Kernel.DeclaredResourceController | evidence | L2 | 4 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.DeclaredResourceController.AuthorityInvocation.mk | Kernel.DeclaredResourceController | evidence | L2 | 3 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.DeclaredResourceController.PreparedInvocation.mk | Kernel.ResourceTransaction | evidence | L2 | 7 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.DeclaredResourceController.PreparedPolicyLeg.mk | Kernel.PreparedInvocationDiagnostics | evidence | L2 | 4 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.DeclaredResourceController.PreparedTarget.mk | Kernel.ResourceTransaction | evidence | L2 | 5 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.DeclaredResourceScalar.PreparedCell.mk | Kernel.DeclaredResourceScalar | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.FleetTurn.Accepted.mk | Kernel.FleetTurn | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.FleetTurn.DecodedIngress.mk | Kernel.FleetTurn | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.FleetTurn.Prepared.mk | Kernel.FleetTurn | evidence | L2 | 3 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.FleetTurnReceiver.AcceptedTurn.mk | Kernel.FleetTurnReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.FnConsumerFrontierGateway.Checked.mk | Kernel.FnConsumerFrontierGateway | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.FnConsumerFrontierGateway.CheckedOpened.mk | Kernel.FnConsumerFrontierGateway | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.FnConsumerFrontierGateway.Prepared.mk | Kernel.FnConsumerFrontierGateway | evidence | L2 | 5 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.FnConsumerNamespaceAdmission.AcceptedVerified.mk | Kernel.FnConsumerNamespaceAdmission | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.FnConsumerNamespaceAdmissionAt.Conditional.mk | Kernel.FnConsumerNamespaceAdmissionAt | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.FnConsumerNamespaceHistory.Original.mk | Kernel.FnConsumerNamespaceHistory | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.FnEmptyPollAdmissionAtV2.Accepted.mk | Kernel.FnEmptyPollAdmissionAtV2 | evidence | L2 | 4 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.FnEmptyPollAdmissionV2.AcceptedVerified.mk | Kernel.FnEmptyPollAdmissionV2 | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.FnEmptyPollAdmissionV2.Checked.mk | Kernel.FnEmptyPollAdmissionV2 | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.FnSelectedPollAdmission.AcceptedVerified.mk | Kernel.FnSelectedPollAdmission | evidence | L2 | 3 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.FnSelectedPollAdmission.Checked.mk | Kernel.FnSelectedPollAdmission | evidence | L2 | 4 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.FnSelectedPollAdmissionAt.Accepted.mk | Kernel.FnSelectedPollAdmissionAt | evidence | L2 | 8 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.FnSelectiveReleaseAdmission.Accepted.mk | Kernel.FnSelectiveReleaseAdmission | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.FnSelectiveReleaseSignature.Checked.mk | Kernel.FnSelectiveReleaseSignature | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.FnSelectiveReleaseSourceAuthority.Checked.mk | Kernel.FnSelectiveReleaseSourceAuthority | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.FnSelectiveReleaseSourceAuthority.Prepared.mk | Kernel.FnSelectiveReleaseSourceAuthority | evidence | L2 | 6 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.FnSelectiveReleaseSourceReceiver.Accepted.mk | Kernel.FnSelectiveReleaseSourceReceiver | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.GrainResourceBirthAdmission.Accepted.mk | Kernel.GrainResourceBirthAdmission | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.GrainResourceBirthAdmission.Pending.mk | Kernel.GrainResourceBirthAdmission | evidence | L2 | 5 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.GrainResourceBirthPolicyController.DecodedIngress.mk | Kernel.GrainResourceBirthPolicyController | evidence | L2 | 6 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.GrainResourceBirthTransaction.PreparedTargets.mk | Kernel.GrainResourceBirthTransaction | evidence | L2 | 0 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.JobMoneyReceiver.Accepted.mk | Kernel.JobMoneyReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.JobMoneyReceiver.AcceptedMoney.mk | Kernel.JobMoneyReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.JobMoneyReceiver.DecodedIngress.mk | Kernel.JobMoneyReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.JobMoneyReceiver.Prepared.mk | Kernel.JobMoneyReceiver | evidence | L2 | 7 proof / 11 data fields; layer-1 review pending
Minidregg.Kernel.JointControlBootstrap.Admission.mk | Kernel.JointControlBootstrap | evidence | L2 | 3 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.JointControlBootstrapBundle.Accepted.mk | Kernel.JointControlBootstrapBundle | evidence | L2 | 7 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.JointControlBootstrapBundle.Initialization.mk | Kernel.JointControlBootstrapBundle | evidence | L2 | 2 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.JointPromiseAuthorization.Accepted.mk | Kernel.JointPromiseAuthorization | evidence | L2 | 5 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.JointReceiver.Ordered.mk | Kernel.JointReceiver | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.JointReceiver.Pending.mk | Kernel.JointReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.JointReceiverAdmission.Reserved.mk | Kernel.JointReceiverAdmission | evidence | L2 | 12 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.NativeHistorySelection.Candidate.mk | Kernel.NativeHistorySelection | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHistorySelection.Matched.mk | Kernel.NativeHistorySelection | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.NativeHost.Opened.mk | Kernel.NativeHostContext | evidence | L2 | 1 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostGenesis.Built.mk | Kernel.NativeHostGenesis | evidence | L2 | 3 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.AgentDispatchAt.mk | Kernel.NativeHostReplay | evidence | L2 | 6 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.BeginAtV3.mk | Kernel.NativeHostReplay | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.BeginAtV4.mk | Kernel.NativeHostReplay | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.ClaimAt.mk | Kernel.NativeHostReplay | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.ClaimAtV2.mk | Kernel.NativeHostReplay | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.ClaimAtV3.mk | Kernel.NativeHostReplay | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.ClaimAtV4.mk | Kernel.NativeHostReplay | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.CompletionAt.mk | Kernel.NativeHostReplay | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.CompletionAtV2.mk | Kernel.NativeHostReplay | evidence | L2 | 4 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.CompletionAtV4.mk | Kernel.NativeHostReplay | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.CreatedAt.mk | Kernel.NativeHostReplay | evidence | L2 | 5 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.Derived.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 18 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.DispatchAt.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.FailedStartRecoveryAt.mk | Kernel.NativeHostReplay | evidence | L2 | 4 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.LifetimeDispatchAt.mk | Kernel.NativeHostReplay | evidence | L2 | 10 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.LifetimeGrantIssueAt.mk | Kernel.NativeHostReplay | evidence | L2 | 5 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorBegin.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorBeginV2.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorBeginV3.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorBeginV4.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorClaimV2.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorClaimV3.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorClaimV4.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorCreatedV3.mk | Kernel.NativeHostReplay | evidence | L2 | 2 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorDispatchReserve.mk | Kernel.NativeHostReplay | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorIssue.mk | Kernel.NativeHostReplay | evidence | L2 | 0 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorLifetimeGrant.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorRecovery.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorRunningV3.mk | Kernel.NativeHostReplay | evidence | L2 | 3 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.PriorSelectedRelease.mk | Kernel.NativeHostReplay | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.RunningAt.mk | Kernel.NativeHostReplay | evidence | L2 | 5 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.SessionEnrollmentAt.mk | Kernel.NativeHostReplay | evidence | L2 | 5 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.SuffixVerified.mk | Kernel.NativeHostReplay | evidence | L2 | 8 proof / 16 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.SuffixWalked.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.Verified.mk | Kernel.NativeHostReplay | evidence | L2 | 3 proof / 16 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.VerifiedSelection.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostReplay.Walked.mk | Kernel.NativeHostReplay | evidence | L2 | 1 proof / 16 data fields; layer-1 review pending
Minidregg.Kernel.NativeHostServed.OpenedServed.mk | Kernel.NativeHostServed | evidence | L2 | the Host's served open (kn2-store-open ii); layer-1 review pending
Minidregg.Kernel.NativeObservationController.AuthorizedIntent.mk | Kernel.NativeObservationController | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.NativeObservationController.CheckedGrant.mk | Kernel.NativeObservationController | evidence | L2 | 2 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.NativeObservationController.Selected.mk | Kernel.NativeObservationController | evidence | L2 | 5 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ObjectAudienceInstall.Prepared.mk | Kernel.ObjectAudienceInstall | evidence | L2 | 5 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Abandonment.mk | Kernel.ObjectiveActivity | evidence | L2 | 10 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Abort.mk | Kernel.ObjectiveActivityUpgrade | evidence | L2 | upgrade-turns (DEPUTY-OB-ENG): proof fields mirror the admitting checks per its audit; L1 theorem pending from OB-ENG
Minidregg.Kernel.ObjectiveActivity.Adoption.mk | Kernel.ObjectiveActivityUpgrade | evidence | L2 | upgrade-turns (DEPUTY-OB-ENG): proof fields mirror the admitting checks per its audit; L1 theorem pending from OB-ENG
Minidregg.Kernel.ObjectiveActivity.Birth.mk | Kernel.ObjectiveActivity | evidence | L2 | 15 proof / 11 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.BirthPrefix.mk | Kernel.ObjectiveActivity | evidence | L2 | DEPUTY-OB-ENG type; layer-1 review pending (OB-ENG)
Minidregg.Kernel.ObjectiveActivity.Creation.mk | Kernel.ObjectiveActivity | evidence | L2 | 3 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Delivery.mk | Kernel.ObjectiveActivity | evidence | L2 | 23 proof / 20 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Exhaustion.mk | Kernel.ObjectiveActivity | evidence | L2 | 20 proof / 15 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Instantiated.mk | Kernel.ObjectiveActivity | evidence | L2 | 1 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Migrated.mk | Kernel.ObjectiveActivityUpgrade | evidence | L2 | upgrade-turns (DEPUTY-OB-ENG): proof fields mirror the admitting checks per its audit; L1 theorem pending from OB-ENG
Minidregg.Kernel.ObjectiveActivity.Migration.mk | Kernel.ObjectiveActivity | evidence | L2 | upgrade-turns ObjectRecord migration (DEPUTY-OB-ENG); L1 theorem pending from OB-ENG
Minidregg.Kernel.ObjectiveActivity.Postings.mk | Kernel.ObjectiveActivity | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Program.mk | Kernel.ObjectiveActivity | evidence | L2 | 3 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Publication.mk | Kernel.ObjectiveActivity | evidence | L2 | 5 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Rebirth.mk | Kernel.ObjectiveActivityUpgrade | evidence | L2 | upgrade-turns (DEPUTY-OB-ENG): proof fields mirror the admitting checks per its audit; L1 theorem pending from OB-ENG
Minidregg.Kernel.ObjectiveActivity.Registration.mk | Kernel.ObjectiveDomain | evidence | L2 | 7 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Replay.mk | Kernel.ObjectiveActivity | evidence | L2 | 4 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.Resolution.mk | Kernel.ObjectiveActivity | evidence | L2 | 5 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.ResumeHead.mk | Kernel.ObjectiveActivity | evidence | L2 | DEPUTY-OB-ENG type; layer-1 review pending (OB-ENG)
Minidregg.Kernel.ObjectiveActivity.ResumeTail.mk | Kernel.ObjectiveActivity | evidence | L2 | DEPUTY-OB-ENG type; layer-1 review pending (OB-ENG)
Minidregg.Kernel.ObjectiveActivity.TopUp.mk | Kernel.ObjectiveActivity | evidence | L2 | 3 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivity.TypedData.mk | Kernel.ObjectiveActivity | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivityReceiver.Accepted.mk | Kernel.ObjectiveActivityReceiver | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivityReceiver.DecodedIngress.mk | Kernel.ObjectiveActivityReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveActivityReceiver.Prepared.mk | Kernel.ObjectiveActivityReceiver | evidence | L2 | 6 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveBendArtifactSource.Current.mk | Kernel.ObjectiveBendArtifactSource | evidence | L2 | 3 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveBendArtifactSource.Loaded.mk | Kernel.ObjectiveBendArtifactSource | evidence | L2 | 5 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveBendNativeAdmission.Admitted.mk | Kernel.ObjectiveBendNativeAdmission | evidence | L2 | 7 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveBendNativeAdmission.Core.mk | Kernel.ObjectiveBendNativeAdmission | evidence | L2 | 11 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveBendNativeAdmission.Selection.mk | Kernel.ObjectiveBendNativeAdmission | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveBendNativeAdmission.SourceSelection.mk | Kernel.ObjectiveBendNativeAdmission | evidence | L2 | 9 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveBendNativeInput.AdmittedRead.mk | Kernel.ObjectiveBendNativeInput | evidence | L2 | 1 proof / 9 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveBendNativeInput.Bound.mk | Kernel.ObjectiveBendNativeInput | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending; mints: ObjectiveBendNativeInput.bind (review pending: binds by data, no proposition argument)
Minidregg.Kernel.ObjectiveBendPreparedOutput.Prepared.mk | Kernel.ObjectiveBendPreparedOutput | evidence | L2 | 2 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveBendPublishedPackage.Loaded.mk | Kernel.ObjectiveBendPublishedPackage | evidence | L2 | 7 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveCall.Deliverable.mk | Kernel.ObjectiveCall | evidence | L2 | 5 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveCall.Invocation.mk | Kernel.ObjectiveCall | evidence | L2 | 7 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveCall.Method.mk | Kernel.ObjectiveCall | evidence | L2 | 5 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.ObjectiveSend.MessageDelivery.mk | Kernel.ObjectiveSend | evidence | L2 | 14 proof / 12 data fields; layer-1 review pending
Minidregg.Kernel.ParticipantFactoryProvisioning.Accepted.mk | Kernel.ParticipantFactoryProvisioning | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ParticipantFactoryProvisioning.DecodedIngress.mk | Kernel.ParticipantFactoryProvisioning | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ParticipantFactoryProvisioning.Prepared.mk | Kernel.ParticipantFactoryProvisioning | evidence | L2 | 1 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.ParticipantFactoryProvisioningReceiver.AcceptedProvisioning.mk | Kernel.ParticipantFactoryProvisioningReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ParticipantKeyEnrollment.Accepted.mk | Kernel.ParticipantKeyEnrollment | evidence | L2 | 3 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ParticipantKeyEnrollment.DecodedIngress.mk | Kernel.ParticipantKeyEnrollment | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ParticipantKeyEnrollment.Prepared.mk | Kernel.ParticipantKeyEnrollment | evidence | L2 | 4 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.ParticipantKeyEnrollmentReceiver.AcceptedEnrollment.mk | Kernel.ParticipantKeyEnrollmentReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PayAssignmentReceiver.Accepted.mk | Kernel.PayAssignmentReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PayAssignmentReceiver.AcceptedAssignment.mk | Kernel.PayAssignmentReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PayAssignmentReceiver.DecodedIngress.mk | Kernel.PayAssignmentReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PayAssignmentReceiver.Prepared.mk | Kernel.PayAssignmentReceiver | evidence | L2 | 1 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.PayBookReceiver.Accepted.mk | Kernel.PayBookReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PayBookReceiver.AcceptedChange.mk | Kernel.PayBookReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PayBookReceiver.DecodedIngress.mk | Kernel.PayBookReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PayBookReceiver.Prepared.mk | Kernel.PayBookReceiver | evidence | L2 | 1 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.PayCellDomain.Loaded.mk | Kernel.PayCellDomain | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.PayClaimCommand.Checked.mk | Kernel.PayClaimCommand | evidence | L2 | 0 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PayClaimCommand.DecodedIngress.mk | Kernel.PayClaimCommand | evidence | L2 | 3 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PayClaimReceiver.AcceptedClaim.mk | Kernel.PayClaimReceiver | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PayClaimReceiver.Prepared.mk | Kernel.PayClaimReceiver | evidence | L2 | 4 proof / 13 data fields; layer-1 review pending
Minidregg.Kernel.PayClaimReceiver.SourceWitness.mk | Kernel.PayClaimReceiver | evidence | L2 | 1 proof / 0 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolReceiver.Accepted.mk | Kernel.PayEnrolReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolReceiver.AcceptedEnrol.mk | Kernel.PayEnrolReceiver | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolReceiver.DecodedIngress.mk | Kernel.PayEnrolReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolReceiver.EnrolLegs.mk | Kernel.PayEnrolReceiver | evidence | L2 | 10 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolReceiver.Prepared.mk | Kernel.PayEnrolReceiver | evidence | L2 | 8 proof / 13 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolV2Legs.EnrolLegs.mk | Kernel.PayEnrolV2Legs | evidence | L2 | 15 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolV2Legs.RenewLegs.mk | Kernel.PayEnrolV2Legs | evidence | L2 | 5 proof / 0 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolV2Receiver.Accepted.mk | Kernel.PayEnrolV2Receiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolV2Receiver.AcceptedEnrol.mk | Kernel.PayEnrolV2Receiver | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PayEnrolV2Receiver.Prepared.mk | Kernel.PayEnrolV2Receiver | evidence | L2 | 10 proof / 15 data fields; layer-1 review pending
Minidregg.Kernel.PayObservationReceiver.DecodedIngress.mk | Kernel.PayObservationReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PayObservationReceiver.Planned.mk | Kernel.PayObservationReceiver | evidence | L1 Minidregg.Kernel.PayObservationReceiver.Planned.sound | loaded cells exact, tip retained, clock at the tip slot, Book = batch applied
Minidregg.Kernel.PayObservationReceiver.Prepared.mk | Kernel.PayObservationReceiver | evidence | L1 Minidregg.Kernel.PayObservationReceiver.Prepared.sound | receiver-sourced receipt for the carried envelope, request bound to the pay head; the receipt verdict is L2
Minidregg.Kernel.PolicyInstallReceiver.AcceptedInstall.mk | Kernel.PolicyInstallReceiver | evidence | L2 | 4 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.PolicyInstallReceiver.DecodedIngress.mk | Kernel.PolicyInstallReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PolicyInstallReceiver.Prepared.mk | Kernel.PolicyInstallReceiver | evidence | L2 | 9 proof / 8 data fields; layer-1 review pending
Minidregg.Kernel.PurseRefillReceiver.Accepted.mk | Kernel.PurseRefillReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PurseRefillReceiver.AcceptedRefill.mk | Kernel.PurseRefillReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.PurseRefillReceiver.DecodedIngress.mk | Kernel.PurseRefillReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.PurseRefillReceiver.Prepared.mk | Kernel.PurseRefillReceiver | evidence | L2 | 5 proof / 10 data fields; layer-1 review pending
Minidregg.Kernel.RealmWellReceiver.Accepted.mk | Kernel.RealmWellReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.RealmWellReceiver.AcceptedWell.mk | Kernel.RealmWellReceiver | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.RealmWellReceiver.DecodedIngress.mk | Kernel.RealmWellReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.RealmWellReceiver.Prepared.mk | Kernel.RealmWellReceiver | evidence | L2 | 1 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.RecipientReadEntitlement.CheckedView.mk | Kernel.RecipientReadEntitlement | evidence | L2 | 8 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.mk | Kernel.ResourceBirthController | evidence | L2 | 14 proof / 9 data fields; layer-1 review pending
Minidregg.Kernel.ResourceBirthController.Concrete.PreparedDraft.mk | Kernel.ResourceBirthController | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ResourceBirthController.Concrete.PreparedGrainBirth.mk | Kernel.ResourceBirthController | evidence | L2 | 1 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.ResourceBirthController.Concrete.PreparedGrainDraft.mk | Kernel.ResourceBirthController | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ResourceBirthController.Concrete.PreparedPostAuthority.mk | Kernel.ResourceBirthController | evidence | L2 | 4 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.ResourceBirthController.Concrete.PreparedPreAuthority.mk | Kernel.ResourceBirthController | evidence | L2 | 11 proof / 7 data fields; layer-1 review pending
Minidregg.Kernel.ResourceBirthPolicyController.Concrete.AcceptedBirth.mk | Kernel.ResourceBirthPolicyController | evidence | L2 | 1 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.ResourceBirthPolicyController.Concrete.DecodedIngress.mk | Kernel.ResourceBirthPolicyController | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ResourceMoneyOperationDomain.CheckedSamples.mk | Kernel.ResourceMoneyOperationDomain | evidence | L2 | 2 proof / 0 data fields; layer-1 review pending
Minidregg.Kernel.ResourceMoneyOperationDomain.Prepared.mk | Kernel.ResourceMoneyOperationDomain | evidence | L2 | 5 proof / 0 data fields; layer-1 review pending
Minidregg.Kernel.ResourceMoneyOperationDomain.SampledFunding.mk | Kernel.ResourceMoneyOperationDomain | evidence | L2 | 4 proof / 0 data fields; layer-1 review pending
Minidregg.Kernel.ResourceMoneyReceiver.Prepared.mk | Kernel.ResourceMoneyReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.ResourceObservationAdmission.Checked.mk | Kernel.ResourceObservationAdmission | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.ResourceObservationAdmission.Prepared.mk | Kernel.ResourceObservationAdmission | evidence | L2 | 9 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.RunComputeBudget.CheckedSteps.mk | Kernel.RunComputeBudget | evidence | L2 | 1 proof / 0 data fields; layer-1 review pending
Minidregg.Kernel.RunComputeBudget.Prepared.mk | Kernel.RunComputeBudget | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.RunComputeBudget.PreparedBook.mk | Kernel.RunComputeBudget | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.RunComputeBudget.PreparedQuota.mk | Kernel.RunComputeBudget | evidence | L2 | 1 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.RunComputeBudgetDomain.LoadedBook.mk | Kernel.RunComputeBudgetDomain | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.RunComputeBudgetDomain.Prepared.mk | Kernel.RunComputeBudgetDomain | evidence | L2 | 0 proof / 4 data fields; layer-1 review pending
Minidregg.Kernel.SeatReceiver.Accepted.mk | Kernel.SeatReceiver | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.SeatReceiver.DecodedIngress.mk | Kernel.SeatReceiver | evidence | L2 | 2 proof / 3 data fields; layer-1 review pending
Minidregg.Kernel.SeatReceiver.Prepared.mk | Kernel.SeatReceiver | evidence | L2 | 5 proof / 6 data fields; layer-1 review pending
Minidregg.Kernel.SeatStore.Decided.mk | Kernel.SeatStore | evidence | L2 | 9 proof / 11 data fields; layer-1 review pending
Minidregg.Kernel.SeatStore.HeldEnd.mk | Kernel.SeatStore | evidence | L2 | 4 proof / 5 data fields; layer-1 review pending
Minidregg.Kernel.SubjectKeyCommitmentAdoption.Accepted.mk | Kernel.SubjectKeyCommitmentAdoption | evidence | L2 | 3 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.SubjectKeyCommitmentAdoption.AcceptedAdoption.mk | Kernel.SubjectKeyCommitmentAdoption | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.SubjectKeyCommitmentAdoption.DecodedIngress.mk | Kernel.SubjectKeyCommitmentAdoption | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.SubjectKeyCommitmentAdoption.Prepared.mk | Kernel.SubjectKeyCommitmentAdoption | evidence | L2 | 4 proof / 1 data fields; layer-1 review pending
Minidregg.Kernel.SubjectKeyRotation.Checked.mk | Kernel.Receivers.SubjectKeyRotation | evidence | L1 Minidregg.Kernel.SubjectKeyRotation.Checked.sound | every gate check is a proof field; sound derives the commitment, succession and freshness via gate_ok_iff
Minidregg.Kernel.SubjectKeyRotation.DecodedIngress.mk | Kernel.Receivers.SubjectKeyRotation | evidence | L2 | 1 proof / 2 data fields; layer-1 review pending
Minidregg.Kernel.SubjectKeyRotation.Prepared.mk | Kernel.Receivers.SubjectKeyRotation | evidence | L1 Minidregg.Kernel.SubjectKeyRotation.Prepared.gated_by_possession | the gate ran under the key of the possession signature it holds; that ReceiverSignature is L2
Minidregg.Kernel.SystemCellDomain.Loaded.mk | Kernel.SystemCellDomain | evidence | L2 | 2 proof / 2 data fields; layer-1 review pending
Minidregg.Theory.CanonicalReactiveView.PreparedReaction.mk | Theory.CanonicalReactiveView | evidence | L2 | 3 proof / 2 data fields; layer-1 review pending
Minidregg.Theory.CellState.Materialized.mk | Theory.CellState | evidence | L2 | 0 proof / 1 data fields; layer-1 review pending; mints: materialize (the root is computed from the logical store by the materializer, not asserted)
Minidregg.Theory.CellState.ValidatedPatch.mk | Theory.CellState | evidence | L2 | 2 proof / 0 data fields; layer-1 review pending
Minidregg.Theory.GuardedAdvice.VerifiedFill.mk | Theory.GuardedAdvice | evidence | L2 | 8 proof / 1 data fields; layer-1 review pending
Minidregg.Theory.ObjectiveBendDemandData.ExecutionWith.mk | Theory.ObjectiveBendDemandData | evidence | L2 | 1 proof / 4 data fields; layer-1 review pending
Minidregg.Theory.ObjectiveBendDemandData.ExtractionWith.mk | Theory.ObjectiveBendDemandData | evidence | L2 | 1 proof / 1 data fields; layer-1 review pending
Minidregg.Theory.ReactiveCellTransition.Accepted.mk | Theory.ReactiveCellTransition | evidence | L2 | 2 proof / 1 data fields; layer-1 review pending
Minidregg.Theory.ReceiptEvent.mk | Theory.AcceptedCellEffect | evidence | L2 | 5 proof / 10 data fields; layer-1 review pending
Minidregg.Theory.Receiving.Receiver.Accepted.mk | Theory.Receiving | evidence | L1 Minidregg.Theory.Receiving.Receiver.Accepted.admits | carries `admits`: prepared under covering vouchers, shape and laws passed; the vouchers are L2
Minidregg.Theory.Receiving.Vouchers.mk | Theory.Receiving | evidence | L2 | the claims the Receiver's verifier answered true on; an oracle (IO) verdict no proof expresses; minted only by Receiver.admitVia; mints: Vouchers.empty (vouches for nothing)
restrict | Minidregg.Compiler.DurableHistory.Head.genesis | Compiler.DurableHistoryStore, Compiler.DurableReceiverIO, Compiler.DurableServed | a genesis head for a non-empty Store is a replay bypass: only the open mints one
restrict | Minidregg.Compiler.DurableHistory.StoreIdentity.ofOpen | Compiler.DurableHistoryStore, Compiler.DurableReceiverIO, Compiler.DurableServed | a Store identity comes only from the open
"

end Minidregg.TokenCensus
