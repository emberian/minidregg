import Kernel.NativeJointAgreement

/- This gate audits named general claims. It is not a build/deployment or
cryptographic-finality claim; no closed-case #guard replaces a theorem. -/
#print axioms Minidregg.Kernel.JointInvocationCandidate.candidate_encode_injective
#print axioms Minidregg.Kernel.JointInvocationCandidate.admitted_guard_in_footprint
#print axioms Minidregg.Kernel.JointDecisionRecovery.commit_abort_exclusive
#print axioms Minidregg.Kernel.JointDecisionRecovery.decideVote_preserves_decided
#print axioms Minidregg.Kernel.JointDecisionRecovery.no_survives_late_yes
#print axioms Minidregg.Kernel.JointDecisionRecovery.decideVote_final_yes_requires_others
#print axioms Minidregg.Kernel.JointDecisionRecovery.handoff_retains_liabilities
#print axioms Minidregg.Kernel.NativeJointAgreement.replay_append
#print axioms Minidregg.Kernel.NativeJointAgreement.restore_wrong_candidate
#print axioms Minidregg.Kernel.NativeJointAgreement.disabled_cannot_vote
#print axioms Minidregg.Kernel.NativeJointAgreement.vote_once

#print axioms Minidregg.Kernel.JointReservation.allowed_compatible
#print axioms Minidregg.Kernel.JointReservation.allowed_funded
#print axioms Minidregg.Kernel.JointReservation.compatible_install_preserves_bytes
#print axioms Minidregg.Kernel.JointReservation.compatible_install_preserves_root

#print axioms Minidregg.Kernel.JointDecisionRecovery.Trace.preserves_decided
#print axioms Minidregg.Kernel.JointDecisionRecovery.abort_stable_under_trace

#print axioms Minidregg.Kernel.NativeJointAgreement.journal_encode_injective
