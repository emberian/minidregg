/-
Exact axiom pins for the generation/revision and explicit-delegation foundation.
These check the named live declarations. They do not assert deployment, native
signature provenance, an available receiver, or a complete umbrella build.
-/
import Theory.CredentialAuthorityEffects

/-- info: 'Minidregg.Theory.CredentialAuthorityFamily.DelegationShape.recipient_is_subject' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityFamily.DelegationShape.recipient_is_subject

/-- info: 'Minidregg.Theory.CredentialAuthorityFamily.DelegationShape.requires_delegate_verb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityFamily.DelegationShape.requires_delegate_verb

/-- info: 'Minidregg.Theory.CredentialAuthorityFamily.DelegationShape.no_other_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityFamily.DelegationShape.no_other_target

/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.LineageBounds.refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Capability.LineageBounds.refl

/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.LineageBounds.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Capability.LineageBounds.trans

/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.Attenuates.lineageBounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Capability.Attenuates.lineageBounds

/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.Lineage.root_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Capability.Lineage.root_bounds

/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.Lineage.root_admissible_of_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Capability.Lineage.root_admissible_of_strict

/-- info: 'Minidregg.Theory.CredentialAuthorityState.LineageValid.root_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityState.LineageValid.root_bounds

/-- info: 'Minidregg.Theory.CredentialAuthorityState.LineageValid.nonempty_lineage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityState.LineageValid.nonempty_lineage

/-- info: 'Minidregg.Theory.CredentialAuthorityState.LineageValid.root_admissible_of_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityState.LineageValid.root_admissible_of_strict

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.IssueEvidence.reject_existing_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.IssueEvidence.reject_existing_id

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DescentEvidence.reject_existing_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DescentEvidence.reject_existing_child

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DescentEvidence.reject_spent_nullifier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DescentEvidence.reject_spent_nullifier

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.capabilityProduction_preserves_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.capabilityProduction_preserves_present

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.AttenuateEvidence.childLineageAnchored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.AttenuateEvidence.childLineageAnchored

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.childLineageValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.childLineageValid

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.childLineageAnchored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.childLineageAnchored

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.acceptDelegation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.acceptDelegation

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.parent_use_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.parent_use_verified

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.parent_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.parent_exact

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.child_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.child_bounds

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_missing_delegate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_missing_delegate

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_non_capability_mode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_non_capability_mode

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_wrong_parent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_wrong_parent

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_wrong_grantor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_wrong_grantor

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_bearer_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.DelegationEvidence.reject_bearer_child

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.delegation_post_capability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.delegation_post_capability_exact

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.delegation_post_nullifier_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.delegation_post_nullifier_exact

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.delegation_post_lineage_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.delegation_post_lineage_valid

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.issue_post_lineage_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.issue_post_lineage_valid

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.attenuation_post_lineage_anchored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.attenuation_post_lineage_anchored

/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.Admissible.at_policy_revision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Capability.Admissible.at_policy_revision

/-- info: 'Minidregg.Theory.TypedAuthorization.wrong_policy_revision_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.wrong_policy_revision_rejected

/-- info: 'Minidregg.Theory.TypedAuthorization.Authorized.current_policy_address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Authorized.current_policy_address

/-- info: 'Minidregg.Theory.TypedAuthorization.demo_generation_revision_independent' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.demo_generation_revision_independent

/-- info: 'Minidregg.Theory.TypedAuthorization.demo_existing_grant_survives_source_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.demo_existing_grant_survives_source_update

/-- info: 'Minidregg.Theory.TypedAuthorization.demo_stale_revision_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.demo_stale_revision_rejected

/-- info: 'Minidregg.Theory.TypedAuthorization.demo_explicit_generation_rotation_revokes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.demo_explicit_generation_rotation_revokes

/-- info: 'Minidregg.Theory.AuthorizationDeclaration.verify_wrong_policy_revision_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.AuthorizationDeclaration.verify_wrong_policy_revision_rejected

/-- info: 'Minidregg.Theory.AuthorizationDeclaration.declaration_requestFields_length' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.AuthorizationDeclaration.declaration_requestFields_length

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.RotateEpochDeclaration.source_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.RotateEpochDeclaration.source_framed

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.rotation_joint_post_source_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.rotation_joint_post_source_framed

/-- info: 'Minidregg.Theory.CredentialAuthorityEffects.rotation_post_source_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.CredentialAuthorityEffects.rotation_post_source_framed

