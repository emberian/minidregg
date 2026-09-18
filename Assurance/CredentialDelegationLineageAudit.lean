/- Kernel-axiom pins for the actual mixed-lineage checker and its constructive/refusal witnesses. -/
import Assurance.CredentialDelegationLineageWitness

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.capabilityIdFreshCheck_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.capabilityIdFreshCheck_iff

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.delegationShapeCheck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.delegationShapeCheck_iff

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.delegationShapeCheck_refuses_missing_delegate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.delegationShapeCheck_refuses_missing_delegate

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.delegationShapeCheck_refuses_bearer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.delegationShapeCheck_refuses_bearer

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.lineageCheckAux_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.lineageCheckAux_iff

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.LineageAnchored.cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.LineageAnchored.cons

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.LineageAnchored.parent_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.LineageAnchored.parent_exact

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.LineageAnchored.of_present_reads_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.LineageAnchored.of_present_reads_preserved

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.storedLineageCheck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.storedLineageCheck_iff

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.storedLineageCheck_refuses_parent_substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.storedLineageCheck_refuses_parent_substitution

/-- info: 'Minidregg.Theory.CredentialLineageAdmission.storedLineageCheck_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Theory.CredentialLineageAdmission.storedLineageCheck_congr

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.explicit_transfer_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.explicit_transfer_accepted

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.strict_same_holder_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.strict_same_holder_accepted

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.unmarked_transfer_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.unmarked_transfer_refused

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.absent_delegation_permission_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.absent_delegation_permission_refused

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.bearer_transfer_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.bearer_transfer_refused

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.substituted_parent_still_well_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.substituted_parent_still_well_shaped

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.substituted_parent_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.substituted_parent_refused

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.orphaned_transfer_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.orphaned_transfer_refused

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.grantor_rotation_keeps_historical_lineage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.grantor_rotation_keeps_historical_lineage

/-- info: 'Minidregg.Assurance.CredentialDelegationLineageWitness.mixed_lineage_does_not_imply_root_admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.CredentialDelegationLineageWitness.mixed_lineage_does_not_imply_root_admission
