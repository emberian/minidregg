/- Exact axiom pins for shared native source admission and evidence retention. -/
import Compiler.CredentialAuthorityPolicyRegistry

/-- info: 'Minidregg.Compiler.CanonicalPolicyAdmission.admit_preserves_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CanonicalPolicyAdmission.admit_preserves_evidence

/-- info: 'Minidregg.Compiler.CanonicalPolicyAdmission.verifies_policy_generation_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CanonicalPolicyAdmission.verifies_policy_generation_independent

/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.capabilityEvidence_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.capabilityEvidence_success

/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.sourceCapabilityOnlyEvidence_names_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.sourceCapabilityOnlyEvidence_names_parent

/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.capabilityCheck_eq_of_capability_reads_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.capabilityCheck_eq_of_capability_reads_eq

/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.native_use_holder_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.native_use_holder_current

/-- info: 'Minidregg.Compiler.CredentialAuthorityPolicyRegistry.source_capability_only_requires_native_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.CredentialAuthorityPolicyRegistry.source_capability_only_requires_native_request
