/-
# Assurance.Deployed -- Aggregated deployed assurance frontier

Imports and binds the deployed certifying-checker and wire/store codec assurance modules:
- `Assurance.DeployedCredentialLifecycle` (`StoreCodec` authority cell lifecycle)
- `Assurance.DeployedReceiptOpening` (`op 151` `worldReceiptProof` / `ReceiptContinuity` wire codec & `opens_sound` bridge)
- `Assurance.DeployedCertifyingSolvers` (`CertifiedClearing` `Cert-F` + `SeatStore.decodeAction` & `Pred.hashEq` `cSHAKE256("DREGG.PRED.HASHEQ/v2")` soundness)
-/
import Assurance.DeployedCredentialLifecycle
import Assurance.DeployedReceiptOpening
import Assurance.DeployedCertifyingSolvers
import Theory.AssertAxioms

namespace Minidregg.Assurance.Deployed

open Minidregg.Assurance.DeployedCredentialLifecycle
open Minidregg.Assurance.DeployedReceiptOpening
open Minidregg.Assurance.DeployedCertifyingSolvers

set_option autoImplicit false

/-- Combined computable audit for `op 151` receipt-continuity opening and the certifying
solvers (`CertifiedClearing` `Cert-F` + `Pred.hashEq`). -/
def checkDeployedAssurance : Bool :=
  checkReceiptOpeningBridge && checkCertifyingSolversAudit

#guard checkReceiptOpeningBridge = true
#guard checkCertifyingSolversAudit = true
#guard checkDeployedAssurance = true

/-- Combined theorem witness referencing the deployed store/wire codecs, `op 151` opening
soundness, `Cert-F` clearing soundness, and `Pred.hashEq` binding/rejection. -/
theorem deployedAssuranceFrontier :
    (∀ n, Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.nat.toLawful.decode
      (Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.encodeNat n) = some n) ∧
    (∀ rec, openingRecordCodec.decode (openingRecordCodec.encode rec) = some rec) ∧
    (∀ env, continuityEnvelopeCodec.decode (continuityEnvelopeCodec.encode env) = some env) ∧
    Minidregg.Pred.HashEqDigest.deployed =
      Minidregg.Compiler.Sp800185Cshake256.cshake256Bytes
        Minidregg.Pred.HashEqDigest.customization :=
  ⟨encodeNat_roundtrip,
   openingRecordCodec_roundtrip,
   continuityEnvelopeCodec_roundtrip,
   Minidregg.Pred.HashEqDigest.deployed_eq_cshake256Bytes⟩

#assert_axioms deployedAssuranceFrontier
#assert_axioms Minidregg.Assurance.DeployedReceiptOpening.wireOpening_sound
#assert_axioms Minidregg.Assurance.DeployedReceiptOpening.wireContinuity_verify_sound
#assert_axioms Minidregg.Assurance.DeployedReceiptOpening.wireContinuity_known_binds_chain
#assert_axioms Minidregg.Assurance.DeployedCertifyingSolvers.decodeAction_clear_inferred
#assert_axioms Minidregg.Assurance.DeployedCertifyingSolvers.verifyClearing_sound
#assert_axioms Minidregg.Assurance.DeployedCertifyingSolvers.decoded_clear_action_sound
#assert_axioms Minidregg.Assurance.DeployedCertifyingSolvers.hashEq_rejects_mismatched_digest
#assert_axioms Minidregg.Assurance.DeployedCertifyingSolvers.hashEq_concrete_binding

/-- info: 'Minidregg.Assurance.Deployed.deployedAssuranceFrontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployedAssuranceFrontier

end Minidregg.Assurance.Deployed
