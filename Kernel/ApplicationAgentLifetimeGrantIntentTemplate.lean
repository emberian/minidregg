/-
Deterministic event27 intent data from the lower native birth and current app
delegation components. This module has no receive/submit entry point. Its
`template` is not issue authority: the upper Replay admission must also prove
the exact original ticket issue at a verified prefix before durable dispatch.
-/
import Kernel.ApplicationAgentLifetimeGrantAdmission

namespace Minidregg.Kernel.ApplicationAgentLifetimeGrantIntentTemplate
open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ApplicationAgentLifetimeGrantSource
open Minidregg.Kernel.ApplicationAgentLifetimeGrantAdmission
set_option autoImplicit false

variable {F : Type} [Field F] [DecidableEq F]
variable {profile : CanonicalRuntimeProfile.Profile F}
variable {config : NativeHost.Config} {pins : FactoryPins}
variable {durable : ResourceBirthController.Concrete.Durable} {height : Height}
variable {ingress : ApplicationAgentLifetimeGrantSource.Ingress}

def issueNullifier (domain : Digest) (ingress : ApplicationAgentLifetimeGrantSource.Ingress)
    (descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (issueMarker ingress.spec descriptor)

def readGuards (accepted : Accepted profile config pins durable height ingress) :
    List ReadGuard :=
  ResourceBirthReceiver.readGuards accepted.birth ++
    ApplicationAgentLifetimeGrantDelegation.readGuards accepted.appPrepared

theorem readGuards_readonly (accepted : Accepted profile config pins durable height ingress)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.cellId ∉ accepted.birth.prepared.writes.map DataWrite.cellId := by
  rcases List.mem_append.mp member with birth | app
  · exact ResourceBirthReceiver.readGuards_readonly accepted.birth guard birth
  · exact accepted.appReadOnly guard app

theorem readGuards_exact (accepted : Accepted profile config pins durable height ingress)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  rcases List.mem_append.mp member with birth | app
  · exact ResourceBirthReceiver.readGuards_exact accepted.birth guard birth
  · exact accepted.appChecked.guardsCurrent guard app

/-- The writes the issue commits: `finalWrites`, the admitted birth's own; its
naming check ran over exactly these (`Accepted.births_named`). -/
def writes (accepted : Accepted profile config pins durable height ingress) :
    List DataWrite := finalWrites accepted.birth

theorem writes_unique (accepted : Accepted profile config pins durable height ingress) :
    ((writes accepted).map DataWrite.cellId).Nodup :=
  accepted.birth.prepared.writesUnique

theorem compositeGuards_readonly
    (accepted : Accepted profile config pins durable height ingress)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.cellId ∉ (writes accepted).map DataWrite.cellId :=
  readGuards_readonly accepted guard member

theorem composite_roots_bound
    (accepted : Accepted profile config pins durable height ingress)
    (write : DataWrite) (member : write ∈ writes accepted) :
    ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost :=
  accepted.birth.prepared.write_roots_bound write member

/-- Charge: the resource birth's own (its descriptor carries the whole initialized
grant cell, so turn and storage bytes count it), the extra signed app authority
check, the complete outer ingress and the app read guard.  The accepted birth fee
remains the only Book debit. -/
def charge (accepted : Accepted profile config pins durable height ingress) : Charge
  | .incidences => ResourceBirthReceiver.charge accepted.birth .incidences + 1
  | .turnBytes => ResourceBirthReceiver.charge accepted.birth .turnBytes +
      (ingressCodec.encode ingress).length
  | .memoryTouches => ResourceBirthReceiver.charge accepted.birth .memoryTouches + 1
  | .witnessBytes => ResourceBirthReceiver.charge accepted.birth .witnessBytes +
      ingress.appEnvelope.length
  | .proofWork => ResourceBirthReceiver.charge accepted.birth .proofWork + 1
  | .storageBytes => ResourceBirthReceiver.charge accepted.birth .storageBytes +
      (ingressCodec.encode ingress).length
  | .sideEffectCount => ResourceBirthReceiver.charge accepted.birth .sideEffectCount + 1
  | .feeDebit => ResourceBirthReceiver.charge accepted.birth .feeDebit
  | .networkBytes | .leaseByteBlocks => 0

theorem charge_fee_exact (accepted : Accepted profile config pins durable height ingress) :
    charge accepted .feeDebit = accepted.birth.descriptor.fee.amount := rfl

theorem charge_fee_source_quoted (accepted : Accepted profile config pins durable height ingress) :
    charge accepted .feeDebit = accepted.birth.descriptor.quotedFee config.tariff := by
  rw [charge_fee_exact]
  exact accepted.special_fee_bound

/-- The special event and nullifier distinguish this composite issue from an
ordinary resource birth. Both prior-image admissions were checked at the same
`durable`; the app read guard fences its cell root, while the birth's complete
authority guards and the full-image CAS fence current policy/grant state. The
newborn owner/control grants go to the issuer; the participant's bounded
grant-resource-only observe selector is born in the same checked descriptor.
Event26 must still verify its current signature, law and revocation status. -/
def template (accepted : Accepted profile config pins durable height ingress) :
    DataIntent ResourceBirthCodec.rootBytes where
  transactionId := accepted.birth.descriptor.transactionId
  writes := writes accepted
  readGuards := readGuards accepted
  nullifiers := ResourceBirthReceiver.birthNullifier config.deployment.domain
      accepted.birth.descriptor.authorityNullifier ::
    [issueNullifier config.deployment.domain ingress accepted.birth.descriptor]
  exactCharge := charge accepted
  event := ApplicationAgentLifetimeGrantSource.event config.deployment.domain ingress
  subject := some accepted.birth.descriptor.creator
  postRootsBound := composite_roots_bound accepted
  guardsReadOnly := compositeGuards_readonly accepted

/-- **The committed births are named**: every write of the intent that creates
its cell -- the initialized content cell included -- is named by the step the
factory law admitted.  The intent commits exactly `finalWrites`. -/
theorem template_births_named (accepted : Accepted profile config pins durable height ingress) :
    ∀ write ∈ (template accepted).writes, ResourceBirthController.Concrete.bornIn write = true →
      ReceivingLaw.namesBirth accepted.birth.factoryStep write = true :=
  accepted.births_named

#assert_axioms template_births_named

theorem template_event_version (accepted : Accepted profile config pins durable height ingress) :
    (template accepted).event.codecVersion = 27 := rfl

theorem template_retains_outer (accepted : Accepted profile config pins durable height ingress) :
    (template accepted).event.canonicalBytes = ingressCodec.encode ingress := rfl


end Minidregg.Kernel.ApplicationAgentLifetimeGrantIntentTemplate
