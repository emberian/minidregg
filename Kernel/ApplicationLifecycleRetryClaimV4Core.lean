/- One-use current retry CLAIM. The versioned BEGIN and admitted failed
recovery are reselected at their exact prefixes; legacy first-attempt and
created-volume markers remain unchanged. Native replay supplies both same-walk
provenance obligations before receiving this conditional intent. -/
import Kernel.ApplicationLifecycleRetryClaimV4Ingress
import Kernel.ApplicationLifecycleRetryBeginV4Admission

namespace Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Core

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

open Minidregg.Compiler.ServedBasis (Ground Grounded)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (Reader)

structure Conditional (config : Config) {store : StoreIdentity} (head : Head store)
    (ground : Ground config.deployment) (ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress) where
  private mk ::
  original : NativeHistorySelection.Candidate config head ingress.base.source.originalIndex
  originalAccepted : ApplicationLifecycleRetryBeginV4Admission.Accepted config head original.ground
    ingress.originalBegin
  originalMatch : NativeHistorySelection.Matched original originalAccepted.intent
  current : ApplicationLifecycleClaimCurrent.Accepted config.deployment config.profile
    ⟨config.federation, config.genesisHeight + ground.height⟩ ground ingress.base
  exact : ingress.originalExact = true
  installed : ApplicationLifecycleBeginV3Admission.installedExact config.deployment
    ingress.originalBegin.begin current.packageRead.selected.observed.before = true
  markers : ApplicationFailedCreateRetryEvidence.markersCurrent config ground
    ingress.originalBegin.retry = true

/-- Every key the current part of a retry claim reads: the claim's and the retry markers'. -/
def keys (ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress) : DurableView.Keys :=
  let current := ApplicationLifecycleClaimCurrent.keys ingress.base
  let retry := ApplicationFailedCreateRetryEvidence.keys ingress.originalBegin.retry
  ⟨current.transactions ++ retry.transactions, current.nullifiers ++ retry.nullifiers⟩

def prepare (config : Config) {store : StoreIdentity}
    (reader : Reader ResourceBirthCodec.rootBytes store)
    (grounded : Grounded config.deployment reader.head)
    (ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress) :
    IO (Except String (Conditional config reader.head grounded.ground ingress)) := do
  let ground := grounded.ground
  if exact : ingress.originalExact = true then
    let original ← match ← NativeHistorySelection.select config reader ground.height
        ingress.base.source.originalIndex
        (ApplicationLifecycleRetryBeginV4Admission.keys ingress.originalBegin) with
      | .error detail => return .error detail
      | .ok original => pure original
    let originalAccepted ← match ← ApplicationLifecycleRetryBeginV4Admission.admitNative
        config reader original.grounded ingress.originalBegin with
      | .error detail => return .error detail
      | .ok originalAccepted => pure originalAccepted
    let originalMatch ← match NativeHistorySelection.matchIntent original
        originalAccepted.intent with
      | .error detail => return .error detail
      | .ok matched => pure matched
    let current ← match ← ApplicationLifecycleClaimCurrent.admitLoaded
        config.deployment config.profile
        ⟨config.federation, config.genesisHeight + ground.height⟩
        config.signature ground ingress.base with
      | .error detail => return .error detail
      | .ok current => pure current
    if installed : ApplicationLifecycleBeginV3Admission.installedExact config.deployment
        ingress.originalBegin.begin current.packageRead.selected.observed.before = true then
      if markers : ApplicationFailedCreateRetryEvidence.markersCurrent config ground
          ingress.originalBegin.retry = true then
        return .ok ⟨original, originalAccepted, originalMatch, current, exact, installed, markers⟩
      else return .error "retry CLAIM first/created/recovery/one-use token markers refuse"
    else return .error "retry CLAIM current package differs from exact retry descriptor"
  else return .error "retry CLAIM full original versioned BEGIN projection differs"

def event
    (ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress) : StableEvent where
  codecVersion := 70
  domain := ingress.base.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/RETRY-CREATE-CLAIM-EVENT/v4".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

def Conditional.intent {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress}
    (conditional : Conditional config head ground ingress) :
    DataIntent rootBytes :=
  let ordinary := ApplicationLifecycleClaimCore.intentFromCurrent conditional.current
    (event ingress) ingress.canonicalBytes.length
  let marker := ingress.retryToken
  { ordinary with
    nullifiers := ordinary.nullifiers ++ [marker]
    exactCharge := fun dimension => match dimension with
      | .storageBytes => ordinary.exactCharge .storageBytes + marker.canonicalBytes.length
      | other => ordinary.exactCharge other }

theorem Conditional.intent_consumes_retry {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress}
    (conditional : Conditional config head ground ingress) :
    ingress.retryToken ∈ conditional.intent.nullifiers := by
  simp [Conditional.intent]

theorem Conditional.intent_writes {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress}
    (conditional : Conditional config head ground ingress) :
    conditional.intent.writes =
      (ApplicationLifecycleClaimCore.intentFromCurrent conditional.current
        (event ingress) ingress.canonicalBytes.length).writes := rfl

end Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Core
