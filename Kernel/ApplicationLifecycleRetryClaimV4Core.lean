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

structure Conditional (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress) where
  private mk ::
  original : NativeHistorySelection.Candidate config opened ingress.base.source.originalIndex
  originalAccepted : ApplicationLifecycleRetryBeginV4Admission.Accepted config original.prior
    ingress.originalBegin
  originalMatch : NativeHistorySelection.Matched original originalAccepted.intent
  current : ApplicationLifecycleClaimCurrent.Accepted config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress.base
  exact : ingress.originalExact = true
  installed : ApplicationLifecycleBeginV3Admission.installedExact config.deployment
    ingress.originalBegin.begin current.packageRead.selected.observed.before = true
  markers : ApplicationFailedCreateRetryEvidence.markersCurrent config opened
    ingress.originalBegin.retry = true

def prepare (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress) :
    IO (Except String (Conditional config opened ingress)) := do
  if exact : ingress.originalExact = true then
    let original ← match NativeHistorySelection.select config opened
        ingress.base.source.originalIndex with
      | .error detail => return .error detail
      | .ok original => pure original
    let originalAccepted ← match ← ApplicationLifecycleRetryBeginV4Admission.admitNative
        config original.prior ingress.originalBegin with
      | .error detail => return .error detail
      | .ok originalAccepted => pure originalAccepted
    let originalMatch ← match NativeHistorySelection.matchIntent original
        originalAccepted.intent with
      | .error detail => return .error detail
      | .ok matched => pure matched
    let current ← match ← ApplicationLifecycleClaimCurrent.admitLoaded
        config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩
        config.signature opened.durable ingress.base with
      | .error detail => return .error detail
      | .ok current => pure current
    if installed : ApplicationLifecycleBeginV3Admission.installedExact config.deployment
        ingress.originalBegin.begin current.packageRead.selected.observed.before = true then
      if markers : ApplicationFailedCreateRetryEvidence.markersCurrent config opened
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

def Conditional.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress}
    (conditional : Conditional config opened ingress) :
    DataIntent rootBytes :=
  let ordinary := ApplicationLifecycleClaimCore.intentFromCurrent conditional.current
    (event ingress) ingress.canonicalBytes.length
  let marker := ingress.retryToken
  { ordinary with
    nullifiers := ordinary.nullifiers ++ [marker]
    exactCharge := fun dimension => match dimension with
      | .storageBytes => ordinary.exactCharge .storageBytes + marker.canonicalBytes.length
      | other => ordinary.exactCharge other }

theorem Conditional.intent_consumes_retry {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress}
    (conditional : Conditional config opened ingress) :
    ingress.retryToken ∈ conditional.intent.nullifiers := by
  simp [Conditional.intent]

theorem Conditional.intent_writes {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress}
    (conditional : Conditional config opened ingress) :
    conditional.intent.writes =
      (ApplicationLifecycleClaimCore.intentFromCurrent conditional.current
        (event ingress) ingress.canonicalBytes.length).writes := rfl

end Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Core
