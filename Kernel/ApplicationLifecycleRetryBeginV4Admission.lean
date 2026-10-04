/- Explicit repeat authority for retry BEGIN. This gate retains the old DRC
current-management and package checks and adds full failed-recovery evidence.
Native replay must also prove that the original claim belongs to its same
chronological walk; this conditional layer exposes no receiving operation. -/
import Kernel.ApplicationLifecycleRetryBeginV4Ingress

namespace Minidregg.Kernel.ApplicationLifecycleRetryBeginV4Admission

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Accepted (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleRetryBeginV4Ingress.Ingress) where
  private mk ::
  base : ApplicationLifecycleBeginReceiver.Accepted config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress.begin.base
  shape : ingress.shape = true
  installed : ApplicationLifecycleBeginV3Admission.installedExact config.deployment
    ingress.begin base.selected.observed.before = true
  evidence : ApplicationFailedCreateRetryEvidence.Conditional config opened
    ingress.retry ingress.begin

def admitNative (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleRetryBeginV4Ingress.Ingress) :
    IO (Except String (Accepted config opened ingress)) := do
  let base ← match ← ApplicationLifecycleBeginReceiver.admitLoaded
      config.deployment config.profile
      ⟨config.federation, logicalHeight config opened.durable⟩
      config.signature opened.durable ingress.begin.base with
    | .error detail => return .error detail
    | .ok base => pure base
  if shape : ingress.shape = true then
    if installed : ApplicationLifecycleBeginV3Admission.installedExact config.deployment
        ingress.begin base.selected.observed.before = true then
      let evidence ← match ← ApplicationFailedCreateRetryEvidence.prepare
          config opened ingress.retry ingress.begin with
        | .error detail => return .error detail
        | .ok evidence => pure evidence
      return .ok ⟨base, shape, installed, evidence⟩
    else return .error "retry BEGIN current installed package differs from exact failed create"
  else return .error "retry BEGIN nonce/descriptor/recovery selection refused"

/-- Registry-reserved source event69. No client frame selects the event family.
Native replay supplies the chronological gate before any receiving action. -/
def event
    (ingress : ApplicationLifecycleRetryBeginV4Ingress.Ingress) : StableEvent where
  codecVersion := 69
  domain := ingress.begin.base.domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/RETRY-CREATE-BEGIN-EVENT/v4".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

def Accepted.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleRetryBeginV4Ingress.Ingress}
    (accepted : Accepted config opened ingress) : DataIntent rootBytes :=
  let legacy := accepted.base.intent
  let ordinary := accepted.base.invocation.dataIntent accepted.base.shape
  { legacy with
    exactCharge := fun dimension => match dimension with
      | .turnBytes => ingress.canonicalBytes.length
      | .witnessBytes => ingress.canonicalBytes.length
      | .storageBytes => ordinary.exactCharge .storageBytes + ingress.canonicalBytes.length +
          (ApplicationLifecycleBegin.stableNullifier config.deployment.domain
            config.profile.semantics ingress.begin.base.source).canonicalBytes.length
      | other => legacy.exactCharge other
    event := event ingress }

theorem Accepted.intent_no_retry_consumption {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleRetryBeginV4Ingress.Ingress}
    (accepted : Accepted config opened ingress) :
    accepted.intent.nullifiers = accepted.base.intent.nullifiers := rfl

theorem Accepted.intent_writes {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleRetryBeginV4Ingress.Ingress}
    (accepted : Accepted config opened ingress) :
    accepted.intent.writes = accepted.base.intent.writes := rfl

end Minidregg.Kernel.ApplicationLifecycleRetryBeginV4Admission
