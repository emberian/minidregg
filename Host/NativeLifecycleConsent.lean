/- Full-peer consent adapters for independently retained specialized requests.
The request is local custody's input, never decoded from a remote plan. Each
branch runs the real current-source authoring route and returns its complete
canonical plan; the session compares all bytes before exposing any headers. -/
import Kernel.NativeHostReplay
import Kernel.ApplicationShareIssueAuthoring
import Kernel.ApplicationDispatchAuthoring
import Kernel.ApplicationDispatchAgentPaidAuthoring
import Kernel.ApplicationAgentLifetimeDispatchPaidAuthoring
import Host.ApplicationAgentLifetimeGrantAuthoring
import Host.ApplicationGrainSessionEnrollmentAuthoring
import Host.NativeReserveBirthAuthoring
import Host.ApplicationLifecycleCompletionOperator
import Host.ApplicationLifecycleClaimOperator
import Host.ApplicationLifecycleLaunchBeginAuthoring
import Host.ApplicationLifecycleLaunchClaimAuthoring
import Host.ApplicationLifecycleLaunchCompletionAuthoring
import Host.ApplicationFailedStartRecoveryAuthoring
import Host.SourceAgreementJson
import Compiler.FnEvidenceCodec

namespace Minidregg.Host.NativeLifecycleConsent
open Minidregg.Compiler Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel Minidregg.Host
set_option autoImplicit false

def supported (operation : UInt8) : Bool :=
  [32, 36, 48, 58, 74, 78, 80, 82, 201].contains operation

/-- Operator configuration may further restrict a request. It cannot supply
consent: paid/reserve fixed selectors are retained in the exact LOCAL request.
Current-source planners still select every authority root, generation and role. -/
def expectedPlanBytes (config : NativeHost.Config) {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (operation : UInt8)
    (request : List UInt8) : IO (List UInt8) := do
  unless request.length ≤ FnEvidenceCodec.maxHostFrameBytes do
    throw (IO.userError "local specialized request exceeds native frame bound")
  let bytes ← match operation with
    | 32 => do
      let plan ← IO.ofExcept (ApplicationShareIssueAuthoring.prepareRequestLoaded
        config verified.opened request)
      pure (ApplicationShareIssueAuthoring.planCodec.encode plan)
    | 36 => do
      let plan ← IO.ofExcept (ApplicationDispatchAuthoring.prepareRequestVerified
        config verified request)
      pure (ApplicationDispatchAuthoring.planCodec.encode plan)
    | 48 => do
      let some authored := ApplicationDispatchAgentPaidAuthoring.paidRequestCodec.decode request
        | throw (IO.userError "noncanonical local paid-agent request")
      let plan ← IO.ofExcept (ApplicationDispatchAgentPaidAuthoring.preparePaidVerified
        config verified authored)
      pure (ApplicationDispatchAgentPaidAuthoring.paidPlanCodec.encode plan)
    | 58 => do
      let some authored := ApplicationDispatchAgentPaidAuthoring.requestCodec.decode request
        | throw (IO.userError "noncanonical local agent-reserve request")
      let plan ← IO.ofExcept (ApplicationDispatchAgentPaidAuthoring.prepareReserveVerified
        config verified authored)
      pure (ApplicationDispatchAgentPaidAuthoring.reservePlanCodec.encode plan)
    | 74 => do
      let plan ← IO.ofExcept (ApplicationAgentLifetimeGrantAuthoring.prepareRequestLoaded
        verified request)
      pure (ApplicationAgentLifetimeGrantAuthoring.planCodec.encode plan)
    | 78 => do
      let some authored := ApplicationAgentLifetimeDispatchPaidAuthoring.paidRequestCodec.decode request
        | throw (IO.userError "noncanonical local lifetime-paid request")
      let plan ← IO.ofExcept (ApplicationAgentLifetimeDispatchPaidAuthoring.preparePaidVerified
        config verified authored)
      pure (ApplicationAgentLifetimeDispatchPaidAuthoring.paidPlanCodec.encode plan)
    | 80 => do
      let some authored := ApplicationAgentLifetimeDispatchPaidAuthoring.requestCodec.decode request
        | throw (IO.userError "noncanonical local lifetime-reserve request")
      let plan ← IO.ofExcept (ApplicationAgentLifetimeDispatchPaidAuthoring.prepareReserveVerified
        config verified authored)
      pure (ApplicationAgentLifetimeDispatchPaidAuthoring.reservePlanCodec.encode plan)
    | 82 => do
      let plan ← IO.ofExcept (ApplicationGrainSessionEnrollmentAuthoring.prepareRequestVerified
        config verified request)
      pure (ApplicationGrainSessionEnrollmentAuthoring.planCodec.encode plan)
    | 201 => IO.ofExcept (← NativeReserveBirthAuthoring.authorWireLoaded
        config verified.opened request)
    | _ => throw (IO.userError "unsupported local lifecycle consent operation")
  unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
    throw (IO.userError "local specialized plan exceeds native frame bound")
  pure bytes

/-- These identities come from custody's local settings, not the plan body. -/
structure Management where
  subject : Nat
  keyId : Nat

structure Selector where
  app : Nat
  packageManifest : Nat
  snapshotManifest : Nat
  appCapability : Nat
  appObserveCapability : Nat
  packageCapability : Nat
  packageObserveCapability : Nat

instance : Lean.FromJson Selector where
  fromJson? json := do
    let object ← json.getObj?
    let expected := ["app", "packageManifest", "snapshotManifest", "appCapability",
      "appObserveCapability", "packageCapability", "packageObserveCapability"]
    let actual := object.foldl (init := []) (fun fields key _ => key :: fields)
    unless actual.length == expected.length && actual.all expected.contains do
      throw "local lifecycle selector has missing or unknown fields"
    let field := fun (name : String) => do
      let text ← json.getObjValAs? String name
      unless !text.isEmpty && text.length ≤ 78 &&
          !(text.length > 1 && text.front == '0') && text.all Char.isDigit do
        throw s!"local lifecycle selector {name} is not canonical decimal"
      let some value := text.toNat? | throw "invalid local lifecycle selector"
      pure value
    return ⟨← field "app", ← field "packageManifest", ← field "snapshotManifest",
      ← field "appCapability", ← field "appObserveCapability",
      ← field "packageCapability", ← field "packageObserveCapability"⟩

def splitRequest (bytes : List UInt8) : IO (Selector × List UInt8) := do
  unless bytes.length ≥ 4 do throw (IO.userError "short local lifecycle pair")
  let width := bytes[0]!.toNat + 256 * bytes[1]!.toNat +
    65536 * bytes[2]!.toNat + 16777216 * bytes[3]!.toNat
  unless width > 0 && width ≤ 4096 && width ≤ bytes.length - 4 do
    throw (IO.userError "invalid local lifecycle selector length")
  let some source := String.fromUTF8? ((bytes.drop 4).take width).toByteArray
    | throw (IO.userError "local lifecycle selector is not UTF-8")
  let json ← IO.ofExcept (SourceAgreementJson.parse source)
  let selector : Selector ← IO.ofExcept (Lean.fromJson? json)
  pure (selector, bytes.drop (4 + width))

def Selector.beginPin (s : Selector) (m : Management) : ApplicationLifecycleBeginOperator.Pin :=
  ⟨s.app, s.packageManifest, s.snapshotManifest, m.subject, m.keyId,
    ⟨s.appCapability⟩, ⟨s.packageObserveCapability⟩⟩

def Selector.claimPin (s : Selector) (m : Management) : ApplicationLifecycleClaimOperator.Pin :=
  { app := s.app, packageManifest := s.packageManifest,
    managementSubject := m.subject, managementKeyId := m.keyId,
    appCapability := ⟨s.appCapability⟩, appObserveCapability := ⟨s.appObserveCapability⟩,
    packageObserveCapability := ⟨s.packageObserveCapability⟩ }

def Selector.completionPin (s : Selector) (m : Management) : ApplicationLifecycleCompletionOperator.Pin :=
  { app := s.app, packageManifest := s.packageManifest,
    managementSubject := m.subject, managementKeyId := m.keyId,
    appCapability := ⟨s.appCapability⟩, appObserveCapability := ⟨s.appObserveCapability⟩,
    packageCapability := ⟨s.packageCapability⟩,
    packageObserveCapability := ⟨s.packageObserveCapability⟩ }

def managedSupported (operation : UInt8) : Bool :=
  [44, 50, 52, 66, 68, 70, 206].contains operation

/-- Same source planners as native Host.Main, with independently retained
selectors and local management identity. Recovery verifies the genuine signed
custodian report and original admitted BEGIN/claim; this does not mint a report. -/
def expectedManagedPlanBytes (config : NativeHost.Config) {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target)
    (managementSubject managementKeyId : Nat) (operation : UInt8)
    (request : List UInt8) : IO (List UInt8) := do
  unless request.length ≤ FnEvidenceCodec.maxHostFrameBytes do
    throw (IO.userError "local managed request exceeds native frame bound")
  let (selector, payload) ← splitRequest request
  let management : Management := ⟨managementSubject, managementKeyId⟩
  let bytes ← match operation with
    | 44 => do
      let plan ← IO.ofExcept (← ApplicationLifecycleCompletionOperator.prepareRequestVerified
        config verified (selector.completionPin management) payload)
      pure (ApplicationLifecycleCompletionOperator.planCodec.encode plan)
    | 50 => do
      let plan ← IO.ofExcept (ApplicationLifecycleBeginOperator.prepareRequestVerified
        config verified (selector.beginPin management) payload)
      pure (ApplicationLifecycleBeginOperator.planCodec.encode plan)
    | 52 => do
      let plan ← IO.ofExcept (ApplicationLifecycleClaimOperator.prepareRequestVerified
        config verified (selector.claimPin management) payload)
      pure (ApplicationLifecycleClaimOperator.planCodec.encode plan)
    | 66 => do
      let pin := selector.beginPin management
      if let some authored := ApplicationLifecycleLaunchBeginAuthoring.requestCodec.decode payload then
        if authored.kind == .stop then do
          let plan ← IO.ofExcept (ApplicationLifecycleLaunchBeginAuthoring.prepareStopRequestVerified
            config verified pin payload)
          pure (ApplicationLifecycleLaunchBeginAuthoring.stopPlanCodec.encode plan)
        else do
          let plan ← IO.ofExcept (ApplicationLifecycleLaunchBeginAuthoring.prepareVerified
            config verified pin authored)
          pure (ApplicationLifecycleLaunchBeginAuthoring.planCodec.encode plan)
      else do
        let plan ← IO.ofExcept (← ApplicationLifecycleLaunchBeginAuthoring.prepareContinueRequestVerified
          config verified pin payload)
        pure (ApplicationLifecycleLaunchBeginAuthoring.planCodec.encode plan)
    | 68 => do
      let plan ← IO.ofExcept (ApplicationLifecycleLaunchClaimAuthoring.prepareRequestVerified
        config verified (selector.claimPin management) payload)
      pure (ApplicationLifecycleLaunchClaimAuthoring.planCodec.encode plan)
    | 70 => do
      let plan ← IO.ofExcept (← ApplicationLifecycleLaunchCompletionAuthoring.prepareRequestVerified
        config verified (selector.completionPin management) payload)
      pure (ApplicationLifecycleLaunchCompletionAuthoring.planCodec.encode plan)
    | 206 => do
      let plan ← IO.ofExcept (← ApplicationFailedStartRecoveryAuthoring.prepareRequestVerified
        config verified (selector.completionPin management) payload)
      pure (ApplicationFailedStartRecoveryAuthoring.planCodec.encode plan)
    | _ => throw (IO.userError "unsupported local managed consent operation")
  unless bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
    throw (IO.userError "local managed plan exceeds native frame bound")
  pure bytes

end Minidregg.Host.NativeLifecycleConsent
