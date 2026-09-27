/- Live event20 registration requires a native-verified, same-walk Mini history.
The lower conditional check alone cannot authorize a registration or select a
legacy predecessor; the private Replay.Verified projection supplies both. -/
import Kernel.FnConsumerNamespaceAdmissionAt
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.FnConsumerNamespaceAdmission

open Minidregg.Kernel
open Minidregg.Kernel.FnConsumerNamespaceRegistration
open Minidregg.Compiler

set_option autoImplicit false

structure AcceptedVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) where
  private mk ::
  namespaceAbsent : verified.frontierRegistrationAbsent
    ingress.spec.consumerNamespace = true
  legacy : Option FnConsumerNamespaceAdmissionAt.Legacy
  legacyExact : verified.frontierLegacyFor ingress.spec = .ok legacy
  lower : FnConsumerNamespaceAdmissionAt.Conditional config verified.opened
    legacy ingress

def admitVerified {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    IO (Except String (AcceptedVerified verified ingress)) := do
  if namespaceAbsent : verified.frontierRegistrationAbsent
      ingress.spec.consumerNamespace = true then
    match legacyExact : verified.frontierLegacyFor ingress.spec with
    | .error _ => return .error "fn consumer registration lineage refused"
    | .ok legacy =>
        match ← FnConsumerNamespaceAdmissionAt.prepareConditional config
            verified.opened legacy ingress with
        | .error reason => return .error reason
        | .ok lower => return .ok ⟨namespaceAbsent, legacy, legacyExact, lower⟩
  else return .error "fn consumer namespace already registered"

def AcceptedVerified.intent {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress)
    (accepted : AcceptedVerified verified ingress) :
    DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes :=
  accepted.lower.intent config verified.opened accepted.legacy ingress

end Minidregg.Kernel.FnConsumerNamespaceAdmission
