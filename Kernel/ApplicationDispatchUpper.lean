/-
Live native join of a verifier-selected original app share issue and one
current-image dispatch. The accepted value retains the exact historical issue
index, complete original intent proof, current native DRC/observations, and
full outer wrapper binding. It has no CAS or host delivery permit yet: Replay
must admit the special event using its private chronological issue context,
and the physical receiver must obtain exact post-CAS readback.
-/
import Kernel.ApplicationShareIssueHistorical
import Kernel.ApplicationDispatchHistoricalCore

namespace Minidregg.Kernel.ApplicationDispatchUpper

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationDispatchHistoricalCore

set_option autoImplicit false

/-- Translate only the verifier-selected original issue admission into the
cycle-safe source evidence. The exact record equality comes from the same
selected native replay walk and its complete IntentRecord comparison. -/
def issueEvidence {config : Config} {target : Durable} {index : Nat}
    (issued : ApplicationShareIssueHistorical.Issued config target index) :
    IssuedEvidence config :=
  issued.toEvidence

/-- The constructor is private; this is still only an *admitted pending
candidate*. It is not an external delivery permit until durable exact readback
and a Replay-native special event branch confirm its commitment. -/
structure Accepted (config : Config) (target : Durable)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) where
  private mk ::
  index : Nat
  issued : ApplicationShareIssueHistorical.Issued config target index
  current : CheckedCandidate config target ingress (issueEvidence issued)

/-- `issueIndex` is a selector, not authority. `select` verifies the entire
physical current image, re-admits the original composite issue at the actual
original prefix, and compares the complete original record. Current dispatch
admission separately checks all present grants, roots, law, permissions,
principal and request bytes. -/
def admit (config : Config) (target : Durable) (issueIndex : Nat)
    (bytes : List UInt8) : IO (Except String
      (Σ ingress : ApplicationDispatchAdmissionIngress.Ingress,
        Accepted config target ingress)) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | return .error "noncanonical special dispatch ingress"
  let .ok issued ← ApplicationShareIssueHistorical.select config target issueIndex
    | return .error "verified share issue unavailable"
  let .ok current ← ApplicationDispatchHistoricalCore.checkCurrent config target ingress
      (issueEvidence issued)
    | return .error "current dispatch authority or issue binding refused"
  return .ok ⟨ingress, ⟨issueIndex, issued, current⟩⟩

/-- A source-derived candidate to hand to the special durable receiver. A
caller may not submit this to a generic DRC route and call that a permit. -/
def Accepted.pendingIntent {config : Config} {target : Durable}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (accepted : Accepted config target ingress) : DurableDataIntent.DataIntent rootBytes :=
  ApplicationDispatchPending.candidateIntent accepted.current.checked

end Minidregg.Kernel.ApplicationDispatchUpper
