/- Restart consumer for source-owned Activity publication. Historical origin is
obtained from one actual verified native history selection, re-admitted at its
original prefix, and matched to the full retained record. A decoded pending
checkpoint alone is never accepted as provenance. This high-level module stays
above NativeHostReplay; its low event64 constructors live below that replay.
-/
import Kernel.NativeHostReplay
import Kernel.BendActivityOutcome

namespace Minidregg.Kernel.BendActivityRecovery
open Minidregg.Compiler
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

structure Recovered (config : Config) (target : DeclaredResourceController.Durable)
    (action : BendActivityDispatch.Action) where
  selection : NativeHostReplay.VerifiedSelection config target action.pendingIndex
  origin : BendActivityDispatch.Origin config selection.verified.opened action

/-- Actual source replay first; native pending re-admission then uses that exact
original-height prefix, including its then-current laws, grants and keys. -/
def recover (config : Config) (target : DeclaredResourceController.Durable)
    (action : BendActivityDispatch.Action) : IO (Except String (Recovered config target action)) := do
  let .ok selection ← NativeHostReplay.verifyLoadedSelected config target action.pendingIndex
    | return .error "Activity historical source verification refused"
  let .ok pending ← BendActivityPendingAdmission.admit config selection.selected.before action.pendingSource true
    | return .error "Activity original pending source admission refused"
  let some origin := BendActivityDispatch.bindOrigin selection.verified.opened action
      selection.selected.before pending
    | return .error "Activity pending record differs from verified history"
  return .ok ⟨selection,origin⟩

inductive Result (config : Config) (action : BendActivityDispatch.Action) where
  | refused (reason : String)
  | handled (target : DeclaredResourceController.Durable)
      (recovered : Recovered config target action)
      (result : BendActivityDispatch.Result recovered.origin)

/-- Load the current actual store, restore provenance from its verified history,
then publish/recover exactly the retained original application. A refusal or
uncertain native outcome does not synthesize a response or start a fresh call. -/
def receiveDispatch (config : Config) (bytes : List UInt8) :
    IO (Except String (Sigma fun action => Result config action)) := do
  if bytes.length > 4194304 then return .error "Activity dispatch source capacity"
  let some action := BendActivityDispatch.decode bytes | return .error "Activity dispatch source malformed"
  match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
  | .error reason => return .ok ⟨action,.refused reason⟩
  | .ok target =>
      match ← recover config target action with
      | .error reason => return .ok ⟨action,.refused reason⟩
      | .ok recovered =>
          let result ← BendActivityDispatch.receive recovered.origin
          return .ok ⟨action,.handled target recovered result⟩

/-- Reconstruct the actual original publication at its verified original prefix,
then compare the whole installed dispatch record. No provider/cache JSON enters
this native-publication outcome path. -/
def recoverResolution {config : Config} (target : DeclaredResourceController.Durable)
    {action : BendActivityOutcome.Action}
    {opened : Opened config}
    (origin : BendActivityDispatch.Origin config opened action.dispatch) :
    IO (Except String (BendActivityOutcome.Resolution origin)) := do
  match selected : action.publicationIndex with
  | none =>
      if absent : DurableCommitProtocol.Snapshot.lookupRecorded
          (BendActivityOutcome.applicationId origin) opened.durable.snapshot.model.journal = none then
        return .ok (.cancelled selected absent)
      else return .error "Activity cancellation refuses a recorded original publication"
  | some index =>
      let .ok publication ← NativeHostReplay.verifyLoadedSelected config target index
        | return .error "Activity publication source verification refused"
      let .ok original ← recover config publication.selected.before.durable action.dispatch
        | return .error "Activity publication original pending provenance refused"
      let .ok admitted ← BendActivityDispatch.admit original.origin
        | return .error "Activity original-height dispatch admission refused"
      let some receipt := BendActivityOutcome.bindPublication origin
          original.selection.verified.opened original.origin admitted
        | return .error "Activity publication differs from the actual retained native record"
      return .ok (.published receipt)

inductive OutcomeResult (config : Config) (action : BendActivityOutcome.Action) where
  | refused (reason : String)
  | handled (target : DeclaredResourceController.Durable)
      (recovered : Recovered config target action.dispatch)
      (result : BendActivityOutcome.Result recovered.origin)

/-- Concrete restart receiving for publication/cancellation and typed machine
resumption. Unknown publication is refused and leaves the pending continuation
intact. The controller's exact native operation identity supports lost-reply
recovery; an actual native append is still required before work can continue. -/
def receiveOutcome (config : Config) (bytes : List UInt8) :
    IO (Except String (Sigma fun action => OutcomeResult config action)) := do
  if bytes.length > 4194304 then return .error "Activity outcome source capacity"
  let some action := BendActivityOutcome.decode bytes | return .error "Activity outcome source malformed"
  match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
  | .error reason => return .ok ⟨action,.refused reason⟩
  | .ok target =>
      match ← recover config target action.dispatch with
      | .error reason => return .ok ⟨action,.refused reason⟩
      | .ok recovered =>
          match ← recoverResolution target recovered.origin with
          | .error reason => return .ok ⟨action,.refused reason⟩
          | .ok resolution =>
              let result ← BendActivityOutcome.receive recovered.origin resolution
              return .ok ⟨action,.handled target recovered result⟩

#assert_axioms recoverResolution
#assert_axioms receiveOutcome
#assert_axioms recover
#assert_axioms receiveDispatch
end Minidregg.Kernel.BendActivityRecovery
