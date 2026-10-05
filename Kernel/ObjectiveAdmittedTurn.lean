/- One admitted kernel turn of the object kernel: the activity turns of
`Kernel.ObjectiveActivity` and the call tree of `Kernel.ObjectiveCall`. Its own
module (in the `ObjectiveActivity` namespace, names unchanged) because the call
kernel builds on the activity kernel and the turn sum must name both. -/
import Kernel.ObjectiveSend

namespace Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
set_option autoImplicit false

/-! ## One admitted turn -/

/-- **One admitted kernel turn** on a snapshot at a height: the witness of
exactly one of the kernel's admission functions (each `private mk`, so built
only by `publish`, `create`, `birth`, `resolve`, `deliver`, `topUp`,
`writeState`, `exhaust`, `abandon`, `ObjectiveCall.invoke` or `ObjectiveSend.deliverMessage`). Every write the kernel activity commits
is `AdmittedTurn.intent` of one (the native receiver's decided turn is this
type, `ObjectiveActivityReceiver.Decided`), and the invariant
`stored_checkpoints_typed` (`Kernel.ObjectiveCheckpointInvariant`) is stated
over exactly these. -/
inductive AdmittedTurn {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) : Type where
  | publish (stored : Stored) (publication : Publication config snapshot stored)
  | create (request : CreateRequest) (created : Creation config snapshot request)
  | birth (request : BirthRequest) (born : Birth config snapshot height request)
  | resolve (request : ResolveRequest) (resolution : Resolution config snapshot height request)
  | deliver (request : DeliverRequest) (delivery : Delivery config snapshot height request)
  | topUp (request : TopUpRequest) (topped : TopUp config snapshot request)
  | writeState (request : StateWriteRequest) (written : StateWrite config snapshot height request)
  | exhaust (request : ExhaustRequest) (exhausted : Exhaustion config snapshot height request)
  | abandon (request : AbandonRequest) (abandoned : Abandonment config snapshot height request)
  | invoke (request : ObjectiveCall.InvokeRequest) (invoked : ObjectiveCall.Invocation config snapshot height request)
  | deliverMessage (request : ObjectiveSend.MessageRequest)
      (delivered : ObjectiveSend.MessageDelivery config snapshot height request)

/-- The posts a turn commits. -/
def AdmittedTurn.posts {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} : AdmittedTurn config snapshot height → List Post
  | .publish _ publication => publication.posts
  | .create _ created => created.posts
  | .birth _ born => born.posts
  | .resolve _ resolution => resolution.posts
  | .deliver _ delivery => delivery.posts
  | .topUp _ topped => [topped.posted.write config snapshot]
  | .writeState _ written => written.posts
  | .exhaust _ exhausted => exhausted.posts
  | .abandon _ abandoned => abandoned.posts
  | .invoke _ invoked => invoked.posts
  | .deliverMessage _ delivered => delivered.posts

/-- The one intent a turn commits under a receiver's sealing. -/
def AdmittedTurn.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (sealing : Seal) : AdmittedTurn config snapshot height → DataIntent rootBytes
  | .publish _ publication => publication.intent sealing
  | .create _ created => created.intent sealing
  | .birth _ born => born.intent sealing
  | .resolve _ resolution => resolution.intent sealing
  | .deliver _ delivery => delivery.intent sealing
  | .topUp _ topped => topped.intent sealing
  | .writeState _ written => written.intent sealing
  | .exhaust _ exhausted => exhausted.intent sealing
  | .abandon _ abandoned => abandoned.intent sealing
  | .invoke _ invoked => invoked.intent sealing
  | .deliverMessage _ delivered => delivered.intent sealing

/-- Every turn's intent is `intentOf` its posts: its writes are exactly the
post images, nothing else. -/
theorem AdmittedTurn.intent_writes {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} (sealing : Seal) (turn : AdmittedTurn config snapshot height) :
    (turn.intent sealing).writes = turn.posts.map (Post.write rootBytes) := by
  cases turn <;> rfl

#assert_axioms AdmittedTurn.intent_writes

end Minidregg.Kernel.ObjectiveActivity
