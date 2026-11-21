/- One admitted kernel turn of the object kernel: the activity turns of
`Kernel.ObjectiveActivity` and the call tree of `Kernel.ObjectiveCall`. Its own
module (in the `ObjectiveActivity` namespace, names unchanged) because the call
kernel builds on the activity kernel and the turn sum must name both. -/
module

public import Kernel.ObjectiveSend
public import Kernel.ObjectiveDomain

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

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
`exhaust`, `abandon`, `ObjectiveCall.invoke`, `ObjectiveSend.deliverMessage`, `chargeFailure`, or the
upgrade turns `adopt`, `migrate`, `abortDrained`, `rebirth` of `Kernel.ObjectiveActivityUpgrade`). Every write the kernel activity commits
is `AdmittedTurn.intent` of one (the native receiver's decided turn is this
type, `ObjectiveActivityReceiver.Decided`), and the invariant
`stored_checkpoints_typed` (`Kernel.ObjectiveCheckpointInvariant`) is stated
over exactly these. -/
inductive AdmittedTurn {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) : Type where
  | publish (stored : Stored) (publication : Publication config snapshot stored)
  | create (request : CreateRequest) (created : Creation config snapshot height request)
  /-- A signed birth: never a rebirth's (whose predecessor `rebirth` retires in the same turn). -/
  | birth (request : BirthRequest) (signed : request.predecessor = none) (born : Birth config snapshot height request)
  | resolve (request : ResolveRequest) (resolution : Resolution config snapshot height request)
  | deliver (request : DeliverRequest) (delivery : Delivery config snapshot height request)
  | topUp (request : TopUpRequest) (topped : TopUp config snapshot request)
  | exhaust (request : ExhaustRequest) (exhausted : Exhaustion config snapshot height request)
  | abandon (request : AbandonRequest) (abandoned : Abandonment config snapshot height request)
  | invoke (request : ObjectiveCall.InvokeRequest) (invoked : ObjectiveCall.Invocation config snapshot height request)
  | deliverMessage (request : ObjectiveSend.MessageRequest)
      (delivered : ObjectiveSend.MessageDelivery config snapshot height request)
  | adopt (request : AdoptRequest) (adopted : Adoption config snapshot height request)
  | migrate (request : MigrateRequest) (migrated : Migrated config snapshot height request)
  | abortDrained (request : AbortRequest) (aborted : Abort config snapshot height request)
  | rebirth (request : RebirthRequest) (reborn : Rebirth config snapshot height request)
  /-- Register an invariant domain over member objects (`Kernel.ObjectiveDomain`). -/
  | registerDomain (request : RegisterRequest) (registered : Registration config snapshot height request)
  /-- A CHARGED FAILURE (GPT-6 row E): a signed, authorized, funded turn whose decision failed
  after the validator's work. It posts the Book only (the price of the declared envelope). -/
  | failed (request : FailureRequest) (charged : ChargedFailure config snapshot request)

/-- The posts a turn commits. -/
def AdmittedTurn.posts {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} : AdmittedTurn config snapshot height → List Post
  | .publish _ publication => publication.posts
  | .create _ created => created.posts
  | .birth _ _ born => born.posts
  | .resolve _ resolution => resolution.posts
  | .deliver _ delivery => delivery.posts
  | .topUp _ topped => [topped.posted.write config snapshot]
  | .exhaust _ exhausted => exhausted.posts
  | .abandon _ abandoned => abandoned.posts
  | .invoke _ invoked => invoked.posts
  | .deliverMessage _ delivered => delivered.posts
  | .adopt _ adopted => adopted.posts
  | .migrate _ migrated => migrated.posts
  | .abortDrained _ aborted => aborted.posts
  | .rebirth _ reborn => reborn.posts
  | .registerDomain _ registered => registered.posts
  | .failed _ charged => charged.posts

/-- **The Book operations a turn posts**: the operations of the one batch its kernel turn
admitted on the loaded Book (`Postings.batch`), and none for a turn that posts no batch
(a publication, a creation, a resolution). A rebirth's are its birth's. -/
def AdmittedTurn.operations {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} : AdmittedTurn config snapshot height → List Theory.CanonicalResourceKernel.Operation
  | .publish _ _ | .create _ _ | .resolve _ _ => []
  | .birth _ _ born => born.posted.batch.operations
  | .deliver _ delivery => delivery.posted.batch.operations
  | .topUp _ topped => topped.posted.batch.operations
  | .exhaust _ exhausted => exhausted.posted.batch.operations
  | .abandon _ abandoned => abandoned.posted.batch.operations
  | .invoke _ invoked => invoked.posted.batch.operations
  | .deliverMessage _ delivered => delivered.posted.batch.operations
  | .adopt _ adopted => adopted.posted.batch.operations
  | .migrate _ migrated => migrated.posted.batch.operations
  | .abortDrained _ aborted => aborted.posted.batch.operations
  | .rebirth _ reborn => reborn.born.posted.batch.operations
  | .registerDomain _ registered => registered.posted.batch.operations
  | .failed _ charged => charged.posted.batch.operations

/-- The one intent a turn commits under a receiver's sealing. -/
def AdmittedTurn.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (sealing : Seal) : AdmittedTurn config snapshot height → DataIntent rootBytes
  | .publish _ publication => publication.intent sealing
  | .create _ created => created.intent sealing
  | .birth _ _ born => born.intent sealing
  | .resolve _ resolution => resolution.intent sealing
  | .deliver _ delivery => delivery.intent sealing
  | .topUp _ topped => topped.intent sealing
  | .exhaust _ exhausted => exhausted.intent sealing
  | .abandon _ abandoned => abandoned.intent sealing
  | .invoke _ invoked => invoked.intent sealing
  | .deliverMessage _ delivered => delivered.intent sealing
  | .adopt _ adopted => adopted.intent sealing
  | .migrate _ migrated => migrated.intent sealing
  | .abortDrained _ aborted => aborted.intent sealing
  | .rebirth _ reborn => reborn.intent sealing
  | .registerDomain _ registered => registered.intent sealing
  | .failed _ charged => charged.intent sealing

/-- Every turn's intent is `intentOf` its posts: its writes are exactly the
post images, nothing else. -/
theorem AdmittedTurn.intent_writes {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} (sealing : Seal) (turn : AdmittedTurn config snapshot height) :
    (turn.intent sealing).writes = turn.posts.map (Post.write rootBytes) := by
  cases turn <;> rfl

#assert_axioms AdmittedTurn.intent_writes

end Minidregg.Kernel.ObjectiveActivity
