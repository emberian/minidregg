/- The deployed commit path is the invariant's step relation.

`Kernel.ObjectiveCheckpointInvariant.Step` has three kinds of step: an admitted
kernel activity turn (`ObjectiveActivity.AdmittedTurn`, with its final posts), an
intent whose posts the seat kernel checked inert, or an intent the ordinary gate
admits. This module proves that the node's own judge produces nothing else. The
replay walk (`NativeHostReplay.advance`, which reopen and `audit` also run)
judges every record it re-admits with `Loaded.judge derived.transport`, the
same rule the live receiving loop applies (`advance_judged`). A record that passes is
either

* the kernel activity's own typed turn (`Derived.kernel`, `.activity`): its
  intent is `AdmittedTurn.finalIntent` of the turn the activity receiver decided,
  over the final posts `ActivitySeatEnd.finalize` made, under that receiver's
  sealing;
* the seat kernel's own typed turn (`Derived.kernel`, `.seat`): its writes are
  the decided turn's posts, which the seat kernel checked inert
  (`SeatStore.Decided.inert`); or
* judged by a source gate whose facet is not the object kernel's, so it
  writes no protected coordinate (`ordinaryGate`).

`derived_route` states this. -/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ObjectiveActivityGateRoute
open Minidregg.Theory
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeHostReplay
set_option autoImplicit false

theorem bind_ok_left {ε : Type} {a b : Except ε Unit} (ok : (a >>= fun _ => b) = .ok ()) : a = .ok () := by
  cases a with
  | error e => cases ok
  | ok u => cases u; rfl

/-- A record admitted by the durable writer carries its source-gate evidence. -/
theorem judge_source {rootBytes : List UInt8 → TypedAuthorization.Digest}
    (transport : Compiler.DurableReceiverIO.Transport) (loaded : Compiler.DurableReceiverIO.Loaded rootBytes)
    (intent : DataIntent rootBytes) (judged : Compiler.DurableReceiverIO.Judged transport loaded intent) :
    transport.sourceGate loaded.snapshot intent = .ok () :=
  judged.intentExact ▸ judged.commit.source

/-- **Every judged record is a step of the checkpoint invariant.** A record the
replay walk re-admits and judges is the kernel activity's own admitted turn, a
seat turn whose posts touch no kernel-activity cell, or it writes no protected
coordinate. -/
theorem derived_route {config : Config} {opened : Opened config} (derived : Derived config opened)
    (judged : Compiler.DurableReceiverIO.Judged derived.transport opened.durable derived.intent) :
    (∃ (kernel : ObjectiveActivity.Config) (height : Nat)
        (turn : ObjectiveActivity.AdmittedTurn kernel opened.durable.snapshot height)
        (sealing : ObjectiveActivityWire.Seal) (posts : List ObjectiveActivityWire.Post)
        (extra : List DurableDataIntent.ReadGuard),
        ActivitySeatEnd.finish kernel opened.durable.snapshot height turn = .ok (posts, extra) ∧
          derived.intent = ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn) ∨
      (∃ posts : List ObjectiveActivityWire.Post,
        derived.intent.writes = posts.map (ObjectiveActivityWire.Post.write Compiler.ResourceBirthCodec.rootBytes) ∧
          SeatStore.Inert opened.durable.snapshot posts) ∨
      ObjectiveActivityGate.ordinaryGate derived.intent = .ok () :=
  judged.route

#assert_axioms bind_ok_left
#assert_axioms judge_source
#assert_axioms derived_route
end Minidregg.Kernel.ObjectiveActivityGateRoute
