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

/-- A record the durable judge admits passed its transport's source gate. -/
theorem judge_source {rootBytes : List UInt8 → TypedAuthorization.Digest}
    (transport : Compiler.DurableReceiverIO.Transport) (loaded : Compiler.DurableReceiverIO.Loaded rootBytes)
    (intent : DataIntent rootBytes) (ok : loaded.judge transport intent = .ok ()) :
    transport.sourceGate loaded.snapshot intent = .ok () := by
  simp only [Compiler.DurableReceiverIO.Loaded.judge] at ok
  exact bind_ok_left ok

/-- **Every judged record is a step of the checkpoint invariant.** A record the
replay walk re-admits and judges is the kernel activity's own admitted turn, a
seat turn whose posts touch no kernel-activity cell, or it writes no protected
coordinate. -/
theorem derived_route {config : Config} {opened : Opened config} (derived : Derived config opened)
    (judged : opened.durable.judge derived.transport derived.intent = .ok ()) :
    (∃ (kernel : ObjectiveActivity.Config) (height : Nat)
        (turn : ObjectiveActivity.AdmittedTurn kernel opened.durable.snapshot height)
        (sealing : ObjectiveActivityWire.Seal) (posts : List ObjectiveActivityWire.Post)
        (extra : List DurableDataIntent.ReadGuard),
        ActivitySeatEnd.finish kernel opened.durable.snapshot height turn = .ok (posts, extra) ∧
          derived.intent = ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn) ∨
      (∃ posts : List ObjectiveActivityWire.Post,
        derived.intent.writes = posts.map (ObjectiveActivityWire.Post.write Compiler.ResourceBirthCodec.rootBytes) ∧
          SeatStore.Inert opened.durable.snapshot posts) ∨
      ObjectiveActivityGate.ordinaryGate derived.intent = .ok () := by
  have source := judge_source _ _ _ judged
  unfold Derived.transport at source
  cases held : derived.kernel with
  | some kernel =>
    cases kernel with
    | activity ingress verdict exact =>
      left
      cases verdict with
      | accepted accepted =>
        exact ⟨_, _, accepted.prepared.decided,
          ObjectiveActivityReceiver.admissionSeal accepted.prepared ingress, accepted.prepared.final.1,
          accepted.prepared.final.2, accepted.prepared.finalExact, exact⟩
      | failed failed =>
        -- A charged failure is the kernel's own `failed` turn (the Book only), under the same seal.
        exact ⟨_, _, ObjectiveActivity.AdmittedTurn.failed failed.request failed.failure,
          ObjectiveActivityReceiver.sealAt (profile := config.profile) failed.gated.authority ingress.command ingress,
          failed.final.1, failed.final.2, failed.finalExact, exact⟩
    | seat ingress accepted exact =>
      right; left
      exact ⟨accepted.prepared.decided.posts, by rw [exact]; rfl, accepted.prepared.decided.inert⟩
  | none =>
    right; right
    rw [held] at source
    simp only at source
    have joint : ∀ {s : DataSnapshot Minidregg.Compiler.ResourceBirthCodec.rootBytes},
        config.otherFacetGate .joint s derived.intent = .ok () →
          ObjectiveActivityGate.ordinaryGate derived.intent = .ok () :=
      fun ok => config.sourceGate_ordinary (own := some .joint) (by decide) ok
    split at source
    · exact joint (bind_ok_left source)
    · split at source
      · exact joint (bind_ok_left source)
      · split at source
        · exact joint (bind_ok_left source)
        · unfold Config.transport at source
          split at source <;>
          exact config.sourceGate_ordinary (own := none) (by decide) source

#assert_axioms bind_ok_left
#assert_axioms judge_source
#assert_axioms derived_route
end Minidregg.Kernel.ObjectiveActivityGateRoute
