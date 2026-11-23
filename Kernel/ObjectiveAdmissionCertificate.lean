/- Stage-0 certificates bind the exact source intent and its derived Turn.
The durable log still encodes the intent; World-indexed host state is FD-1.
-/
module

public import Kernel.ObjectiveActivityReceiverCore
public import Kernel.ObjectiveActivityGate
public import Kernel.SeatReceiverCore
public import Kernel.HostRefinesWorldCore
public import Kernel.DeployedHistory

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
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.ObjectiveAdmissible

open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.HostRefinesWorld
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Kernel.World

set_option autoImplicit false

abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev W := World deployedR TransactionId Digest
abbrev T := DTurn deployedR Digest

/-- The receiver's checked computation, indexed by its exact output intent.
There is no constructor for an independently substituted post or guard list. -/
inductive Source : ObjectiveActivity.Config → (p : Durable) →
    DataIntent ResourceBirthCodec.rootBytes → Prop
  | activity {F : Type} [Field F] [DecidableEq F]
      {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
      {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
      {ingress : ObjectiveActivityReceiver.DecodedIngress}
      (accepted : ObjectiveActivityReceiver.Accepted deployment profile ambient p ingress) :
      Source accepted.prepared.config p (ObjectiveActivityReceiver.intent accepted)
  | failed {F : Type} [Field F] [DecidableEq F]
      {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
      {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
      {ingress : ObjectiveActivityReceiver.DecodedIngress}
      (failed : ObjectiveActivityReceiver.Failed deployment profile ambient p ingress) :
      Source failed.gated.config p failed.intent
  | seat {F : Type} [Field F] [DecidableEq F]
      {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
      {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
      {ingress : SeatReceiver.DecodedIngress}
      (accepted : SeatReceiver.Accepted deployment profile ambient p ingress)
      (ob : ObjectiveActivity.Config) : Source ob p (SeatReceiver.intent accepted)
  | foreign {ob : ObjectiveActivity.Config} {p : Durable}
      (intent : DataIntent ResourceBirthCodec.rootBytes)
      (gate : ObjectiveActivityGate.ordinaryGate intent = .ok ()) : Source ob p intent

/-- The three receiver routes, stated over the exact source intent. -/
def Route (p : Durable) (intent : DataIntent ResourceBirthCodec.rootBytes) : Prop :=
  (∃ (ob : ObjectiveActivity.Config) (height : Nat)
      (turn : ObjectiveActivity.AdmittedTurn ob p.snapshot height)
      (sealing : ObjectiveActivityWire.Seal) (posts : List ObjectiveActivityWire.Post)
      (extra : List ReadGuard),
      ActivitySeatEnd.finish ob p.snapshot height turn = .ok (posts, extra) ∧
        intent = ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn) ∨
    (∃ posts : List ObjectiveActivityWire.Post,
      intent.writes = posts.map (ObjectiveActivityWire.Post.write ResourceBirthCodec.rootBytes) ∧
        SeatStore.Inert p.snapshot posts) ∨
    ObjectiveActivityGate.ordinaryGate intent = .ok ()

theorem Source.route {ob : ObjectiveActivity.Config} {p : Durable}
    {intent : DataIntent ResourceBirthCodec.rootBytes} (source : Source ob p intent) :
    Route p intent := by
  cases source with
  | activity accepted =>
    exact Or.inl ⟨_, _, accepted.prepared.decided,
      ObjectiveActivityReceiver.admissionSeal accepted.prepared _, accepted.prepared.final.1,
      accepted.prepared.final.2, accepted.prepared.finalExact, rfl⟩
  | failed failed =>
    exact Or.inl ⟨_, _, .failed failed.request failed.failure,
      { ObjectiveActivityReceiver.sealAt failed.gated.authority _ _ with
        event := ObjectiveActivityReceiver.failedEvent (ObjectiveActivityReceiver.event _ _ _) failed.cause },
      failed.final.1, failed.final.2, failed.finalExact, rfl⟩
  | seat accepted ob =>
    exact Or.inr (Or.inl ⟨accepted.prepared.decided.posts, rfl, accepted.prepared.decided.inert⟩)
  | foreign intent gate => exact Or.inr (Or.inr gate)

#assert_axioms Source.route

/-- Executable data proposed by the receiver, before derivation and preflight. -/
structure Proposal (p : Durable) where
  config : ObjectiveActivity.Config
  intent : DataIntent ResourceBirthCodec.rootBytes
  source : Source config p intent

def Proposal.activity {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
    {ingress : ObjectiveActivityReceiver.DecodedIngress}
    (verdict : ObjectiveActivityReceiver.Verdict deployment profile ambient p ingress) : Proposal p :=
  match verdict with
  | .accepted accepted => ⟨accepted.prepared.config, _, .activity accepted⟩
  | .failed failed => ⟨failed.gated.config, _, .failed failed⟩

def Proposal.seat {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
    {ingress : SeatReceiver.DecodedIngress}
    (accepted : SeatReceiver.Accepted deployment profile ambient p ingress) : Proposal p :=
  ⟨accepted.prepared.config, _, .seat accepted _⟩

theorem Proposal.activity_intent {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : ObjectiveKernelConfig.Ambient} {p : Durable}
    {ingress : ObjectiveActivityReceiver.DecodedIngress}
    (verdict : ObjectiveActivityReceiver.Verdict deployment profile ambient p ingress) :
    (Proposal.activity verdict).intent = verdict.intent := by cases verdict <;> rfl

#assert_axioms Proposal.activity_intent

/-- Data, not merely a Boolean or proposition: the writer obtains its only
intent from this certificate. Both its run and derived Turn are bound to it. -/
structure CheckedCommit (ob : ObjectiveActivity.Config) (p : Durable) (t : T) where
  intent : DataIntent ResourceBirthCodec.rootBytes
  source : Source ob p intent
  derived : Turn.ofLoaded bridge DeployedHistory.history p intent = .ok t
  /-- The turn is charged what the intent charges, on every lane (the append
  path refuses any other). -/
  charged : t.charge = intent.exactCharge
  installs : Installs (execute .complete p.snapshot intent) = true

/-- Derivation is checked against the current loaded image; a failed check
produces no certificate and hence cannot reach the checked writer. -/
def Proposal.check {p : Durable} (proposal : Proposal p) :
    Except String ((t : T) × {certificate : CheckedCommit proposal.config p t //
      certificate.intent = proposal.intent}) :=
  match derived : Turn.ofLoaded bridge DeployedHistory.history p proposal.intent with
  | .error reason => .error s!"receiver intent has no World turn: {repr reason}"
  | .ok t =>
    match charged : DeployedCharge.mismatch t.charge proposal.intent.exactCharge with
    | some lane => .error s!"receiver intent's charge is not its turn's: {repr lane}"
    | none =>
    if installs : Installs (execute .complete p.snapshot proposal.intent) = true then
      .ok ⟨t, ⟨proposal.intent, proposal.source, derived, DeployedCharge.mismatch_none charged, installs⟩, rfl⟩
    else .error "receiver intent does not install at this opening"

end Minidregg.Kernel.ObjectiveAdmissible
