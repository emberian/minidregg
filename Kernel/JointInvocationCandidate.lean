/- Exact joint candidates for the existing resource invocation receiver.

The descriptor is private protocol state, not a public participant manifest.
No digest collision assumption identifies two candidates: canonical bytes keep
all projections, source command bytes, attempts and custody descriptors.
-/
import Kernel.DeclaredResourceController
import Compiler.DurableReceiverCodec

namespace Minidregg.Kernel.JointInvocationCandidate

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DeclaredResourceController

set_option autoImplicit false

/-- One independently governed projection. Custody stays parameterized to avoid
coupling semantic domain membership to the private executor/holder committee. -/
structure Projection (Custody : Type) where
  domain : Digest
  epoch : Nat
  generation : Nat
  intent : IntentRecord
  custody : Custody

/-- Exact command and exact projections, with one already-required final signer.
`lineage` is the existing invocation nullifier, retained across retry attempts. -/
structure Candidate (Custody : Type) where
  commandBytes : List UInt8
  semantics : Digest
  lineage : StableNullifier
  attempt : Nat
  participants : List (Projection Custody)
  lastSigner : Digest
  originFence : Nat

def Projection.footprint {Custody : Type} (p : Projection Custody) : List CellId :=
  p.intent.writes.map DataWrite.cellId ++ p.intent.readGuards.map ReadGuard.cellId

def Candidate.required {Custody : Type} (c : Candidate Custody) : List Digest :=
  c.participants.map Projection.domain

/-- Structural scope only. This does not assert completeness of an arbitrary
hidden evaluator footprint or authorization of a participant projection. -/
structure Plan (Custody : Type) where
  candidate : Candidate Custody
  distinct : candidate.required.Nodup
  last : Fin candidate.participants.length
  last_exact : (candidate.participants[last]).domain = candidate.lastSigner
  origin_lineage : candidate.lineage ∈ (candidate.participants[last]).intent.nullifiers

theorem Plan.last_required {Custody : Type} (p : Plan Custody) :
    p.candidate.lastSigner ∈ p.candidate.required := by
  rw [← p.last_exact]
  exact List.mem_map.mpr ⟨p.candidate.participants[p.last], List.getElem_mem _, rfl⟩

def projectionStream {Custody : Type} (custody : StreamCodec Custody) :
    StreamCodec (Projection Custody) :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product DurableReceiverCodec.intentStream custody))))
    (fun p => (p.domain, p.epoch, p.generation, p.intent, p.custody))
    (fun (d, e, g, i, c) => ⟨d, e, g, i, c⟩)
    (by intro p; cases p; rfl)

def candidateStream {Custody : Type} (custody : StreamCodec Custody) :
    StreamCodec (Candidate Custody) :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product digestStream
      (StreamCodec.product DurableReceiverCodec.nullifierStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product (StreamCodec.list (projectionStream custody))
            (StreamCodec.product digestStream StreamCodec.nat))))))
    (fun c => (c.commandBytes, c.semantics, c.lineage, c.attempt,
      c.participants, c.lastSigner, c.originFence))
    (fun (b, s, l, a, ps, d, f) => ⟨b, s, l, a, ps, d, f⟩)
    (by intro c; cases c; rfl)

/-- The codec is injective without any injectivity assumption about roots. -/
theorem candidate_encode_injective {Custody : Type} (custody : StreamCodec Custody) :
    Function.Injective (candidateStream custody).encode := by
  intro a b same
  have decoded := congrArg (candidateStream custody).toLawful.decode same
  have left := (candidateStream custody).toLawful.decode_encode a
  have right := (candidateStream custody).toLawful.decode_encode b
  change (candidateStream custody).toLawful.decode ((candidateStream custody).encode a) = some a at left
  change (candidateStream custody).toLawful.decode ((candidateStream custody).encode b) = some b at right
  rw [left, right] at decoded
  exact Option.some.inj decoded

/-- Native projection bridge: all values come from the actual accepted receiver,
including audience read guards, exact compute fees and signed event bytes. -/
def projectionOfAccepted {Custody F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {ground : Ground deployment} {command : Command}
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed)
    (shape : PhysicalShape prepared) (epoch generation : Nat) (custody : Custody) :
    Projection Custody :=
  ⟨deployment.domain, epoch, generation,
    IntentRecord.ofIntent (accepted.dataIntent shape), custody⟩

@[simp] theorem projectionOfAccepted_intent {Custody F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {ground : Ground deployment} {command : Command}
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed)
    (shape : PhysicalShape prepared) (epoch generation : Nat) (custody : Custody) :
    (projectionOfAccepted accepted shape epoch generation custody).intent.bind?
      ResourceBirthCodec.rootBytes = some (accepted.dataIntent shape) := by
  exact IntentRecord.bind_ofIntent _

/-- A YES admission must be from the actual current receiver, not an asserted
Boolean. The physical image equality is checked by the agreement adapter before
recording the reservation. This does not itself implement a reservation law. -/
structure CurrentAdmission {Custody F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command)
    (signed : SignedCommand) (projection : Projection Custody) where
  /-- The joint candidate is admitted on the full shape (its YES proposal records the
  source image): the ground of its preparation is the image's own loads. -/
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  prepared : PreparedInvocation deployment profile ambient
    (Minidregg.Compiler.ServedBasis.Ground.full durable directory authority) command
  accepted : AcceptedInvocation prepared signed
  shape : PhysicalShape prepared
  domain_exact : projection.domain = deployment.domain
  record_exact : projection.intent = IntentRecord.ofIntent (accepted.dataIntent shape)
  ready : (accepted.dataIntent shape).preflight durable.snapshot = .ok ()

/-- Every authority/clock/audience guard of the existing receiver belongs to
what the reservation must protect. No submitter-declared footprint is used. -/
theorem admitted_guard_in_footprint {Custody F : Type} [Field F] [DecidableEq F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command}
    {signed : SignedCommand} {projection : Projection Custody}
    (admission : CurrentAdmission deployment profile ambient durable command signed projection)
    (guard : ReadGuard) (member : guard ∈ (admission.accepted.dataIntent admission.shape).readGuards) :
    guard.cellId ∈ projection.footprint := by
  unfold Projection.footprint
  rw [admission.record_exact]
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨guard, member, rfl⟩

end Minidregg.Kernel.JointInvocationCandidate
