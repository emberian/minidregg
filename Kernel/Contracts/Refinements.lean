/-
# Kernel.Contracts.Refinements — existing Mini types into the shared contracts

ADDITIVE: every existing type is imported and read, none is changed. Each
refinement is a named projection plus a theorem that it keeps the domain's
canonical bytes (decoding the projected bytes recovers the domain value) or the
domain's real guarantee (the Install cut's effects are what the actual
installer installs; the Reserve cut's footprint is what the actual reservation
gate protects).

Identities:
* `ReceiptContinuity.Identity` ≃ `WorldSource` (`worldSource_equiv`).
* `ReceiptContinuity.Identity × Point` ↪ `RevisionRef` (`revisionRef_ofPoint_injective`).
* `NativeHostCodec.Receipt` ↪ `AcceptanceRef` for a fixed world source
  (`acceptanceRef_ofReceipt_injective`); its revision is the continuity point
  `⟨acceptedCount, worldRoot⟩` (`ofReceipt_revision`).
* (transaction id, event id) of an `IntentRecord` ↪ `InvocationId`
  (`invocationId_ofIds_injective`); a receipt and the record it names give the
  same invocation (`ofReceipt_invocation`).
* `CellId` ↪ `ObjectRef` in a fixed domain and kind (`objectRef_ofCell_injective`).
* `ArtifactRef` has NO injective Mini source: the nearest, a `DataWrite` post
  image, is bytes, and a digest+length reference can only be MATCHED by them
  (`artifactRef_ofWrite_matches`), never recover them without hash injectivity,
  which nothing here assumes.

Cuts (proved here; the domain files are outside the cut lane's set):
* `PayObservation.Command` → **Invoke**, not Observe. Mini's "observation"
  command mutates the pay cell under the observer's capability: it is an
  invocation whose content attests an external observation
  (`payObservation_toInvoke_exact`).
* `PayEnrolClaim.Observation` → Observe in a supplied context
  (`enrolObservation_toObserve_exact`).
* `FnSelectiveRelease.Release` → Release; its projection bytes ARE the native
  signature's preimage (`selectiveRelease_toRelease_exact`).
* `JointReservation.Reservation` → Reserve; the per-domain type carries no
  authorizing law, so the refinement takes it as a parameter
  (`jointReservation_toReserve_protects`).
* `DurableDataIntent.DataIntent` → Install; candidate = the physical record
  frame bytes (`dataIntent_toInstall_candidate`), and every Install effect is
  exactly what `DataSnapshot.install` writes (`dataIntent_toInstall_effects_installed`).
-/
import Kernel.Contracts.Cuts
import Compiler.NativeHostCodec
import Compiler.DurableCheckpointCodec
import Kernel.ReceiptContinuity
import Kernel.PayObservation
import Kernel.PayEnrolClaim
import Kernel.FnSelectiveRelease
import Kernel.JointReservation

namespace Minidregg.Kernel.Contracts.Refinements

open Minidregg.Kernel.Contracts
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent (DataIntent DataWrite ReadGuard CellId DataSnapshot)
open Minidregg.Kernel.DurableReceiver (IntentRecord)

set_option autoImplicit false

/-! ## Identities -/

def WorldSource.ofIdentity (i : ReceiptContinuity.Identity) : WorldSource :=
  ⟨i.domain, i.semantics, i.expectedSeed⟩

def WorldSource.toIdentity (s : WorldSource) : ReceiptContinuity.Identity :=
  ⟨s.domain, s.semantics, s.seed⟩

theorem worldSource_equiv :
    (∀ i, WorldSource.toIdentity (WorldSource.ofIdentity i) = i) ∧
    (∀ s, WorldSource.ofIdentity (WorldSource.toIdentity s) = s) :=
  ⟨fun i => by cases i; rfl, fun s => by cases s; rfl⟩

def RevisionRef.ofPoint (i : ReceiptContinuity.Identity) (p : ReceiptContinuity.Point) :
    RevisionRef :=
  ⟨WorldSource.ofIdentity i, p.height, p.worldRoot⟩

theorem revisionRef_ofPoint_injective :
    Function.Injective (fun ip : ReceiptContinuity.Identity × ReceiptContinuity.Point =>
      RevisionRef.ofPoint ip.1 ip.2) := by
  rintro ⟨⟨d, s, e⟩, ⟨h, r⟩⟩ ⟨⟨d', s', e'⟩, ⟨h', r'⟩⟩ same
  simp only [RevisionRef.ofPoint, WorldSource.ofIdentity, RevisionRef.mk.injEq,
    WorldSource.mk.injEq] at same
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := same
  rfl

def AcceptanceRef.ofReceipt (source : WorldSource) (r : Compiler.NativeHostCodec.Receipt) :
    AcceptanceRef :=
  ⟨⟨source, r.transactionId, r.eventId⟩, ⟨source, r.acceptedCount, r.worldRoot⟩⟩

theorem acceptanceRef_ofReceipt_injective (source : WorldSource) :
    Function.Injective (AcceptanceRef.ofReceipt source) := by
  rintro ⟨t, e, n, w⟩ ⟨t', e', n', w'⟩ same
  simp only [AcceptanceRef.ofReceipt, AcceptanceRef.mk.injEq, InvocationId.mk.injEq,
    RevisionRef.mk.injEq] at same
  obtain ⟨⟨-, rfl, rfl⟩, -, rfl, rfl⟩ := same
  rfl

theorem ofReceipt_revision (i : ReceiptContinuity.Identity)
    (r : Compiler.NativeHostCodec.Receipt) :
    (AcceptanceRef.ofReceipt (WorldSource.ofIdentity i) r).revision =
      RevisionRef.ofPoint i ⟨r.acceptedCount, r.worldRoot⟩ := rfl

def InvocationId.ofRecord (source : WorldSource) (r : IntentRecord) : InvocationId :=
  ⟨source, r.transactionId, r.event.eventId⟩

theorem invocationId_ofIds_injective (source : WorldSource) :
    Function.Injective (fun ids : Digest × Digest => (⟨source, ids.1, ids.2⟩ : InvocationId)) := by
  rintro ⟨t, e⟩ ⟨t', e'⟩ same
  simp only [InvocationId.mk.injEq] at same
  obtain ⟨-, rfl, rfl⟩ := same
  rfl

/-- A receipt and the accepted record it names identify the same invocation. -/
theorem ofReceipt_invocation (source : WorldSource) (r : Compiler.NativeHostCodec.Receipt)
    (record : IntentRecord) (names : r.transactionId = record.transactionId)
    (event : r.eventId = record.event.eventId) :
    (AcceptanceRef.ofReceipt source r).invocation = InvocationId.ofRecord source record := by
  simp [AcceptanceRef.ofReceipt, InvocationId.ofRecord, names, event]

def ObjectRef.ofCell (domain kind : Digest) (cell : CellId) : ObjectRef := ⟨cell, domain, kind⟩

theorem objectRef_ofCell_injective (domain kind : Digest) :
    Function.Injective (ObjectRef.ofCell domain kind) := by
  intro a b same
  simp only [ObjectRef.ofCell, ObjectRef.mk.injEq] at same
  exact same.1

def ArtifactRef.ofWrite (format : Digest) (origin : RevisionRef) (w : DataWrite) : ArtifactRef :=
  ⟨w.exactPost, w.canonicalPostBytes.length, format, origin, []⟩

/-- Bytes match a reference when they hash to its digest and have its length. -/
def ArtifactRef.Matches (rootBytes : List UInt8 → Digest) (a : ArtifactRef)
    (bytes : List UInt8) : Prop :=
  rootBytes bytes = a.digest ∧ bytes.length = a.length

/-- A post image written by a bound intent matches its artifact reference: the
digest is the intent's own `postRootsBound`, not a hash assumption. -/
theorem artifactRef_ofWrite_matches {rootBytes : List UInt8 → Digest}
    (intent : DataIntent rootBytes) (format : Digest) (origin : RevisionRef)
    (w : DataWrite) (member : w ∈ intent.writes) :
    ArtifactRef.Matches rootBytes (ArtifactRef.ofWrite format origin w) w.canonicalPostBytes :=
  ⟨intent.postRootsBound w member, rfl⟩

/-! ## Invoke: the pay "observation" command -/

/-- Deployment coordinates of the cells the pay observation names. -/
structure PayCells where
  pay : ObjectRef
  authority : ObjectRef

def payObservation_toInvoke (cells : PayCells) (c : PayObservation.Command) : Invoke where
  resources := [cells.pay]
  command := PayObservation.commandCodec.encode c
  actor := c.observer
  guards := [⟨cells.pay, c.expectedPayRoot⟩, ⟨cells.authority, c.expectedAuthorityRoot⟩]
  law := ⟨cells.authority, c.expectedAuthorityRoot⟩

/-- The Invoke keeps the signed command's canonical bytes (decoding recovers
the command), its actor is the signing observer, and it is injective. -/
theorem payObservation_toInvoke_exact (cells : PayCells) :
    (∀ c, PayObservation.commandCodec.decode (payObservation_toInvoke cells c).command = some c ∧
      (payObservation_toInvoke cells c).actor = c.observer) ∧
    Function.Injective (payObservation_toInvoke cells) := by
  refine ⟨fun c => ⟨PayObservation.commandCodec.decode_encode c, rfl⟩, ?_⟩
  intro a b same
  have bytes := congrArg Invoke.command same
  have da := PayObservation.commandCodec.decode_encode a
  rw [show (payObservation_toInvoke cells a).command = PayObservation.commandCodec.encode a
    from rfl] at bytes
  rw [bytes] at da
  exact (Option.some.inj (da.symm.trans (PayObservation.commandCodec.decode_encode b))).symm ▸ rfl

/-! ## Observe: enrolment deposit provenance -/

/-- What an `Observe` needs beyond the observed value; the enrolment record
deliberately does not carry it. -/
structure ObserveContext where
  resource : ObjectRef
  viewer : SubjectId
  sources : List Guard
  law : LawRef

def enrolObservation_toObserve (ctx : ObserveContext) (o : PayEnrolClaim.Observation) : Observe where
  resource := ctx.resource
  projection := ⟨PayEnrolClaim.observationFrame, PayEnrolClaim.observationCodec.encode o⟩
  viewer := ctx.viewer
  sources := ctx.sources
  law := ctx.law

theorem enrolObservation_toObserve_exact (ctx : ObserveContext) :
    (∀ o, PayEnrolClaim.observationCodec.decode (enrolObservation_toObserve ctx o).projection.bytes =
      some o) ∧
    Function.Injective (enrolObservation_toObserve ctx) := by
  refine ⟨fun o => PayEnrolClaim.observationCodec.decode_encode o, ?_⟩
  intro a b same
  have bytes := congrArg (fun o : Observe => o.projection.bytes) same
  have da := PayEnrolClaim.observationCodec.decode_encode a
  have db := PayEnrolClaim.observationCodec.decode_encode b
  simp only [enrolObservation_toObserve] at bytes
  rw [bytes, db] at da
  exact (Option.some.inj da).symm

/-! ## Release: fn selective release -/

structure AudienceCells where
  policy : ObjectRef
  keyset : ObjectRef
  ownerLaw : ObjectRef

def selectiveReleaseFrame : List UInt8 := "DREGG/FN/SELECTIVE-RELEASE/v2".toUTF8.toList

def selectiveRelease_toRelease (cells : AudienceCells) (r : FnSelectiveRelease.Release) : Release where
  projection := ⟨selectiveReleaseFrame, FnSelectiveRelease.releaseCodec.encode r⟩
  audience := [⟨cells.policy, r.destination.audience.policyRoot⟩,
    ⟨cells.keyset, r.destination.audience.keysetRoot⟩]
  law := ⟨cells.ownerLaw, r.owner.policyRoot⟩

/-- The Release cut's projection bytes are exactly the message the native
signature verifier checks, and they recover the release. -/
theorem selectiveRelease_toRelease_exact (cells : AudienceCells) :
    (∀ r, (selectiveRelease_toRelease cells r).projection.bytes = FnSelectiveRelease.signedPreimage r ∧
      FnSelectiveRelease.releaseCodec.decode (selectiveRelease_toRelease cells r).projection.bytes =
        some r) ∧
    Function.Injective (selectiveRelease_toRelease cells) := by
  refine ⟨fun r => ⟨rfl, FnSelectiveRelease.releaseCodec.decode_encode r⟩, ?_⟩
  intro a b same
  exact FnSelectiveRelease.signedPreimage_injective
    (congrArg (fun x : Release => x.projection.bytes) same)

/-! ## Reserve: joint reservations -/

def jointReservation_toReserve (source : WorldSource) (kind : Digest) (law : LawRef)
    (r : JointReservation.Reservation) : Reserve where
  candidate := r.candidateBytes
  footprint := r.footprint.map (ObjectRef.ofCell r.domain kind)
  law := law
  obligation := ⟨InvocationId.ofRecord source r.intent, r.lineage.nullifierId, r.domain⟩

/-- **The Reserve cut's footprint is what the real reservation gate protects.**
Every object in the projected footprint keeps its exact bytes across any
install that passed `JointReservation.Compatible` against the held reservation
(by `JointReservation.compatible_install_preserves_bytes`, the actual installer). -/
theorem jointReservation_toReserve_protects (source : WorldSource) (kind : Digest) (law : LawRef)
    (held : JointReservation.Reservation) {rootBytes : List UInt8 → Digest}
    (intent : DataIntent rootBytes)
    (compatible : JointReservation.Compatible held (IntentRecord.ofIntent intent))
    (before : DataSnapshot rootBytes) (object : ObjectRef)
    (member : object ∈ (jointReservation_toReserve source kind law held).footprint) :
    (DataSnapshot.install before intent).canonicalBytes object.native =
      before.canonicalBytes object.native := by
  obtain ⟨cell, guarded, rfl⟩ := List.mem_map.mp member
  exact JointReservation.compatible_install_preserves_bytes held intent compatible before cell guarded

/-! ## Install: the durable data intent -/

def DataWrite.toEffect (domain kind : Digest) (w : DataWrite) : Effect :=
  ⟨ObjectRef.ofCell domain kind w.cellId, w.expectedPre, w.exactPost, w.canonicalPostBytes⟩

def dataIntent_toInstall {rootBytes : List UInt8 → Digest} (source : WorldSource)
    (kind : Digest) (intent : DataIntent rootBytes) : Install where
  candidate := Compiler.DurableCheckpointCodec.recordFrame.encode (IntentRecord.ofIntent intent)
  preimage := intent.writes.map (fun w => ⟨ObjectRef.ofCell source.domain kind w.cellId, w.expectedPre⟩) ++
    intent.readGuards.map (fun g => ⟨ObjectRef.ofCell source.domain kind g.cellId, g.expectedRoot⟩)
  effects := intent.writes.map (DataWrite.toEffect source.domain kind)
  obligation := ⟨InvocationId.ofRecord source (IntentRecord.ofIntent intent), intent.transactionId,
    source.domain⟩

/-- The Install candidate is the exact physical record frame, and it decodes
back to the accepted record. -/
theorem dataIntent_toInstall_candidate {rootBytes : List UInt8 → Digest} (source : WorldSource)
    (kind : Digest) (intent : DataIntent rootBytes) :
    Compiler.DurableCheckpointCodec.recordFrame.decode (dataIntent_toInstall source kind intent).candidate =
      some (IntentRecord.ofIntent intent) :=
  Compiler.DurableCheckpointCodec.Framed.decode_encode _ _

/-- **The Install cut's exact effects are what the real installer installs**:
for an intent with unique write cells, installing it leaves every projected
effect's object holding exactly that effect's post bytes. -/
theorem dataIntent_toInstall_effects_installed {rootBytes : List UInt8 → Digest}
    (source : WorldSource) (kind : Digest) (intent : DataIntent rootBytes)
    (unique : (intent.writes.map DataWrite.cellId).Nodup) (before : DataSnapshot rootBytes)
    (effect : Effect) (member : effect ∈ (dataIntent_toInstall source kind intent).effects) :
    (DataSnapshot.install before intent).canonicalBytes effect.object.native = effect.postBytes := by
  obtain ⟨w, inWrites, rfl⟩ := List.mem_map.mp member
  exact DataSnapshot.install_canonicalBytes_of_member before intent unique w inWrites

#assert_axioms worldSource_equiv
#assert_axioms revisionRef_ofPoint_injective
#assert_axioms acceptanceRef_ofReceipt_injective
#assert_axioms ofReceipt_revision
#assert_axioms invocationId_ofIds_injective
#assert_axioms ofReceipt_invocation
#assert_axioms objectRef_ofCell_injective
#assert_axioms artifactRef_ofWrite_matches
#assert_axioms payObservation_toInvoke_exact
#assert_axioms enrolObservation_toObserve_exact
#assert_axioms selectiveRelease_toRelease_exact
#assert_axioms jointReservation_toReserve_protects
#assert_axioms dataIntent_toInstall_candidate
#assert_axioms dataIntent_toInstall_effects_installed

end Minidregg.Kernel.Contracts.Refinements
