/-
Strict source-owned host framing. These are transport products over actual
controller bytes, not a second executor or an authority assertion. Each
operation's existing strict receiving codec still decodes its inner payload.
No raw DataIntent, supplied height, profile, or post-state is a call variant.
-/
import Compiler.NativeHostProfile
import Kernel.DeclaredResourceController
import Kernel.PolicyInstallReceiver
import Kernel.ResourceBirthReceiver
import Kernel.CapabilityDelegationReceiver
import Kernel.CapabilityRevocationReceiver
import Kernel.WorldRoot
import Compiler.RefusalReason

namespace Minidregg.Compiler.NativeHostCodec

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel

set_option autoImplicit false

/-! ## The world root (DATAMODEL §3.2/§3.4, step C1)

Receipts, signing plans and observation challenges bind `(worldRoot, height)`.
The world root is `Kernel.WorldRoot`'s authenticated map over the world's
slots: the system slot holds the height and the log root (which chains every
accepted record from a genesis root binding the deployment and the seed), and
each cell slot holds the cell's current root.  No caller chooses a replacement
summary or a digest algorithm. -/

/-- The log root before any turn: binds the deployment and the seed. -/
def logRoot0 (domain semantics : Digest) (seed : DurableReceiver.Seed) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.GENESIS-LOG/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product digestStream DurableReceiverCodec.seedStream)).encode
        (domain, semantics, seed))).digest

/-- The log root after the image's accepted records. -/
def logRoot (domain semantics : Digest) (image : DurableReceiver.Image) : Digest :=
  DurableCheckpointCodec.chainAfter (logRoot0 domain semantics image.seed) image.accepted

/-- The height: accepted turns since genesis (`Kernel.World.fold_head` from a
genesis head at 0). -/
def height (image : DurableReceiver.Image) : Nat := image.accepted.length

/-- What a world slot holds. -/
inductive Leaf where
  | system (height : Nat) (logRoot : Digest)
  | cell (bytes : List UInt8)

/-- A slot's root: the system slot hashes its height and log root; a cell slot
is the deployed cell root of its current bytes. -/
def leafRoot : Leaf → Digest
  | .system height logRoot => DurableCheckpointCodec.systemLeaf height logRoot
  | .cell bytes => ResourceBirthCodec.rootBytes bytes

/-- The world's entries: the system slot, then every cell the image names. -/
def worldEntries (domain semantics : Digest) (image : DurableReceiver.Image) :
    List (WorldRoot.Key × Leaf) :=
  (.system, .system (height image) (logRoot domain semantics image)) ::
    image.cellIds.map fun cellId => (.cell cellId.value, .cell (image.currentBytes cellId))

/-- **The world root** of an image, evaluated sparsely. -/
def worldRoot (domain semantics : Digest) (image : DurableReceiver.Image) : Digest :=
  WorldRoot.deployedRoot ((worldEntries domain semantics image).map fun e => (e.1, leafRoot e.2))

/-- The world root is A3's two-level `worldRoot` over (slot ↦ leaf root) at the
deployed scheme. -/
theorem worldRoot_eq_entryRoot (domain semantics : Digest) (image : DurableReceiver.Image) :
    worldRoot domain semantics image =
      WorldRoot.entryRoot WorldRoot.deployed leafRoot (worldEntries domain semantics image) :=
  (WorldRoot.entryRoot_deployed leafRoot _).symm

/-- **Openings (§3.4).**  When no two of the image's slots share an index path,
a named cell's current root opens at the world root. -/
theorem cell_opens (domain semantics : Digest) (image : DurableReceiver.Image)
    (cellId : DurableDataIntent.CellId) (named : cellId ∈ image.cellIds)
    (hix : ∀ e ∈ worldEntries domain semantics image,
      WorldRoot.deployed.ix e.1 = WorldRoot.deployed.ix (.cell cellId.value) → e.1 = .cell cellId.value) :
    WorldRoot.deployed.verify (worldRoot domain semantics image) (.cell cellId.value)
      (some (ResourceBirthCodec.rootBytes (image.currentBytes cellId)))
      (WorldRoot.deployed.opening (Theory.AuthMap.worldSlots leafRoot
        (WorldRoot.slotsOf WorldRoot.deployed.ix (worldEntries domain semantics image))) (.cell cellId.value)) =
      true := by
  have opens := Theory.AuthMap.world_opening WorldRoot.deployed leafRoot
    (WorldRoot.slotsOf WorldRoot.deployed.ix (worldEntries domain semantics image)) (.cell cellId.value)
  rw [WorldRoot.lookup_slotsOf _ _ _ hix] at opens
  have hall : ∀ e ∈ (worldEntries domain semantics image).filter
      (fun e => decide (e.1 = WorldRoot.Key.cell cellId.value)),
      e = (.cell cellId.value, .cell (image.currentBytes cellId)) := by
    intro e he
    rcases List.mem_filter.mp he with ⟨he, hk⟩
    simp only [decide_eq_true_eq] at hk
    simp only [worldEntries, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨c, _, rfl⟩
    · simp at hk
    · simp only [WorldRoot.Key.cell.injEq] at hk
      have : c = cellId := by cases c; cases cellId; simp_all
      subst this; rfl
  have hne : (worldEntries domain semantics image).filter
      (fun e => decide (e.1 = WorldRoot.Key.cell cellId.value)) ≠ [] := by
    intro hnil
    have : ((WorldRoot.Key.cell cellId.value, Leaf.cell (image.currentBytes cellId)) :
        WorldRoot.Key × Leaf) ∈ (worldEntries domain semantics image).filter
          (fun e => decide (e.1 = WorldRoot.Key.cell cellId.value)) := by
      refine List.mem_filter.mpr ⟨?_, by simp⟩
      simp only [worldEntries, List.mem_cons, List.mem_map]
      exact Or.inr ⟨cellId, named, rfl⟩
    rw [hnil] at this
    simp at this
  have hone : ((worldEntries domain semantics image).filter
      fun e => decide (e.1 = WorldRoot.Key.cell cellId.value)).getLast? =
        some (.cell cellId.value, .cell (image.currentBytes cellId)) := by
    rw [List.getLast?_eq_getLast hne]
    exact congrArg some (hall _ (List.getLast_mem hne))
  rw [hone] at opens
  simpa [leafRoot, worldRoot_eq_entryRoot, WorldRoot.entryRoot] using opens

def framedRaw {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
    { encode value := frame ++ stream.encode value
      decode bytes := if bytes.take frame.length = frame then
        stream.toLawful.decode (bytes.drop frame.length) else none
      decode_encode := by
        intro value
        have exact := stream.toLawful.decode_encode value
        change stream.toLawful.decode (stream.encode value) = some value at exact
        simp [exact] }

def framed {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
  ResourceBirthCodec.strictCodec (framedRaw frame stream)

theorem framed_canonical {α : Type} (frame : List UInt8) (stream : StreamCodec α)
    {bytes : List UInt8} {value : α}
    (decoded : (framed frame stream).decode bytes = some value) :
    (framed frame stream).encode value = bytes :=
  ResourceBirthCodec.strictCodec_canonical (framedRaw frame stream) decoded

def signedInvocationStream : StreamCodec DeclaredResourceController.SignedCommand :=
  StreamCodec.xmap (StreamCodec.product bytesStream
    (StreamCodec.product (StreamCodec.list bytesStream)
      (StreamCodec.product (StreamCodec.list bytesStream) bytesStream)))
    (fun value => (value.commandBytes, value.targetEnvelopes,
      value.observeEnvelopes, value.authorityEnvelope))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro value; cases value; rfl)

inductive SignedCall where
  | birth (ingress : List UInt8)
  | invoke (ingress : DeclaredResourceController.SignedCommand)
  | install (ingress : List UInt8)
  | delegate (ingress : List UInt8)
  | revoke (ingress : List UInt8)
  /-- K-RENOUNCE: a holder revokes a capability it holds. -/
  | renounce (ingress : List UInt8)

abbrev CallWire := Sum (List UInt8)
  (Sum DeclaredResourceController.SignedCommand
    (Sum (List UInt8) (Sum (List UInt8) (Sum (List UInt8) (List UInt8)))))

def SignedCall.toWire : SignedCall → CallWire
  | .birth bytes => .inl bytes
  | .invoke signed => .inr (.inl signed)
  | .install bytes => .inr (.inr (.inl bytes))
  | .delegate bytes => .inr (.inr (.inr (.inl bytes)))
  | .revoke bytes => .inr (.inr (.inr (.inr (.inl bytes))))
  | .renounce bytes => .inr (.inr (.inr (.inr (.inr bytes))))

def SignedCall.ofWire : CallWire → SignedCall
  | .inl bytes => .birth bytes
  | .inr (.inl signed) => .invoke signed
  | .inr (.inr (.inl bytes)) => .install bytes
  | .inr (.inr (.inr (.inl bytes))) => .delegate bytes
  | .inr (.inr (.inr (.inr (.inl bytes)))) => .revoke bytes
  | .inr (.inr (.inr (.inr (.inr bytes)))) => .renounce bytes

def callStream : StreamCodec SignedCall :=
  StreamCodec.xmap (StreamCodec.sum bytesStream
    (StreamCodec.sum signedInvocationStream
      (StreamCodec.sum bytesStream (StreamCodec.sum bytesStream
        (StreamCodec.sum bytesStream bytesStream)))))
    SignedCall.toWire SignedCall.ofWire (by intro value; cases value <;> rfl)

/-- Version 4 (K-RENOUNCE): the call gains `renounce`; a v3 call refuses. -/
def callFrame : List UInt8 := "DREGG/NATIVE-HOST/SIGNED-CALL/v4".toUTF8.toList

def callCodec : LawfulCodec SignedCall :=
  framed callFrame callStream

/-- The capability choices are supplied for the ordered conserved debit legs;
all request coordinates and physical auxiliary allocations are source-derived. -/
inductive Draft where
  | birth (descriptor : List UInt8) (sourceCapabilities : List CapabilityId)
  | invoke (command : List UInt8)
  | install (subject : SubjectId) (control : CapabilityId) (declaration : List UInt8)
  | delegate (command : List UInt8)
  | revoke (command : List UInt8)
  /-- K-RENOUNCE: the renounce command (`CapabilityRenounce.commandCodec`). -/
  | renounce (command : List UInt8)
  deriving DecidableEq, Repr

abbrev DraftWire := Sum (List UInt8 × List CapabilityId)
  (Sum (List UInt8)
    (Sum (SubjectId × CapabilityId × List UInt8) (Sum (List UInt8) (Sum (List UInt8) (List UInt8)))))

def Draft.toWire : Draft → DraftWire
  | .birth bytes capabilities => .inl (bytes, capabilities)
  | .invoke bytes => .inr (.inl bytes)
  | .install subject control bytes => .inr (.inr (.inl (subject, control, bytes)))
  | .delegate bytes => .inr (.inr (.inr (.inl bytes)))
  | .revoke bytes => .inr (.inr (.inr (.inr (.inl bytes))))
  | .renounce bytes => .inr (.inr (.inr (.inr (.inr bytes))))

def Draft.ofWire : DraftWire → Draft
  | .inl (bytes, capabilities) => .birth bytes capabilities
  | .inr (.inl bytes) => .invoke bytes
  | .inr (.inr (.inl (subject, control, bytes))) => .install subject control bytes
  | .inr (.inr (.inr (.inl bytes))) => .delegate bytes
  | .inr (.inr (.inr (.inr (.inl bytes)))) => .revoke bytes
  | .inr (.inr (.inr (.inr (.inr bytes)))) => .renounce bytes

def draftStream : StreamCodec Draft :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.product bytesStream
      (StreamCodec.list CredentialAuthorityEntryCodec.capabilityIdStream))
      (StreamCodec.sum bytesStream
        (StreamCodec.sum (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
          (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream bytesStream))
          (StreamCodec.sum bytesStream (StreamCodec.sum bytesStream bytesStream)))))
    Draft.toWire Draft.ofWire (by intro value; cases value <;> rfl)

/-- Version 4 (K-RENOUNCE): the draft gains `renounce`; a v3 draft refuses. -/
def draftFrame : List UInt8 := "DREGG/NATIVE-HOST/DRAFT/v4".toUTF8.toList

def draftCodec : LawfulCodec Draft :=
  framed draftFrame draftStream

/-- `role,index` is an ordered incidence label, not a user-selected authority.
The exact canonical header names the chosen key and full typed request. -/
structure SigningSlot where
  role : Nat
  index : Nat
  header : List UInt8
  deriving DecidableEq, Repr

def signingSlotStream : StreamCodec SigningSlot :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat bytesStream))
    (fun value => (value.role, value.index, value.header))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩) (by intro value; cases value; rfl)

structure SigningPlan where
  domain : Digest
  semantics : Digest
  worldRoot : Digest
  height : Nat
  finalizedDraft : Draft
  slots : List SigningSlot

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
        (StreamCodec.product draftStream (StreamCodec.list signingSlotStream))))))
    (fun value => (value.domain, value.semantics, value.worldRoot, value.height,
      value.finalizedDraft, value.slots))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2⟩) (by intro value; cases value; rfl)

/-- Version 5 (K-RENOUNCE): the finalized draft it carries gained `renounce`.
Version 4 bound the world root, not the whole-image boundary. -/
def signingPlanFrame : List UInt8 := "DREGG/NATIVE-HOST/SIGNING-PLAN/v5".toUTF8.toList

def signingPlanCodec : LawfulCodec SigningPlan :=
  framed signingPlanFrame signingPlanStream

def retiredSigningPlanFrame : List UInt8 := "DREGG/NATIVE-HOST/SIGNING-PLAN/v4".toUTF8.toList

structure Receipt where
  transactionId : Digest
  eventId : Digest
  /-- The height of the world this transaction produced: accepted entries
  through this transaction, not the current tip. -/
  acceptedCount : Nat
  /-- The world root at that height. -/
  worldRoot : Digest
  deriving DecidableEq, Repr

def receiptStream : StreamCodec Receipt :=
  StreamCodec.xmap (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat digestStream)))
    (fun value => (value.transactionId, value.eventId, value.acceptedCount, value.worldRoot))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro value; cases value; rfl)

def confirmationStream : StreamCodec DurableReceiverIO.Confirmation :=
  StreamCodec.xmap (StreamCodec.sum StreamCodec.bool StreamCodec.bool)
    (fun value => match value with
      | .installed => .inl false
      | .recoveredAfterUncertainResponse => .inl true
      | .replayed => .inr false)
    (fun wire => match wire with
      | .inl false => .installed
      | .inl true => .recoveredAfterUncertainResponse
      | .inr _ => .replayed)
    (by intro value; cases value <;> rfl)

/-- Refusal payload is a named reason from the closed `RefusalReason` set, a
stable source-selected phase, a diagnostic and, for a law refusal, the failing
clause of the law (`LawLeaf`). It does not contain internal snapshots,
journals, capability records or intents. -/
inductive Outcome where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | refused (reason : RefusalReason) (phase : List UInt8) (detail : List UInt8)
      (leaf : Option LawLeaf := none)
  | contention
  | unavailable (detail : List UInt8)
  | uncertain (detail : List UInt8)
  | absent

abbrev OutcomeWire := Sum (DurableReceiverIO.Confirmation × Receipt)
  (Sum (RefusalReason × List UInt8 × List UInt8 × Option LawLeaf)
    (Sum Bool (Sum (List UInt8) (List UInt8))))

def Outcome.toWire : Outcome → OutcomeWire
  | .confirmed kind receipt => .inl (kind, receipt)
  | .refused reason phase detail leaf => .inr (.inl (reason, phase, detail, leaf))
  | .contention => .inr (.inr (.inl false))
  | .absent => .inr (.inr (.inl true))
  | .unavailable detail => .inr (.inr (.inr (.inl detail)))
  | .uncertain detail => .inr (.inr (.inr (.inr detail)))

def Outcome.ofWire : OutcomeWire → Outcome
  | .inl (kind, receipt) => .confirmed kind receipt
  | .inr (.inl (reason, phase, detail, leaf)) => .refused reason phase detail leaf
  | .inr (.inr (.inl false)) => .contention
  | .inr (.inr (.inl true)) => .absent
  | .inr (.inr (.inr (.inl detail))) => .unavailable detail
  | .inr (.inr (.inr (.inr detail))) => .uncertain detail

def outcomeStream : StreamCodec Outcome :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.product confirmationStream receiptStream)
      (StreamCodec.sum (StreamCodec.product RefusalReason.stream
          (StreamCodec.product bytesStream
            (StreamCodec.product bytesStream (StreamCodec.option LawLeaf.stream))))
        (StreamCodec.sum StreamCodec.bool (StreamCodec.sum bytesStream bytesStream))))
    Outcome.toWire Outcome.ofWire (by intro value; cases value <;> rfl)

/-- Version 4: receipts bind `(worldRoot, height)` (not the whole-image
boundary); a refusal carries its closed `RefusalReason` and, for a law
refusal, the failing clause (`LawLeaf`). Version-1, version-2 and version-3
outcomes refuse; none is reinterpreted. -/
def outcomeFrame : List UInt8 := "DREGG/NATIVE-HOST/OUTCOME/v4".toUTF8.toList

def outcomeCodec : LawfulCodec Outcome :=
  framed outcomeFrame outcomeStream

def retiredOutcomeFrame : List UInt8 := "DREGG/NATIVE-HOST/OUTCOME/v1".toUTF8.toList

/-- A version-1 outcome frame refuses to decode. -/
theorem v1_outcome_refused (payload : List UInt8) :
    outcomeCodec.decode (retiredOutcomeFrame ++ payload) = none := by
  have lengthExact : outcomeFrame.length = retiredOutcomeFrame.length := by decide +kernel
  have different : retiredOutcomeFrame ≠ outcomeFrame := by decide +kernel
  have raw : (framedRaw outcomeFrame outcomeStream).decode (retiredOutcomeFrame ++ payload) = none := by
    simp [framedRaw, lengthExact, different]
  simp [outcomeCodec, framed, ResourceBirthCodec.strictCodec, raw]

def retiredOutcomeFrameV2 : List UInt8 := "DREGG/NATIVE-HOST/OUTCOME/v2".toUTF8.toList

/-- A version-2 outcome frame (receipts carrying the whole-image boundary)
refuses to decode. -/
theorem v2_outcome_refused (payload : List UInt8) :
    outcomeCodec.decode (retiredOutcomeFrameV2 ++ payload) = none := by
  have lengthExact : outcomeFrame.length = retiredOutcomeFrameV2.length := by decide +kernel
  have different : retiredOutcomeFrameV2 ≠ outcomeFrame := by decide +kernel
  have raw : (framedRaw outcomeFrame outcomeStream).decode (retiredOutcomeFrameV2 ++ payload) = none := by
    simp [framedRaw, lengthExact, different]
  simp [outcomeCodec, framed, ResourceBirthCodec.strictCodec, raw]

def retiredOutcomeFrameV3 : List UInt8 := "DREGG/NATIVE-HOST/OUTCOME/v3".toUTF8.toList

/-- A version-3 outcome frame refuses to decode: wave-c's v3 (a refusal
without its reason) and P-LAW's v3 (a reason and clause over the whole-image
receipt) were two shapes under one name; v4 supersedes both. -/
theorem v3_outcome_refused (payload : List UInt8) :
    outcomeCodec.decode (retiredOutcomeFrameV3 ++ payload) = none := by
  have lengthExact : outcomeFrame.length = retiredOutcomeFrameV3.length := by decide +kernel
  have different : retiredOutcomeFrameV3 ≠ outcomeFrame := by decide +kernel
  have raw : (framedRaw outcomeFrame outcomeStream).decode (retiredOutcomeFrameV3 ++ payload) = none := by
    simp [framedRaw, lengthExact, different]
  simp [outcomeCodec, framed, ResourceBirthCodec.strictCodec, raw]

/-- A version-4 signing plan (its draft without `renounce`) refuses to decode. -/
theorem v4_signingPlan_refused (payload : List UInt8) :
    signingPlanCodec.decode (retiredSigningPlanFrame ++ payload) = none := by
  have lengthExact : signingPlanFrame.length = retiredSigningPlanFrame.length := by decide +kernel
  have different : retiredSigningPlanFrame ≠ signingPlanFrame := by decide +kernel
  have raw : (framedRaw signingPlanFrame signingPlanStream).decode
      (retiredSigningPlanFrame ++ payload) = none := by
    simp [framedRaw, lengthExact, different]
  simp [signingPlanCodec, framed, ResourceBirthCodec.strictCodec, raw]


def retiredDraftFrame : List UInt8 := "DREGG/NATIVE-HOST/DRAFT/v3".toUTF8.toList
def retiredCallFrame : List UInt8 := "DREGG/NATIVE-HOST/SIGNED-CALL/v3".toUTF8.toList

/-- A version-3 draft (without `renounce`) refuses to decode. -/
theorem v3_draft_refused (payload : List UInt8) :
    draftCodec.decode (retiredDraftFrame ++ payload) = none := by
  have lengthExact : draftFrame.length = retiredDraftFrame.length := by
    decide +kernel
  have different : retiredDraftFrame ≠ draftFrame := by decide +kernel
  have raw : (framedRaw draftFrame draftStream).decode
      (retiredDraftFrame ++ payload) = none := by
    simp [framedRaw, lengthExact, different]
  simp [draftCodec, framed, ResourceBirthCodec.strictCodec, raw]

/-- A version-3 signed call (without `renounce`) refuses to decode. -/
theorem v3_call_refused (payload : List UInt8) :
    callCodec.decode (retiredCallFrame ++ payload) = none := by
  have lengthExact : callFrame.length = retiredCallFrame.length := by
    decide +kernel
  have different : retiredCallFrame ≠ callFrame := by decide +kernel
  have raw : (framedRaw callFrame callStream).decode
      (retiredCallFrame ++ payload) = none := by
    simp [framedRaw, lengthExact, different]
  simp [callCodec, framed, ResourceBirthCodec.strictCodec, raw]

@[simp] theorem call_roundtrip (value : SignedCall) :
    callCodec.decode (callCodec.encode value) = some value := callCodec.decode_encode value

@[simp] theorem plan_roundtrip (value : SigningPlan) :
    signingPlanCodec.decode (signingPlanCodec.encode value) = some value :=
  signingPlanCodec.decode_encode value

@[simp] theorem outcome_roundtrip (value : Outcome) :
    outcomeCodec.decode (outcomeCodec.encode value) = some value := outcomeCodec.decode_encode value

theorem call_canonical {bytes : List UInt8} {value : SignedCall}
    (decoded : callCodec.decode bytes = some value) : callCodec.encode value = bytes :=
  framed_canonical _ _ decoded

theorem plan_canonical {bytes : List UInt8} {value : SigningPlan}
    (decoded : signingPlanCodec.decode bytes = some value) : signingPlanCodec.encode value = bytes :=
  framed_canonical _ _ decoded

/-- A framed codec refuses bytes that do not begin with its own frame. -/
theorem framed_other_frame_refused {α : Type} (frame : List UInt8) (stream : StreamCodec α)
    (bytes : List UInt8) (other : bytes.take frame.length ≠ frame) :
    (framed frame stream).decode bytes = none := by
  simp [framed, ResourceBirthCodec.strictCodec, framedRaw, other]

/-- A refusal frame names its reason and its law clause. -/
theorem outcome_refusal_reason_decoded (reason : RefusalReason) (phase detail : List UInt8)
    (leaf : Option LawLeaf) :
    outcomeCodec.decode (outcomeCodec.encode (.refused reason phase detail leaf)) =
      some (.refused reason phase detail leaf) := outcomeCodec.decode_encode _

theorem outcome_canonical {bytes : List UInt8} {value : Outcome}
    (decoded : outcomeCodec.decode bytes = some value) : outcomeCodec.encode value = bytes :=
  framed_canonical _ _ decoded

/-- info: 'Minidregg.Compiler.NativeHostCodec.v1_outcome_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v1_outcome_refused
/-- info: 'Minidregg.Compiler.NativeHostCodec.v2_outcome_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v2_outcome_refused
/-- info: 'Minidregg.Compiler.NativeHostCodec.v3_outcome_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v3_outcome_refused
/-- info: 'Minidregg.Compiler.NativeHostCodec.v4_signingPlan_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v4_signingPlan_refused
/-- info: 'Minidregg.Compiler.NativeHostCodec.v3_draft_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v3_draft_refused
/-- info: 'Minidregg.Compiler.NativeHostCodec.v3_call_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v3_call_refused
/-- info: 'Minidregg.Compiler.NativeHostCodec.worldRoot_eq_entryRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms worldRoot_eq_entryRoot
/-- info: 'Minidregg.Compiler.NativeHostCodec.cell_opens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cell_opens

end Minidregg.Compiler.NativeHostCodec

