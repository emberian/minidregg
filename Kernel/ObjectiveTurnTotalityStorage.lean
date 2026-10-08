/- Exact storage accounting for the Objective receiver's full post images.
The framing gap is intentional until FD-1; no tariff is changed here.
Activity: 40 bytes; Book: 26; seat: 26 (the real SEAT-CELL frame has 15 bytes);
retirement: 4; unchanged posts: their full image. Counts inspect actual deltas.
This is source-level accounting, not evidence of deployment or admission totality. -/
import Kernel.DeployedHistory
import Kernel.ObjectiveActivityReceiver
import Kernel.HostRefinesWorld
import Kernel.ObjectiveTurnTotality

namespace Minidregg.Kernel.ObjectiveTurnTotalityStorage

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.World
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.DeployedHistory
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.DurableDataIntent (DataIntent DataWrite ReadGuard TransactionId StableNullifier)

set_option autoImplicit false

/-- The three live whole-blob kinds emitted by the receiver. -/
inductive BlobKind where
  | activity | book | seat
  deriving DecidableEq

def BlobKind.kind : BlobKind → deployedR.Kind
  | .activity => .objectiveActivity
  | .book => .resourceBook
  | .seat => .seat

def BlobKind.address (k : BlobKind) : Address (deployedR.layout k.kind) :=
  match k with
  | .activity => ⟨(), ()⟩
  | .book => ⟨.book, ()⟩
  | .seat => ⟨(), ()⟩

abbrev BlobKind.Value (k : BlobKind) := (deployedR.layout k.kind).Value k.address.1

def BlobKind.state (k : BlobKind) (v : Option k.Value) : Store (deployedR.layout k.kind) :=
  (0 : Store (deployedR.layout k.kind)).set k.address v

def BlobKind.framing : BlobKind → Nat
  | .activity => 40 | .book => 26 | .seat => 26

def BlobKind.valueBytes (k : BlobKind) (v : k.Value) : Nat :=
  ((wireOf k.kind).valueStream k.address.1 |>.encode v).length

theorem BlobKind.address_unique (k : BlobKind) (a : Address (deployedR.layout k.kind)) :
    a = k.address := by
  cases k <;> rcases a with ⟨ns, key⟩ <;> cases ns <;> cases key <;> rfl

theorem BlobKind.rom_empty (k : BlobKind) (s : Store (deployedR.layout k.kind)) :
    romPart s = 0 := by
  apply DFinsupp.ext
  intro a
  cases k <;> rw [romPart_apply] <;> rfl

/-- Every self-diff consists solely of reads, for arbitrary registry kinds. -/
theorem self_diff_bytes (k : deployedR.Kind) (s : Store (deployedR.layout k))
    (as : List (Address (deployedR.layout k))) :
    ((diff as s s).map (opBytes k)).sum = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : s a with
    | none => simpa [diff, guardOp, changeOp, h] using ih
    | some x => simpa [diff, guardOp, changeOp, h, opBytes] using ih

/-- Retirement contributes only frees, never newly written values. -/
theorem retire_diff_bytes (k : deployedR.Kind) (s : Store (deployedR.layout k))
    (as : List (Address (deployedR.layout k))) :
    ((diff as s 0).map (opBytes k)).sum = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : s a with
    | none => simpa [diff, guardOp, changeOp, h] using ih
    | some x => simpa [diff, guardOp, changeOp, h, opBytes] using ih

/-- Concrete wire framing, independently checked at each live post kind. -/
theorem live_image_bytes (k : BlobKind) (v : k.Value) :
    (encodeCell (some ⟨k.kind, k.state (some v)⟩)).length = k.valueBytes v + k.framing := by
  cases k with
  | activity => exact objective_post_bytes v
  | book =>
    change (List.append [68,82,2,1] (List.append [68,82,1,4]
      (CanonicalResourcePageMaterializer.wireFrame ++ 0 :: 1 ::
        CanonicalResourcePageMaterializer.bookStream.encode v))).length = _
    simp [BlobKind.valueBytes, BlobKind.kind, BlobKind.address, BlobKind.framing,
      wireOf, bookWire, CanonicalResourcePageMaterializer.wireFrame]
  | seat =>
    change (List.append [68,82,2,1] (List.append [68,82,1,20]
      (SeatCell.spec.wireFrame ++ (ProtectedCell.wirePayloadStream SeatCell.spec).encode
        (1, some v)))).length = _
    have frameLength : "DREGG/SEAT-CELL".toByteArray.toList.length = 15 := by decide +kernel
    have versionLength : (StreamCodec.nat.encode 1).length = 2 := rfl
    simp [BlobKind.valueBytes, BlobKind.kind, BlobKind.address, BlobKind.framing,
      wireOf, seatWire, ProtectedCell.wirePayloadStream, StreamCodec.product,
      StreamCodec.option, SeatCell.spec, SeatCell.payloadStream, frameLength, versionLength]
    omega

/-- A live whole-blob post makes the actual codec cover exactly its one address. -/
theorem live_cover (k : BlobKind) (s : Store (deployedR.layout k.kind)) (v : k.Value) :
    bridge.codec.cover k.kind s (k.state (some v)) = [k.address] := by
  have nd := bridge.codec.cover_nodup k.kind s (k.state (some v))
  have member : k.address ∈ bridge.codec.cover k.kind s (k.state (some v)) :=
    bridge.codec.mem_cover _ (Or.inr (by simp [BlobKind.state]))
  generalize bridge.codec.cover k.kind s (k.state (some v)) = xs at *
  cases xs with
  | nil => simp at member
  | cons a rest =>
    have eq := k.address_unique a
    subst a
    have empty : rest = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro b hb
      have eq := k.address_unique b
      subst b
      exact (List.nodup_cons.mp nd).1 hb
    rw [empty]

theorem live_leg_bytes (k : BlobKind) (c : CellId)
    (s : Store (deployedR.layout k.kind)) (v : k.Value) :
    legBytes ⟨c, k.kind, bridge.codec.legPatch k.kind s (k.state (some v))⟩ =
      if s k.address = some v then 0 else k.valueBytes v := by
  unfold legBytes Codec.legPatch
  rw [live_cover]
  cases h : s k.address with
  | none => simp [diff, guardOp, changeOp, h, BlobKind.state, opBytes, BlobKind.valueBytes]
  | some old =>
    by_cases eq : old = v
    · subst old
      simp [diff, guardOp, changeOp, h, BlobKind.state, opBytes]
    · simp [diff, guardOp, changeOp, h, BlobKind.state, opBytes, BlobKind.valueBytes, eq]

/-- The named per-live-post equality includes the unchanged-post case explicitly. -/
theorem receiver_charge_eq_legBytes_plus_framing (k : BlobKind) (c : CellId)
    (s : Store (deployedR.layout k.kind)) (v : k.Value) :
    (encodeCell (some ⟨k.kind, k.state (some v)⟩)).length =
      legBytes ⟨c, k.kind, bridge.codec.legPatch k.kind s (k.state (some v))⟩ +
        (if s k.address = some v then
          (encodeCell (some ⟨k.kind, k.state (some v)⟩)).length else k.framing) := by
  rw [live_leg_bytes]
  split_ifs
  · simp
  · exact live_image_bytes k v

theorem retired_charge_eq_legBytes_plus_framing (k : deployedR.Kind) (c : CellId)
    (s : Store (deployedR.layout k)) :
    (ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry .retired).length =
      legBytes ⟨c, k, bridge.codec.legPatch k s 0⟩ + 4 := by
  change 4 = ((diff _ s 0).map (opBytes k)).sum + 4
  rw [retire_diff_bytes]

#assert_axioms self_diff_bytes retire_diff_bytes live_image_bytes
#assert_axioms receiver_charge_eq_legBytes_plus_framing retired_charge_eq_legBytes_plus_framing

/-- Only image/delta shapes, with no accounting assumption. The pre-store of
an update or retirement is unrestricted. -/
inductive PostShape : List UInt8 → Delta deployedR → Prop where
  | burn (k : deployedR.Kind) :
      PostShape (ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry .retired)
        (.burn k)
  | create (k : BlobKind) (v : k.Value) :
      PostShape (encodeCell (some ⟨k.kind, k.state (some v)⟩))
        (.create k.kind (k.state (some v)))
  | change (k : BlobKind) (s : Store (deployedR.layout k.kind)) (v : k.Value) :
      PostShape (encodeCell (some ⟨k.kind, k.state (some v)⟩))
        (.change k.kind s (k.state (some v)))
  | retire (k : deployedR.Kind) (s : Store (deployedR.layout k)) :
      PostShape (ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry .retired)
        (.retire k s)

inductive PostClass where
  | activityChanged | bookChanged | seatChanged | retired | unchanged
  deriving DecidableEq

def kindClass : deployedR.Kind → PostClass
  | .objectiveActivity => .activityChanged
  | .resourceBook => .bookChanged
  | .seat => .seatChanged
  | _ => .unchanged

/-- Classification reads the decoded post delta, never its byte charge. -/
def deltaClass : Delta deployedR → PostClass
  | .create k _ => kindClass k
  | .change k s s' => if s = s' then .unchanged else kindClass k
  | .retire _ _ | .burn _ => .retired
  | .absent => .unchanged

def deltaStorage (c : CellId) (d : Delta deployedR) : Nat :=
  (((d.leg? bridge.codec c).toList).map legBytes).sum +
    (((d.create? c).toList).map fun born => imageBytes born.2.1).sum

/-- kern-r0's burn contributes an empty birth and an empty self-diff leg.
Both terms are zero under the deployed history, for every carrier kind. -/
theorem burn_storage_zero (c : CellId) (k : deployedR.Kind) :
    deltaStorage c (.burn k) = 0 := by
  simp [deltaStorage, Delta.leg?, Delta.create?, imageBytes_empty, legBytes,
    Codec.legPatch, self_diff_bytes]

def classFraming (bytes : List UInt8) : PostClass → Nat
  | .activityChanged => 40 | .bookChanged => 26 | .seatChanged => 26
  | .retired => 4 | .unchanged => bytes.length

theorem state_eq_iff (k : BlobKind) (s : Store (deployedR.layout k.kind)) (v : k.Value) :
    s = k.state (some v) ↔ s k.address = some v := by
  constructor
  · rintro rfl; simp [BlobKind.state]
  · intro h
    apply DFinsupp.ext
    intro a
    rw [k.address_unique a]
    simpa [BlobKind.state] using h

/-- Per-post charge equals its actual delta storage plus the classified gap. -/
theorem post_shape_charge (c : CellId) {bytes : List UInt8} {d : Delta deployedR}
    (shape : PostShape bytes d) :
    bytes.length = deltaStorage c d + classFraming bytes (deltaClass d) := by
  cases shape with
  | burn k =>
    rw [burn_storage_zero]
    rfl
  | create k v =>
    simp only [deltaStorage, Delta.leg?, Delta.create?, Option.toList_some, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, BlobKind.rom_empty,
      imageBytes_empty, deltaClass]
    rw [live_leg_bytes]
    simp only [DFinsupp.zero_apply, reduceCtorEq, ↓reduceIte]
    cases k <;> exact live_image_bytes _ _
  | change k s v =>
    simp only [deltaStorage, Delta.leg?, Delta.create?, Option.toList_some, Option.toList_none,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, deltaClass]
    simp only [state_eq_iff]
    by_cases same : s k.address = some v
    · simp [same, classFraming, live_leg_bytes]
    · simp only [same, ↓reduceIte, live_leg_bytes]
      cases k <;> exact live_image_bytes _ _
  | retire k s =>
    simpa [deltaStorage, Delta.leg?, Delta.create?, deltaClass, classFraming] using
      retired_charge_eq_legBytes_plus_framing k c s

variable {rootBytes : List UInt8 → Digest}

def postClass (cells : CellId → Option (Cell deployedR)) (post : Post) : Option PostClass :=
  match deltaOf bridge.codec cells (post.write rootBytes) with
  | .error _ => none
  | .ok d => some (deltaClass d)

/-- Counts are computed from the posts and their actual decoded deltas. -/
def countClass (cells : CellId → Option (Cell deployedR)) (posts : List Post)
    (cl : PostClass) : Nat :=
  (posts.map fun post => if postClass (rootBytes := rootBytes) cells post = some cl then 1 else 0).sum

def unchangedBytes (cells : CellId → Option (Cell deployedR)) (posts : List Post) : Nat :=
  (posts.map fun post => if postClass (rootBytes := rootBytes) cells post = some .unchanged
    then post.bytes.length else 0).sum

def framing (cells : CellId → Option (Cell deployedR)) (posts : List Post) : Nat :=
  40 * countClass (rootBytes := rootBytes) cells posts .activityChanged +
  26 * countClass (rootBytes := rootBytes) cells posts .bookChanged +
  26 * countClass (rootBytes := rootBytes) cells posts .seatChanged +
  4 * countClass (rootBytes := rootBytes) cells posts .retired +
  unchangedBytes (rootBytes := rootBytes) cells posts

/-- Structural expressibility premise, separate from the accounting conclusion. -/
def PostsSupported (cells : CellId → Option (Cell deployedR)) (posts : List Post) : Prop :=
  ∀ post ∈ posts, ∃ d, deltaOf bridge.codec cells (post.write rootBytes) = .ok d ∧
    PostShape post.bytes d

def writeStorage (cells : CellId → Option (Cell deployedR)) (w : DataWrite) : Nat :=
  match deltaOf bridge.codec cells w with
  | .ok d => deltaStorage w.cellId.value d
  | .error _ => 0

/-- Folding decoded deltas accounts for both legs and ROM birth images. -/
theorem deltas_storage (cells : CellId → Option (Cell deployedR)) (ws : List DataWrite) :
    storageOf history
      ((deltas bridge.codec cells ws).filterMap fun d => d.2.create? d.1)
      ((deltas bridge.codec cells ws).filterMap fun d => d.2.leg? bridge.codec d.1) =
    (ws.map (writeStorage cells)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases h : deltaOf bridge.codec cells w with
    | error e => simpa [deltas, h, writeStorage] using ih
    | ok d =>
      cases hc : d.create? w.cellId.value <;> cases hl : d.leg? bridge.codec w.cellId.value <;>
        simp_all [storageOf, history, WorldRoot.cshakeHistory, deltas, writeStorage, deltaStorage] <;> omega

/-- Guard legs have no newly written values even outside the three post kinds. -/
theorem guard_storage_zero (cells : CellId → Option (Cell deployedR)) (ids : List CellId) :
    ((ids.filterMap (guardLeg bridge.codec cells)).map legBytes).sum = 0 := by
  induction ids with
  | nil => rfl
  | cons c cs ih =>
    cases h : cells c with
    | none => simpa [guardLeg, h] using ih
    | some cell =>
      simpa [guardLeg, h, legBytes, Codec.legPatch, self_diff_bytes] using ih

theorem intent_storage (cells : CellId → Option (Cell deployedR)) (intent : DataIntent rootBytes) :
    storageOf history (createsOf bridge.codec cells intent) (legsOf bridge.codec cells intent) =
      (intent.writes.map (writeStorage cells)).sum := by
  have h := deltas_storage cells intent.writes
  simpa [createsOf, legsOf, storageOf, history, WorldRoot.cshakeHistory,
    List.map_append, List.sum_append, guard_storage_zero] using h

/-- The receiver charge definition is essential: it is the sum of full images. -/
theorem receiver_charge_eq_storage_plus_framing
    (ingress : ObjectiveActivityReceiver.DecodedIngress)
    (cells : CellId → Option (Cell deployedR)) (posts : List Post) (guards : List ReadGuard)
    (supported : PostsSupported (rootBytes := rootBytes) cells posts) :
    ObjectiveActivityReceiver.charge ingress posts guards .storageBytes =
      ((posts.map (Post.write rootBytes)).map (writeStorage cells)).sum +
        framing (rootBytes := rootBytes) cells posts := by
  induction posts with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨d, hd, hs⟩ := supported p (by simp)
    have hp := post_shape_charge p.cell.value hs
    have ht := ih (fun q hq => supported q (by simp [hq]))
    have cell : (Post.write rootBytes p).cellId.value = p.cell.value := rfl
    cases hc : deltaClass d <;>
      simp_all [ObjectiveActivityReceiver.charge, framing, countClass, unchangedBytes,
        postClass, writeStorage, classFraming, Nat.mul_add] <;> omega

#assert_axioms burn_storage_zero post_shape_charge intent_storage receiver_charge_eq_storage_plus_framing

/-- The actual `intentOf`, sealed with this receiver's charge function. -/
theorem intentOf_charge_eq_storage_plus_framing
    (ingress : ObjectiveActivityReceiver.DecodedIngress) (sealing : Seal)
    (cells : CellId → Option (Cell deployedR)) (transaction : TransactionId)
    (posts : List Post) (guards : List ReadGuard) (nullifiers : List StableNullifier)
    (supported : PostsSupported (rootBytes := rootBytes) cells posts) :
    let intent := intentOf rootBytes transaction posts guards nullifiers
      { sealing with charge := ObjectiveActivityReceiver.charge ingress }
    intent.exactCharge .storageBytes =
      storageOf history (createsOf bridge.codec cells intent) (legsOf bridge.codec cells intent) +
        framing (rootBytes := rootBytes) cells posts := by
  dsimp only
  rw [intent_storage]
  exact receiver_charge_eq_storage_plus_framing ingress cells posts
    (readOnly rootBytes posts (guards ++ sealing.guards)) supported

/-- All admitted turn constructors use the same final posts and receiver seal. -/
theorem finalIntent_charge_eq_storage_plus_framing
    {config : ObjectiveActivity.Config} {snapshot : ObjectiveActivity.Snapshot rootBytes} {height : Nat}
    (ingress : ObjectiveActivityReceiver.DecodedIngress) (sealing : Seal)
    (cells : CellId → Option (Cell deployedR)) (posts : List Post) (extra : List ReadGuard)
    (turn : ObjectiveActivity.AdmittedTurn config snapshot height)
    (supported : PostsSupported (rootBytes := rootBytes) cells posts) :
    let intent := ActivitySeatEnd.AdmittedTurn.finalIntent
      { sealing with charge := ObjectiveActivityReceiver.charge ingress } posts extra turn
    intent.exactCharge .storageBytes =
      storageOf history (createsOf bridge.codec cells intent) (legsOf bridge.codec cells intent) +
        framing (rootBytes := rootBytes) cells posts := by
  cases turn <;> exact intentOf_charge_eq_storage_plus_framing ingress sealing cells _ posts _ _ supported

/-- Specialization to the intent the native Objective receiver actually emits. -/
theorem prepared_intent_charge_eq_storage_plus_framing
    {F : Type} [Field F] {deployment : ObjectiveActivityReceiver.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : ObjectiveKernelConfig.Ambient}
    {durable : ObjectiveActivityReceiver.Durable} {command : ObjectiveActivityReceiver.Command}
    (prepared : ObjectiveActivityReceiver.Prepared deployment profile ambient durable command)
    (ingress : ObjectiveActivityReceiver.DecodedIngress)
    (cells : CellId → Option (Cell deployedR))
    (supported : PostsSupported (rootBytes := ResourceBirthCodec.rootBytes) cells prepared.final.1) :
    (prepared.intent ingress).exactCharge .storageBytes =
      storageOf history (createsOf bridge.codec cells (prepared.intent ingress))
        (legsOf bridge.codec cells (prepared.intent ingress)) +
      framing (rootBytes := ResourceBirthCodec.rootBytes) cells prepared.final.1 :=
  finalIntent_charge_eq_storage_plus_framing ingress
    (ObjectiveActivityReceiver.admissionSeal prepared ingress) cells prepared.final.1 prepared.final.2
    prepared.decided supported

/-- In particular, the storage-above-charge condition is false. -/
theorem prepared_storage_le_charge
    {F : Type} [Field F] {deployment : ObjectiveActivityReceiver.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : ObjectiveKernelConfig.Ambient}
    {durable : ObjectiveActivityReceiver.Durable} {command : ObjectiveActivityReceiver.Command}
    (prepared : ObjectiveActivityReceiver.Prepared deployment profile ambient durable command)
    (ingress : ObjectiveActivityReceiver.DecodedIngress)
    (cells : CellId → Option (Cell deployedR))
    (supported : PostsSupported (rootBytes := ResourceBirthCodec.rootBytes) cells prepared.final.1) :
    storageOf history (createsOf bridge.codec cells (prepared.intent ingress))
      (legsOf bridge.codec cells (prepared.intent ingress)) ≤
      (prepared.intent ingress).exactCharge .storageBytes := by
  rw [prepared_intent_charge_eq_storage_plus_framing prepared ingress cells supported]
  exact Nat.le_add_right _ _

/-- Wire constructors used by the Objective receiver. This premise says nothing
about costs, old stores, patches, or framing counts. -/
def PostImage (bytes : List UInt8) : Prop :=
  (∃ k : BlobKind, ∃ v : k.Value, bytes = encodeCell (some ⟨k.kind, k.state (some v)⟩)) ∨
    bytes = ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry .retired

/-- Successful decoding plus a receiver image constructor supplies PostShape. -/
theorem postShape_of_delta_success
    {cells : CellId → Option (Cell deployedR)} {p : Post} {d : Delta deployedR}
    (success : deltaOf bridge.codec cells (p.write rootBytes) = .ok d)
    (image : PostImage p.bytes) : PostShape p.bytes d := by
  have spec := deltaOf_spec success
  rcases image with ⟨k, v, image⟩ | image
  · have decoded : bridge.codec.decode (p.write rootBytes).canonicalPostBytes =
        some (some ⟨k.kind, k.state (some v)⟩) := by
      change decodeCell p.bytes = _
      rw [image, bridge_decode_total_on_registry]
    cases d with
    | absent => simp [decoded] at spec
    | burn kind => simp [decoded] at spec
    | create kind s =>
      have eq := Option.some.inj (Option.some.inj (spec.2.symm.trans decoded))
      cases eq
      rw [image]
      exact PostShape.create k v
    | change kind s s' =>
      have eq := Option.some.inj (Option.some.inj (spec.2.symm.trans decoded))
      cases eq
      rw [image]
      exact PostShape.change k s v
    | retire kind s => simp [decoded] at spec
  · have decoded : bridge.codec.decode (p.write rootBytes).canonicalPostBytes = some none := by
      change decodeCell p.bytes = _
      rw [image]
      exact decodeCell_retired.1
    have retires : bridge.codec.retires (p.write rootBytes).canonicalPostBytes = true := by
      change retiresCell p.bytes = _
      rw [image]
      exact decodeCell_retired.2
    cases d with
    | absent => simp [decoded, retires] at spec
    | burn kind => rw [image]; exact PostShape.burn kind
    | create kind s => simp [decoded] at spec
    | change kind s s' => simp [decoded] at spec
    | retire kind s => rw [image]; exact PostShape.retire kind s

/-- Post support is derived from `ofLoaded` success and image constructors;
it is not an additional accounting promise. -/
theorem postsSupported_ofLoaded
    {loaded : DurableReceiverIO.Loaded rootBytes} {intent : DataIntent rootBytes}
    {posts : List Post} {t : DTurn deployedR Digest}
    (success : HostRefinesWorld.Turn.ofLoaded bridge history loaded intent = .ok t)
    (writes : intent.writes = posts.map (Post.write rootBytes))
    (images : ∀ p ∈ posts, PostImage p.bytes) :
    PostsSupported (rootBytes := rootBytes) (HostRefinesWorld.cellsOf bridge loaded.snapshot) posts := by
  intro p hp
  have derived := ofCells_ok success
  have member : p.write rootBytes ∈ intent.writes := by rw [writes]; exact List.mem_map_of_mem hp
  obtain ⟨d, hd, _⟩ := delta_of_write derived member
  exact ⟨d, hd, postShape_of_delta_success hd (images p hp)⟩

#assert_axioms intentOf_charge_eq_storage_plus_framing finalIntent_charge_eq_storage_plus_framing
#assert_axioms prepared_intent_charge_eq_storage_plus_framing prepared_storage_le_charge
#assert_axioms postShape_of_delta_success postsSupported_ofLoaded

namespace SeedlessWitness

open ObjectiveTurnTotality

/-- Exactly the receiver-style posts in the existing seedless-create witness. -/
def posts : List Post := [post 1 .object]

def cells : CellId → Option (Cell deployedR) := fun c => preWorld.cells c

theorem supported : PostsSupported (rootBytes := ResourceBirthCodec.rootBytes) cells posts := by
  intro p hp
  simp only [posts, List.mem_singleton] at hp
  subst p
  let d : Delta deployedR := .create .objectiveActivity (payloadCell .object).store
  have hd : deltaOf bridge.codec cells ((post 1 .object).write ResourceBirthCodec.rootBytes) =
      .ok d := by
    change deltaOf bridge.codec cells _ = .ok (.create .objectiveActivity _)
    simp [deltaOf, cells, preWorld, post, Post.write, bridge, codec, Codec.ofWires,
      bridge_decode_total_on_registry, payloadCell]
  refine ⟨d, hd, ?_⟩
  exact PostShape.create .activity ⟨.object, [], []⟩

/-- Every count is pinned on a nonempty real intent, including zero unchanged bytes. -/
theorem counts :
    countClass (rootBytes := ResourceBirthCodec.rootBytes) cells posts .activityChanged = 1 ∧
    countClass (rootBytes := ResourceBirthCodec.rootBytes) cells posts .bookChanged = 0 ∧
    countClass (rootBytes := ResourceBirthCodec.rootBytes) cells posts .seatChanged = 0 ∧
    countClass (rootBytes := ResourceBirthCodec.rootBytes) cells posts .retired = 0 ∧
    countClass (rootBytes := ResourceBirthCodec.rootBytes) cells posts .unchanged = 0 ∧
    unchangedBytes (rootBytes := ResourceBirthCodec.rootBytes) cells posts = 0 := by
  decide +kernel

/-- The general equality instantiated with the seedless intent's actual creates
and legs; the ingress cannot affect the storage lane. -/
theorem receiver_equality (ingress : ObjectiveActivityReceiver.DecodedIngress) :
    ObjectiveActivityReceiver.charge ingress posts [] .storageBytes =
      storageOf history (createsOf bridge.codec cells seedlessCreateIntent)
        (legsOf bridge.codec cells seedlessCreateIntent) +
        (40 * 1 + 26 * 0 + 26 * 0 + 4 * 0 + 0) := by
  rw [intent_storage]
  have h := receiver_charge_eq_storage_plus_framing ingress cells posts [] supported
  have gap : framing (rootBytes := ResourceBirthCodec.rootBytes) cells posts = 40 := by
    simp [framing, counts.1, counts.2.1, counts.2.2.1, counts.2.2.2.1, counts.2.2.2.2.2]
  simpa only [gap] using h

/-- The witness's own storage lane equals the real derived storage plus the named counts. -/
theorem intent_equality :
    seedlessCreateIntent.exactCharge .storageBytes =
      storageOf history (createsOf bridge.codec cells seedlessCreateIntent)
        (legsOf bridge.codec cells seedlessCreateIntent) +
        (40 * 1 + 26 * 0 + 26 * 0 + 4 * 0 + 0) := by
  decide +kernel

#assert_axioms supported counts receiver_equality intent_equality

end SeedlessWitness

/-- An unchanged live post really normalizes to the single whole-blob read. -/
theorem unchanged_post_is_read (k : BlobKind) (v : k.Value) :
    bridge.codec.legPatch k.kind (k.state (some v)) (k.state (some v)) =
      [.read k.address.1 k.address.2 (some v)] := by
  unfold Codec.legPatch
  rw [live_cover]
  simp [diff, guardOp, changeOp, BlobKind.state]

/-- Direct links to the receiver's activity and seat image constructors. -/
theorem activity_image_supported (role : ObjectiveActivityCell.Role) (key body : List UInt8) :
    PostImage (ObjectiveActivity.image role key body) :=
  Or.inl ⟨.activity, ⟨role, key, body⟩, rfl⟩

theorem seat_image_supported (role : SeatCell.Role) (key body : List UInt8) :
    PostImage (SeatStore.image role key body) :=
  Or.inl ⟨.seat, ⟨role, key, body⟩, rfl⟩

theorem book_image_supported (book : Minidregg.Theory.CanonicalResourceKernel.Book) :
    PostImage (ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
      (.live ⟨.resourceBook, Minidregg.Theory.CellState.materialize
        CanonicalResourcePageMaterializer.materializer
        (CanonicalResourcePageMaterializer.stateOfOption (some book))⟩)) :=
  Or.inl ⟨.book, book, rfl⟩

theorem retired_image_supported : PostImage ObjectiveActivity.retiredImage := Or.inr rfl

theorem finalIntent_writes
    {config : ObjectiveActivity.Config} {snapshot : ObjectiveActivity.Snapshot rootBytes} {height : Nat}
    (sealing : Seal) (posts : List Post) (extra : List ReadGuard)
    (turn : ObjectiveActivity.AdmittedTurn config snapshot height) :
    (ActivitySeatEnd.AdmittedTurn.finalIntent sealing posts extra turn).writes =
      posts.map (Post.write rootBytes) := by
  cases turn <;> rfl

/-- Loaded-path equality: the only image premise is supplied by the receiver's
post constructors above; support follows from successful turn conversion. -/
theorem prepared_ofLoaded_charge_eq_storage_plus_framing
    {F : Type} [Field F] {deployment : ObjectiveActivityReceiver.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : ObjectiveKernelConfig.Ambient}
    {durable : ObjectiveActivityReceiver.Durable} {command : ObjectiveActivityReceiver.Command}
    (prepared : ObjectiveActivityReceiver.Prepared deployment profile ambient durable command)
    (ingress : ObjectiveActivityReceiver.DecodedIngress) {t : DTurn deployedR Digest}
    (success : HostRefinesWorld.Turn.ofLoaded bridge history durable (prepared.intent ingress) = .ok t)
    (images : ∀ p ∈ prepared.final.1, PostImage p.bytes) :
    (prepared.intent ingress).exactCharge .storageBytes = storageOf history t.creates t.legs +
      framing (rootBytes := ResourceBirthCodec.rootBytes)
        (HostRefinesWorld.cellsOf bridge durable.snapshot) prepared.final.1 := by
  have supported := postsSupported_ofLoaded success
    (finalIntent_writes _ _ _ prepared.decided) images
  have eqTurn := (ofCells_ok success).eq
  subst t
  exact prepared_intent_charge_eq_storage_plus_framing prepared ingress _ supported

#assert_axioms unchanged_post_is_read activity_image_supported seat_image_supported
#assert_axioms book_image_supported retired_image_supported finalIntent_writes
#assert_axioms prepared_ofLoaded_charge_eq_storage_plus_framing


namespace BurnWitness

open ObjectiveTurnTotality

/-- The tombstone post from kern-r0's constructed fresh-retirement intent. -/
def posts : List Post :=
  [⟨⟨1⟩, ResourceBirthCodec.rootBytes [], ObjectiveActivity.retiredImage⟩]

/-- Fresh retirement is counted once as retired; it is not a live changed post. -/
theorem counts :
    countClass (rootBytes := ResourceBirthCodec.rootBytes) SeedlessWitness.cells posts .activityChanged = 0 ∧
    countClass (rootBytes := ResourceBirthCodec.rootBytes) SeedlessWitness.cells posts .bookChanged = 0 ∧
    countClass (rootBytes := ResourceBirthCodec.rootBytes) SeedlessWitness.cells posts .seatChanged = 0 ∧
    countClass (rootBytes := ResourceBirthCodec.rootBytes) SeedlessWitness.cells posts .retired = 1 ∧
    countClass (rootBytes := ResourceBirthCodec.rootBytes) SeedlessWitness.cells posts .unchanged = 0 ∧
    unchangedBytes (rootBytes := ResourceBirthCodec.rootBytes) SeedlessWitness.cells posts = 0 := by
  decide +kernel

/-- The actual fresh-retirement intent has zero World storage and four image bytes. -/
theorem intent_equality :
    storageOf history (createsOf bridge.codec SeedlessWitness.cells freshRetirementIntent)
      (legsOf bridge.codec SeedlessWitness.cells freshRetirementIntent) = 0 ∧
    freshRetirementIntent.exactCharge .storageBytes =
      storageOf history (createsOf bridge.codec SeedlessWitness.cells freshRetirementIntent)
        (legsOf bridge.codec SeedlessWitness.cells freshRetirementIntent) +
        (40 * 0 + 26 * 0 + 26 * 0 + 4 * 1 + 0) := by
  decide +kernel

#assert_axioms counts intent_equality

end BurnWitness

end Minidregg.Kernel.ObjectiveTurnTotalityStorage
