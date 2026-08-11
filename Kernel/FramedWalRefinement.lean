/-
# Kernel.FramedWalRefinement -- bytes, torn tails, and an explicit sync barrier

`DurableWalHandler` constructs an append-only logical WAL, but intentionally
leaves bytes, framing, partial writes, and `fsync` outside its claim.  This
module takes one bounded step toward a deployment without pretending to verify
an operating system or storage device.

The physical carrier here stores versioned, checksummed byte frames.  A frame
codec is fallible.  Recovery accepts the durable region only when every frame
decodes, ignores a separately modelled torn final segment, and otherwise
fails closed to the checkpoint.  Volatile staging and a torn prefix refine the
logical WAL's crash-before schedule; a successful sync barrier refines its
guarded commit-marker step.

The important ceiling remains explicit: `DeviceStep.sync` is an abstract
device transition, not a theorem about POSIX `fsync`, a filesystem, a disk
controller, or stable media.  A concrete deployment must refine its actual
I/O transitions to `DeviceStep`.  In particular, this file proves neither
liveness nor survival of an unmodelled fault domain.
-/
import Kernel.DurableWalHandler

namespace Minidregg.Kernel.FramedWalRefinement

open Minidregg.Theory
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableWalHandler

set_option autoImplicit false

universe u v w x

/-! ## Fallible versioned byte framing -/

/-- Deployment-supplied payload and checksum functions.  No global codec law
is smuggled into this carrier: each staged/synced record must exhibit its own
round trip.  This accommodates Rust decoders which are opaque and fallible. -/
structure FrameCodec (A : Type u) where
  magic : UInt8
  version : UInt8
  encodePayload : A -> List UInt8
  decodePayload : List UInt8 -> Option A
  checksum : List UInt8 -> UInt8

namespace FrameCodec

variable {A : Type u}

/-- One storage-segment frame.  Segment boundaries belong to the abstract
device below; bytes inside the segment carry magic, version, payload, and a
one-byte checksum. -/
def encodeFrame (codec : FrameCodec A) (value : A) : List UInt8 :=
  let payload := codec.encodePayload value
  [codec.magic, codec.version] ++ payload ++
    [codec.checksum (codec.version :: payload)]

/-- Fail-closed frame decoder.  Unknown magic/version, a missing checksum,
checksum disagreement, or payload rejection all produce `none`. -/
def decodeFrame (codec : FrameCodec A) (bytes : List UInt8) : Option A :=
  match bytes with
  | magic :: version :: body =>
      if magic != codec.magic then none
      else if version != codec.version then none
      else
        match body.getLast? with
        | none => none
        | some claimed =>
            let payload := body.dropLast
            if claimed != codec.checksum (version :: payload) then none
            else codec.decodePayload payload
  | _ => none

/-- The exact record-local obligation needed at the write boundary. -/
def RoundTrips (codec : FrameCodec A) (value : A) : Prop :=
  codec.decodeFrame (codec.encodeFrame value) = some value

/-- A mismatched checksum is rejected before the payload decoder is trusted. -/
theorem decodeFrame_badChecksum (codec : FrameCodec A)
    (payload : List UInt8) (claimed : UInt8)
    (bad : claimed != codec.checksum (codec.version :: payload)) :
    codec.decodeFrame
        ([codec.magic, codec.version] ++ payload ++ [claimed]) = none := by
  simp [decodeFrame, bad]

/-- A frame from another codec version is rejected even when its remaining
bytes happen to be meaningful to the payload decoder. -/
theorem decodeFrame_wrongVersion (codec : FrameCodec A)
    (version : UInt8) (body : List UInt8)
    (wrong : version != codec.version) :
    codec.decodeFrame (codec.magic :: version :: body) = none := by
  simp [decodeFrame, wrong]

end FrameCodec

/-! ## Physical media model and recovery -/

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w}
  {Event : Type x}

abbrev WalIntent := Intent TxId CellId Nullifier Event

/-- A bounded storage-device model.

* `durableFrames` are segment-framed bytes reported durable by the device;
* `tornTail` is a persistent prefix of a frame which never became a segment;
* `cache` is volatile page-cache/staging data and is lost on crash.

Neither a record boundary nor persistence is inferred from an OS call.  They
are state in this transition system, ready for a real implementation to
refine. -/
structure DeviceState
    (TxId : Type u) (CellId : Type v) (Nullifier : Type w) (Event : Type x) where
  checkpoint : Snapshot TxId CellId Nullifier Event
  durableFrames : List (List UInt8)
  tornTail : Option (List UInt8)
  cache : Option (List UInt8)

namespace DeviceState

variable (codec : FrameCodec (WalIntent (TxId := TxId) (CellId := CellId)
  (Nullifier := Nullifier) (Event := Event)))

/-- Decode the entire framed region.  One corrupt frame invalidates the region
rather than allowing records after a damaged boundary to be reinterpreted. -/
def decodeAll : List (List UInt8) ->
    Option (List (WalIntent (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)))
  | [] => some []
  | bytes :: rest => do
      let record <- codec.decodeFrame bytes
      let records <- decodeAll rest
      pure (record :: records)

@[simp] theorem decodeAll_nil : decodeAll codec [] = some [] := rfl

theorem decodeAll_append_frame
    (frames : List (List UInt8))
    (records : List (WalIntent (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)))
    (intent : WalIntent (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event))
    (clean : decodeAll codec frames = some records)
    (roundTrip : codec.RoundTrips intent) :
    decodeAll codec (frames ++ [codec.encodeFrame intent]) =
      some (records ++ [intent]) := by
  induction frames generalizing records with
  | nil =>
      simp only [decodeAll_nil, Option.some.injEq] at clean
      subst records
      change
        (codec.decodeFrame (codec.encodeFrame intent)).bind
            (fun record => some [record]) = some [intent]
      rw [roundTrip]
      rfl
  | cons bytes rest ih =>
      cases decoded : codec.decodeFrame bytes with
      | none => simp [decodeAll, decoded] at clean
      | some record =>
          cases decodedRest : decodeAll codec rest with
          | none => simp [decodeAll, decoded, decodedRest] at clean
          | some tail =>
              have clean' : record :: tail = records := by
                simpa [decodeAll, decoded, decodedRest] using clean
              subst records
              change
                decodeAll codec (bytes :: (rest ++ [codec.encodeFrame intent])) =
                  some (record :: (tail ++ [intent]))
              simp only [decodeAll, decoded]
              rw [show decodeAll codec (rest ++ [codec.encodeFrame intent]) =
                some (tail ++ [intent]) from ih tail decodedRest]
              rfl

/-- Recovery accepts all durable frames or fails closed to the checkpoint.
The torn tail and volatile cache never participate. -/
def recovered [DecidableEq CellId] [DecidableEq Nullifier]
    (device : DeviceState TxId CellId Nullifier Event) :
    Snapshot TxId CellId Nullifier Event :=
  match decodeAll codec device.durableFrames with
  | some records => records.foldl Snapshot.install device.checkpoint
  | none => device.checkpoint

/-- Expose why recovery did not consume every byte. -/
inductive RecoveryStatus
  | clean
  | ignoredTornTail
  | corruptFrame
  deriving DecidableEq, Repr

def recoveryStatus (device : DeviceState TxId CellId Nullifier Event) :
    RecoveryStatus :=
  match decodeAll codec device.durableFrames with
  | none => .corruptFrame
  | some _ => if device.tornTail.isSome then .ignoredTornTail else .clean

/-- The byte device's exact logical WAL abstraction. -/
def abstract [DecidableEq CellId] [DecidableEq Nullifier]
    (device : DeviceState TxId CellId Nullifier Event) :
    WalState TxId CellId Nullifier Event where
  checkpoint := device.checkpoint
  committed := (decodeAll codec device.durableFrames).getD []
  staged := device.cache.bind codec.decodeFrame

@[simp] theorem abstract_recovered [DecidableEq CellId]
    [DecidableEq Nullifier]
    (device : DeviceState TxId CellId Nullifier Event) :
    (abstract codec device).recovered = recovered codec device := by
  unfold abstract recovered WalState.recovered
  cases decodeAll codec device.durableFrames <;> rfl

/-- Persistent torn bytes are ignored by recovery, but visibly reported. -/
@[simp] theorem recovered_tornTail [DecidableEq CellId]
    [DecidableEq Nullifier]
    (device : DeviceState TxId CellId Nullifier Event)
    (tail : Option (List UInt8)) :
    recovered codec { device with tornTail := tail } = recovered codec device :=
  rfl

/-- Volatile bytes are equally absent from cold-start meaning. -/
@[simp] theorem recovered_cache [DecidableEq CellId]
    [DecidableEq Nullifier]
    (device : DeviceState TxId CellId Nullifier Event)
    (cache : Option (List UInt8)) :
    recovered codec { device with cache := cache } = recovered codec device :=
  rfl

end DeviceState

/-! ## Explicit device transitions and refinement to the logical WAL -/

variable [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
  [DecidableEq Event]

section Generic

variable (codec : FrameCodec (WalIntent (TxId := TxId) (CellId := CellId)
  (Nullifier := Nullifier) (Event := Event)))

/-- Proof payload for the linearizing sync transition.  Calling something
`fsync` is not evidence: the complete prior region must decode, the volatile
frame must be exact, the torn tail must have been repaired, and the recovered
snapshot must pass the protocol's replay and fail-closed preflight checks. -/
structure SyncReady
    (device : DeviceState TxId CellId Nullifier Event)
    (intent : WalIntent (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)) : Type (max u v w x) where
  records : List (WalIntent (TxId := TxId) (CellId := CellId)
    (Nullifier := Nullifier) (Event := Event))
  clean : DeviceState.decodeAll codec device.durableFrames = some records
  noTornTail : device.tornTail = none
  staged : device.cache = some (codec.encodeFrame intent)
  roundTrip : codec.RoundTrips intent
  unrecorded : Snapshot.lookupRecorded intent.transactionId
    (DeviceState.recovered codec device).journal = none
  preflighted : intent.preflight (DeviceState.recovered codec device) = .ok ()

/-- Device actions.  `tear` writes only a strict prefix and loses the cache;
`sync` is the sole semantic linearization point. -/
inductive DeviceStep :
    DeviceState TxId CellId Nullifier Event ->
      WalIntent (TxId := TxId) (CellId := CellId)
        (Nullifier := Nullifier) (Event := Event) ->
      DeviceState TxId CellId Nullifier Event -> Type (max u v w x)
  | stage (device) (intent) (roundTrip : codec.RoundTrips intent) :
      DeviceStep device intent
        { device with cache := some (codec.encodeFrame intent) }
  | tear (device) (intent) (staged : device.cache = some (codec.encodeFrame intent))
      (cut : Nat) (strict : cut < (codec.encodeFrame intent).length) :
      DeviceStep device intent
        { device with tornTail := some ((codec.encodeFrame intent).take cut)
                      cache := none }
  | crash (device) (intent) :
      DeviceStep device intent { device with cache := none }
  | truncateTornTail (device) (intent) :
      DeviceStep device intent { device with tornTail := none }
  | sync (device) (intent) (ready : SyncReady codec device intent) :
      DeviceStep device intent
        { device with
            durableFrames := device.durableFrames ++ [codec.encodeFrame intent]
            tornTail := none
            cache := none }
  | decline (device) (intent) : DeviceStep device intent device

/-- The sync transition is the exact semantic linearization point: recovery
after appending the verified frame is one `Snapshot.install` over recovery
before it.  This is a theorem about `DeviceStep.sync`'s model, not about an OS
call with the same name. -/
theorem recovered_after_sync
    (device : DeviceState TxId CellId Nullifier Event)
    (intent : WalIntent (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event))
    (ready : SyncReady codec device intent) :
    DeviceState.recovered codec
        { device with
            durableFrames := device.durableFrames ++ [codec.encodeFrame intent]
            tornTail := none
            cache := none } =
      Snapshot.install (DeviceState.recovered codec device) intent := by
  have decoded := DeviceState.decodeAll_append_frame codec
    device.durableFrames ready.records intent ready.clean ready.roundTrip
  simp only [DeviceState.recovered, decoded, ready.clean]
  simp [List.foldl_append]

/-- Every byte-device action is an admissible action of the already verified
logical WAL.  Thus the new byte layer does not silently add a second commit
semantics. -/
def step_refines_wal
    {before after : DeviceState TxId CellId Nullifier Event}
    {intent : WalIntent (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event)}
    (step : DeviceStep codec before intent after) :
    WalStep (DeviceState.abstract codec before) intent
      (DeviceState.abstract codec after) := by
  cases step with
  | stage roundTrip =>
      have decoded : codec.decodeFrame (codec.encodeFrame intent) = some intent :=
        roundTrip
      simpa only [DeviceState.abstract, Option.bind_some, decoded] using
        (WalStep.stage (DeviceState.abstract codec before) intent)
  | tear staged cut strict =>
      simpa [DeviceState.abstract] using
        (WalStep.crash (DeviceState.abstract codec before) intent)
  | crash =>
      simpa [DeviceState.abstract] using
        (WalStep.crash (DeviceState.abstract codec before) intent)
  | truncateTornTail =>
      simpa [DeviceState.abstract] using
        (WalStep.decline (DeviceState.abstract codec before) intent)
  | sync ready =>
      have decoded := DeviceState.decodeAll_append_frame codec
        before.durableFrames ready.records intent ready.clean ready.roundTrip
      have abstractRecovered :
          (DeviceState.abstract codec before).recovered =
            DeviceState.recovered codec before :=
        DeviceState.abstract_recovered codec before
      have staged : (DeviceState.abstract codec before).staged = some intent := by
        simp only [DeviceState.abstract, ready.staged, Option.bind_some]
        exact ready.roundTrip
      have logicalStep := WalStep.commit (DeviceState.abstract codec before) intent
        staged (by simpa [abstractRecovered] using ready.unrecorded)
        (by simpa [abstractRecovered] using ready.preflighted)
      simpa only [DeviceState.abstract, ready.clean, decoded, Option.getD_some,
        Option.bind_none] using logicalStep
  | decline =>
      exact WalStep.decline (DeviceState.abstract codec before) intent

/-- Representation is exactly recovered logical meaning. -/
def Represents (device : DeviceState TxId CellId Nullifier Event)
    (model : Snapshot TxId CellId Nullifier Event) : Prop :=
  DeviceState.recovered codec device = model

/-- The byte-device transition system inherits atomicity from the logical WAL
through an actual step translation, not through an `atomic = true` flag. -/
theorem deviceRefinement :
    ImplementationRefinement TxId CellId Nullifier Event
      (DeviceState TxId CellId Nullifier Event)
      (DeviceStep codec) (Represents codec) where
  simulates := by
    intro physicalBefore physicalAfter modelBefore intent represented stepped
    have representedWal : DurableWalHandler.Represents
        (DeviceState.abstract codec physicalBefore) modelBefore := by
      simpa [Represents, DurableWalHandler.Represents,
        DeviceState.abstract_recovered] using represented
    rcases walRefinement.simulates representedWal
      (step_refines_wal codec stepped) with ⟨schedule, simulated⟩
    exact ⟨schedule, by
      simpa [Represents, DurableWalHandler.Represents,
        DeviceState.abstract_recovered] using simulated⟩

/-- A stale root (or any other fail-closed preflight error) makes the sync
barrier uninhabited.  Bytes may be staged or torn, but cannot linearize. -/
theorem no_sync_of_preflight_error
    (device : DeviceState TxId CellId Nullifier Event)
    (intent : WalIntent (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event))
    (reason : RejectReason)
    (failed : intent.preflight (DeviceState.recovered codec device) =
      .error reason) :
    ¬ Nonempty (SyncReady codec device intent) := by
  rintro ⟨ready⟩
  rw [ready.preflighted] at failed
  contradiction

end Generic

/-! ## Closed positive, torn-write, corruption, and stale teeth -/

namespace ClosedInstance

open Minidregg.Kernel.DurableWalHandler.ClosedInstance

/-- A deliberately narrow executable payload codec.  It accepts exactly the
one closed witness intent; all other payload bytes fail.  This demonstrates
that the physical carrier is inhabited without claiming a production codec. -/
def codec : FrameCodec (Intent Nat Nat Nat Nat) where
  magic := 215
  version := 1
  encodePayload := fun _ => [10, 20, 30]
  decodePayload := fun payload => if payload = [10, 20, 30] then some intent else none
  checksum := fun bytes => bytes.foldl (fun acc byte => acc + byte) 0

theorem intent_roundTrips : codec.RoundTrips intent := by rfl

/-- Clean media with the exact encoded intent in volatile staging. -/
def beforeSync : DeviceState Nat Nat Nat Nat where
  checkpoint := device.checkpoint
  durableFrames := []
  tornTail := none
  cache := some (codec.encodeFrame intent)

def syncReady : SyncReady codec beforeSync intent where
  records := []
  clean := rfl
  noTornTail := rfl
  staged := rfl
  roundTrip := intent_roundTrips
  unrecorded := unrecorded
  preflighted := preflighted

/-- **Positive inhabitant:** the checked byte frame crosses the abstract sync
barrier and appends one durable segment. -/
def syncedStep : DeviceStep codec beforeSync intent
    { beforeSync with
        durableFrames := [codec.encodeFrame intent]
        tornTail := none
        cache := none } :=
  .sync beforeSync intent syncReady

def afterSync : DeviceState Nat Nat Nat Nat where
  checkpoint := device.checkpoint
  durableFrames := [codec.encodeFrame intent]
  tornTail := none
  cache := none

/-- Cold-start recovery after sync is the exact atomic protocol install. -/
theorem afterSync_recovers_install :
    DeviceState.recovered codec afterSync =
      Snapshot.install device.recovered intent := by
  have decoded : DeviceState.decodeAll codec [codec.encodeFrame intent] =
      some [intent] := by
    simp only [DeviceState.decodeAll]
    rw [intent_roundTrips]
    rfl
  simp only [DeviceState.recovered, afterSync, decoded]
  rfl

/-- A crash after writing only a strict prefix leaves the old snapshot. -/
def afterTornPrefix : DeviceState Nat Nat Nat Nat where
  checkpoint := beforeSync.checkpoint
  durableFrames := beforeSync.durableFrames
  tornTail := some ((codec.encodeFrame intent).take 3)
  cache := none

def tornStep : DeviceStep codec beforeSync intent afterTornPrefix :=
  .tear beforeSync intent rfl 3 (by decide)

theorem tornPrefix_recovers_old :
    DeviceState.recovered codec afterTornPrefix = device.recovered := rfl

theorem tornPrefix_reports_torn :
    DeviceState.recoveryStatus codec afterTornPrefix =
      .ignoredTornTail := rfl

/-- A later torn record cannot erase an already synced frame. -/
def committedWithTornSuccessor : DeviceState Nat Nat Nat Nat where
  checkpoint := afterSync.checkpoint
  durableFrames := afterSync.durableFrames
  tornTail := some ((codec.encodeFrame intent).take 2)
  cache := none

theorem committedPrefix_survives_torn_successor :
    DeviceState.recovered codec committedWithTornSuccessor =
      Snapshot.install device.recovered intent := by
  rw [show DeviceState.recovered codec committedWithTornSuccessor =
      DeviceState.recovered codec afterSync from rfl]
  exact afterSync_recovers_install

/-- A checksum-corrupt durable segment fails closed to the checkpoint. -/
def corruptFrame : List UInt8 :=
  [codec.magic, codec.version] ++ [10, 20, 30] ++ [0]

theorem corruptFrame_rejected : codec.decodeFrame corruptFrame = none := by decide

def afterCorruption : DeviceState Nat Nat Nat Nat where
  checkpoint := device.checkpoint
  durableFrames := [corruptFrame]
  tornTail := none
  cache := none

theorem corruption_reports_fault :
    DeviceState.recoveryStatus codec afterCorruption = .corruptFrame := by decide

theorem corrupted_commit_not_represent_install :
    ¬ Represents codec afterCorruption (Snapshot.install device.recovered intent) := by
  intro represented
  apply install_ne device.recovered intent
  simpa [Represents, DeviceState.recovered, DeviceState.decodeAll,
    afterCorruption, corruptFrame, corruptFrame_rejected] using represented.symm

/-- The same intent becomes stale when its expected root no longer matches the
checkpoint, so no sync proof can be constructed for the moved device. -/
def staleDevice : DeviceState Nat Nat Nat Nat where
  checkpoint := { device.checkpoint with roots := fun _ => ⟨9⟩ }
  durableFrames := []
  tornTail := none
  cache := some (codec.encodeFrame intent)

theorem stale_preflight :
    intent.preflight (DeviceState.recovered codec staleDevice) =
      .error .stalePreRoot := by decide

theorem stale_cannot_sync :
    ¬ Nonempty (SyncReady codec staleDevice intent) :=
  no_sync_of_preflight_error codec staleDevice intent .stalePreRoot stale_preflight

end ClosedInstance

/-! ## Axiom audit -/

/-- info: 'Minidregg.Kernel.FramedWalRefinement.FrameCodec.decodeFrame_badChecksum' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FrameCodec.decodeFrame_badChecksum
/-- info: 'Minidregg.Kernel.FramedWalRefinement.DeviceState.decodeAll_append_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeviceState.decodeAll_append_frame
/-- info: 'Minidregg.Kernel.FramedWalRefinement.step_refines_wal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_refines_wal
/-- info: 'Minidregg.Kernel.FramedWalRefinement.recovered_after_sync' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recovered_after_sync
/-- info: 'Minidregg.Kernel.FramedWalRefinement.deviceRefinement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deviceRefinement
/-- info: 'Minidregg.Kernel.FramedWalRefinement.ClosedInstance.afterSync_recovers_install' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.afterSync_recovers_install
/-- info: 'Minidregg.Kernel.FramedWalRefinement.ClosedInstance.corrupted_commit_not_represent_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.corrupted_commit_not_represent_install
/-- info: 'Minidregg.Kernel.FramedWalRefinement.ClosedInstance.stale_cannot_sync' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.stale_cannot_sync

end Minidregg.Kernel.FramedWalRefinement
