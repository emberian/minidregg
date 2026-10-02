/-
A carried segment retains the old durable Image, including its exact accepted
records. One explicitly authorized internal intent changes the interpretation's
physical source cells. It does not bootstrap a Seed from the materialized cells.

This module constructs and checks the byte/state boundary. Old signed admission,
external operator authorization, the fixed semantic transformation, and actual
new-profile validation are separate receiving obligations in CarriedSegmentIO;
a caller cannot obtain those obligations by supplying this manifest alone.
-/
import Compiler.DurableReceiverIO
import Compiler.ResourceBirthCodec
import Compiler.NativeHostCodec
import Kernel.ReceiptContinuity

namespace Minidregg.Kernel.CarriedSegment

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

structure Identity where
  domain : Digest
  semantics : Digest
  genesis : Digest
  deriving DecidableEq, Repr

structure Point where
  height : Nat
  worldRoot : Digest
  logChain : Digest
  deriving DecidableEq, Repr

/-- Artifact digests are opaque SHA-256 bytes, with length checked below. They
pin code/configuration bytes; they are not policy or world-root digests. -/
structure CapsulePins where
  host : List UInt8
  storageHelper : List UInt8
  signatureVerifier : List UInt8
  configuration : List UInt8
  profile : List UInt8
  deriving DecidableEq, Repr

/-- Excludes the resulting head: the signed body becomes the carry event; the
resulting head is derived from that event and the exact old Image. -/
structure Body where
  source : Identity
  cut : Point
  sourceImage : Digest
  sourceCapsule : CapsulePins
  target : Identity
  targetCapsule : CapsulePins
  transformation : Nat
  writes : Digest
  originIndex : Digest
  operatorPublicKey : List UInt8
  nonce : List UInt8
  deriving DecidableEq, Repr

def digest (domain : String) (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash domain.toUTF8.toList bytes).digest

def identityBytes (identity : Identity) : List UInt8 :=
  (StreamCodec.list digestStream).encode
    [identity.domain, identity.semantics, identity.genesis]

def pointBytes (point : Point) : List UInt8 :=
  (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream digestStream)).encode
    (point.height, point.worldRoot, point.logChain)

def capsuleBytes (pins : CapsulePins) : List UInt8 :=
  (StreamCodec.list bytesStream).encode
    [pins.host, pins.storageHelper, pins.signatureVerifier, pins.configuration, pins.profile]

def CapsulePins.wellFormed (pins : CapsulePins) : Bool :=
  [pins.host, pins.storageHelper, pins.signatureVerifier, pins.configuration, pins.profile].all
    (fun value => value.length == 32)

def Body.bytes (body : Body) : List UInt8 :=
  "DREGG.CARRIED-SEGMENT/v1".toUTF8.toList ++
    (StreamCodec.list bytesStream).encode
      [identityBytes body.source, pointBytes body.cut,
       digestStream.encode body.sourceImage, capsuleBytes body.sourceCapsule,
       identityBytes body.target, capsuleBytes body.targetCapsule,
       StreamCodec.nat.encode body.transformation, digestStream.encode body.writes,
       digestStream.encode body.originIndex, body.operatorPublicKey, body.nonce]

def Body.id (body : Body) : Digest :=
  digest "DREGG.CARRIED-SEGMENT.ID/v1" body.bytes

/-- The result is signed after the event has produced its target root. This
edge stays beside the log, never inside its own event, so there is no root cycle.
Public clients verify this explicit external handoff without private cell data. -/
structure EdgeSeal where
  body : Body
  targetStart : Point
  sourceSiblings : List Digest
  targetSiblings : List Digest
  signature : List UInt8
  deriving DecidableEq, Repr

def EdgeSeal.signingBytes (edge : EdgeSeal) : List UInt8 :=
  "DREGG.CARRIED-SEGMENT.SEAL/v1".toUTF8.toList ++
    (StreamCodec.list bytesStream).encode [edge.body.bytes, pointBytes edge.targetStart]

/-- Public conditions on the authorized bridge. This is deliberately not a
claim that public clients possess or replay private source-state bytes. The IO
checker additionally verifies the detached signature using the independently
pinned operator key and pinned cryptographic helper. -/
def checkPublic (expectedSource : Identity) (trustedOperator : List UInt8)
    (edge : EdgeSeal) : Except String Point := do
  let body := edge.body
  if body.source != expectedSource then throw "carry edge belongs to another source identity"
  if trustedOperator.length != 32 || body.operatorPublicKey != trustedOperator then
    throw "carry edge has no preexisting operator authority"
  if edge.signature.length != 64 then throw "carry edge signature length"
  if !body.sourceCapsule.wellFormed || !body.targetCapsule.wellFormed then
    throw "carry edge capsule pins are malformed"
  if body.target.domain != body.source.domain || body.target.genesis != body.source.genesis then
    throw "carry edge changes original domain or genesis"
  if body.target.semantics == body.source.semantics then throw "carry edge does not change profile"
  if body.transformation != 1 || body.nonce.length != 32 then throw "unsupported carry edge"
  if edge.targetStart.height != body.cut.height + 1 then throw "carry edge resets or skips logical history"
  if !ReceiptContinuity.opens ⟨body.cut.height, body.cut.worldRoot⟩
      body.cut.logChain edge.sourceSiblings then throw "carry old-cut opening refused"
  if !ReceiptContinuity.opens ⟨edge.targetStart.height, edge.targetStart.worldRoot⟩
      edge.targetStart.logChain edge.targetSiblings then throw "carry target-start opening refused"
  pure edge.targetStart

/-- Global accepted counts select the historical interpreter. This selector
never changes an old receipt's root into a root under the new interpretation. -/
def sourceSegmentFor (edge : EdgeSeal) (height : Nat) : Bool := height ≤ edge.body.cut.height

@[simp] theorem original_cut_stays_historical (edge : EdgeSeal) :
    sourceSegmentFor edge edge.body.cut.height = true := by simp [sourceSegmentFor]

def imageDigest (image : Image) : Digest :=
  digest "DREGG.CARRIED-SEGMENT.IMAGE/v1" (DurableReceiverCodec.encode image)

/-- Includes every exact recorded intent, not just transaction IDs or a caller's
receipt list. Original signed envelopes and effects remain in those records. -/
def originIndexDigest (image : Image) : Digest :=
  digest "DREGG.CARRIED-SEGMENT.ORIGINS/v1"
    ((StreamCodec.list DurableReceiverCodec.intentStream).encode image.accepted)

def writesDigest (writes : List (CellId × List UInt8)) : Digest :=
  digest "DREGG.CARRIED-SEGMENT.WRITES/v1"
    ((StreamCodec.list (StreamCodec.product digestStream bytesStream)).encode writes)

def seedIdentity (seed : Seed) : Digest :=
  digest "DREGG.NATIVE-HOST.GENESIS/v1" (DurableReceiverCodec.seedStream.encode seed)

def pointOf (loaded : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) : Point :=
  ⟨loaded.height, loaded.worldRoot, loaded.chain⟩

/-- The operator key is deliberately an independent caller-owned trust pin.
This checker never promotes a key found in the body into that pin. -/
def checkBody (expectedSource : Identity) (trustedOperator : List UInt8)
    (loaded : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (body : Body) (changes : List (CellId × List UInt8)) : Except String Unit := do
  if body.source != expectedSource then throw "carry source identity differs from trusted source"
  if body.cut != pointOf loaded then throw "carry cut is not the exact loaded source head"
  if loaded.logStart != NativeHostCodec.logRoot0 body.source.domain body.source.semantics loaded.image.seed then
    throw "carry source log is not rooted in the source profile"
  if body.source.genesis != seedIdentity loaded.image.seed then throw "carry source genesis mismatch"
  if body.sourceImage != imageDigest loaded.image then throw "carry source image mismatch"
  if body.originIndex != originIndexDigest loaded.image then throw "carry origin/receipt index mismatch"
  if body.writes != writesDigest changes then throw "carry writes mismatch"
  if body.target.domain != body.source.domain || body.target.genesis != body.source.genesis then
    throw "this carry preserves the original domain and genesis"
  if body.target.semantics == body.source.semantics then throw "same-profile upgrade is not this carry"
  if !body.sourceCapsule.wellFormed || !body.targetCapsule.wellFormed then throw "malformed capsule pin"
  if trustedOperator.length != 32 || body.operatorPublicKey != trustedOperator then
    throw "carry operator was not independently authorized"
  if body.nonce.length != 32 then throw "carry nonce must contain 32 bytes"
  if changes.isEmpty || !decide (changes.map Prod.fst).Nodup then throw "empty or duplicate carry writes"
  -- Version 1 has one source-owned semantic transformation; callers cannot name
  -- a permissive arbitrary function. The IO receiver computes these changes.
  if body.transformation != 1 then throw "unsupported carry transformation"

def carryWrites (before : DataSnapshot ResourceBirthCodec.rootBytes)
    (changes : List (CellId × List UInt8)) : List DataWrite :=
  changes.map fun (identifier, bytes) =>
    ⟨identifier, before.model.roots identifier, ResourceBirthCodec.rootBytes bytes, bytes⟩

/-- Zero charge means a schema cut cannot refresh or debit any allowance lane.
It claims no fresh user nullifier; its stable transaction ID handles cut retry. -/
def intent (before : DataSnapshot ResourceBirthCodec.rootBytes) (body : Body)
    (changes : List (CellId × List UInt8)) : DataIntent ResourceBirthCodec.rootBytes where
  transactionId := body.id
  writes := carryWrites before changes
  readGuards := []
  nullifiers := []
  exactCharge := fun _ => 0
  event := ⟨1, body.target.domain, body.id, body.bytes⟩
  subject := none
  postRootsBound := by
    intro write member
    obtain ⟨⟨identifier, bytes⟩, _, rfl⟩ := List.mem_map.mp member
    rfl
  guardsReadOnly := by simp

/-- These are preservation statements about the ACTUAL shared installer. -/
theorem install_consumed (before : DataSnapshot ResourceBirthCodec.rootBytes)
    (body : Body) (changes : List (CellId × List UInt8)) :
    (DataSnapshot.install before (intent before body changes)).model.consumed =
      before.model.consumed := by
  funext nullifier
  simp [DataSnapshot.install, DurableCommitProtocol.Snapshot.install, intent, DataIntent.erase]

theorem install_allowance (before : DataSnapshot ResourceBirthCodec.rootBytes)
    (body : Body) (changes : List (CellId × List UInt8)) :
    (DataSnapshot.install before (intent before body changes)).model.available =
      before.model.available := by
  funext lane
  simp [DataSnapshot.install, DurableCommitProtocol.Snapshot.install, intent, DataIntent.erase]

theorem install_journal (before : DataSnapshot ResourceBirthCodec.rootBytes)
    (body : Body) (changes : List (CellId × List UInt8)) :
    (DataSnapshot.install before (intent before body changes)).model.journal =
      ((intent before body changes).transactionId, (intent before body changes).erase) ::
        before.model.journal := rfl

theorem install_history (before : DataSnapshot ResourceBirthCodec.rootBytes)
    (body : Body) (changes : List (CellId × List UInt8)) :
    (DataSnapshot.install before (intent before body changes)).model.history =
      before.model.history ++ [(intent before body changes).erase.event] := rfl

/-- Preserve every original byte and its ordering. No regenerated genesis,
filtered origin index, balance reset or journal reset exists on this path. -/
def targetImage (source : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (body : Body) (changes : List (CellId × List UInt8)) : Image :=
  source.image.append (intent source.snapshot body changes)

theorem target_seed (source : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (body : Body) (changes : List (CellId × List UInt8)) :
    (targetImage source body changes).seed = source.image.seed := rfl

theorem target_prefix (source : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (body : Body) (changes : List (CellId × List UInt8)) :
    (targetImage source body changes).accepted.take source.height = source.image.accepted := by
  simp [targetImage, Image.append, DurableReceiverIO.Loaded.height]

def buildTarget (expectedSource : Identity) (trustedOperator : List UInt8)
    (source : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes)
    (body : Body) (changes : List (CellId × List UInt8)) :
    Except String (DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes) := do
  checkBody expectedSource trustedOperator source body changes
  -- Replays the same byte-level executor over the complete original journal,
  -- then the one carry record. Semantic readmission is capsule-dispatched.
  DurableReceiverIO.loadImage ResourceBirthCodec.rootBytes
    (NativeHostCodec.logRoot0 body.target.domain body.target.semantics source.image.seed)
    (targetImage source body changes)

end Minidregg.Kernel.CarriedSegment
