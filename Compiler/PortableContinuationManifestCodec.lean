/- Canonical portable custody bytes over the ONE durable image codec.
Internal source image/custody bytes are private. Participant ACK frames contain
only public identity, point and participant/key, not the private manifest. -/
import Kernel.PortableContinuationManifest
import Compiler.DurableReceiverCodec

namespace Minidregg.Compiler.PortableContinuationManifestCodec
open Minidregg.Kernel.PortableContinuationManifest
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableReceiverCodec
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

def identityStream : StreamCodec Identity :=
  StreamCodec.xmap (StreamCodec.product digestStream (StreamCodec.product digestStream digestStream))
    (fun identity => (identity.domain, identity.semantics, identity.expectedSeed))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩) (by intro identity; cases identity; rfl)

def pointStream : StreamCodec Minidregg.Kernel.ReceiptContinuity.Point :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat digestStream)
    (fun point => (point.height, point.worldRoot)) (fun tuple => ⟨tuple.1, tuple.2⟩)
    (by intro point; cases point; rfl)

def prefixStream : StreamCodec Prefix :=
  StreamCodec.xmap (StreamCodec.product identityStream
    (StreamCodec.product bytesStream (StreamCodec.list bytesStream)))
    (fun prefix => (prefix.identity, prefix.seed, prefix.records))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩) (by intro prefix; cases prefix; rfl)

def artifactStream : StreamCodec Artifact :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun artifact => (artifact.coordinate, artifact.exactInventory))
    (fun tuple => ⟨tuple.1, tuple.2⟩) (by intro artifact; cases artifact; rfl)

def manifestStream : StreamCodec Manifest :=
  StreamCodec.xmap (StreamCodec.product prefixStream (StreamCodec.product bytesStream
    (StreamCodec.product pointStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream (StreamCodec.list artifactStream))))))
    (fun manifest => (manifest.prefix, manifest.image, manifest.point, manifest.generation,
      manifest.predecessor, manifest.artifacts))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1,
      tuple.2.2.2.2.1, tuple.2.2.2.2.2⟩) (by intro manifest; cases manifest; rfl)

def frame : Bytes := "DREGG.PORTABLE.CUSTODY/v1".toUTF8.toList

def framedManifest : StreamCodec Manifest :=
  StreamCodec.xmap (StreamCodec.product bytesStream manifestStream)
    (fun manifest => (frame, manifest)) Prod.snd (by intro manifest; rfl)

def encode (manifest : Manifest) : Bytes := framedManifest.encode manifest

def decode (bytes : Bytes) : Option Manifest := do
  let manifest ← framedManifest.toLawful.decode bytes
  if encode manifest = bytes then some manifest else none

@[simp] theorem decode_encode (manifest : Manifest) : decode (encode manifest) = some manifest := by
  have roundtrip := framedManifest.toLawful.decode_encode manifest
  change framedManifest.toLawful.decode (encode manifest) = some manifest at roundtrip
  simp [decode, roundtrip]

theorem decode_canonical {bytes : Bytes} {manifest : Manifest}
    (accepted : decode bytes = some manifest) : encode manifest = bytes := by
  unfold decode at accepted
  cases decoded : framedManifest.toLawful.decode bytes with
  | none => simp [decoded] at accepted
  | some result =>
    simp only [decoded, bind, Option.bind] at accepted
    split at accepted
    · cases accepted; assumption
    · cases accepted

def prefixOf (identity : Identity) (image : Minidregg.Kernel.DurableReceiver.Image) : Prefix :=
  ⟨identity, seedStream.encode image.seed, image.accepted.map intentStream.encode⟩

def pointOf (identity : Identity) (image : Minidregg.Kernel.DurableReceiver.Image) :
    Minidregg.Kernel.ReceiptContinuity.Point :=
  ⟨image.accepted.length, NativeHostCodec.worldRoot identity.domain identity.semantics image⟩

def fromImage (identity : Identity) (image : Minidregg.Kernel.DurableReceiver.Image)
    (generation : Nat) (predecessor : Bytes) (artifacts : List Artifact) : Manifest :=
  ⟨prefixOf identity image, DurableReceiverCodec.encode image, pointOf identity image,
    generation, predecessor, artifacts⟩

/-- Bind EVERY source record and cell to the public endpoint. Replay/signature
admission uses NativeHostReplay and the trusted expected-seed configuration;
this check alone is not a source-authorized install or a history audit. -/
def bindImage (manifest : Manifest) : Option Minidregg.Kernel.DurableReceiver.Image := do
  let image ← DurableReceiverCodec.decode manifest.image
  if manifest.prefix = prefixOf manifest.prefix.identity image ∧
      manifest.point = pointOf manifest.prefix.identity image then some image else none

theorem bindImage_exact {manifest : Manifest} {image : Minidregg.Kernel.DurableReceiver.Image}
    (bound : bindImage manifest = some image) :
    DurableReceiverCodec.encode image = manifest.image ∧
    manifest.prefix = prefixOf manifest.prefix.identity image ∧
    manifest.point = pointOf manifest.prefix.identity image := by
  unfold bindImage at bound
  cases decoded : DurableReceiverCodec.decode manifest.image with
  | none => simp [decoded] at bound
  | some result =>
    simp only [decoded, bind, Option.bind] at bound
    split at bound
    · rename_i checked
      cases bound
      exact ⟨DurableReceiverCodec.decode_canonical decoded, checked.1, checked.2⟩
    · cases bound

def acknowledgementStream : StreamCodec Acknowledgement :=
  StreamCodec.xmap (StreamCodec.product subjectStream (StreamCodec.product bytesStream
    (StreamCodec.product identityStream pointStream)))
    (fun ack => (ack.participant, ack.publicKey, ack.identity, ack.point))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩) (by intro ack; cases ack; rfl)

/-- Domain separation includes source genesis identity and participant/key.
Unlike a full private manifest, this frame is safe to sign/retain as a public
commitment. Signed point alone does not grant any restore/transfer authority. -/
def acknowledgementFrame (ack : Acknowledgement) : Bytes :=
  "DREGG.PORTABLE.PARTICIPANT-ACK/v1".toUTF8.toList ++ acknowledgementStream.encode ack

def successorStream : StreamCodec SuccessorCore :=
  StreamCodec.xmap (StreamCodec.product manifestStream (StreamCodec.product bytesStream
    (StreamCodec.product StreamCodec.nat bytesStream)))
    (fun successor => (successor.retained, successor.targetConfiguration,
      successor.nextGeneration, successor.privateDescriptor))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro successor; cases successor; rfl)

/-- Bytes selected by the existing CURRENT source reservation/decision. Its
opaque certificate/evidence is not part of semantic successor identity. -/
def successorCandidate (request : SuccessorRequest) : Bytes :=
  "DREGG.PORTABLE.SUCCESSOR-CANDIDATE/v1".toUTF8.toList ++ successorStream.encode request.core

theorem successorCore_injective : Function.Injective successorStream.encode := by
  intro left right same
  have decoded := congrArg (fun bytes => successorStream.decodePrefix (bytes ++ [])) same
  rw [successorStream.decodePrefix_encode, successorStream.decodePrefix_encode] at decoded
  exact congrArg Prod.fst (Option.some.inj decoded)

/-- One native selected candidate names ONE complete successor, including the
old full manifest, target config, arbitrary Nat generation and private descriptor.
The authority/retention/fence proof is still the ReadySuccessor join, not these
byte equalities or a new portable journal. -/
theorem one_successor_of_selected_candidate {left right : SuccessorRequest}
    {selected : Bytes} (leftSelected : successorCandidate left = selected)
    (rightSelected : successorCandidate right = selected) : left.core = right.core := by
  apply successorCore_injective
  have same : successorCandidate left = successorCandidate right := leftSelected.trans rightSelected.symm
  unfold successorCandidate at same
  exact List.append_cancel_left same

#assert_axioms successorCore_injective
#assert_axioms one_successor_of_selected_candidate
#assert_axioms decode_encode
#assert_axioms decode_canonical
#assert_axioms bindImage_exact
end Minidregg.Compiler.PortableContinuationManifestCodec
