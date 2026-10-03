/- Explicit source-owned worker credential and signed current-home projection.
Opaque credential identity is not interpreted as a public key. The exact
subject/key binding is authored in the protected source control payload. -/
import Compiler.PortableHomeTransferFrame
namespace Minidregg.Compiler.PortableHomeWorkerContext
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.PortableHomeTransfer
set_option autoImplicit false
structure WorkerCredential where
  credentialId : List UInt8
  principal : Principal
  deriving DecidableEq

def credentialStream : StreamCodec WorkerCredential :=
  StreamCodec.xmap (StreamCodec.product bytesStream PortableHomeTransferCodec.principalStream)
    (fun c => (c.credentialId,c.principal)) (fun (i,p) => ⟨i,p⟩)
    (by intro c; cases c; rfl)
structure Projection where
  pin : PortableHomeTransferFrame.Pin
  home : List UInt8
  host : List UInt8
  credential : List UInt8
  privateGeneration : Nat
  privateDescriptor : List UInt8
  epoch : Nat
  phase : Phase
  deriving DecidableEq

def pinStream : StreamCodec PortableHomeTransferFrame.Pin :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product (HyperdocumentCodec.identifierStream .v1 .atom) digestStream))
    (fun p => (p.cell,p.atom,p.schema)) (fun (c,a,s) => ⟨c,a,s⟩)
    (by intro p; cases p; rfl)
def projectionStream : StreamCodec Projection :=
  StreamCodec.xmap (StreamCodec.product pinStream
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
      PortableHomeTransferCodec.phaseStream)))))))
    (fun p => (p.pin,p.home,p.host,p.credential,p.privateGeneration,p.privateDescriptor,p.epoch,p.phase))
    (fun (pin,h,host,c,g,d,e,p) => ⟨pin,h,host,c,g,d,e,p⟩)
    (by intro p; cases p; rfl)

def framed {α : Type} (domain : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
  ResourceBirthCodec.strictCodec {
    encode := fun value => domain ++ stream.encode value
    decode := fun bytes => if bytes.take domain.length = domain then
      stream.toLawful.decode (bytes.drop domain.length) else none
    decode_encode := by
      intro value
      have exact := stream.toLawful.decode_encode value
      change stream.toLawful.decode (stream.encode value) = some value at exact
      simp [exact] }
def credentialCodec : LawfulCodec WorkerCredential :=
  framed "DREGG.PORTABLE.HOME-WORKER/v1".toUTF8.toList credentialStream
def projectionCodec : LawfulCodec Projection :=
  framed "DREGG.PORTABLE.HOME-DISPATCH-PROJECTION/v1".toUTF8.toList projectionStream

def project (pin : PortableHomeTransferFrame.Pin) (state : State) : Projection :=
  ⟨pin,state.home,state.currentHost,state.currentCredential,state.privateGeneration,
    state.privateDescriptor,state.epoch,state.phase⟩
def DispatchAllowed (state : State) : Prop := state.phase = .serving ∨ FreshWork state
instance (state : State) : Decidable (DispatchAllowed state) := by
  unfold DispatchAllowed FreshWork; infer_instance

@[simp] theorem credential_roundtrip (c : WorkerCredential) :
    credentialCodec.decode (credentialCodec.encode c) = some c := credentialCodec.decode_encode c
@[simp] theorem projection_roundtrip (p : Projection) :
    projectionCodec.decode (projectionCodec.encode p) = some p := projectionCodec.decode_encode p
#assert_axioms credential_roundtrip
#assert_axioms projection_roundtrip
end Minidregg.Compiler.PortableHomeWorkerContext
