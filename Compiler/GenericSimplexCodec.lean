import Kernel.GenericSimplex
import Compiler.DurableReceiverCodec
namespace Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false
def blockStream : StreamCodec Block := StreamCodec.list bytesStream
def argumentStream : StreamCodec Argument := StreamCodec.option blockStream
def kindTag : Kind → Nat
  | .propose => 0 | .vote => 1 | .commit => 2 | .candidate => 3 | .ready => 4
def kindOfTag : Nat → Kind
  | 0 => .propose | 1 => .vote | 2 => .commit | 3 => .candidate | _ => .ready
def messageStream : StreamCodec Message :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat argumentStream)))
    (fun m => (m.sender, m.view, kindTag m.kind, m.value))
    (fun (s,v,k,a) => ⟨s,v,kindOfTag k,a⟩)
    (by intro m; cases m with | mk s v k a => cases k <;> rfl)
/-- Canonical decoding rejects tag aliases and trailing bytes. -/
def decodeMessage (bytes : Bytes) : Option Message := do
  let m ← messageStream.toLawful.decode bytes
  if messageStream.encode m == bytes then some m else none
structure Event where
  tag : Nat
  payload : Bytes
  deriving DecidableEq, BEq, Repr, Inhabited
def eventStream : StreamCodec Event :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat bytesStream)
    (fun e => (e.tag,e.payload)) (fun (t,p) => ⟨t,p⟩)
    (by intro e; cases e; rfl)
def encodeInput : Input → Event
  | .delivery m => ⟨0,messageStream.encode m⟩
  | .tick t => ⟨1,StreamCodec.nat.encode t⟩
  | .deliveryAt t m => ⟨5,(StreamCodec.product StreamCodec.nat messageStream).encode (t,m)⟩
  | .checked b => ⟨2,blockStream.encode b⟩
  | .offer b => ⟨3,b⟩
  | .poll => ⟨4,[]⟩
def decodeInput (e : Event) : Option Input := do
  let input ← match e.tag with
    | 0 => return .delivery (← decodeMessage e.payload)
    | 1 => return .tick (← StreamCodec.nat.toLawful.decode e.payload)
    | 2 => return .checked (← blockStream.toLawful.decode e.payload)
    | 3 => some (.offer e.payload)
    | 4 => if e.payload.isEmpty then some .poll else none
    | 5 => do
        let (t,m) ← (StreamCodec.product StreamCodec.nat messageStream).toLawful.decode e.payload
        return .deliveryAt t m
    | _ => none
  if encodeInput input == e then some input else none
/-- Five fields since the timeout-backoff epoch. A four-field pre-epoch
Context does not decode: such journals and contexts refuse to load. -/
def configStream : StreamCodec Config :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))))
    (fun c => (c.parties,c.faults,c.timeout,c.pumpBudget,c.backoffCap))
    (fun (n,f,t,p,b) => ⟨n,f,t,p,b⟩) (by intro c; cases c; rfl)
/-- Exact deployment/epoch/instance bytes, not an unqualified digest. -/
structure Context where
  scope : Bytes
  epoch : Nat
  instanceBytes : Bytes
  config : Config
  publicKeys : List Bytes
  deriving DecidableEq, BEq, Repr, Inhabited
def contextStream : StreamCodec Context :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream (StreamCodec.product configStream (StreamCodec.list bytesStream)))))
    (fun c => (c.scope,c.epoch,c.instanceBytes,c.config,c.publicKeys))
    (fun (s,e,i,c,p) => ⟨s,e,i,c,p⟩) (by intro c; cases c; rfl)
def Context.wellFormed (c : Context) : Bool :=
  c.config.wellFormed && c.publicKeys.length == c.config.parties &&
    c.publicKeys.eraseDups.length == c.publicKeys.length &&
    c.publicKeys.all (fun k => k.length == 1952)
structure Attestation where
  signer : Nat
  signature : Bytes
  deriving DecidableEq, BEq, Repr, Inhabited
structure Certificate where
  context : Context
  view : Nat
  block : Block
  signers : List Attestation
  deriving DecidableEq, BEq, Repr, Inhabited
def attestationStream : StreamCodec Attestation :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat bytesStream)
    (fun a => (a.signer,a.signature)) (fun (s,b) => ⟨s,b⟩) (by intro a; cases a; rfl)
def certificateStream : StreamCodec Certificate :=
  StreamCodec.xmap
    (StreamCodec.product contextStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product blockStream (StreamCodec.list attestationStream))))
    (fun c => (c.context,c.view,c.block,c.signers))
    (fun (c,v,b,s) => ⟨c,v,b,s⟩) (by intro c; cases c; rfl)
/-- A transferable signature witnesses a durable COMMIT protocol send. It does
not require the signer to have received a COMMIT quorum itself. Version 2
separates this statement from the obsolete local-output attestation. -/
def commitmentBytes (context : Context) (view : Nat) (block : Block) : Bytes :=
  [77,73,78,73,45,83,73,77,80,76,69,88,45,67,79,77,77,73,84,45,83,69,78,68,2] ++
    (StreamCodec.product contextStream (StreamCodec.product StreamCodec.nat blockStream)).encode
      (context,view,block)
def exportable (s : State) (view : Nat) (block : Block) : Bool :=
  !s.failed && view > 0 && !block.isEmpty &&
    (viewAt s view).sentCommit == some block &&
    s.audit.contains (.send ⟨s.self,view,.commit,some block⟩)
/-- Transferable COMMIT evidence is retained with the actual delivery event. -/
structure CommitWitness where
  view : Nat
  block : Block
  attestation : Attestation
  deriving DecidableEq, BEq, Repr
def commitWitnessStream : StreamCodec CommitWitness :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product blockStream attestationStream))
    (fun w => (w.view,w.block,w.attestation))
    (fun (v,b,a) => ⟨v,b,a⟩) (by intro w; cases w; rfl)
def CommitWitness.message (w : CommitWitness) : Message :=
  ⟨w.attestation.signer,w.view,.commit,some w.block⟩
end Minidregg.Compiler.GenericSimplexCodec
