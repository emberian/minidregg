module

public import Kernel.GenericSimplex
public import Compiler.DurableReceiverCodec

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

@[expose] public section

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
/-- The five kind tags; any other natural is refused (it used to decode as
`.ready`). -/
def kindStream : StreamCodec Kind :=
  StreamCodec.retract StreamCodec.nat kindTag kindOfTag (by intro kind; cases kind <;> rfl)

def messageStream : StreamCodec Message :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product kindStream argumentStream)))
    (fun m => (m.sender, m.view, m.kind, m.value))
    (fun (s,v,k,a) => ⟨s,v,k,a⟩)
    (by intro m; cases m; rfl)
/-- `messageStream` is canonical: tag aliases and trailing bytes have no
decoding (`decodeMessage_canonical`). -/
def decodeMessage (bytes : Bytes) : Option Message := messageStream.toLawful.decode bytes
theorem decodeMessage_canonical {bytes : Bytes} {m : Message}
    (decoded : decodeMessage bytes = some m) : messageStream.encode m = bytes :=
  messageStream.toLawful_canonical bytes m decoded
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
/-- Each arm decodes its payload canonically and the tag selects the arm, so a
decoded input is the input of exactly that event (`decodeInput_canonical`). -/
def decodeInput (e : Event) : Option Input :=
  match e.tag with
  | 0 => return .delivery (← decodeMessage e.payload)
  | 1 => return .tick (← StreamCodec.nat.toLawful.decode e.payload)
  | 2 => return .checked (← blockStream.toLawful.decode e.payload)
  | 3 => some (.offer e.payload)
  | 4 => if e.payload.isEmpty then some .poll else none
  | 5 => do
      let (t,m) ← (StreamCodec.product StreamCodec.nat messageStream).toLawful.decode e.payload
      return .deliveryAt t m
  | _ => none
theorem decodeInput_canonical {e : Event} {input : Input}
    (decoded : decodeInput e = some input) : encodeInput input = e := by
  obtain ⟨tag, payload⟩ := e
  rcases tag with _ | _ | _ | _ | _ | _ | tag <;>
    simp only [decodeInput, bind, Option.bind] at decoded
  · cases m : decodeMessage payload with
    | none => simp [m] at decoded
    | some message =>
      simp [m, pure] at decoded; subst decoded
      simp [encodeInput, decodeMessage_canonical m]
  · cases t : StreamCodec.nat.toLawful.decode payload with
    | none => simp [t] at decoded
    | some tick =>
      simp [t, pure] at decoded; subst decoded
      simp [encodeInput, StreamCodec.toLawful_canonical _ _ _ t]
  · cases b : blockStream.toLawful.decode payload with
    | none => simp [b] at decoded
    | some block =>
      simp [b, pure] at decoded; subst decoded
      simp [encodeInput, StreamCodec.toLawful_canonical _ _ _ b]
  · simp at decoded; subst decoded; rfl
  · by_cases empty : payload.isEmpty
    · simp [empty] at decoded; subst decoded
      simp [encodeInput, List.isEmpty_iff.mp empty]
    · simp [empty] at decoded
  · cases d : (StreamCodec.product StreamCodec.nat messageStream).toLawful.decode payload with
    | none => simp [d] at decoded
    | some pair =>
      obtain ⟨t, m⟩ := pair
      simp [d, pure] at decoded; subst decoded
      simp [encodeInput, StreamCodec.toLawful_canonical _ _ _ d]
  · cases decoded
#assert_axioms decodeMessage_canonical
#assert_axioms decodeInput_canonical
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

/-! ## Engine state image (journal checkpoints)

A checkpoint stores the replayed `State` itself, field by field, so a reopen
decodes it instead of replaying every input since genesis. -/

def viewStream : StreamCodec View :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product argumentStream
      (StreamCodec.product StreamCodec.bool (StreamCodec.product StreamCodec.bool
      (StreamCodec.product argumentStream (StreamCodec.product (StreamCodec.list argumentStream)
      (StreamCodec.product (StreamCodec.list argumentStream) (StreamCodec.product (StreamCodec.list argumentStream)
      (StreamCodec.product (StreamCodec.list blockStream) (StreamCodec.product StreamCodec.bool
      (StreamCodec.product argumentStream (StreamCodec.list messageStream))))))))))))
    (fun v => (v.number,v.proposal,v.voted,v.disableRequested,v.sentCommit,v.sentCandidates,
      v.sentReadyCore,v.sentReadyRelay,v.prepared,v.disabled,v.committed,v.received))
    (fun (a,b,c,d,e,f,g,h,i,j,k,l) => ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩) (by intro v; cases v; rfl)

abbrev AuditWire := Nat × Nat × Nat × Option Message × Block

def auditWire : AuditEvent → AuditWire
  | .send m => (0,0,0,some m,[])
  | .prepare party view block => (1,party,view,none,block)
  | .disable party view => (2,party,view,none,[])
  | .commit party view block => (3,party,view,none,block)
  | .idle => (4,0,0,none,[])

def auditOfWire : AuditWire → AuditEvent
  | (tag,party,view,m,block) => match tag with
    | 0 => .send (m.getD default)
    | 1 => .prepare party view block
    | 2 => .disable party view
    | 3 => .commit party view block
    | _ => .idle

/-- The wires `auditWire` produces: a known tag, and the fields that tag does
not carry left at their one spelling (zero, `none`, empty). Every other wire is
refused (an unknown tag used to decode as `.idle`, and unused fields were
dropped). A shape check, not a re-encode. -/
def auditWireOk : AuditWire → Bool
  | (0, 0, 0, some _, []) => true
  | (1, _, _, none, _) => true
  | (2, _, _, none, []) => true
  | (3, _, _, none, _) => true
  | (4, 0, 0, none, []) => true
  | _ => false

def auditEventStream : StreamCodec AuditEvent :=
  StreamCodec.xmap
    (StreamCodec.refine
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat (StreamCodec.product (StreamCodec.option messageStream) blockStream))))
      (fun wire => auditWireOk wire = true))
    (fun event => ⟨auditWire event, by cases event <;> rfl⟩)
    (fun wire => auditOfWire wire.val)
    (by intro e; cases e <;> rfl)
    (by
      rintro ⟨⟨tag, party, view, m, block⟩, ok⟩
      apply Subtype.ext
      rcases tag with _ | _ | _ | _ | _ | tag <;> rcases party with _ | party <;>
        rcases view with _ | view <;> rcases m with _ | m <;> rcases block with _ | ⟨first, block⟩ <;>
        first | rfl | cases ok)

def stateStream : StreamCodec State :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.list viewStream) (StreamCodec.product (StreamCodec.list blockStream)
      (StreamCodec.product (StreamCodec.list bytesStream) (StreamCodec.product (StreamCodec.list messageStream)
      (StreamCodec.product (StreamCodec.list auditEventStream) (StreamCodec.product (StreamCodec.list blockStream)
      (StreamCodec.product blockStream (StreamCodec.product StreamCodec.bool
      (StreamCodec.product StreamCodec.bool StreamCodec.nat)))))))))))))
    (fun s => (s.self,s.current,s.deadline,s.now,s.views,s.checked,s.offers,s.outbox,s.audit,
      s.delivered,s.committedTip,s.needsPoll,s.failed,s.lastCommitted))
    (fun (a,b,c,d,e,f,g,h,i,j,k,l,m,n) => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩) (by intro s; cases s; rfl)
end Minidregg.Compiler.GenericSimplexCodec
