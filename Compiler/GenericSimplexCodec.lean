module

public import Kernel.GenericSimplex
public import Kernel.GenericSimplexRelative
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
open Minidregg.Kernel.GenericSimplexRelative in
/-- A message as it travels and as the journal keeps it: the sender's height, the block as
the payloads above it, and for a COMMIT the signed statement. -/
def wireMessageStream : StreamCodec WireMessage :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product kindStream (StreamCodec.product StreamCodec.nat
        (StreamCodec.product argumentStream
          (StreamCodec.option (StreamCodec.product StreamCodec.nat bytesStream)))))))
    (fun m => (m.sender, m.view, m.kind, m.height, m.value, m.statement))
    (fun (s,v,k,h,a,t) => ⟨s,v,k,h,a,t⟩)
    (by intro m; cases m; rfl)
open Minidregg.Kernel.GenericSimplexRelative in
/-- What a journal records: an input of the running replica, the driver's acknowledgement
that it handed outputs to its transport, or the application's that it took committed
payloads. Replay applies each in order (`GenericSimplexIO.applyEntry`). -/
inductive Entry where
  | input (input : WireInput)
  | flush (sends owed : Nat)
  | consume (count : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited
open Minidregg.Kernel.GenericSimplexRelative in
def encodeEntry : Entry → Event
  | .input (.delivery m) => ⟨0,wireMessageStream.encode m⟩
  | .input (.tick t) => ⟨1,StreamCodec.nat.encode t⟩
  | .input (.checked h b) => ⟨2,(StreamCodec.product StreamCodec.nat blockStream).encode (h,b)⟩
  | .input (.offer b) => ⟨3,b⟩
  | .input .poll => ⟨4,[]⟩
  | .input (.deliveryAt t m) => ⟨5,(StreamCodec.product StreamCodec.nat wireMessageStream).encode (t,m)⟩
  | .flush s o => ⟨6,(StreamCodec.product StreamCodec.nat StreamCodec.nat).encode (s,o)⟩
  | .consume n => ⟨7,StreamCodec.nat.encode n⟩
open Minidregg.Kernel.GenericSimplexRelative in
/-- Each arm decodes its payload canonically and the tag selects the arm, so a decoded entry
is the entry of exactly that event (`decodeEntry_canonical`). -/
def decodeEntry (e : Event) : Option Entry :=
  match e.tag with
  | 0 => return .input (.delivery (← wireMessageStream.toLawful.decode e.payload))
  | 1 => return .input (.tick (← StreamCodec.nat.toLawful.decode e.payload))
  | 2 => do
      let (h,b) ← (StreamCodec.product StreamCodec.nat blockStream).toLawful.decode e.payload
      return .input (.checked h b)
  | 3 => some (.input (.offer e.payload))
  | 4 => if e.payload.isEmpty then some (.input .poll) else none
  | 5 => do
      let (t,m) ← (StreamCodec.product StreamCodec.nat wireMessageStream).toLawful.decode e.payload
      return .input (.deliveryAt t m)
  | 6 => do
      let (s,o) ← (StreamCodec.product StreamCodec.nat StreamCodec.nat).toLawful.decode e.payload
      return .flush s o
  | 7 => return .consume (← StreamCodec.nat.toLawful.decode e.payload)
  | _ => none
theorem decodeEntry_canonical {e : Event} {entry : Entry}
    (decoded : decodeEntry e = some entry) : encodeEntry entry = e := by
  obtain ⟨tag, payload⟩ := e
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag <;>
    simp only [decodeEntry, bind, Option.bind] at decoded
  · cases m : wireMessageStream.toLawful.decode payload with
    | none => simp [m] at decoded
    | some message =>
      simp [m, pure] at decoded; subst decoded
      simp [encodeEntry, StreamCodec.toLawful_canonical _ _ _ m]
  · cases t : StreamCodec.nat.toLawful.decode payload with
    | none => simp [t] at decoded
    | some tick =>
      simp [t, pure] at decoded; subst decoded
      simp [encodeEntry, StreamCodec.toLawful_canonical _ _ _ t]
  · cases d : (StreamCodec.product StreamCodec.nat blockStream).toLawful.decode payload with
    | none => simp [d] at decoded
    | some pair =>
      obtain ⟨h, b⟩ := pair
      simp [d, pure] at decoded; subst decoded
      simp [encodeEntry, StreamCodec.toLawful_canonical _ _ _ d]
  · simp at decoded; subst decoded; rfl
  · by_cases empty : payload.isEmpty
    · simp [empty] at decoded; subst decoded
      simp [encodeEntry, List.isEmpty_iff.mp empty]
    · simp [empty] at decoded
  · cases d : (StreamCodec.product StreamCodec.nat wireMessageStream).toLawful.decode payload with
    | none => simp [d] at decoded
    | some pair =>
      obtain ⟨t, m⟩ := pair
      simp [d, pure] at decoded; subst decoded
      simp [encodeEntry, StreamCodec.toLawful_canonical _ _ _ d]
  · cases d : (StreamCodec.product StreamCodec.nat StreamCodec.nat).toLawful.decode payload with
    | none => simp [d] at decoded
    | some pair =>
      obtain ⟨s, o⟩ := pair
      simp [d, pure] at decoded; subst decoded
      simp [encodeEntry, StreamCodec.toLawful_canonical _ _ _ d]
  · cases n : StreamCodec.nat.toLawful.decode payload with
    | none => simp [n] at decoded
    | some count =>
      simp [n, pure] at decoded; subst decoded
      simp [encodeEntry, StreamCodec.toLawful_canonical _ _ _ n]
  · cases decoded
#assert_axioms decodeMessage_canonical
#assert_axioms decodeEntry_canonical
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
/-- A quorum of COMMIT signatures on one statement: the view, and the chain as its length
and running digest. It carries no payload: a holder reads the chain it is for from what it
already holds (`GenericSimplexIO.VerifiedCommit.Reads`). -/
structure Certificate where
  context : Context
  view : Nat
  length : Nat
  digest : Bytes
  signers : List Attestation
  deriving DecidableEq, BEq, Repr, Inhabited
def attestationStream : StreamCodec Attestation :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat bytesStream)
    (fun a => (a.signer,a.signature)) (fun (s,b) => ⟨s,b⟩) (by intro a; cases a; rfl)
def certificateStream : StreamCodec Certificate :=
  StreamCodec.xmap
    (StreamCodec.product contextStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product bytesStream (StreamCodec.list attestationStream)))))
    (fun c => (c.context,c.view,c.length,c.digest,c.signers))
    (fun (c,v,l,d,s) => ⟨c,v,l,d,s⟩) (by intro c; cases c; rfl)
/-- cSHAKE256 customization of the chain digest: "minidregg/simplex/chain". -/
def chainSeparator : Bytes :=
  [109,105,110,105,100,114,101,103,103,47,115,105,109,112,108,101,120,47,99,104,97,105,110]
/-- cSHAKE256 customization of the application half of the digest: "minidregg/simplex/history". -/
def historySeparator : Bytes :=
  [109,105,110,105,100,114,101,103,103,47,115,105,109,112,108,101,120,47,104,105,115,116,111,114,121]
/-- The running digest of an application history: the nonempty payloads of a chain, in
order. A holder of the source records alone computes it, with no knowledge of where the
protocol's empty payloads fell. -/
def historyExtend (digest payload : Bytes) : Bytes :=
  (Minidregg.Compiler.Sp800185Cshake256.hash historySeparator (digest ++ bytesStream.encode payload)).bytes
def historyDigest (context : Context) : Minidregg.Kernel.GenericSimplexRelative.ChainDigest where
  origin := (Minidregg.Compiler.Sp800185Cshake256.hash historySeparator (contextStream.encode context)).bytes
  extend := historyExtend
/-- The running digest of a domain's chain (`GenericSimplexRelative.ChainDigest`): 64 bytes,
two running cSHAKE256 digests side by side. The first 32 are over every payload (the exact
consensus ancestry, empty protocol payloads included); the last 32 are `historyDigest` of
the nonempty payloads (`chainDigest_history`). Both origins bind the context, so one
domain's digest is not another's; each payload enters length-prefixed, so the chain's split
into payloads is bound. Extending it is at most two cSHAKE256 calls over 32 bytes and the
payload. -/
def chainDigest (context : Context) : Minidregg.Kernel.GenericSimplexRelative.ChainDigest where
  origin := (Minidregg.Compiler.Sp800185Cshake256.hash chainSeparator (contextStream.encode context)).bytes ++
    (historyDigest context).origin
  extend := fun digest payload =>
    (Minidregg.Compiler.Sp800185Cshake256.hash chainSeparator (digest.take 32 ++ bytesStream.encode payload)).bytes ++
      (if payload.isEmpty then digest.drop 32 else historyExtend (digest.drop 32) payload)
/-- The application half of a chain digest. -/
def historyHalf (digest : Bytes) : Bytes := digest.drop 32
theorem chainDigest_over_history (context : Context) (run : Block) (digest : Bytes) :
    historyHalf ((chainDigest context).over digest run) =
      (historyDigest context).over (historyHalf digest) (applicationHistory run) := by
  induction run generalizing digest with
  | nil => rfl
  | cons payload rest ih =>
    have step : historyHalf ((chainDigest context).extend digest payload) =
        if payload.isEmpty then historyHalf digest else historyExtend (historyHalf digest) payload := by
      simp only [chainDigest, historyHalf]
      rw [List.drop_left' (Minidregg.Compiler.Sp800185Cshake256.Output.length_exact _)]
    show historyHalf ((chainDigest context).over ((chainDigest context).extend digest payload) rest) = _
    rw [ih, step]
    by_cases empty : payload.isEmpty
    · simp [applicationHistory, empty]
    · simp [applicationHistory, empty, Minidregg.Kernel.GenericSimplexRelative.ChainDigest.over, historyDigest]
/-- **The application half of a chain's digest is the digest of its application history.**
A COMMIT statement therefore binds the source records a chain orders, to a reader who holds
only those records. -/
theorem chainDigest_history (context : Context) (chain : Block) :
    historyHalf ((chainDigest context).of chain) =
      (historyDigest context).of (applicationHistory chain) := by
  unfold Minidregg.Kernel.GenericSimplexRelative.ChainDigest.of
  rw [chainDigest_over_history]
  congr 1
#assert_axioms chainDigest_history
/-- What a COMMIT signature is over: the context, the view, and the chain the COMMIT is for
as its length (every payload, empty protocol payloads included) and its running digest.
Nothing in it depends on the height a block is written from, so members at different
heights sign the same bytes for the same chain. Version 4: the digest is `chainDigest`'s 64
bytes (version 3 signed the 32-byte chain half alone; version 2 the whole chain). -/
def commitStatementBytes (context : Context) (view length : Nat) (digest : Bytes) : Bytes :=
  [77,73,78,73,45,83,73,77,80,76,69,88,45,67,79,77,77,73,84,45,83,69,78,68,4] ++
    (StreamCodec.product contextStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat bytesStream))).encode (context,view,length,digest)
/-- A transferable signature witnesses a durable COMMIT protocol send. It does
not require the signer to have received a COMMIT quorum itself. The statement for a whole
chain: a holder of the chain up to any height computes the same bytes from its own digest
and the payloads above it (`ChainDigest.over`). -/
def commitmentBytes (context : Context) (view : Nat) (block : Block) : Bytes :=
  commitStatementBytes context view block.length ((chainDigest context).of block)
/-- A transferable COMMIT signature, kept by the statement it signs. The block a COMMIT
carries travels with its delivery (`WireMessage`); the signature is over the statement alone,
so one kept signature serves the COMMIT written from any height. -/
structure CommitWitness where
  view : Nat
  length : Nat
  digest : Bytes
  attestation : Attestation
  deriving DecidableEq, BEq, Repr
def commitWitnessStream : StreamCodec CommitWitness :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream attestationStream)))
    (fun w => (w.view,w.length,w.digest,w.attestation))
    (fun (v,l,d,a) => ⟨v,l,d,a⟩) (by intro w; cases w; rfl)
/-- The witness signs this COMMIT: same signer, view and statement. -/
def CommitWitness.signs (w : CommitWitness) (m : Minidregg.Kernel.GenericSimplexRelative.WireMessage) : Bool :=
  m.kind == .commit && m.sender == w.attestation.signer && m.view == w.view &&
    m.statement == some (w.length,w.digest)

/-! ## Engine state image (journal checkpoints)

A checkpoint stores the replayed `Replica` itself, field by field, so a reopen
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
      (StreamCodec.product StreamCodec.bool (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.list messageStream) (StreamCodec.product (StreamCodec.list StreamCodec.nat)
      (StreamCodec.product (StreamCodec.list (StreamCodec.product StreamCodec.nat messageStream))
      (StreamCodec.list (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))))))))))))))
    (fun s => (s.self,s.current,s.deadline,s.now,s.views,s.checked,s.offers,s.outbox,s.audit,
      s.delivered,s.committedTip,s.needsPoll,s.failed,s.lastCommitted,s.floorEvidence,s.served,s.relay,s.ahead))
    (fun (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r) => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r⟩) (by intro s; cases s; rfl)
open Minidregg.Kernel.GenericSimplexRelative in
/-- The running replica: the engine's state above its committed height, and what it keeps
beside it. Its size does not depend on the committed height. -/
def replicaStream : StreamCodec Replica :=
  StreamCodec.xmap
    (StreamCodec.product stateStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product
        (StreamCodec.list (StreamCodec.product StreamCodec.nat
          (StreamCodec.product bytesStream (StreamCodec.list messageStream))))
      (StreamCodec.product (StreamCodec.list wireMessageStream)
      (StreamCodec.product (StreamCodec.list wireMessageStream)
      (StreamCodec.product (StreamCodec.list (StreamCodec.product StreamCodec.nat wireMessageStream))
        blockStream))))))))
    (fun r => (r.core,r.height,r.digest,r.records,r.evidence,r.far,r.sends,r.owed,r.committed))
    (fun (a,b,c,d,e,f,g,h,i) => ⟨a,b,c,d,e,f,g,h,i⟩) (by intro r; cases r; rfl)
end Minidregg.Compiler.GenericSimplexCodec
