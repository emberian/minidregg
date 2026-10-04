/- Wire pieces shared by answer slots (`Kernel.AnswerSlot`) and the kernel
activity record (`Kernel.ObjectiveActivity`): the domain-separated digest, the
checkpoint bytes (the Core4 checkpoint tokens of `Theory.ObjectiveBendCheckpoint`
under one prefix stream codec), first-order `Data` bytes, strict framed codecs,
and the one constructor of a root-bound `DataIntent` from post images.

Nothing here decides anything: it is the byte layer the two kernel modules
judge with. Every decoder is strict (a decoded value re-encodes to exactly the
bytes it came from), so a cell holds one spelling of each value. -/
import Kernel.DurableDataIntent
import Theory.ObjectiveBendCheckpoint
import Theory.ObjectiveBendDemandData
import Theory.ObjectiveBendTyping
import Compiler.Tower256ConcreteBackend
import Compiler.PolicyRecordCodec
import Compiler.ResourceBirthCodec
import Theory.AssertAxioms
import Theory.ResourceCost

namespace Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.ObjectiveBendCheckpoint (Token Tokens encodeState decodeState)
open Minidregg.Theory.ObjectiveBendDemandMachine (State)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
set_option autoImplicit false

abbrev Bytes := List UInt8

/-- One domain-separated cSHAKE256 digest. -/
def tagged (customization : String) (input : Bytes) : Digest :=
  (Sp800185Cshake256.hash customization.toUTF8.toList input).digest

/-! ## Small stream codecs -/

def unitStream : StreamCodec Unit where
  encode _ := []
  decodePrefix bytes := some ((), bytes)
  decodePrefix_encode := by intro value suffix; cases value; rfl

def subjectStream : StreamCodec SubjectId :=
  StreamCodec.xmap StreamCodec.nat (fun subject => subject.value) (fun value => ⟨value⟩)
    (by intro subject; cases subject; rfl)

def readGuardStream : StreamCodec ReadGuard :=
  StreamCodec.xmap (StreamCodec.product digestStream digestStream)
    (fun guard => (guard.cellId, guard.expectedRoot)) (fun pair => ⟨pair.1, pair.2⟩)
    (by intro guard; cases guard; rfl)

def stringStream : StreamCodec String := PolicyRecordCodec.stringStream

/-- A frame prefix plus a stream codec, strict: decoding refuses any other
spelling of the same value (`ResourceBirthCodec.strictCodec`). -/
def framedRaw {α : Type} (frame : Bytes) (stream : StreamCodec α) : LawfulCodec α where
  encode value := frame ++ stream.encode value
  decode bytes := if bytes.take frame.length = frame then
    stream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro value
    have exact := stream.toLawful.decode_encode value
    change stream.toLawful.decode (stream.encode value) = some value at exact
    simp [exact]

def framed {α : Type} (frame : Bytes) (stream : StreamCodec α) : LawfulCodec α :=
  ResourceBirthCodec.strictCodec (framedRaw frame stream)

theorem framed_roundTrip {α : Type} (frame : Bytes) (stream : StreamCodec α) (value : α) :
    (framed frame stream).decode ((framed frame stream).encode value) = some value :=
  (framed frame stream).decode_encode value

theorem framed_canonical {α : Type} {frame : Bytes} {stream : StreamCodec α} {bytes : Bytes}
    {value : α} (decoded : (framed frame stream).decode bytes = some value) :
    (framed frame stream).encode value = bytes :=
  ResourceBirthCodec.strictCodec_canonical (framedRaw frame stream) decoded

/-! ## Checkpoint bytes

The checkpoint is the exact machine state's token list
(`ObjectiveBendCheckpoint.encodeState`) as one prefix stream; its round trip is
`decodeCheckpoint_checkpointBytes` in `Theory.ObjectiveResumeContract`, from
`state_roundTrip`. -/

def tokenStream : StreamCodec Token :=
  StreamCodec.xmap (StreamCodec.sum StreamCodec.nat stringStream)
    (fun token => match token with | .nat value => .inl value | .text value => .inr value)
    (fun wire => match wire with | .inl value => .nat value | .inr value => .text value)
    (by intro token; cases token <;> rfl)

def tokensStream : StreamCodec Tokens := StreamCodec.list tokenStream

def checkpointBytes (state : State) : Bytes := tokensStream.encode (encodeState state)

def decodeCheckpoint (bytes : Bytes) : Option State := do
  let tokens ← tokensStream.toLawful.decode bytes
  decodeState tokens

theorem checkpointBytes_tokens (state : State) :
    tokensStream.toLawful.decode (checkpointBytes state) = some (encodeState state) :=
  tokensStream.toLawful.decode_encode _

/-- The checkpoint identity bound into the await id and the activity record. -/
def checkpointDigest (bytes : Bytes) : Digest :=
  tagged "DREGG/OBJECTIVE/ACTIVITY/CHECKPOINT/v1" bytes

/-! ## First-order data bytes

`Data` (the values Plans, responses, declared state and answers are made of) as
tokens, with its own round trip. -/

mutual
def encodeData : Data → Tokens
  | .natural value => [.nat 0, .nat value]
  | .boolean value => [.nat 1, .nat (if value then 1 else 0)]
  | .label value => [.nat 2, .text value]
  | .record fields => .nat 3 :: encodeDataFields fields
  | .variant label payload => .nat 4 :: .text label :: encodeData payload
def encodeDataFields : List (String × Data) → Tokens
  | [] => [.nat 0]
  | (name, value) :: rest => .nat 1 :: .text name :: (encodeData value ++ encodeDataFields rest)
end

mutual
def decodeData : Nat → Tokens → Option (Data × Tokens)
  | 0, _ => none
  | _ + 1, .nat 0 :: .nat value :: rest => some (.natural value, rest)
  | _ + 1, .nat 1 :: .nat 0 :: rest => some (.boolean false, rest)
  | _ + 1, .nat 1 :: .nat 1 :: rest => some (.boolean true, rest)
  | _ + 1, .nat 2 :: .text value :: rest => some (.label value, rest)
  | fuel + 1, .nat 3 :: rest => do
      let (fields, rest) ← decodeDataFields fuel rest
      pure (.record fields, rest)
  | fuel + 1, .nat 4 :: .text label :: rest => do
      let (payload, rest) ← decodeData fuel rest
      pure (.variant label payload, rest)
  | _ + 1, _ => none
def decodeDataFields : Nat → Tokens → Option (List (String × Data) × Tokens)
  | 0, _ => none
  | _ + 1, .nat 0 :: rest => some ([], rest)
  | fuel + 1, .nat 1 :: .text name :: rest => do
      let (value, rest) ← decodeData fuel rest
      let (others, rest) ← decodeDataFields fuel rest
      pure ((name, value) :: others, rest)
  | _ + 1, _ => none
end

mutual
theorem data_roundTrip : ∀ (data : Data) (fuel : Nat) (rest : Tokens),
    (encodeData data).length ≤ fuel → decodeData fuel (encodeData data ++ rest) = some (data, rest)
  | .natural value, fuel + 1, rest, _ => by simp [encodeData, decodeData]
  | .boolean value, fuel + 1, rest, _ => by cases value <;> simp [encodeData, decodeData]
  | .label value, fuel + 1, rest, _ => by simp [encodeData, decodeData]
  | .record fields, fuel + 1, rest, h => by
      simp only [encodeData, List.length_cons] at h
      simp [encodeData, decodeData, dataFields_roundTrip fields fuel rest (by omega)]
  | .variant label payload, fuel + 1, rest, h => by
      simp only [encodeData, List.length_cons] at h
      simp [encodeData, decodeData, data_roundTrip payload fuel rest (by omega)]
  | data, 0, rest, h => by cases data <;> simp [encodeData] at h
theorem dataFields_roundTrip : ∀ (fields : List (String × Data)) (fuel : Nat) (rest : Tokens),
    (encodeDataFields fields).length ≤ fuel →
      decodeDataFields fuel (encodeDataFields fields ++ rest) = some (fields, rest)
  | [], fuel + 1, rest, _ => by simp [encodeDataFields, decodeDataFields]
  | (name, value) :: others, fuel + 1, rest, h => by
      simp only [encodeDataFields, List.length_cons, List.length_append] at h
      simp [encodeDataFields, decodeDataFields, List.append_assoc,
        data_roundTrip value fuel _ (by omega), dataFields_roundTrip others fuel rest (by omega)]
  | fields, 0, rest, h => by cases fields <;> simp [encodeDataFields] at h
end

def dataBytes (data : Data) : Bytes := tokensStream.encode (encodeData data)

/-- Strict: the decoded value re-encodes to exactly these bytes. -/
def decodeDataBytes (bytes : Bytes) : Option Data := do
  let tokens ← tokensStream.toLawful.decode bytes
  let (data, rest) ← decodeData (tokens.length + 1) tokens
  if rest.isEmpty && dataBytes data == bytes then some data else none

theorem decodeDataBytes_dataBytes (data : Data) : decodeDataBytes (dataBytes data) = some data := by
  unfold decodeDataBytes
  rw [show tokensStream.toLawful.decode (dataBytes data) = some (encodeData data) from
    tokensStream.toLawful.decode_encode _]
  have decoded := data_roundTrip data ((encodeData data).length + 1) [] (by omega)
  rw [List.append_nil] at decoded
  simp [decoded]

theorem decodeDataBytes_canonical {bytes : Bytes} {data : Data}
    (decoded : decodeDataBytes bytes = some data) : dataBytes data = bytes := by
  unfold decodeDataBytes at decoded
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
  obtain ⟨tokens, _, rest, _, check⟩ := decoded
  split at check
  · rename_i ok
    cases Option.some.inj check
    simp only [Bool.and_eq_true, beq_iff_eq] at ok
    exact ok.2
  · cases check

/-! ## Root-bound intents from post images -/

/-- One post image of one cell, written against the root the admission read. -/
structure Post where
  cell : CellId
  pre : Digest
  bytes : Bytes
  deriving DecidableEq, Repr

def Post.write (rootBytes : Bytes → Digest) (post : Post) : DataWrite :=
  ⟨post.cell, post.pre, rootBytes post.bytes, post.bytes⟩

/-- Guards on cells this intent writes are dropped: the write's own pre-root
CAS already binds them. -/
def readOnly (rootBytes : Bytes → Digest) (posts : List Post) (guards : List ReadGuard) : List ReadGuard :=
  guards.filter fun guard => decide (guard.cellId ∉ (posts.map (Post.write rootBytes)).map DataWrite.cellId)

/-- What the admitting receiver adds to a kernel turn: the guards of the
authority it checked (authority cell, capability laws), its own claims (the
signed marker), the replay event that carries the signed ingress, the signer,
and the exact charge of the turn's footprint. The kernel turn is ONE intent
whatever sealing it carries: `intentOf` below. -/
structure Seal where
  guards : List ReadGuard
  nullifiers : List StableNullifier
  event : StableEvent
  subject : Option SubjectId
  charge : List Post → List ReadGuard → Minidregg.Theory.ResourceCost.Charge

/-- The one constructor of every activity-kernel intent: writes are exactly the
post images, so their roots are bound by construction; the seal's guards and
claims join the kernel's. -/
def intentOf (rootBytes : Bytes → Digest) (transaction : TransactionId) (posts : List Post)
    (guards : List ReadGuard) (nullifiers : List StableNullifier) (sealing : Seal) : DataIntent rootBytes where
  transactionId := transaction
  writes := posts.map (Post.write rootBytes)
  readGuards := readOnly rootBytes posts (guards ++ sealing.guards)
  nullifiers := nullifiers ++ sealing.nullifiers
  exactCharge := sealing.charge posts (readOnly rootBytes posts (guards ++ sealing.guards))
  event := sealing.event
  subject := sealing.subject
  postRootsBound := by
    intro write member
    simp only [List.mem_map] at member
    obtain ⟨post, _, rfl⟩ := member
    rfl
  guardsReadOnly := by
    intro guard member
    exact of_decide_eq_true (List.mem_filter.mp member).2

@[simp] theorem intentOf_nullifiers (rootBytes : Bytes → Digest) (transaction : TransactionId)
    (posts : List Post) (guards : List ReadGuard) (nullifiers : List StableNullifier) (sealing : Seal) :
    (intentOf rootBytes transaction posts guards nullifiers sealing).nullifiers = nullifiers ++ sealing.nullifiers := rfl

@[simp] theorem intentOf_writes (rootBytes : Bytes → Digest) (transaction : TransactionId)
    (posts : List Post) (guards : List ReadGuard) (nullifiers : List StableNullifier) (sealing : Seal) :
    (intentOf rootBytes transaction posts guards nullifiers sealing).writes =
      posts.map (Post.write rootBytes) := rfl

@[simp] theorem intentOf_transaction (rootBytes : Bytes → Digest) (transaction : TransactionId)
    (posts : List Post) (guards : List ReadGuard) (nullifiers : List StableNullifier) (sealing : Seal) :
    (intentOf rootBytes transaction posts guards nullifiers sealing).transactionId = transaction := rfl

/-- A kernel claim: version, the activity kernel's domain, a tagged id, and the
exact claim bytes (byte-distinct claims stay distinct under a colliding hash). -/
def domain : Digest := tagged "DREGG/OBJECTIVE/ACTIVITY/DOMAIN/v1" []

def claim (kind : String) (bytes : Bytes) : StableNullifier :=
  { codecVersion := 1, domain := domain,
    nullifierId := tagged ("DREGG/OBJECTIVE/ACTIVITY/CLAIM/" ++ kind) bytes,
    canonicalBytes := kind.toUTF8.toList ++ bytes }

def event (kind : String) (bytes : Bytes) : StableEvent :=
  { codecVersion := 1, domain := domain,
    eventId := tagged ("DREGG/OBJECTIVE/ACTIVITY/EVENT/" ++ kind) bytes,
    canonicalBytes := kind.toUTF8.toList ++ bytes }

#assert_axioms framed_roundTrip
#assert_axioms framed_canonical
#assert_axioms checkpointBytes_tokens
#assert_axioms data_roundTrip
#assert_axioms decodeDataBytes_dataBytes
#assert_axioms decodeDataBytes_canonical
end Minidregg.Kernel.ObjectiveActivityWire
