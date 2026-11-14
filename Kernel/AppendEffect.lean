/-
# `Kernel/AppendEffect.lean` — the stream append, declared

`appendEffect` is the registered operation at code 2 (JSON `append`): one entry recorded at the
head of a room's stream. Its cell is the stream's head (`StreamCell.headLayout`, packed
`⟨.stream, cell⟩`); an object's append verb authorizes it; it pins no root (`commutes`: the
entry goes at the head the receiver loads, and nothing in the signed request names that head).

One plan (`appendPlan`) decides everything: the two length bounds, the channel law at the
loaded head (`DomainEpoch.admitAppend`), the head's presence and its `room` binding, the `ref`
bound, then the loaded head and the entry at its next position. The semantics is the plan's one
guarded head write; the declaration's birth (`Effect.born`) is the plan's entry as a fresh
entry cell. So an admitted append has exactly one birth and a refused one has none
(`appendBorn_iff`).

The record holds the admission height, which a member neither signs nor is served, so the
declaration states no member patch.

* `appendSpec_complete`: every admitted append writes only the head's field and replays.
* `appendPlan_ok`: an admitted plan's head is the loaded one and its entry is the next.
* `JointSlots.streamSlots_unjoint`: no slot of its view is a joint key.
-/
module

public import Kernel.ResourceEffect
public import Kernel.ScalarEffect
public import Kernel.ResourceGrammarJson
public import Kernel.DomainEpochLaw
public import Compiler.StreamCell
public import Compiler.ResourceAuthorityProjection
public import Effects.Revival.EngineProofs
public import Theory.AssertAxioms

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

@[expose] public section

namespace Minidregg.Kernel.DeclaredResourceController

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Effects
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- **The transaction's marker**: one operation per (signer, nonce) under the domain and the
profile. The payload bytes are not in it: a replay that swaps a payload under the same nonce is
the same operation, which the exact ingress lookup refuses as a conflicting use. A different
ingress family cannot carry a signature over (the signed bytes are framed by the family); it
can only collide with the original operation. Collision resistance is a cryptographic
assumption, not codec injectivity. -/
def transactionMarker (domain semantics : Digest) (subject : SubjectId) (nonce : Nat) : Nat :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.IDENTITY/v3".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream StreamCodec.nat))).encode
      (domain, semantics, subject, nonce))).digest.value

/-- What an append refuses, beside the header's refusals. -/
inductive AppendRefusal where
  /-- The topic is longer than `StreamCell.maxTopicBytes`. -/
  | streamTopic
  /-- The payload is longer than `StreamCell.maxPayloadBytes`. -/
  | streamPayload
  /-- CH-EPOCH: a channel record's append refused by the channel law, the clause named. -/
  | channel (reason : DomainEpoch.Refusal)
  /-- The loaded stream cell holds no head. -/
  | headAbsent
  /-- The head is a fleet topic's: only the fleet receiver appends to it. -/
  | topicHead
  /-- The `ref` names an entry of the same stream beyond its head: a reference points back at
  an existing entry, never at one still in flight. -/
  | streamRef
  deriving DecidableEq, Repr

def AppendRefusal.name : AppendRefusal → String
  | .streamTopic => "streamTopic"
  | .streamPayload => "streamPayload"
  | .channel _ => "channel"
  | .headAbsent => "headAbsent"
  | .topicHead => "topicHead"
  | .streamRef => "streamRef"

/-- The channel law's clause, as the detail of a `channel` refusal. -/
def AppendRefusal.detail : AppendRefusal → ByteArray
  | .channel reason => (reprStr reason).toUTF8
  | _ => .empty

/-- The record an append stores: the request's entry plus the signing subject, the admission
height and the exact transaction id. -/
def appendRecord (ctx : EffectCtx) (request : StreamCell.Append) : StreamCell.StreamRecord :=
  ⟨ctx.subject, ctx.ambient.height,
    ⟨transactionMarker ctx.snapshot.domain ctx.semantics ctx.subject ctx.nonce⟩, request.entry⟩

/-- **The append's plan** at a loaded head store: the loaded head and the entry at its next
position, or the first refusal. An append is computed at the stream cell it meets: its channel
is admitted at that cell and its entry goes at that cell's head. -/
def appendPlan (ctx : EffectCtx) (request : StreamCell.Append)
    (store : Store StreamCell.headLayout) :
    Except AppendRefusal (StreamCell.Head × StreamCell.Entry) :=
  if request.topic.length ≤ StreamCell.maxTopicBytes then
    if request.payload.length ≤ StreamCell.maxPayloadBytes then
      match DomainEpoch.admitAppend store ctx.subject request with
      | .error reason => .error (.channel reason)
      | .ok () =>
        match StreamCell.headOf store with
        | none => .error .headAbsent
        | some head =>
          -- A fleet topic's head is appended only by the fleet receiver.
          if head.binding = .room then
            if request.ref.any (fun r => r.1 == ctx.target && head.count < r.2) then
              .error .streamRef
            else .ok (head, StreamCell.appendEntry ctx.target head (appendRecord ctx request))
          else .error .topicHead
    else .error .streamPayload
  else .error .streamTopic

/-- An admitted plan's head is the loaded head and its entry is the one at the next position. -/
theorem appendPlan_ok {ctx : EffectCtx} {request : StreamCell.Append}
    {store : Store StreamCell.headLayout} {head : StreamCell.Head} {entry : StreamCell.Entry}
    (ok : appendPlan ctx request store = .ok (head, entry)) :
    StreamCell.headOf store = some head ∧
      entry = StreamCell.appendEntry ctx.target head (appendRecord ctx request) := by
  unfold appendPlan at ok
  split at ok
  · split at ok
    · split at ok
      · cases ok
      · split at ok
        · cases ok
        · rename_i loadedHead loaded
          split at ok
          · split at ok
            · cases ok
            · cases ok; exact ⟨loaded, rfl⟩
          · cases ok
    · cases ok
  · cases ok

/-- The semantics: the plan's one guarded head write. -/
def appendSem (ctx : EffectCtx) (request : StreamCell.Append)
    (store : Store StreamCell.headLayout) :
    Except AppendRefusal (Patch StreamCell.headLayout) :=
  (appendPlan ctx request store).map fun planned => [StreamCell.headWriteOp planned.1 planned.2]

/-- An admitted append's patch is the head write of the loaded head and the next entry. -/
theorem appendSem_ok {ctx : EffectCtx} {request : StreamCell.Append}
    {store : Store StreamCell.headLayout} {ps : Patch StreamCell.headLayout}
    (ok : appendSem ctx request store = .ok ps) :
    ∃ head, StreamCell.headOf store = some head ∧
      appendPlan ctx request store = .ok (head,
        StreamCell.appendEntry ctx.target head (appendRecord ctx request)) ∧
      ps = [StreamCell.headWriteOp head
        (StreamCell.appendEntry ctx.target head (appendRecord ctx request))] := by
  unfold appendSem at ok
  cases planned : appendPlan ctx request store with
  | error refusal => rw [planned] at ok; cases ok
  | ok pair =>
    obtain ⟨head, entry⟩ := pair
    rw [planned] at ok
    obtain ⟨loaded, rfl⟩ := appendPlan_ok planned
    exact ⟨head, loaded, rfl, (Except.ok.inj ok).symm⟩

/-- **The entry an append gives birth to**: the plan's, when the plan admits. -/
def appendedEntry (ctx : EffectCtx) (request : StreamCell.Append)
    (store : Store StreamCell.headLayout) : Option StreamCell.Entry :=
  match appendPlan ctx request store with
  | .ok planned => some planned.2
  | .error _ => none

/-- The fresh entry cell: its id is the hash of the head cell and the position, its content
the one entry. -/
def entryBirth (entry : StreamCell.Entry) : Nat × PackedCell Registry :=
  (StreamCell.entryCellId entry.head entry.sequence,
    ⟨.streamEntry, materialize StreamCell.entryMaterializer (StreamCell.entryStore entry)⟩)

/-- An append gives birth to an entry exactly when its semantics admits. -/
theorem appendBorn_iff (ctx : EffectCtx) (request : StreamCell.Append)
    (store : Store StreamCell.headLayout) :
    (appendedEntry ctx request store).isSome = true ↔ ∃ ps, appendSem ctx request store = .ok ps := by
  unfold appendedEntry appendSem
  cases appendPlan ctx request store with
  | error refusal =>
    constructor
    · intro born; cases born
    · rintro ⟨_, ok⟩; cases ok
  | ok planned =>
    constructor
    · intro _; exact ⟨_, rfl⟩
    · intro _; rfl

/-- **`append_entry_at_next`.** The entry of an admitted append is the one at the loaded head's
next position, with the head's tail as its parent. -/
theorem appendedEntry_at_next {ctx : EffectCtx} {request : StreamCell.Append}
    {store : Store StreamCell.headLayout} {entry : StreamCell.Entry}
    (born : appendedEntry ctx request store = some entry) :
    ∃ head, StreamCell.headOf store = some head ∧
      entry = ⟨ctx.target, head.count + 1, head.tail, appendRecord ctx request⟩ := by
  unfold appendedEntry at born
  cases planned : appendPlan ctx request store with
  | error refusal => rw [planned] at born; cases born
  | ok pair =>
    obtain ⟨head, planEntry⟩ := pair
    rw [planned] at born
    obtain ⟨loaded, rfl⟩ := appendPlan_ok planned
    exact ⟨head, loaded, (Option.some.inj born).symm⟩

/-- The policy slots of one stream append: the entry's fields as request slots, so a stream law
can name its author (`request/subject`), its topics (`request/topic/…`) or its addressee
(`request/to`); plus the position. -/
def streamSlots (request : StreamCell.Append) (before : Store StreamCell.headLayout) :
    List (String × Int) :=
  [("request/topic/length", Int.ofNat request.topic.length),
   ("stream/sequence", Int.ofNat (StreamCell.nextSeqOf before))] ++
  Minidregg.Compiler.ResourceAuthorityProjection.bytesSlots "request/topic" 0 request.topic ++
  (match request.recipient with
    | some subject => [("request/to", Int.ofNat subject.value)]
    | none => []) ++
  (match request.ref with
    | some (cell, sequence) => [("request/ref/cell", Int.ofNat cell), ("request/ref/sequence", Int.ofNat sequence)]
    | none => [])

namespace JointSlots

theorem bytesSlots_unjoint (stem : String) (c : Char) (hc : stem.toList.head? = some c) (ne : c ≠ 'j') :
    ∀ (offset : Nat) (bytes : List UInt8), Unjoint (ResourceAuthorityProjection.bytesSlots stem offset bytes)
  | _, [] => by intro p hp; simp [ResourceAuthorityProjection.bytesSlots] at hp
  | offset, byte :: rest => by
      intro p hp
      simp only [ResourceAuthorityProjection.bytesSlots, List.mem_cons] at hp
      rcases hp with rfl | hp
      · have : (s!"{stem}/{offset}").toList.head? = some c := by
          show (stem ++ "/" ++ toString offset).toList.head? = some c
          simp only [String.append_assoc]
          exact head_append _ _ _ hc
        rw [this]; simpa using ne
      · exact bytesSlots_unjoint stem c hc ne (offset + 1) rest p hp

/-- A stream append's slots (`request/topic…`, `stream/sequence`, `request/to`,
`request/ref/…`) are not joint keys. -/
theorem streamSlots_unjoint (request : StreamCell.Append) (before : Store StreamCell.headLayout) :
    Unjoint (streamSlots request before) := by
  unfold streamSlots
  refine unjoint_append _ _ (unjoint_append _ _ (unjoint_append _ _ ?_
    (bytesSlots_unjoint "request/topic" 'r' (by decide) (by decide) _ _)) ?_) ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> decide
  · intro p hp
    cases h : request.recipient with
    | none => simp [h] at hp
    | some subject =>
        simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp; dsimp only; decide
  · intro p hp
    cases h : request.ref with
    | none => simp [h] at hp
    | some pair =>
        obtain ⟨cell, sequence⟩ := pair
        simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> decide

end JointSlots

/-- The verb an append is authorized under: an object's append; any other role's ordinary write
(which the header then refuses, since only an object is accepted). -/
def appendVerb : (kind : ResourceKind) → Verb kind
  | .object => .appendObject
  | kind => DeclaredResourceScalar.ordinaryVerb kind

theorem appendVerb_writes (kind : ResourceKind) : observes (appendVerb kind) = false := by
  cases kind <;> rfl

/-- **The append's declaration**: an object's stream head at the append's schema version; no
root is pinned; no rotate; the one field is the head. -/
def appendSpec : Revival.EffectSpec EffectCtx (Revival.storeSubstrate StreamCell.headLayout)
    StreamCell.Append AppendRefusal where
  opStream := StreamCell.appendStream
  refusalName := AppendRefusal.name
  refusalDetail := AppendRefusal.detail
  accepts kind := kind == .object
  version := StreamCell.commandVersion
  sem := appendSem
  rotate _ _ := []
  rotated _ := false
  field _ := .body
  amount _ _ := 0
  frame _ := {.body}
  verb kind _ := appendVerb kind
  view _ request before _ := streamSlots request before
  commutes _ := true

/-- The head write of the loaded head is valid at the loaded store: its guard is that head. -/
theorem appendWrite_valid {store : Store StreamCell.headLayout} {head : StreamCell.Head}
    (loaded : StreamCell.headOf store = some head) (entry : StreamCell.Entry) :
    Patch.ValidFrom store [StreamCell.headWriteOp head entry] :=
  ⟨⟨rfl, loaded⟩, trivial⟩

open Minidregg.Effects.Revival in
/-- **The append declaration is complete**: an admitted append writes only the head's field,
and its one guarded write replays (its guard is the loaded head). -/
theorem appendSpec_complete : appendSpec.Complete := by
  intro ctx request store ps ok
  obtain ⟨head, loaded, _, rfl⟩ := appendSem_ok (show appendSem ctx request store = .ok ps from ok)
  refine ⟨fun loc _ _ => Finset.mem_singleton_self _, ?_⟩
  have replayed := store_run_validFrom (L := StreamCell.headLayout) _ store
    (appendWrite_valid loaded (StreamCell.appendEntry ctx.target head (appendRecord ctx request)))
  exact (congrArg Option.isSome replayed).trans rfl

/-! ## The JSON face -/

/-- The JSON face: `{"type": "append", "topic", "payload", "to", "ref"}`, the topic and payload
in hex. -/
def appendOfJson (path : String) (json : Lean.Json) : Except String StreamCell.Append := do
  let obj ← EffectJson.exactObject path ["type", "topic", "payload", "to", "ref"] json
  let topic ← ContentJson.decodeHex (path ++ ".topic") (← EffectJson.field path "topic" obj)
  let payload ← ContentJson.decodeHex (path ++ ".payload") (← EffectJson.field path "payload" obj)
  let recipient ← EffectJson.optional (path ++ ".to") EffectJson.nat (← EffectJson.field path "to" obj)
  let ref ← EffectJson.optional (path ++ ".ref") ResourceGrammarJson.streamRef
    (← EffectJson.field path "ref" obj)
  pure ⟨topic, payload, recipient.map SubjectId.mk, ref⟩

/-- What an inbox shows of an append: the two lengths. The text rides in the signed command and
is not repeated beside it. -/
def appendToJson (request : StreamCell.Append) : List (String × Lean.Json) :=
  [("topicBytes", EffectJson.decimal request.topic.length),
   ("payloadBytes", EffectJson.decimal request.payload.length)]

/-- **The stream append, as the registry binds it** (code 2, JSON `append`). The declared cell is
a stream's head; the role is checked by the declaration's `accepts`. -/
def appendEffect : Effect where
  name := "append"
  L := StreamCell.headLayout
  wire := StreamCell.headWire
  O := StreamCell.Append
  R := AppendRefusal
  decO := inferInstance
  spec := appendSpec
  pack := fun _ cell => ⟨.stream, cell⟩
  unpack := fun _ packed =>
    match packed with
    | ⟨.stream, value⟩ => some value
    | _ => none
  toJson := appendToJson
  ofJson := appendOfJson
  display := fun _ =>
    ["stream append: one entry (the cell keeps its digest; the text rides in this signed command)"]
  refusalText := fun name detail =>
    if name == "channel" then "(" ++ (String.fromUTF8? detail).getD "" ++ ")" else ""
  born := fun ctx request store => (appendedEntry ctx request store).map entryBirth
  born_admitted := by
    intro ctx request store stated
    exact (appendBorn_iff ctx request store).mp (by simpa using stated)
  unpack_pack := fun _ _ => rfl
  pack_unpack := by
    intro kind packed cell selected
    split at selected
    · cases selected; rfl
    · cases selected
  observes_silent := by
    intro ctx request s ps observed _
    have writes := appendVerb_writes ctx.kind
    rw [show appendSpec.verb ctx.kind request = appendVerb ctx.kind from rfl, writes] at observed
    cases observed
  complete := appendSpec_complete
  view_unjoint := fun _ request before _ => JointSlots.streamSlots_unjoint request before

/-- No member patch: the record holds the admission height. -/
theorem append_member_unstated : appendEffect.member = none := rfl

/-- An append pins no root. -/
theorem append_commutes (request : StreamCell.Append) : appendEffect.spec.commutes request = true := rfl

/-- **An append's birth is complete**: every admitted append gives birth to its entry cell. -/
theorem append_born_complete {ctx : EffectCtx} {request : StreamCell.Append}
    {store : Store StreamCell.headLayout} {ps : Patch StreamCell.headLayout}
    (ok : appendEffect.spec.sem ctx request store = .ok ps) :
    ∃ entry, appendedEntry ctx request store = some entry ∧
      appendEffect.born ctx request store = some (entryBirth entry) := by
  have born := (appendBorn_iff ctx request store).mpr ⟨ps, ok⟩
  cases found : appendedEntry ctx request store with
  | none => rw [found] at born; cases born
  | some entry => exact ⟨entry, rfl, by show (appendedEntry ctx request store).map entryBirth = _; rw [found]; rfl⟩

/-- **What the controller runs for an append**: the plan's refusal under the declaration's
name, or the plan's one head write run at the loaded store. -/
theorem append_run (code : Nat) (ctx : EffectCtx) (request : StreamCell.Append)
    (store : Store StreamCell.headLayout) :
    appendEffect.run code ctx request store =
      match appendPlan ctx request store with
      | .error reason => .error (.refused code reason.name reason.detail)
      | .ok planned => .ok (Patch.run store [StreamCell.headWriteOp planned.1 planned.2]) := by
  cases planned : appendPlan ctx request store with
  | error reason =>
    have sem : appendEffect.spec.sem ctx request store = .error reason := by
      show appendSem ctx request store = _
      unfold appendSem; rw [planned]; rfl
    exact appendEffect.run_refused sem
  | ok pair =>
    obtain ⟨head, entry⟩ := pair
    obtain ⟨loaded, rfl⟩ := appendPlan_ok planned
    have sem : appendEffect.spec.sem ctx request store = .ok [StreamCell.headWriteOp head
        (StreamCell.appendEntry ctx.target head (appendRecord ctx request))] := by
      show appendSem ctx request store = _
      unfold appendSem; rw [planned]; rfl
    exact appendEffect.run_ok sem (appendWrite_valid loaded _)

/-- An admitted append's derived patch is the one guarded write of the loaded head. -/
theorem append_patch {ctx : EffectCtx} {request : StreamCell.Append}
    {store : Store StreamCell.headLayout} {head : StreamCell.Head} {entry : StreamCell.Entry}
    (admitted : appendPlan ctx request store = .ok (head, entry)) :
    appendEffect.patch ctx request store = [StreamCell.headWriteOp head entry] := by
  have emitted : appendEffect.spec.emitted ctx request store =
      .ok [StreamCell.headWriteOp head entry] := by
    show (appendSem ctx request store).map (fun ps => ps ++ []) = _
    unfold appendSem
    rw [admitted]
    rfl
  unfold Effect.patch
  simp only [emitted]
  rfl

/-- An admitted append's birth is its plan's entry, as a fresh entry cell. -/
theorem append_born {ctx : EffectCtx} {request : StreamCell.Append}
    {store : Store StreamCell.headLayout} {head : StreamCell.Head} {entry : StreamCell.Entry}
    (admitted : appendPlan ctx request store = .ok (head, entry)) :
    appendEffect.born ctx request store = some (entryBirth entry) := by
  show (appendedEntry ctx request store).map entryBirth = _
  unfold appendedEntry
  rw [admitted]
  rfl

/-- A topic over the bound is refused at every context and store. -/
theorem appendPlan_longTopic (ctx : EffectCtx) (request : StreamCell.Append)
    (store : Store StreamCell.headLayout)
    (long : ¬ request.topic.length ≤ StreamCell.maxTopicBytes) :
    appendPlan ctx request store = .error .streamTopic := by
  unfold appendPlan
  rw [if_neg long]

#assert_axioms append_run append_patch append_born appendPlan_longTopic
#assert_axioms appendSpec_complete appendBorn_iff appendedEntry_at_next append_born_complete
  JointSlots.streamSlots_unjoint

end Minidregg.Kernel.DeclaredResourceController
