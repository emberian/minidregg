/-
# Kernel.FnArchiveJournal — the archive outbox and the acknowledged-Message-ID record

One append-only journal per Mini Store, in the same SQLite database as the
durable log and bound by the same head anchor (`MINIANC2`: the anchor commits
to the head of both). Replaying it rebuilds the archive state; every
transition is a pure `apply`.

* **The outbox (N2).** A `signed` event persists the exact authored source and
  both signatures before the first send. A second `signed` for the same
  Message-ID is accepted only byte for byte (an idempotent re-append) and is
  otherwise refused: ML-DSA is randomized, so a re-sign is a conflict. Every
  send reads the persisted bytes (`sendable_persisted`, `signed_stable`), and
  a signature is requested only when no bytes are persisted (`needsSignature`).
* **fn's transport outcome lives here, never in an answer slot.** An
  `acknowledged` event records fn's exit 0 (`:accepted`, `:duplicate`, or a
  lookup that found the exact source); `conflicted` and `refused` record its
  definite refusals. Transient refusals and `Unknown` record nothing: the slot
  stays pending and the same bytes are resent or looked up. Nothing here
  decides an `AnswerSlot` (`Kernel/AnswerSlot.lean` slots are write-once and
  decided only by their decider).
* **The acknowledged record (M1 at the client).** {acceptances Mini observed}
  ⊆ {acknowledgements recovered on reopen} (`acknowledged_recovered`). A
  pending slot after reopen is `Unknown`, resolved by Message-ID lookup or a
  same-bytes resend, never by assuming absence. An acknowledged identity fn
  later cannot serve is evidence against fn, not a Mini loss.
* **Read-back (N11) and the cursor (M2 adapter (b)).** A fetched article is
  exposed only after `FnArchive.extract` accepts it against the acknowledged
  identity; `430 withdrawn` is its own outcome, distinct from absence; the
  follower's cursor advances only past a verified bundle and never skips.
* **The fee.** Bytes Mini publishes to fn are permanent by fn's PRF-088, so
  archive storage is a non-refundable permanent-history fee charged at
  publication, sized by octets and fn transactions, never a deposit. An
  unfunded publication is refused before it is signed (`checkFunded`).
-/
import Kernel.FnArchive
import Compiler.DurableLogTags

namespace Minidregg.Kernel.FnArchiveJournal

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.FnArchive

set_option autoImplicit false

/-! ## Events -/

/-- The persisted signed artifact: what every send of this Message-ID carries. -/
structure Signed where
  identity : Identity
  messageId : String
  source : List UInt8
  edSignature : List UInt8
  mlSignature : List UInt8
  /-- The non-refundable fee charged for this publication. -/
  fee : Nat
  deriving DecidableEq, Repr

/-- How fn's acceptance was observed. -/
inductive Basis where
  /-- `hybrid-author` exit 0, `:accepted`. -/
  | accepted
  /-- `hybrid-author` exit 0, `:duplicate`: fn already held these bytes. -/
  | duplicate
  /-- `ARTICLE <msgid>` served a source that `FnArchive.extract` accepted. -/
  | lookup
  deriving DecidableEq, Repr

structure Ack where
  messageId : String
  identity : Identity
  /-- The fn pin the acceptance was observed under (running image digest and
  the store identity fields Mini pins, opaque here). -/
  pin : List UInt8
  basis : Basis
  deriving DecidableEq, Repr

inductive Event where
  | signed (value : Signed)
  | acknowledged (value : Ack)
  /-- `hybrid-author` exit 1 `conflict`: fn holds another carrier under this
  Message-ID and stored nothing. Mini's persisted carrier is the evidence. -/
  | conflicted (messageId : String)
  /-- A definite, non-transient refusal, with fn's reason word. -/
  | refused (messageId : String) (word : String)
  /-- Read-back answered `430 withdrawn` (or the cursor's `FNWD`): the bytes
  stay in fn; never republished over. -/
  | withdrawn (messageId : String)
  /-- Archive fee funding credited to this Store's archive account. -/
  | funded (amount : Nat) (evidence : List UInt8)
  deriving DecidableEq, Repr

def stringStream : StreamCodec String := PolicyRecordCodec.stringStream

def signedStream : StreamCodec Signed :=
  StreamCodec.xmap
    (StreamCodec.product identityStream (StreamCodec.product stringStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream StreamCodec.nat)))))
    (fun s => (s.identity, s.messageId, s.source, s.edSignature, s.mlSignature, s.fee))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2⟩)
    (by intro s; cases s; rfl)

def basisCode : Basis → Nat
  | .accepted => 0 | .duplicate => 1 | .lookup => 2

def basisOfCode : Nat → Basis
  | 0 => .accepted | 1 => .duplicate | _ => .lookup

def basisStream : StreamCodec Basis :=
  StreamCodec.xmap StreamCodec.nat basisCode basisOfCode (by intro b; cases b <;> rfl)

def ackStream : StreamCodec Ack :=
  StreamCodec.xmap
    (StreamCodec.product stringStream (StreamCodec.product identityStream
      (StreamCodec.product bytesStream basisStream)))
    (fun a => (a.messageId, a.identity, a.pin, a.basis))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩)
    (by intro a; cases a; rfl)

/-- The six event kinds as a nested binary sum. -/
abbrev EventWire :=
  Sum Signed (Sum Ack (Sum String (Sum (String × String) (Sum String (Nat × List UInt8)))))

def eventToWire : Event → EventWire
  | .signed s => .inl s
  | .acknowledged a => .inr (.inl a)
  | .conflicted m => .inr (.inr (.inl m))
  | .refused m w => .inr (.inr (.inr (.inl (m, w))))
  | .withdrawn m => .inr (.inr (.inr (.inr (.inl m))))
  | .funded n e => .inr (.inr (.inr (.inr (.inr (n, e)))))

def eventOfWire : EventWire → Event
  | .inl s => .signed s
  | .inr (.inl a) => .acknowledged a
  | .inr (.inr (.inl m)) => .conflicted m
  | .inr (.inr (.inr (.inl (m, w)))) => .refused m w
  | .inr (.inr (.inr (.inr (.inl m)))) => .withdrawn m
  | .inr (.inr (.inr (.inr (.inr (n, e))))) => .funded n e

def eventStream : StreamCodec Event :=
  StreamCodec.xmap
    (StreamCodec.sum signedStream (StreamCodec.sum ackStream
      (StreamCodec.sum stringStream (StreamCodec.sum (StreamCodec.product stringStream stringStream)
        (StreamCodec.sum stringStream (StreamCodec.product StreamCodec.nat bytesStream))))))
    eventToWire eventOfWire (by intro e; cases e <;> rfl)

/-- The journal record's version word; an unknown word refuses to load. -/
def eventFrame : List UInt8 := "DREGG/FN/ARCHIVE-JOURNAL/v1".toUTF8.toList

def eventCodec : LawfulCodec Event := NativeHostCodec.framed eventFrame eventStream

theorem event_decode_encode (event : Event) :
    eventCodec.decode (eventCodec.encode event) = some event :=
  eventCodec.decode_encode event

theorem event_canonical {bytes : List UInt8} {event : Event}
    (decoded : eventCodec.decode bytes = some event) : eventCodec.encode event = bytes :=
  NativeHostCodec.framed_canonical eventFrame eventStream decoded

/-! ## State -/

inductive Terminal where
  | conflicted
  | refused (word : String)
  deriving DecidableEq, Repr

structure Slot where
  signed : Signed
  ack : Option Ack
  terminal : Option Terminal
  withdrawn : Bool
  deriving DecidableEq, Repr

structure State where
  slots : List Slot
  funded : Nat
  charged : Nat
  deriving DecidableEq, Repr

def State.empty : State := ⟨[], 0, 0⟩

def State.lookup (state : State) (messageId : String) : Option Slot :=
  state.slots.find? (·.signed.messageId == messageId)

inductive Refusal where
  /-- N2: the Message-ID already has persisted signed bytes, and these differ. -/
  | resigned (messageId : String)
  /-- One height range has one identity. -/
  | rangeTaken (first last : Nat)
  | unfunded (fee available : Nat)
  | noSlot (messageId : String)
  | ackIdentity (messageId : String)
  | conflictAfterAck (messageId : String)
  | refusedAfterAck (messageId : String)
  deriving DecidableEq, Repr

def Refusal.word : Refusal → String
  | .resigned m => s!"archive {m} already has persisted signed bytes; a re-sign is a conflict (N2)"
  | .rangeTaken first last => s!"heights {first}..{last} are already signed under another identity"
  | .unfunded fee available =>
      s!"archive publication needs a {fee} fee and {available} is funded; refused before posting"
  | .noSlot m => s!"archive {m} has no persisted signed article"
  | .ackIdentity m => s!"acknowledgement of {m} names another identity than its signed article"
  | .conflictAfterAck m => s!"archive {m} is acknowledged; a later conflict is not fn's answer"
  | .refusedAfterAck m => s!"archive {m} is acknowledged; a later refusal is not fn's answer"

def available (state : State) : Nat := state.funded - state.charged

/-- Replace the slot of `messageId` (there is at most one). -/
def State.update (state : State) (messageId : String) (change : Slot → Slot) : State :=
  { state with slots := state.slots.map fun slot =>
      if slot.signed.messageId == messageId then change slot else slot }

def apply (state : State) : Event → Except Refusal State
  | .signed s =>
      match state.lookup s.messageId with
      | some slot => if slot.signed == s then .ok state else .error (.resigned s.messageId)
      | none =>
          if state.slots.any (fun slot => slot.signed.identity.first == s.identity.first) then
            .error (.rangeTaken s.identity.first s.identity.last)
          else if available state < s.fee then .error (.unfunded s.fee (available state))
          else .ok { state with
            slots := state.slots ++ [⟨s, none, none, false⟩], charged := state.charged + s.fee }
  | .acknowledged a =>
      match state.lookup a.messageId with
      | none => .error (.noSlot a.messageId)
      | some slot =>
          if slot.signed.identity != a.identity then .error (.ackIdentity a.messageId)
          else if slot.ack.isSome then .ok state
          else .ok (state.update a.messageId fun slot => { slot with ack := some a })
  | .conflicted m =>
      match state.lookup m with
      | none => .error (.noSlot m)
      | some slot =>
          if slot.ack.isSome then .error (.conflictAfterAck m)
          else .ok (state.update m fun slot => { slot with terminal := some .conflicted })
  | .refused m word =>
      match state.lookup m with
      | none => .error (.noSlot m)
      | some slot =>
          if slot.ack.isSome then .error (.refusedAfterAck m)
          else .ok (state.update m fun slot => { slot with terminal := some (.refused word) })
  | .withdrawn m =>
      match state.lookup m with
      | none => .error (.noSlot m)
      | some _ => .ok (state.update m fun slot => { slot with withdrawn := true })
  | .funded amount _ => .ok { state with funded := state.funded + amount }

def replay (events : List Event) : Except Refusal State :=
  events.foldlM apply State.empty

/-! ## Replay invariants -/

/-- An invariant every event of `events` preserves holds after replaying them. -/
theorem foldlM_invariant (I : State → Prop) :
    ∀ (events : List Event),
      (∀ event ∈ events, ∀ state state', I state → apply state event = .ok state' → I state') →
      ∀ state state', I state → events.foldlM apply state = .ok state' → I state'
  | [], _, state, state', holds, done => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at done
      exact done ▸ holds
  | event :: rest, step, state, state', holds, done => by
      simp only [List.foldlM_cons, bind, Except.bind] at done
      cases applied : apply state event with
      | error _ => simp [applied] at done
      | ok middle =>
          simp only [applied] at done
          exact foldlM_invariant I rest (fun e member => step e (List.mem_cons_of_mem _ member))
            middle state' (step event (List.mem_cons_self ..) state middle holds applied) done

theorem foldlM_split {events : List Event} {state final : State} {event : Event}
    (member : event ∈ events) (done : events.foldlM apply state = .ok final) :
    ∃ (middle next : State) (after : List Event), apply middle event = .ok next ∧
      after.foldlM apply next = .ok final := by
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  subst split
  rw [List.foldlM_append] at done
  cases first : (before.foldlM apply state : Except Refusal State) with
  | error _ => simp [first, bind, Except.bind] at done
  | ok middle =>
      simp only [first, bind, Except.bind, List.foldlM_cons] at done
      cases applied : apply middle event with
      | error _ => simp [applied] at done
      | ok next =>
          simp only [applied] at done
          exact ⟨middle, next, after, applied, done⟩

/-- Every successful `apply` leaves the state unchanged, appends one fresh
signed slot, rewrites slots through a change that keeps their signed bytes
and their acknowledgement, or credits funding. -/
theorem apply_shape {state state' : State} {event : Event}
    (applied : apply state event = .ok state') :
    state' = state ∨
    (∃ s, event = .signed s ∧ state' = { state with
      slots := state.slots ++ [⟨s, none, none, false⟩], charged := state.charged + s.fee }) ∨
    (∃ (target : String) (change : Slot → Slot), (∀ slot, (change slot).signed = slot.signed) ∧
      (∀ slot, slot.ack.isSome = true → (change slot).ack.isSome = true) ∧
      state' = state.update target change) ∨
    (∃ amount, state' = { state with funded := state.funded + amount }) := by
  cases event with
  | signed s =>
      simp only [apply] at applied
      split at applied
      · split at applied
        · cases applied; exact .inl rfl
        · cases applied
      · split at applied
        · cases applied
        · split at applied
          · cases applied
          · cases applied; exact .inr (.inl ⟨s, rfl, rfl⟩)
  | acknowledged a =>
      simp only [apply] at applied
      split at applied
      · cases applied
      · split at applied
        · cases applied
        · split at applied
          · cases applied; exact .inl rfl
          · cases applied
            exact .inr (.inr (.inl ⟨_, fun slot => { slot with ack := some a },
              fun _ => rfl, fun _ _ => rfl, rfl⟩))
  | conflicted m =>
      simp only [apply] at applied
      split at applied
      · cases applied
      · split at applied
        · cases applied
        · cases applied
          exact .inr (.inr (.inl ⟨_, fun slot => { slot with terminal := some .conflicted },
            fun _ => rfl, fun _ h => h, rfl⟩))
  | refused m w =>
      simp only [apply] at applied
      split at applied
      · cases applied
      · split at applied
        · cases applied
        · cases applied
          exact .inr (.inr (.inl ⟨_, fun slot => { slot with terminal := some (.refused w) },
            fun _ => rfl, fun _ h => h, rfl⟩))
  | withdrawn m =>
      simp only [apply] at applied
      split at applied
      · cases applied
      · cases applied
        exact .inr (.inr (.inl ⟨_, fun slot => { slot with withdrawn := true },
          fun _ => rfl, fun _ h => h, rfl⟩))
  | funded amount evidence =>
      simp only [apply] at applied
      cases applied; exact .inr (.inr (.inr ⟨amount, rfl⟩))

/-! ## N2: persisted bytes are the only bytes ever sent -/

theorem lookup_update (state : State) (target messageId : String) (change : Slot → Slot)
    (keeps : ∀ slot, (change slot).signed = slot.signed) :
    (state.update target change).lookup messageId =
      (state.lookup messageId).map
        (fun slot => if slot.signed.messageId == target then change slot else slot) := by
  unfold State.update State.lookup
  rw [List.find?_map]
  have same : ((fun slot : Slot => slot.signed.messageId == messageId) ∘
      (fun slot => if slot.signed.messageId == target then change slot else slot)) =
      (fun slot : Slot => slot.signed.messageId == messageId) := by
    funext slot
    by_cases hit : slot.signed.messageId = target <;> simp [hit, keeps]
  rw [same]

theorem lookup_update_signed (state : State) (target messageId : String) (change : Slot → Slot)
    (keeps : ∀ slot, (change slot).signed = slot.signed) :
    ((state.update target change).lookup messageId).map (·.signed) =
      (state.lookup messageId).map (·.signed) := by
  rw [lookup_update state target messageId change keeps, Option.map_map]
  congr 1
  funext slot
  by_cases hit : slot.signed.messageId = target <;> simp [hit, keeps]

theorem lookup_append (slots : List Slot) (slot : Slot) (messageId : String) :
    (slots ++ [slot]).find? (·.signed.messageId == messageId) =
      match slots.find? (·.signed.messageId == messageId) with
      | some found => some found
      | none => if slot.signed.messageId == messageId then some slot else none := by
  rw [List.find?_append]
  cases slots.find? (·.signed.messageId == messageId) <;> simp [List.find?_cons]
  split <;> simp_all

/-- Once a Message-ID has persisted signed bytes, no event changes them. -/
theorem signed_stable {state state' : State} {event : Event} {messageId : String}
    {bytes : Signed} (applied : apply state event = .ok state')
    (persisted : (state.lookup messageId).map (·.signed) = some bytes) :
    (state'.lookup messageId).map (·.signed) = some bytes := by
  rcases apply_shape applied with same | ⟨s, _, rfl⟩ | ⟨target, change, keeps, _, rfl⟩ | ⟨_, rfl⟩
  · subst same; exact persisted
  · have found : (state.lookup messageId).isSome := by
      cases h : state.lookup messageId <;> simp_all
    simp only [State.lookup] at found persisted ⊢
    rw [lookup_append]
    cases h : state.slots.find? (·.signed.messageId == messageId) with
    | none => simp [h] at found
    | some f => simpa [h] using persisted
  · rw [lookup_update_signed state target messageId change keeps]; exact persisted
  · exact persisted

/-- A persisted `signed` event is the state's bytes for its Message-ID. -/
theorem apply_signed_lookup {state state' : State} {s : Signed}
    (applied : apply state (.signed s) = .ok state') :
    (state'.lookup s.messageId).map (·.signed) = some s := by
  simp only [apply] at applied
  split at applied
  · rename_i slot found
    split at applied
    · rename_i same
      cases applied
      rw [found]; simpa using same
    · cases applied
  · rename_i none_found
    split at applied
    · cases applied
    · split at applied
      · cases applied
      · cases applied
        simp only [State.lookup] at none_found ⊢
        rw [lookup_append, none_found]
        simp

/-- A re-sign under a persisted Message-ID is refused (ML-DSA is randomized:
fresh signatures over the same source are different bytes). -/
theorem resign_refused {state : State} {slot : Slot} {s : Signed}
    (persisted : state.lookup s.messageId = some slot) (different : slot.signed ≠ s) :
    apply state (.signed s) = .error (.resigned s.messageId) := by
  simp [apply, persisted, different]

/-- **N2.** Every `signed` event in a journal that replays is the state's one
persisted artifact for its Message-ID: every signing ever persisted for a
Message-ID is the same bytes. -/
theorem signed_unique {events : List Event} {state : State} {s : Signed}
    (replayed : replay events = .ok state) (member : .signed s ∈ events) :
    (state.lookup s.messageId).map (·.signed) = some s := by
  obtain ⟨_, next, after, applied, rest⟩ := foldlM_split member replayed
  exact foldlM_invariant (fun st => (st.lookup s.messageId).map (·.signed) = some s) after
    (fun _ _ _ _ holds step => signed_stable step holds) next state
    (apply_signed_lookup applied) rest

/-- What the publisher sends for a Message-ID: the persisted bytes of a slot
that fn has not definitely answered. -/
def sendable (state : State) (messageId : String) : Option Signed :=
  match state.lookup messageId with
  | some slot => if slot.ack.isNone && slot.terminal.isNone then some slot.signed else none
  | none => none

/-- A signature is requested only when no bytes are persisted for the
Message-ID: a resend never re-signs. -/
def needsSignature (state : State) (messageId : String) : Bool := (state.lookup messageId).isNone

theorem slots_persisted (events : List Event) :
    ∀ state, replay events = .ok state → ∀ slot ∈ state.slots, .signed slot.signed ∈ events := by
  intro state replayed
  refine foldlM_invariant (fun st => ∀ slot ∈ st.slots, .signed slot.signed ∈ events) events
    ?_ State.empty state (by simp [State.empty]) replayed
  intro event member st st' holds applied
  rcases apply_shape applied with same | ⟨s, rfl, rfl⟩ | ⟨target, change, keeps, _, rfl⟩ | ⟨_, rfl⟩
  · subst same; exact holds
  · intro slot inSlots
    rcases List.mem_append.mp inSlots with old | new
    · exact holds slot old
    · simp at new; subst new; exact member
  · intro slot inSlots
    simp only [State.update, List.mem_map] at inSlots
    obtain ⟨old, oldIn, rfl⟩ := inSlots
    split
    · rw [keeps]; exact holds old oldIn
    · exact holds old oldIn
  · exact holds

/-- **N2, the send path.** The publisher sends only bytes persisted by a
`signed` event of the journal. -/
theorem sendable_persisted {events : List Event} {state : State} {messageId : String}
    {s : Signed} (replayed : replay events = .ok state)
    (send : sendable state messageId = some s) : .signed s ∈ events := by
  unfold sendable at send
  split at send
  · rename_i slot found
    split at send
    · cases send
      exact slots_persisted events state replayed slot (List.mem_of_find?_eq_some found)
    · cases send
  · cases send

/-! ## The acknowledged record -/

/-- Acknowledged slots: Mini's record of the Message-IDs fn acknowledged. -/
def acknowledged (state : State) : List Slot := state.slots.filter (·.ack.isSome)

/-- Pending after reopen: signed, not answered. Each is `Unknown`: resolved by
`ARTICLE <msgid>` or a same-bytes resend, never by assuming absence. -/
def pending (state : State) : List Signed :=
  (state.slots.filter fun slot => slot.ack.isNone && slot.terminal.isNone).map (·.signed)

def HasAck (state : State) (messageId : String) : Prop :=
  ∃ slot ∈ state.slots, slot.signed.messageId = messageId ∧ slot.ack.isSome = true

theorem hasAck_stable {state state' : State} {event : Event} {messageId : String}
    (applied : apply state event = .ok state') (holds : HasAck state messageId) :
    HasAck state' messageId := by
  obtain ⟨slot, inSlots, named, acked⟩ := holds
  rcases apply_shape applied with same | ⟨s, _, rfl⟩ | ⟨target, change, keeps, keepsAck, rfl⟩ | ⟨_, rfl⟩
  · subst same; exact ⟨slot, inSlots, named, acked⟩
  · exact ⟨slot, List.mem_append_left _ inSlots, named, acked⟩
  · refine ⟨if slot.signed.messageId == target then change slot else slot,
      List.mem_map.mpr ⟨slot, inSlots, rfl⟩, ?_, ?_⟩
    · split <;> simp [keeps, named]
    · split
      · exact keepsAck slot acked
      · exact acked
  · exact ⟨slot, inSlots, named, acked⟩

theorem apply_ack_hasAck {state state' : State} {a : Ack}
    (applied : apply state (.acknowledged a) = .ok state') : HasAck state' a.messageId := by
  simp only [apply] at applied
  split at applied
  · cases applied
  · rename_i slot found
    have inSlots := List.mem_of_find?_eq_some found
    have named : slot.signed.messageId = a.messageId := by
      simpa using List.find?_some found
    split at applied
    · cases applied
    · split at applied
      · rename_i already
        cases applied; exact ⟨slot, inSlots, named, already⟩
      · cases applied
        refine ⟨{ slot with ack := some a }, List.mem_map.mpr ⟨slot, inSlots, ?_⟩, named, rfl⟩
        simp [named]

/-- **The acknowledged record, M1 at the client.** Every acceptance Mini
observed and recorded is listed by the reconciliation query after reopen:
{observed acceptances} ⊆ {recovered acknowledgements}. -/
theorem acknowledged_recovered {events : List Event} {state : State} {a : Ack}
    (replayed : replay events = .ok state) (member : .acknowledged a ∈ events) :
    ∃ slot ∈ acknowledged state, slot.signed.messageId = a.messageId := by
  obtain ⟨_, next, after, applied, rest⟩ := foldlM_split member replayed
  obtain ⟨slot, inSlots, named, acked⟩ :=
    foldlM_invariant (fun st => HasAck st a.messageId) after
      (fun _ _ _ _ holds step => hasAck_stable step holds) next state
      (apply_ack_hasAck applied) rest
  exact ⟨slot, List.mem_filter.mpr ⟨inSlots, acked⟩, named⟩

/-! ## The journal's chain and tags (the durable log's construction, its own customization) -/

def journalStart (domain semantics seed : Digest) : Digest :=
  (Sp800185Cshake256.hash "DREGG.FN.ARCHIVE-JOURNAL-ROOT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream digestStream)).encode
      (domain, semantics, seed))).digest

def journalStep (previous : Digest) (record : List UInt8) : Digest :=
  Kernel.WorldRoot.chainDigest previous (Kernel.WorldRoot.turnDigestOfBytes record)

def journalTag (key : DurableCheckpointCodec.MacKey) (seq : Nat) (chain : Digest) : List UInt8 :=
  Sp800185Cshake256.kmac256Bytes key.bytes "DREGG/NATIVE-HOST/ARCHIVE-JOURNAL-TAG/v1".toUTF8.toList
    ((StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat digestStream)).encode
      (key.id, seq, chain))

inductive LoadRefusal where
  | badTag (seq : Nat)
  | undecodable (seq : Nat)
  | refused (seq : Nat) (refusal : Refusal)
  deriving DecidableEq, Repr

def LoadRefusal.word : LoadRefusal → String
  | .badTag seq => s!"archive journal entry tag refused at seq {seq}"
  | .undecodable seq => s!"archive journal entry {seq} is not a journal event"
  | .refused seq refusal => s!"archive journal entry {seq} does not replay: {refusal.word}"

/-- Verify every tag against the chain, decode every record, replay. Returns
the state and the chain after the last entry. -/
def load (key : DurableCheckpointCodec.MacKey) (start : Digest)
    (entries : List (List UInt8 × List UInt8)) : Except LoadRefusal (State × Digest) := do
  let chains := (entries.map (·.1)).scanl journalStep start
  if let some seq := DurableLogTags.firstBadTag (journalTag key) 0 chains (entries.map (·.2)) then
    throw (.badTag seq)
  let (state, _) ← entries.foldlM (init := (State.empty, 1)) fun (state, seq) (record, _) => do
    let some event := eventCodec.decode record | throw (.undecodable seq)
    match apply state event with
    | .ok next => pure (next, seq + 1)
    | .error refusal => throw (.refused seq refusal)
  pure (state, chains.getLast?.getD start)

/-- The entry the next append writes at `seq` after `chain`. -/
def nextEntry (key : DurableCheckpointCodec.MacKey) (seq : Nat) (chain : Digest) (event : Event) :
    List UInt8 × List UInt8 :=
  let record := eventCodec.encode event
  (record, journalTag key seq (journalStep chain record))

/-! ## Read-back (N11): withdrawn is not absent -/

/-- What fn served for `ARTICLE <msgid>`, as the Host read it: the authored
source the native verifier extracted from a served article whose signatures
check under Mini's pinned keys, or one of fn's three `430` answers. -/
inductive Served where
  | article (source : List UInt8)
  /-- `430 withdrawn`: a cancel withdrew it; the bytes stay in fn. -/
  | withdrawn
  /-- `430 no article with that message-id`. -/
  | absent
  /-- `430 article reclaimed`: a signed payload reclaimed, against PRF-088. -/
  | reclaimed
  deriving DecidableEq, Repr

inductive ReadBack where
  | verified (bundle : Bundle)
  | withdrawn
  | absent
  | reclaimed
  | refused (refusal : ExtractRefusal)
  deriving DecidableEq, Repr

def ReadBack.word : ReadBack → String
  | .verified _ => "verified"
  | .withdrawn => "withdrawn: fn holds the bytes under a cancel; never republished over"
  | .absent => "absent"
  | .reclaimed => "reclaimed: fn reclaimed a signed payload (against PRF-088)"
  | .refused refusal => s!"refused: {refusal.word}"

/-- The bytes reach the application only through `extract` against the
identity Mini holds (the M2 adapter contract (a)). -/
def readBack (profile : Profile) (expected : String) : Served → ReadBack
  | .article source =>
      match extract profile expected source with
      | .ok bundle => .verified bundle
      | .error refusal => .refused refusal
  | .withdrawn => .withdrawn
  | .absent => .absent
  | .reclaimed => .reclaimed

theorem readBack_verified {profile : Profile} {expected : String} {served : Served}
    {bundle : Bundle} (verified : readBack profile expected served = .verified bundle) :
    ∃ source, served = .article source ∧ render profile bundle = .ok source ∧
      messageId profile bundle = expected := by
  cases served with
  | article source =>
      simp only [readBack] at verified
      split at verified
      · rename_i accepted
        cases verified
        exact ⟨source, rfl, extract_sound accepted⟩
      · cases verified
  | withdrawn | absent | reclaimed => simp [readBack] at verified

/-- A tampered or substituted article is refused by name: if the served source
is not the rendering of a bundle carrying the expected identity, nothing is
exposed. -/
theorem readBack_refuses_substitute {profile : Profile} {expected : String}
    {source : List UInt8}
    (foreign : ∀ bundle, render profile bundle = .ok source → messageId profile bundle ≠ expected) :
    ∃ refusal, readBack profile expected (.article source) = .refused refusal := by
  simp only [readBack]
  split
  · rename_i bundle accepted
    obtain ⟨rendered, named⟩ := extract_sound accepted
    exact absurd named (foreign bundle rendered)
  · exact ⟨_, rfl⟩

/-! ## The follower's cursor (M2 adapter contract (b)) -/

/-- The next height a follower of the archive has not yet consumed. -/
structure Cursor where
  next : Nat
  deriving DecidableEq, Repr

inductive Followed where
  | delivered (bundle : Bundle)
  /-- The acknowledged identity starts elsewhere: nothing is consumed. -/
  | outOfOrder (expectedFirst next : Nat)
  | held (outcome : ReadBack)
  /-- The bytes verify but name another identity than the acknowledged one. -/
  | identityDiffers
  deriving DecidableEq, Repr

def Followed.word : Followed → String
  | .delivered _ => "delivered"
  | .outOfOrder first next => s!"acknowledged bundle starts at {first}; the cursor is at {next}"
  | .held outcome => s!"cursor held: {outcome.word}"
  | .identityDiffers => "cursor held: the bundle's identity differs from the acknowledged one"

/-- One step: consume the acknowledged bundle that starts at the cursor, or
hold. A missing, withdrawn, reclaimed or invalid object never advances it. -/
def Cursor.step (profile : Profile) (cursor : Cursor) (ack : Ack) (served : Served) :
    Cursor × Followed :=
  if ack.identity.first != cursor.next then (cursor, .outOfOrder ack.identity.first cursor.next)
  else match readBack profile ack.messageId served with
    | .verified bundle =>
        if bundle.identity == ack.identity then (⟨ack.identity.last + 1⟩, .delivered bundle)
        else (cursor, .identityDiffers)
    | outcome => (cursor, .held outcome)

/-- The cursor moves only past a verified bundle with the acknowledged
identity, which starts exactly at the cursor; it lands just past that bundle. -/
theorem step_advances_only_verified {profile : Profile} {cursor : Cursor} {ack : Ack}
    {served : Served} (moved : (cursor.step profile ack served).1 ≠ cursor) :
    ∃ source bundle, served = .article source ∧
      extract profile ack.messageId source = .ok bundle ∧ bundle.identity = ack.identity ∧
      ack.identity.first = cursor.next ∧
      (cursor.step profile ack served).1 = ⟨ack.identity.last + 1⟩ := by
  unfold Cursor.step at moved ⊢
  split
  · simp_all
  · rename_i inOrder
    have first : ack.identity.first = cursor.next := by simpa using inOrder
    split
    · rename_i bundle verified
      split
      · rename_i same
        cases served with
        | article source =>
            simp only [readBack] at verified
            split at verified
            · rename_i accepted
              cases verified
              exact ⟨source, bundle, rfl, accepted, by simpa using same, first, rfl⟩
            · cases verified
        | withdrawn | absent | reclaimed => simp [readBack] at verified
      · simp_all
    · simp_all

/-- An omitted object holds the cursor and names the refusal. -/
theorem step_absent_holds (profile : Profile) (cursor : Cursor) (ack : Ack) :
    (cursor.step profile ack .absent).1 = cursor := by
  unfold Cursor.step; split <;> simp [readBack]

theorem step_withdrawn_holds (profile : Profile) (cursor : Cursor) (ack : Ack) :
    (cursor.step profile ack .withdrawn).1 = cursor ∧
      (ack.identity.first = cursor.next →
        (cursor.step profile ack .withdrawn).2 = .held .withdrawn) := by
  unfold Cursor.step; split <;> simp_all [readBack]

/-! ## The archive fee: permanent history, not a deposit -/

/-- Priced per octet fn stores (the source and fn's carrier around it) and per
fn transaction (one per article). -/
structure Tariff where
  perOctet : Nat
  perTransaction : Nat
  deriving DecidableEq, Repr

def fee (tariff : Tariff) (profile : Profile) (source : List UInt8) : Nat :=
  tariff.perOctet * (source.length + profile.carrierOverhead) + tariff.perTransaction

/-- A charged publication stays charged: no event lowers `charged` (the fee
is never refunded). -/
theorem charged_monotone {state state' : State} {event : Event}
    (applied : apply state event = .ok state') : state.charged ≤ state'.charged := by
  rcases apply_shape applied with same | ⟨s, _, rfl⟩ | ⟨target, change, _, _, rfl⟩ | ⟨_, rfl⟩
  · subst same; exact Nat.le_refl _
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- An unfunded publication is refused before it is persisted, so before any
signature or post. -/
theorem unfunded_refused {state : State} {s : Signed}
    (fresh : state.lookup s.messageId = none)
    (newRange : state.slots.any (fun slot => slot.signed.identity.first == s.identity.first) = false)
    (short : available state < s.fee) :
    apply state (.signed s) = .error (.unfunded s.fee (available state)) := by
  simp [apply, fresh, newRange, short]

#assert_axioms event_decode_encode event_canonical foldlM_invariant foldlM_split apply_shape
  lookup_update lookup_update_signed lookup_append signed_stable apply_signed_lookup
  resign_refused signed_unique slots_persisted sendable_persisted hasAck_stable
  apply_ack_hasAck acknowledged_recovered readBack_verified readBack_refuses_substitute
  step_advances_only_verified step_absent_holds step_withdrawn_holds charged_monotone
  unfunded_refused

end Minidregg.Kernel.FnArchiveJournal
