/-
# Kernel.DomainEpochLaw — the kernel's side of the channel epoch record (CHANNELS.md §2.4, §9 row 8)

`Kernel.DomainEpoch` is what the relay, the members and the witnesses run (codecs, commitment, seal,
opening, tick roots). This module is what the KERNEL runs on an append, in the same namespace and under
the same names it had when both were one file (CH-EPOCH):

* `Prev`, `ChannelLaw`, `checkShape`/`checkLink`/`checkRecord` and both poles of every clause — an
  author is a `SubjectId`, which lives in `Theory.TypedAuthorization` (Mathlib);
* `admitAppend` (run by `computeTarget` at the append) and `recordAppend`, over K-STREAM's
  `StreamCell.Append`;
* `ChannelStoreLaw` (the bounded cached-topic registry clause), and the chain in
  an admitted stream history (`admittedHistory_chain`, `channel_epochs_advance`,
  `one_record_per_epoch`). Historical linkage follows from admission transitions;
  a head alone does not assert arbitrary prior cells form an admitted history.

The split keeps Mathlib out of the runtime library (`channel-lib/build.sh` links the import closure of
`Kernel.DomainEpochExport`, which no longer reaches this module). Pins: `Kernel.DomainEpochAudit`.
-/
import Kernel.DomainEpoch
import Compiler.StreamCell

namespace Minidregg.Kernel.DomainEpoch

open Minidregg.Theory.Channel (Blob fit Profile U16 be16 rd16 rd16_be16 Header Cell Schedule FillPrf
  fillCell Submission Source profileOfId cell_encode_injective)
open Minidregg.Pred.HashEqDigest (utf8)
open Minidregg.Theory.HashBytes (be ofBE Collision length_be)
open Minidregg.Theory.Store (Store)
open Minidregg.Theory.TypedAuthorization (SubjectId)

set_option autoImplicit false

/-! ## §5. The channel law -/

/-- What the previous record of the stream fixes. -/
structure Prev where
  domain : U16
  epoch : UInt64
  author : SubjectId
  deriving DecidableEq, Repr

/-- **`ChannelLaw`.** A record is admitted iff it is well-formed and, after a previous record, it is of
the same domain, its epoch is exactly one more (delta exactly 1), and its author is the previous
record's (the sequencer; the first record's author is bound by the stream's author law). -/
def ChannelLaw (prev : Option Prev) (author : SubjectId) (r : EpochRecord) : Prop :=
  r.WellFormed ∧
    match prev with
    | none => True
    | some p => r.domain = p.domain ∧ r.epoch.toNat = p.epoch.toNat + 1 ∧ author = p.author

def checkShape (r : EpochRecord) : Except Refusal Unit :=
  match profileOfId r.classId with
  | none => .error .unknownClass
  | some P =>
    if r.tickRoots.length ≠ P.E then .error .rootCount
    else if r.n.toNat = 0 ∨ 65536 < r.n.toNat then .error .slotCount
    else .ok ()

def checkLink (prev : Option Prev) (author : SubjectId) (r : EpochRecord) : Except Refusal Unit :=
  match prev with
  | none => .ok ()
  | some p =>
    if r.domain ≠ p.domain then .error .foreignDomain
    else if r.epoch.toNat ≤ p.epoch.toNat then .error .epochNotAfter
    else if p.epoch.toNat + 1 < r.epoch.toNat then .error .epochGap
    else if author ≠ p.author then .error .foreignAuthor
    else .ok ()

/-- The law as the kernel decides it, refusal named. -/
def checkRecord (prev : Option Prev) (author : SubjectId) (r : EpochRecord) : Except Refusal Unit :=
  match checkShape r with
  | .error e => .error e
  | .ok () => checkLink prev author r

theorem checkShape_ok_iff (r : EpochRecord) : checkShape r = .ok () ↔ r.WellFormed := by
  unfold checkShape EpochRecord.WellFormed
  split
  · rename_i h; simp [h]
  · rename_i P h
    simp only [h, Option.some.injEq, exists_eq_left']
    split
    · rename_i hne; simp [hne]
    · split
      · rename_i hn; simp only [reduceCtorEq, false_iff]; omega
      · rename_i hE hn; simp only [true_iff]; omega

theorem checkLink_ok_iff (prev : Option Prev) (author : SubjectId) (r : EpochRecord) :
    checkLink prev author r = .ok () ↔
      match prev with
      | none => True
      | some p => r.domain = p.domain ∧ r.epoch.toNat = p.epoch.toNat + 1 ∧ author = p.author := by
  unfold checkLink
  split
  · simp
  · rename_i p
    split_ifs <;> simp_all <;> omega

/-- **The kernel's check decides `ChannelLaw`.** -/
theorem checkRecord_ok_iff (prev : Option Prev) (author : SubjectId) (r : EpochRecord) :
    checkRecord prev author r = .ok () ↔ ChannelLaw prev author r := by
  unfold checkRecord ChannelLaw
  rw [← checkShape_ok_iff, ← checkLink_ok_iff]
  cases checkShape r with
  | error e => simp
  | ok u => cases u; simp

/-! ### Both poles of every clause, in general -/

section Poles
variable {p : Prev} {author : SubjectId} {r : EpochRecord}

theorem next_record_admitted (wf : r.WellFormed) (dom : r.domain = p.domain)
    (next : r.epoch.toNat = p.epoch.toNat + 1) (seq : author = p.author) :
    checkRecord (some p) author r = .ok () :=
  (checkRecord_ok_iff _ _ _).mpr ⟨wf, dom, next, seq⟩

theorem first_record_admitted (wf : r.WellFormed) : checkRecord none author r = .ok () :=
  (checkRecord_ok_iff _ _ _).mpr ⟨wf, trivial⟩

theorem shape_refusal_first {e : Refusal} (bad : checkShape r = .error e) (prev : Option Prev) :
    checkRecord prev author r = .error e := by
  simp [checkRecord, bad]

/-- **A gap is refused by name**: epoch `prev + 2` (or more). -/
theorem gap_refused (wf : r.WellFormed) (dom : r.domain = p.domain)
    (gap : p.epoch.toNat + 1 < r.epoch.toNat) : checkRecord (some p) author r = .error .epochGap := by
  have := (checkShape_ok_iff r).mpr wf
  simp only [checkRecord, this, checkLink, dom, ne_eq, not_true_eq_false, if_false]
  rw [if_neg (by omega), if_pos gap]

/-- **A repeat or an out-of-order record is refused by name**: epoch `≤ prev` (so `prev − 1` too). -/
theorem out_of_order_refused (wf : r.WellFormed) (dom : r.domain = p.domain)
    (notAfter : r.epoch.toNat ≤ p.epoch.toNat) : checkRecord (some p) author r = .error .epochNotAfter := by
  have := (checkShape_ok_iff r).mpr wf
  simp only [checkRecord, this, checkLink, dom, ne_eq, not_true_eq_false, if_false]
  rw [if_pos notAfter]

/-- **A record by anyone but the sequencer is refused by name.** -/
theorem foreign_author_refused (wf : r.WellFormed) (dom : r.domain = p.domain)
    (next : r.epoch.toNat = p.epoch.toNat + 1) (foreign : author ≠ p.author) :
    checkRecord (some p) author r = .error .foreignAuthor := by
  have := (checkShape_ok_iff r).mpr wf
  simp only [checkRecord, this, checkLink, dom, ne_eq, not_true_eq_false, if_false]
  rw [if_neg (by omega), if_neg (by omega), if_pos foreign]

theorem foreign_domain_refused (wf : r.WellFormed) (dom : r.domain ≠ p.domain) :
    checkRecord (some p) author r = .error .foreignDomain := by
  have := (checkShape_ok_iff r).mpr wf
  simp only [checkRecord, this, checkLink]
  rw [if_pos dom]

/-- **A record whose root count is not its class's `E` is refused by name**, whatever else. -/
theorem root_count_refused {P : Profile} (cls : profileOfId r.classId = some P)
    (count : r.tickRoots.length ≠ P.E) (prev : Option Prev) :
    checkRecord prev author r = .error .rootCount :=
  shape_refusal_first (by simp [checkShape, cls, count]) prev

end Poles

/-! ## §6. The kernel's admission of an append -/

/-- Bounded metadata for the previous admitted entry, authenticated by the head's tail.
`Head.Lawful` binds the cached entry's head, sequence and digest to this head; admission
updates this cache and the fresh entry together. No historical scan occurs here. -/
def lastRecord (store : Minidregg.Compiler.StreamCell.HeadStore) :
    Option Minidregg.Compiler.StreamCell.StreamRecord :=
  (Minidregg.Compiler.StreamCell.headOf store).bind fun head =>
    head.last.map Minidregg.Compiler.StreamCell.Entry.record

/-- What the stream's last record fixes for a channel append: `none` for an empty stream. -/
def prevOf (store : Minidregg.Compiler.StreamCell.HeadStore) : Except Refusal (Option Prev) :=
  match lastRecord store with
  | none => .ok none
  | some last =>
    match classifyTopic last.entry.topic with
    | .channel d e => .ok (some ⟨d, e, last.author⟩)
    | _ => .error .kindMismatch

/-- **The kernel's admission of a stream append** (run by `computeTarget` at the append, where the
payload bytes are). An ordinary topic on an ordinary (or empty) stream is untouched. A channel topic
must carry the canonical encoding of a record with the topic's (domain, epoch) that satisfies
`ChannelLaw` against the stream's last record, by `author` (the append's signing subject). -/
def admitAppend (store : Minidregg.Compiler.StreamCell.HeadStore) (author : SubjectId)
    (request : Minidregg.Compiler.StreamCell.Append) : Except Refusal Unit :=
  match classifyTopic request.topic with
  | .malformed => .error .malformedTopic
  | .ordinary =>
    match lastRecord store with
    | none => .ok ()
    | some last =>
      match classifyTopic last.entry.topic with
      | .channel _ _ => .error .kindMismatch
      | _ => .ok ()
  | .channel d e =>
    match prevOf store with
    | .error reason => .error reason
    | .ok prev =>
      match EpochRecord.decode request.payload with
      | none => .error .malformedRecord
      | some r =>
        if r.domain ≠ d ∨ r.epoch ≠ e then .error .topicMismatch
        else checkRecord prev author r

/-- The append a sequencer makes for a record. -/
def recordAppend (r : EpochRecord) : Minidregg.Compiler.StreamCell.Append :=
  ⟨channelTopic r.domain r.epoch, r.encode, none, none⟩

/-- **At the append, the kernel decides `ChannelLaw`** for a sequencer's record. -/
theorem admitAppend_record (store : Minidregg.Compiler.StreamCell.HeadStore) (author : SubjectId)
    (r : EpochRecord) (prev : Option Prev) (last : prevOf store = .ok prev) :
    admitAppend store author (recordAppend r) = checkRecord prev author r := by
  simp [admitAppend, recordAppend, classifyTopic_channelTopic, last, epochRecord_decode_encode]

theorem admitAppend_record_ok_iff (store : Minidregg.Compiler.StreamCell.HeadStore) (author : SubjectId)
    (r : EpochRecord) (prev : Option Prev) (last : prevOf store = .ok prev) :
    admitAppend store author (recordAppend r) = .ok () ↔ ChannelLaw prev author r := by
  rw [admitAppend_record store author r prev last, checkRecord_ok_iff]

/-! ## §7. The store law the registry checks on every loaded and final stream cell -/

/-- A stored entry's topic is never a malformed channel topic. -/
def EntryOk (record : Minidregg.Compiler.StreamCell.StreamRecord) : Prop :=
  classifyTopic record.entry.topic ≠ .malformed

/-- Consecutive entries: both ordinary, or both channel with the same domain, the next epoch and the
same author. -/
def LinkOk (prev cur : Minidregg.Compiler.StreamCell.StreamRecord) : Prop :=
  match classifyTopic prev.entry.topic, classifyTopic cur.entry.topic with
  | .channel d e, .channel d' e' => d' = d ∧ e'.toNat = e.toNat + 1 ∧ cur.author = prev.author
  | .channel _ _, _ => False
  | _, .channel _ _ => False
  | _, _ => True

instance (prev cur : Minidregg.Compiler.StreamCell.StreamRecord) : Decidable (LinkOk prev cur) := by
  unfold LinkOk; split <;> infer_instance

/-- The bounded registry check. Historical linkage is an invariant of admitted
transitions (`AdmittedHistory`), not something a local head can establish by scanning
absent history. The structural head law separately authenticates the cached entry.
Fleet-topic heads have their own receiving protocol and are deliberately exempt;
only room heads can enter the channel admitted-history relation below. -/
def ChannelStoreLaw (store : Minidregg.Compiler.StreamCell.HeadStore) : Prop :=
  match Minidregg.Compiler.StreamCell.headOf store with
  | none => True
  | some head =>
    match head.binding with
    | .topic _ => True
    | .room =>
      match head.last with
      | none => True
      | some entry => EntryOk entry.record

instance (store : Minidregg.Compiler.StreamCell.HeadStore) : Decidable (ChannelStoreLaw store) := by
  unfold ChannelStoreLaw EntryOk
  split
  · infer_instance
  · split <;> first | infer_instance | (split <;> infer_instance)

theorem empty_channel_lawful : ChannelStoreLaw 0 := by
  simp [ChannelStoreLaw, lastRecord, Minidregg.Compiler.StreamCell.headOf]

open Minidregg.Compiler.StreamCell

/-- Admission establishes the stored topic and the link to the authenticated cached
previous record. The record's author and entry are derived from the signing request. -/
theorem admitAppend_link (store : HeadStore) (author : SubjectId) (request : Append)
    (height : Nat) (transaction : Minidregg.Theory.TypedAuthorization.Digest)
    (ok : admitAppend store author request = .ok ()) :
    EntryOk ⟨author, height, transaction, request.entry⟩ ∧
      ∀ previous, lastRecord store = some previous →
        LinkOk previous ⟨author, height, transaction, request.entry⟩ := by
  cases topic : classifyTopic request.topic with
  | malformed => simp [admitAppend, topic] at ok
  | ordinary =>
    refine ⟨by simp [EntryOk, Append.entry, topic], ?_⟩
    intro previous last
    cases prevTopic : classifyTopic previous.entry.topic with
    | channel d e => simp [admitAppend, topic, last, prevTopic] at ok
    | ordinary => simp [LinkOk, Append.entry, topic, prevTopic]
    | malformed => simp [LinkOk, Append.entry, topic, prevTopic]
  | channel d e =>
    refine ⟨by simp [EntryOk, Append.entry, topic], ?_⟩
    intro previous last
    cases prevTopic : classifyTopic previous.entry.topic with
    | ordinary => simp [admitAppend, topic, prevOf, last, prevTopic] at ok
    | malformed => simp [admitAppend, topic, prevOf, last, prevTopic] at ok
    | channel pd pe =>
      simp only [admitAppend, topic, prevOf, last, prevTopic] at ok
      cases decoded : EpochRecord.decode request.payload with
      | none => simp [decoded] at ok
      | some record =>
        simp only [decoded] at ok
        by_cases mismatch : record.domain ≠ d ∨ record.epoch ≠ e
        · simp [mismatch] at ok
        · simp only [if_neg mismatch] at ok
          have agrees : record.domain = d ∧ record.epoch = e := by
            simpa only [not_or, not_not] using mismatch
          have linked := (checkRecord_ok_iff _ _ _).mp ok
          simp only [ChannelLaw] at linked
          simp only [LinkOk, Append.entry, topic, prevTopic]
          exact ⟨agrees.1 ▸ linked.2.1, agrees.2 ▸ linked.2.2.1, linked.2.2.2⟩

/-- An ordinary append cannot change an established channel into an ordinary stream. -/
theorem ordinary_after_channel_refused (store : HeadStore) (author : SubjectId)
    (request : Append) (previous : StreamRecord) (d : U16) (e : UInt64)
    (last : lastRecord store = some previous)
    (ordinary : classifyTopic request.topic = .ordinary)
    (channel : classifyTopic previous.entry.topic = .channel d e) :
    admitAppend store author request = .error .kindMismatch := by
  simp [admitAppend, ordinary, last, channel]

/-- Nor can a channel append reinterpret an established ordinary stream. -/
theorem channel_after_ordinary_refused (store : HeadStore) (author : SubjectId)
    (request : Append) (previous : StreamRecord) (d : U16) (e : UInt64)
    (last : lastRecord store = some previous)
    (ordinary : classifyTopic previous.entry.topic = .ordinary)
    (channel : classifyTopic request.topic = .channel d e) :
    admitAppend store author request = .error .kindMismatch := by
  simp [admitAppend, channel, prevOf, last, ordinary]

/-- A proof-only history, newest entry first. Unlike an arbitrary collection of
entry cells, its constructors are the same admission and append operations used by
the receiver. No caller supplies a free-standing previous channel record. -/
inductive AdmittedHistory (cellId : Nat) : Head → List StreamRecord → Prop
  | empty : AdmittedHistory cellId emptyRoomHead []
  | append {head : Head} {records : List StreamRecord}
      (history : AdmittedHistory cellId head records)
      (author : SubjectId) (request : Append) (height : Nat)
      (transaction : Minidregg.Theory.TypedAuthorization.Digest)
      (admitted : admitAppend (headStore head) author request = .ok ()) :
      AdmittedHistory cellId
        (head.append (appendEntry cellId head ⟨author, height, transaction, request.entry⟩))
        (⟨author, height, transaction, request.entry⟩ :: records)

/-- The exact cache used at the next admission is the last admitted record. -/
theorem admittedHistory_last {cellId : Nat} {head : Head} {records : List StreamRecord}
    (history : AdmittedHistory cellId head records) :
    lastRecord (headStore head) = records.head? := by
  cases history <;> simp [lastRecord, emptyRoomHead, Head.append, appendEntry]

/-- History positions agree with the physical head's next-position counter. -/
theorem admittedHistory_count {cellId : Nat} {head : Head} {records : List StreamRecord}
    (history : AdmittedHistory cellId head records) : head.count = records.length := by
  induction history with
  | empty => rfl
  | append history author request height transaction admitted ih =>
    simpa only [Head.append, List.length_cons] using congrArg (fun n => n + 1) ih

/-- Each reachable cache is structurally bound to its exact append entry. -/
theorem admittedHistory_head_lawful {cellId : Nat} {head : Head} {records : List StreamRecord}
    (history : AdmittedHistory cellId head records) : head.Lawful cellId := by
  induction history with
  | empty => simp [Head.Lawful, emptyRoomHead, Binding.At]
  | append history author request height transaction admitted ih =>
    exact append_head_lawful cellId _ _ ih

/-- Historical linkage, separate from the constant-cost registry predicate. -/
def HistoryLaw : List StreamRecord → Prop
  | [] => True
  | [record] => EntryOk record
  | current :: previous :: rest =>
      EntryOk current ∧ LinkOk previous current ∧ HistoryLaw (previous :: rest)

theorem historyLaw_tail {record : StreamRecord} {records : List StreamRecord}
    (law : HistoryLaw (record :: records)) : HistoryLaw records := by
  cases records with
  | nil => trivial
  | cons previous rest => exact law.2.2

/-- The historical chain follows from real append admission and the cache update,
not from assuming the desired chain as a registry check. -/
theorem admittedHistory_chain {cellId : Nat} {head : Head} {records : List StreamRecord}
    (history : AdmittedHistory cellId head records) : HistoryLaw records := by
  induction history with
  | empty => trivial
  | @append head records history author request height transaction admitted ih =>
    obtain ⟨entry, link⟩ := admitAppend_link (headStore head) author request height transaction admitted
    cases records with
    | nil => exact entry
    | cons previous rest =>
      exact ⟨entry, link previous (admittedHistory_last history), ih⟩

/-- A channel entry `k` positions before the latest has an epoch exactly `k` lower.
Positions here are offsets in the newest-first admitted history. -/
theorem channel_epochs_from_head {first : StreamRecord} {rest : List StreamRecord}
    (chain : HistoryLaw (first :: rest)) {domain : U16} {epoch : UInt64}
    (topic : classifyTopic first.entry.topic = .channel domain epoch) :
    ∀ (k : Nat) {record : StreamRecord} {d : U16} {e : UInt64},
      (first :: rest)[k]? = some record →
      classifyTopic record.entry.topic = .channel d e → epoch.toNat = e.toNat + k := by
  intro k
  induction k generalizing first rest domain epoch with
  | zero =>
    intro record d e found classified
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst record
    rw [topic] at classified
    cases classified
    omega
  | succ k ih =>
    intro record d e found classified
    cases rest with
    | nil => simp at found
    | cons previous tail =>
      have link := chain.2.1
      cases prevTopic : classifyTopic previous.entry.topic with
      | ordinary => simp [LinkOk, prevTopic, topic] at link
      | malformed => simp [LinkOk, prevTopic, topic] at link
      | channel pd pe =>
        simp only [LinkOk, prevTopic, topic] at link
        have advance := ih chain.2.2 prevTopic (by simpa using found) classified
        omega

/-- The chain between any two positions in the admitted history. -/
theorem channel_epochs_advance (records : List StreamRecord) (chain : HistoryLaw records)
    (i k : Nat) {ri rj : StreamRecord} {di dj : U16} {ei ej : UInt64}
    (hi : records[i]? = some ri) (hj : records[i + k]? = some rj)
    (ci : classifyTopic ri.entry.topic = .channel di ei)
    (cj : classifyTopic rj.entry.topic = .channel dj ej) :
    ei.toNat = ej.toNat + k := by
  induction i generalizing records with
  | zero =>
    cases records with
    | nil => simp at hi
    | cons first rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst first
      exact channel_epochs_from_head chain ci k (by simpa using hj) cj
  | succ i ih =>
    cases records with
    | nil => simp at hi
    | cons first rest =>
      apply ih rest (historyLaw_tail chain) (by simpa using hi)
      simpa [Nat.succ_add] using hj

/-- No two admitted positions have the same channel epoch. This is a property of
one admission history; it does not claim to prevent independently admitted forks. -/
theorem one_record_per_epoch (records : List StreamRecord) (chain : HistoryLaw records)
    {i j : Nat} {ri rj : StreamRecord} {di dj : U16} {e : UInt64}
    (hi : records[i]? = some ri) (hj : records[j]? = some rj)
    (ci : classifyTopic ri.entry.topic = .channel di e)
    (cj : classifyTopic rj.entry.topic = .channel dj e) : i = j := by
  rcases Nat.lt_trichotomy i j with lt | eq | gt
  · have advance := channel_epochs_advance records chain i (j - i) hi
      (by simpa [Nat.add_sub_of_le (Nat.le_of_lt lt)] using hj) ci cj
    omega
  · exact eq
  · have advance := channel_epochs_advance records chain j (i - j) hj
      (by simpa [Nat.add_sub_of_le (Nat.le_of_lt gt)] using hi) cj ci
    omega

/-- Direct receiving-history consequence: no extra historical-chain hypothesis is
needed once each step was admitted by the actual append checker. -/
theorem admittedHistory_one_record_per_epoch {cellId : Nat} {head : Head}
    {records : List StreamRecord} (history : AdmittedHistory cellId head records)
    {i j : Nat} {ri rj : StreamRecord} {di dj : U16} {e : UInt64}
    (hi : records[i]? = some ri) (hj : records[j]? = some rj)
    (ci : classifyTopic ri.entry.topic = .channel di e)
    (cj : classifyTopic rj.entry.topic = .channel dj e) : i = j :=
  one_record_per_epoch records (admittedHistory_chain history) hi hj ci cj

/-! ## §11. Instances and poles on concrete values -/

namespace Example


def sequencer : SubjectId := ⟨10⟩
def stranger : SubjectId := ⟨11⟩
def after4 : Prev := ⟨⟨7, by decide⟩, 4, sequencer⟩

theorem first_admitted : checkRecord none sequencer (record 0 16) = .ok () := rfl
theorem next_admitted : checkRecord (some after4) sequencer (record 5 16) = .ok () := rfl
theorem gap_refused : checkRecord (some after4) sequencer (record 6 16) = .error .epochGap := rfl
theorem out_of_order_refused : checkRecord (some after4) sequencer (record 3 16) = .error .epochNotAfter := rfl
theorem repeat_refused : checkRecord (some after4) sequencer (record 4 16) = .error .epochNotAfter := rfl
theorem short_refused : checkRecord (some after4) sequencer (record 5 15) = .error .rootCount := rfl
theorem long_refused : checkRecord (some after4) sequencer (record 5 17) = .error .rootCount := rfl
theorem stranger_refused : checkRecord (some after4) stranger (record 5 16) = .error .foreignAuthor := rfl

/-- Concrete bounded-cache fixtures exercise the append admission interface,
including both channel/ordinary type changes, rather than only `checkRecord`. -/
def cachedEntry : Entry :=
  ⟨99, 1, none, ⟨sequencer, 1, ⟨0⟩,
    ⟨channelTopic after4.domain after4.epoch, ⟨0⟩, none, none⟩⟩⟩

def cachedHead : Head := emptyRoomHead.append cachedEntry

theorem cached_next_admitted :
    admitAppend (headStore cachedHead) sequencer (recordAppend (record 5 16)) = .ok () := by
  rw [admitAppend_record _ _ _ (some after4) (by rfl)]
  exact next_admitted

theorem cached_gap_refused :
    admitAppend (headStore cachedHead) sequencer (recordAppend (record 6 16)) = .error .epochGap := by
  rw [admitAppend_record _ _ _ (some after4) (by rfl)]
  exact gap_refused

theorem cached_repeat_refused :
    admitAppend (headStore cachedHead) sequencer (recordAppend (record 4 16)) = .error .epochNotAfter := by
  rw [admitAppend_record _ _ _ (some after4) (by rfl)]
  exact repeat_refused

theorem cached_stranger_refused :
    admitAppend (headStore cachedHead) stranger (recordAppend (record 5 16)) = .error .foreignAuthor := by
  rw [admitAppend_record _ _ _ (some after4) (by rfl)]
  exact stranger_refused

theorem cached_ordinary_refused :
    admitAppend (headStore cachedHead) sequencer ⟨[], [], none, none⟩ = .error .kindMismatch := by
  apply ordinary_after_channel_refused _ _ _ cachedEntry.record after4.domain after4.epoch
  · rfl
  · rfl
  · exact classifyTopic_channelTopic _ _

theorem cached_foreign_domain_refused :
    admitAppend (headStore cachedHead) sequencer
      (recordAppend { record 5 16 with domain := ⟨8, by decide⟩ }) = .error .foreignDomain := by
  rw [admitAppend_record _ _ _ (some after4) (by rfl)]
  rfl

def ordinaryEntry : Entry :=
  { cachedEntry with record := { cachedEntry.record with entry :=
      { cachedEntry.record.entry with topic := [] } } }

theorem cached_channel_after_ordinary_refused :
    admitAppend (headStore (emptyRoomHead.append ordinaryEntry)) sequencer
      (recordAppend (record 5 16)) = .error .kindMismatch := by
  apply channel_after_ordinary_refused _ _ _ ordinaryEntry.record (record 5 16).domain (record 5 16).epoch
  · rfl
  · rfl
  · exact classifyTopic_channelTopic _ _

end Example

end Minidregg.Kernel.DomainEpoch
