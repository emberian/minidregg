/-
# Kernel.DomainEpochLaw — the kernel's side of the channel epoch record (CHANNELS.md §2.4, §9 row 8)

`Kernel.DomainEpoch` is what the relay, the members and the witnesses run (codecs, commitment, seal,
opening, tick roots). This module is what the KERNEL runs on an append, in the same namespace and under
the same names it had when both were one file (CH-EPOCH):

* `Prev`, `ChannelLaw`, `checkShape`/`checkLink`/`checkRecord` and both poles of every clause — an
  author is a `SubjectId`, which lives in `Theory.TypedAuthorization` (Mathlib);
* `admitAppend` (run by `computeTarget` at the append) and `recordAppend`, over K-STREAM's
  `StreamCell.Append`;
* `ChannelStoreLaw` (the registry's stream clause) and the chain inside one Store
  (`channel_epochs_advance`, `one_record_per_epoch`).

The split keeps Mathlib out of the runtime library (`channel-lib/build.sh` links the import closure of
`Kernel.DomainEpochExport`, which no longer reaches this module). Pins: `Kernel.DomainEpochAudit`.
-/
import Kernel.DomainEpoch
import Compiler.StreamCell

namespace Minidregg.Kernel.DomainEpoch

open Minidregg.Theory.Channel (Blob fit Profile U16 be16 rd16 rd16_be16 Header Cell Schedule FillPrf
  fillCell Submission Source profileOfId cell_encode_injective)
open Minidregg.Pred.HashEqDigest (be ofBE Collision utf8 length_be)
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

/-- The stream's last record (the one at `nextSeq − 1`). -/
def lastRecord (store : Store Minidregg.Compiler.StreamCell.layout) :
    Option Minidregg.Compiler.StreamCell.StreamRecord :=
  store (Minidregg.Compiler.StreamCell.address store.support.card)

/-- What the stream's last record fixes for a channel append: `none` for an empty stream. -/
def prevOf (store : Store Minidregg.Compiler.StreamCell.layout) : Except Refusal (Option Prev) :=
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
def admitAppend (store : Store Minidregg.Compiler.StreamCell.layout) (author : SubjectId)
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
theorem admitAppend_record (store : Store Minidregg.Compiler.StreamCell.layout) (author : SubjectId)
    (r : EpochRecord) (prev : Option Prev) (last : prevOf store = .ok prev) :
    admitAppend store author (recordAppend r) = checkRecord prev author r := by
  simp [admitAppend, recordAppend, classifyTopic_channelTopic, last, epochRecord_decode_encode]

theorem admitAppend_record_ok_iff (store : Store Minidregg.Compiler.StreamCell.layout) (author : SubjectId)
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

def LinkAt (store : Store Minidregg.Compiler.StreamCell.layout) (k : Nat) : Prop :=
  match store (Minidregg.Compiler.StreamCell.address (k - 1)),
      store (Minidregg.Compiler.StreamCell.address k) with
  | some p, some c => LinkOk p c
  | _, _ => True

instance (store : Store Minidregg.Compiler.StreamCell.layout) (k : Nat) : Decidable (LinkAt store k) := by
  unfold LinkAt; split <;> infer_instance

def EntryAt (store : Store Minidregg.Compiler.StreamCell.layout) (k : Nat) : Prop :=
  match store (Minidregg.Compiler.StreamCell.address k) with
  | some r => EntryOk r
  | none => True

instance (store : Store Minidregg.Compiler.StreamCell.layout) (k : Nat) : Decidable (EntryAt store k) := by
  unfold EntryAt EntryOk; split <;> infer_instance

/-- **`ChannelStoreLaw`**, the registry's stream clause: every entry's topic is well-formed, and
every entry links to the one before it. On a channel stream that is the chain: one domain, epochs
consecutive, one author. -/
def ChannelStoreLaw (store : Store Minidregg.Compiler.StreamCell.layout) : Prop :=
  ∀ a ∈ store.support, EntryAt store a.2 ∧ LinkAt store a.2

instance (store : Store Minidregg.Compiler.StreamCell.layout) : Decidable (ChannelStoreLaw store) := by
  unfold ChannelStoreLaw; infer_instance

theorem empty_channel_lawful : ChannelStoreLaw 0 := by
  intro a member; simp at member


/-! ## §10. No equivocation inside one Store -/

/-- Dense keys are exactly `1 … card`: every position up to the count is present. -/
theorem dense_present (store : Store Minidregg.Compiler.StreamCell.layout)
    (dense : Minidregg.Compiler.StreamCell.Dense store) {m : Nat} (h1 : 1 ≤ m)
    (h2 : m ≤ store.support.card) : Minidregg.Compiler.StreamCell.address m ∈ store.support := by
  classical
  let f : Minidregg.Theory.Store.Address Minidregg.Compiler.StreamCell.layout → Nat := fun a => a.2
  have finj : Set.InjOn f store.support := by
    intro a _ b _ h
    obtain ⟨sa, ka⟩ := a; obtain ⟨sb, kb⟩ := b
    cases sa; cases sb
    simp only [f] at h; subst h; rfl
  have hsub : store.support.image f ⊆ Finset.Icc 1 store.support.card := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr (dense a ha)
  have hcard : (Finset.Icc 1 store.support.card).card ≤ (store.support.image f).card := by
    rw [Finset.card_image_of_injOn finj]; simp
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hm : m ∈ store.support.image f := heq ▸ Finset.mem_Icc.mpr ⟨h1, h2⟩
  obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hm
  obtain ⟨sa, ka⟩ := a
  cases sa
  simp only [f] at hfa
  subst hfa
  exact ha

theorem mem_support_of_some {store : Store Minidregg.Compiler.StreamCell.layout} {k : Nat}
    {r : Minidregg.Compiler.StreamCell.StreamRecord} (h : store (Minidregg.Compiler.StreamCell.address k) = some r) :
    Minidregg.Compiler.StreamCell.address k ∈ store.support :=
  DFinsupp.mem_support_iff.mpr (by rw [h]; exact Option.some_ne_none r)

/-- **The chain inside one Store.** In a lawful stream, a channel entry `k` places after another is
exactly `k` epochs later. -/
theorem channel_epochs_advance (store : Store Minidregg.Compiler.StreamCell.layout)
    (law : Minidregg.Compiler.StreamCell.StreamLaw store) (chain : ChannelStoreLaw store)
    {i : Nat} {ri : Minidregg.Compiler.StreamCell.StreamRecord} {di : U16} {ei : UInt64}
    (hi : store (Minidregg.Compiler.StreamCell.address i) = some ri)
    (ci : classifyTopic ri.entry.topic = .channel di ei) :
    ∀ (k : Nat) {rj : Minidregg.Compiler.StreamCell.StreamRecord} {dj : U16} {ej : UInt64},
      store (Minidregg.Compiler.StreamCell.address (i + k + 1)) = some rj →
      classifyTopic rj.entry.topic = .channel dj ej → ej.toNat = ei.toNat + (k + 1) := by
  have hi1 : 1 ≤ i := (law.1 _ (mem_support_of_some hi)).1
  intro k
  induction k with
  | zero =>
    intro rj dj ej hj cj
    have link : LinkAt store (i + 0 + 1) := (chain _ (mem_support_of_some hj)).2
    unfold LinkAt at link
    rw [show i + 0 + 1 - 1 = i by omega, hj, hi] at link
    simp only [LinkOk, ci, cj] at link
    obtain ⟨_, h, _⟩ := link
    omega
  | succ k ih =>
    intro rj dj ej hj cj
    have link : LinkAt store (i + (k + 1) + 1) := (chain _ (mem_support_of_some hj)).2
    have hjc : i + (k + 1) + 1 ≤ store.support.card := (law.1 _ (mem_support_of_some hj)).2
    have hpres := dense_present store law.1 (m := i + k + 1) (by omega) (by omega)
    have hne : store (Minidregg.Compiler.StreamCell.address (i + k + 1)) ≠ none :=
      DFinsupp.mem_support_iff.mp hpres
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hne
    unfold LinkAt at link
    rw [show i + (k + 1) + 1 - 1 = i + k + 1 by omega, hj, hp] at link
    cases cp : classifyTopic p.entry.topic with
    | channel dp ep =>
      simp only [LinkOk, cp, cj] at link
      obtain ⟨_, h, _⟩ := link
      have := ih hp cp
      omega
    | ordinary => simp [LinkOk, cp, cj] at link
    | malformed => simp [LinkOk, cp, cj] at link

/-- **No equivocation inside one Store.** A lawful stream holds at most one channel entry per epoch:
two channel entries with the same epoch are the same position. -/
theorem one_record_per_epoch (store : Store Minidregg.Compiler.StreamCell.layout)
    (law : Minidregg.Compiler.StreamCell.StreamLaw store) (chain : ChannelStoreLaw store)
    {i j : Nat} {ri rj : Minidregg.Compiler.StreamCell.StreamRecord} {di dj : U16} {e : UInt64}
    (hi : store (Minidregg.Compiler.StreamCell.address i) = some ri)
    (hj : store (Minidregg.Compiler.StreamCell.address j) = some rj)
    (ci : classifyTopic ri.entry.topic = .channel di e) (cj : classifyTopic rj.entry.topic = .channel dj e) :
    i = j := by
  rcases Nat.lt_trichotomy i j with lt | eq | gt
  · have := channel_epochs_advance store law chain hi ci (j - i - 1) (by rw [show i + (j - i - 1) + 1 = j by omega]; exact hj) cj
    omega
  · exact eq
  · have := channel_epochs_advance store law chain hj cj (i - j - 1) (by rw [show j + (i - j - 1) + 1 = i by omega]; exact hi) ci
    omega

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

end Example

end Minidregg.Kernel.DomainEpoch
