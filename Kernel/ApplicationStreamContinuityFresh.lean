/-
STATEMENT (stream continuity, hot route registration).

A hot route registration on a running grain is admitted exactly when the serving
session holds an AUTHENTICATED opening read of the Store's head, is at or above
the grain's birth height, and the Store's tip is exactly that head entry.

Authenticated means `DurableHistory.Head.verify` succeeds on the tag at the
image's height, chain and frontier (the verifier `readerWith` uses). The tag is
the one the image carries (`Loaded.headTag`: set by the open, by an extension of
a physical suffix, and by the append path, `Appended.headTagExact`) or, when the
image carries none, the head entry read back from the Store at the handoff. A
tag that does not verify is never an opening read, even when it equals the tip's
own tag, and `Loaded`'s own tag is checked the same way.

`verdict` is the pure core of `ApplicationStreamContinuity.withOpenedFreshTip`,
which is defined through it: the IO reads the Store, builds a `Held` and a
`Physical`, runs `verdict`, and calls the handoff only when `gate (verdict ..)`
is `none` (`handoff_runs_iff`).
-/
module

public import Compiler.DurableReceiverCore

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
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.ApplicationStreamContinuityFresh

open Minidregg.Compiler
open Minidregg.Compiler.DurableHistory
open Minidregg.Compiler.DurableReceiverIO (Entry)
open Minidregg.Compiler.DurableCheckpointCodec (MacKey)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- What the serving session holds at its image's head. -/
structure Held where
  /-- Height of the held image. -/
  height : Nat
  /-- The frame of the head record (`none`: the history is empty). -/
  headRecord : Option (List UInt8)
  /-- The tag the image carries (`Loaded.headTag`). -/
  headTag : Option (List UInt8)
  /-- The head entry's tag read back from the Store at the handoff. -/
  readTag : Option (List UInt8)
  /-- The opened Store, the image's chain and its accumulator frontier
  (`none`: the image was never read from the Store): what `Head.verify` needs. -/
  store : StoreIdentity
  chain : Digest
  frontier : Option (List (Nat × Digest))

/-- What the Store's tip is when read at the handoff. -/
structure Physical where
  head : Nat
  entries : List Entry

/-- The open's verifier, applied to a tag at the held image's head. -/
def Held.authentic (held : Held) (tag : List UInt8) : Bool :=
  match held.frontier with
  | none => false
  | some frontier =>
      match Head.verify held.store held.height tag held.chain frontier with
      | .ok _ => true
      | .error _ => false

inductive Verdict where
  | admitted
  | emptyHistory
  /-- No tag the image carries and none read back. -/
  | noOpeningRead
  /-- A tag exists but does not authenticate as the head's. -/
  | openingUnverified
  /-- The session's image is below the grain's birth height. -/
  | belowBirth
  /-- The Store's tip is not exactly the session's head entry. -/
  | tipChanged
  | tipUnavailable
  deriving DecidableEq, Repr

/-- The candidate opening tag: the carried one, else the one read back. -/
def Held.candidate (held : Held) : Option (List UInt8) := held.headTag.or held.readTag

/-- `verdict` with the authentication abstracted, so the poles that do not need
a MAC can be closed instances. -/
def decideWith (verifies : List UInt8 → Bool) (birthHeight : Nat) (held : Held)
    (physical : Option Physical) : Verdict :=
  match held.headRecord with
  | none => .emptyHistory
  | some record =>
    match held.candidate with
    | none => .noOpeningRead
    | some tag =>
      if verifies tag = false then .openingUnverified
      else if held.height < birthHeight then .belowBirth
      else match physical with
        | none => .tipUnavailable
        | some tip =>
            if tip.head = held.height ∧ tip.entries = [⟨record.toByteArray, tag⟩] then .admitted
            else .tipChanged

def verdict (birthHeight : Nat) (held : Held) (physical : Option Physical) : Verdict :=
  decideWith held.authentic birthHeight held physical

/-- The refusal text, or `none` to go ahead. -/
def gate : Verdict → Option String
  | .admitted => none
  | .emptyHistory => some "authority handoff requires nonempty history"
  | .noOpeningRead => some "authority handoff requires an opening read from the Store"
  | .openingUnverified => some "authority handoff opening read does not verify as the Store head"
  | .belowBirth => some "authority handoff session is below the grain's birth height"
  | .tipUnavailable => some "authority physical tip unavailable"
  | .tipChanged => some "authority physical tip changed before handoff"

theorem gate_none_iff (v : Verdict) : gate v = none ↔ v = .admitted := by
  cases v <;> simp [gate]

theorem gate_injective (a b : Verdict) (h : gate a = gate b) (ha : a ≠ .admitted) : a = b := by
  cases a <;> cases b <;> simp_all [gate]

/-- The statement. -/
def HotRegistrationAdmitted (birthHeight : Nat) (held : Held) (physical : Option Physical) : Prop :=
  verdict birthHeight held physical = .admitted

theorem decideWith_iff (verifies : List UInt8 → Bool) (birthHeight : Nat) (held : Held)
    (physical : Option Physical) :
    decideWith verifies birthHeight held physical = .admitted ↔
      ∃ record tag, held.headRecord = some record ∧ held.candidate = some tag ∧
        verifies tag = true ∧ birthHeight ≤ held.height ∧
        physical = some ⟨held.height, [⟨record.toByteArray, tag⟩]⟩ := by
  unfold decideWith
  rcases hr : held.headRecord with _ | record
  · simp
  rcases hc : held.candidate with _ | tag
  · simp
  simp only
  by_cases hv' : verifies tag = true
  · simp only [hv', reduceCtorEq, if_false]
    by_cases below : held.height < birthHeight
    · simp only [below, if_true]
      constructor
      · intro h; cases h
      · rintro ⟨_, _, _, _, _, le, _⟩; omega
    · simp only [below, if_false]
      rcases physical with _ | tip
      · simp
      · dsimp only
        by_cases ok : tip.head = held.height ∧ tip.entries = [⟨record.toByteArray, tag⟩]
        · rw [if_pos ok]
          constructor
          · intro _
            refine ⟨record, tag, rfl, rfl, hv', by omega, ?_⟩
            obtain ⟨a, b⟩ := ok
            cases tip; simp_all
          · intro _; rfl
        · rw [if_neg ok]
          constructor
          · intro h; cases h
          · rintro ⟨r, t, hr', hc', _, _, hp⟩
            have e1 : record = r := Option.some.inj hr'
            have e2 : tag = t := Option.some.inj hc'
            subst e1; subst e2
            have hp' := Option.some.inj hp
            subst hp'
            exact absurd ⟨rfl, rfl⟩ ok
  · have hv : verifies tag = false := by simpa using hv'
    simp only [hv, if_true]
    constructor
    · intro h; cases h
    · rintro ⟨r, t, _, hc', hv2, _⟩
      have e2 : tag = t := Option.some.inj hc'
      subst e2
      exact absurd hv2 hv'

/-- The statement, read: the head record, a candidate tag that
`Head.verify` accepts, birth height, and the exact physical tip. -/
theorem hotRegistration_iff (birthHeight : Nat) (held : Held) (physical : Option Physical) :
    HotRegistrationAdmitted birthHeight held physical ↔
      ∃ record tag, held.headRecord = some record ∧
        (held.headTag = some tag ∨ (held.headTag = none ∧ held.readTag = some tag)) ∧
        (∃ frontier head, held.frontier = some frontier ∧
          Head.verify held.store held.height tag held.chain frontier = .ok head) ∧
        birthHeight ≤ held.height ∧
        physical = some ⟨held.height, [⟨record.toByteArray, tag⟩]⟩ := by
  unfold HotRegistrationAdmitted verdict
  rw [decideWith_iff]
  have cand : ∀ tag, held.candidate = some tag ↔
      (held.headTag = some tag ∨ (held.headTag = none ∧ held.readTag = some tag)) := by
    intro tag
    unfold Held.candidate
    rcases held.headTag with _ | t <;> rcases held.readTag with _ | r <;> simp [Option.or]
  have auth : ∀ tag, held.authentic tag = true ↔
      ∃ frontier head, held.frontier = some frontier ∧
        Head.verify held.store held.height tag held.chain frontier = .ok head := by
    intro tag
    unfold Held.authentic
    rcases hf : held.frontier with _ | frontier
    · simp
    · constructor
      · intro h
        cases hv : Head.verify held.store held.height tag held.chain frontier with
        | error r => simp [hv] at h
        | ok head => exact ⟨frontier, head, rfl, hv⟩
      · rintro ⟨f, head, hf', hv⟩
        have e := Option.some.inj hf'
        subst e
        simp [hv]
  constructor
  · rintro ⟨r, t, h1, h2, h3, h4, h5⟩
    exact ⟨r, t, h1, (cand t).1 h2, (auth t).1 h3, h4, h5⟩
  · rintro ⟨r, t, h1, h2, h3, h4, h5⟩
    exact ⟨r, t, h1, (cand t).2 h2, (auth t).2 h3, h4, h5⟩

/-! ## The poles -/

private def tagBytes : List UInt8 := [7]
private def recordBytes : List UInt8 := [1, 2, 3]

/-- A session image at height 5 that carries no tag (it was extended in
memory), for any Store, chain and frontier. -/
def untagged (store : StoreIdentity) (chain : Digest) (frontier : Option (List (Nat × Digest)))
    (readTag : Option (List UInt8)) : Held :=
  ⟨5, some recordBytes, none, readTag, store, chain, frontier⟩

def tipAt (tag : List UInt8) : Option Physical := some ⟨5, [⟨recordBytes, tag⟩]⟩

/-- What the Host writes verifies: for every key, log start, chain, carried
values and frontier, the trailer at a height is accepted by `Head.verify`
(a `Head` is only ever obtained from the verifier). -/
theorem verify_trailer_ok (key : MacKey) (logStart chain root indexRoot : Digest)
    (height : Nat) (frontier : List (Nat × Digest)) :
    ∃ head, Head.verify (StoreIdentity.ofOpen key logStart) height
      (trailer key height ⟨root, chain, frontierDigest height frontier, indexRoot⟩) chain frontier
      = .ok head := by
  simp only [Head.verify, trailerCarried_trailer]
  split
  · exact ⟨_, rfl⟩
  · rename_i r hr
    exact absurd ((verifyTagged_trailer key height
      ⟨root, chain, frontierDigest height frontier, indexRoot⟩).symm.trans hr) (by intro h; cases h)

/-- Satisfiable (the defect case): an image with no carried tag, whose head entry
read back from the Store authenticates under the open's own verifier at the
image's height, chain and frontier, is admitted at the exact tip. For any Store
key, log start, chain, frontier and carried values. -/
theorem satisfiable_verified_reread (key : MacKey) (logStart chain root indexRoot : Digest)
    (frontier : List (Nat × Digest)) :
    let tag := trailer key 5 ⟨root, chain, frontierDigest 5 frontier, indexRoot⟩
    HotRegistrationAdmitted 3
      (untagged (StoreIdentity.ofOpen key logStart) chain (some frontier) (some tag))
      (tipAt tag) := by
  intro tag
  rw [hotRegistration_iff]
  obtain ⟨head, hv⟩ := verify_trailer_ok key logStart chain root indexRoot 5 frontier
  exact ⟨recordBytes, tag, rfl, Or.inr ⟨rfl, rfl⟩, ⟨frontier, head, rfl, hv⟩, by simp [untagged], rfl⟩

/-- Satisfiable: the same with the tag carried by the image. -/
theorem satisfiable_held_tag (key : MacKey) (logStart chain root indexRoot : Digest)
    (frontier : List (Nat × Digest)) :
    let tag := trailer key 5 ⟨root, chain, frontierDigest 5 frontier, indexRoot⟩
    HotRegistrationAdmitted 3
      ⟨5, some recordBytes, some tag, none, StoreIdentity.ofOpen key logStart, chain, some frontier⟩
      (tipAt tag) := by
  intro tag
  rw [hotRegistration_iff]
  obtain ⟨head, hv⟩ := verify_trailer_ok key logStart chain root indexRoot 5 frontier
  exact ⟨recordBytes, tag, rfl, Or.inl rfl, ⟨frontier, head, rfl, hv⟩, by simp, rfl⟩

/-- Teeth, by name: no tag carried and none read back. -/
theorem teeth_noOpeningRead (s : StoreIdentity) (c : Digest) (f : Option (List (Nat × Digest)))
    (t : List UInt8) : verdict 3 (untagged s c f none) (tipAt t) = .noOpeningRead := by
  simp [verdict, decideWith, untagged, Held.candidate]

/-- Teeth: a tag read back that is the tip's own tag but does not authenticate
(an image never read from the Store has no frontier to verify against) is no
opening read. This is the copied-tag forgery. -/
theorem teeth_copiedTagUnverified (s : StoreIdentity) (c : Digest) (t : List UInt8) :
    verdict 3 (untagged s c none (some t)) (tipAt t) = .openingUnverified := by
  simp [verdict, decideWith, untagged, Held.candidate, Held.authentic]

theorem decideWith_unverified (v : List UInt8 → Bool) (b : Nat) (h : Held) (p : Option Physical)
    (record tag : List UInt8) (hr : h.headRecord = some record) (hc : h.candidate = some tag)
    (hv : v tag = false) : decideWith v b h p = .openingUnverified := by
  simp [decideWith, hr, hc, hv]

/-- Teeth: any tag that fails `Head.verify` is refused, whatever the tip. -/
theorem teeth_failedVerify (s : StoreIdentity) (c : Digest) (f : List (Nat × Digest))
    (t : List UInt8) (p : Option Physical) (bad : ∀ h, Head.verify s 5 t c f ≠ .ok h) :
    verdict 3 (untagged s c (some f) (some t)) p = .openingUnverified := by
  have auth : (untagged s c (some f) (some t)).authentic t = false := by
    cases hv : Head.verify s 5 t c f with
    | error r => simp [Held.authentic, untagged, hv]
    | ok h => exact absurd hv (bad h)
  exact decideWith_unverified _ 3 _ p recordBytes t rfl rfl auth

/-- Teeth: a stale tip (the Store moved on past the session's head). -/
theorem teeth_staleTip (v : List UInt8 → Bool) (s : StoreIdentity) (c : Digest)
    (f : Option (List (Nat × Digest))) (hv : v tagBytes = true) :
    decideWith v 3 (untagged s c f (some tagBytes)) (some ⟨6, [⟨[9], [9]⟩]⟩) = .tipChanged := by
  simp [decideWith, untagged, Held.candidate, hv]

/-- Teeth: a tip whose head entry carries another tag at the same height. -/
theorem teeth_forkedTip (v : List UInt8 → Bool) (s : StoreIdentity) (c : Digest)
    (f : Option (List (Nat × Digest))) (hv : v tagBytes = true) :
    decideWith v 3 (untagged s c f (some tagBytes)) (tipAt [8]) = .tipChanged := by
  simpa [decideWith, untagged, Held.candidate, tipAt, tagBytes] using hv

/-- Teeth: the session image is below the grain's birth height. -/
theorem teeth_belowBirth (v : List UInt8 → Bool) (s : StoreIdentity) (c : Digest)
    (f : Option (List (Nat × Digest))) (hv : v tagBytes = true) :
    decideWith v 6 (untagged s c f (some tagBytes)) (tipAt tagBytes) = .belowBirth := by
  simp [decideWith, untagged, Held.candidate, hv]

/-- Teeth: an empty history has no head to read. -/
theorem teeth_emptyHistory (v : List UInt8 → Bool) (s : StoreIdentity) (c : Digest) :
    decideWith v 0 ⟨0, none, none, none, s, c, none⟩ (some ⟨0, []⟩) = .emptyHistory := by
  simp [decideWith]

/-- The refusals are pairwise distinct by name and by text (law 10). -/
theorem refusals_distinct :
    Verdict.noOpeningRead ≠ Verdict.tipChanged ∧ Verdict.noOpeningRead ≠ Verdict.belowBirth ∧
    Verdict.tipChanged ≠ Verdict.belowBirth ∧ Verdict.noOpeningRead ≠ Verdict.openingUnverified ∧
    gate .noOpeningRead ≠ gate .openingUnverified ∧ gate .tipChanged ≠ gate .noOpeningRead := by
  decide

/-- Premise inhabitation: the statement's premise is met by some session. -/
theorem premise_inhabited (key : MacKey) :
    ∃ (birth : Nat) (held : Held) (physical : Option Physical),
      HotRegistrationAdmitted birth held physical :=
  ⟨3, _, _, satisfiable_verified_reread key ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ []⟩

/-- No tag carried, nothing read back: never admitted. -/
theorem noRead_noAdmission (birth : Nat) (h : Held) (p : Option Physical)
    (none_ : h.headTag = none) (nov : h.readTag = none) :
    ¬ HotRegistrationAdmitted birth h p := by
  rw [hotRegistration_iff]
  rintro ⟨r, t, _, ht, _⟩
  rcases ht with ht | ⟨_, hr⟩ <;> simp_all

/-- A tag that fails `Head.verify` is never an opening read (either source). -/
theorem unverified_noAdmission (birth : Nat) (h : Held) (p : Option Physical)
    (bad : ∀ t f hd, Head.verify h.store h.height t h.chain f ≠ .ok hd) :
    ¬ HotRegistrationAdmitted birth h p := by
  rw [hotRegistration_iff]
  rintro ⟨r, t, _, _, ⟨f, hd, _, hv⟩, _⟩
  exact bad t f hd hv

/-- The IO's gate: the handoff runs iff the statement holds of what the IO read. -/
theorem handoff_runs_iff (birth : Nat) (h : Held) (p : Option Physical) :
    gate (verdict birth h p) = none ↔ HotRegistrationAdmitted birth h p :=
  gate_none_iff _

/-- The append path's pin: the image an append returns carries the tag the append
wrote, so the Host's own successor image keeps its head authentication and is
admitted on the carried tag without a re-read. Cannot regress to `none`
silently. -/
theorem appended_headTag {rootBytes : List UInt8 → Digest}
    {loaded : DurableReceiverIO.Loaded rootBytes} {intent : DurableDataIntent.DataIntent rootBytes}
    (a : DurableReceiverIO.Appended rootBytes loaded intent) :
    a.next.headTag = some a.entry.tag := a.headTagExact

#assert_axioms gate_none_iff
#assert_axioms gate_injective
#assert_axioms decideWith_iff
#assert_axioms verify_trailer_ok
#assert_axioms decideWith_unverified
#assert_axioms hotRegistration_iff
#assert_axioms satisfiable_verified_reread
#assert_axioms satisfiable_held_tag
#assert_axioms teeth_noOpeningRead
#assert_axioms teeth_copiedTagUnverified
#assert_axioms teeth_failedVerify
#assert_axioms teeth_staleTip
#assert_axioms teeth_forkedTip
#assert_axioms teeth_belowBirth
#assert_axioms teeth_emptyHistory
#assert_axioms refusals_distinct
#assert_axioms premise_inhabited
#assert_axioms noRead_noAdmission
#assert_axioms unverified_noAdmission
#assert_axioms handoff_runs_iff
#assert_axioms appended_headTag

end Minidregg.Kernel.ApplicationStreamContinuityFresh
