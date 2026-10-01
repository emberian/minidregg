/-
# Kernel.NockEntry — Nock's entry into the kernel's run (moved out of `Kernel.NockRun`)

What `Compiler.Evaluator.nock` fills the kernel-facing fields with, below the
evaluator file so that `Kernel.Run` (which imports the evaluator) does not cycle:

* **`subjectFormula`** (N16): a program without libraries is a core, the run is
  `*[[P sample] slam(arm)]`; with libraries `L₁ … Lₖ` (ABI order) the program is a
  formula over `lib = [L₁ [L₂ … Lₖ]]` and the run is
  `*[[lib [P sample]] [7 [[2 [0 2] 0 6] 0 7] slam(arm)]]`.
* **`oracle`**: one `Theory.Nock.exec`, the count kept on a crash and on exhaustion
  (`Theory.Eval.Ran`). `oracle_is_export`: the byte entry point
  `@[export minidregg_nock_run_jammed]` (`runJammed`) answers the oracle's status,
  steps and the jam of its product on `jam [s f]`.
* **`decodeWrites`**: the product as a Nock list of `[cord value]` against `abi.outputs`.
* **`staleField`** (K-RUN-PIN): which named slot a stale pinned claim missed.

Nothing here is generic; the generic referee is `Kernel.Run`.
-/
import Kernel.NockProgramCell.Sample
import Theory.Nock
import Theory.Eval

namespace Minidregg.Kernel.NockEntry
open Minidregg.Theory
open Minidregg.Theory.Eval
open Minidregg.Compiler
open Minidregg.Compiler.NockProgramCodec
open Minidregg.Kernel.NockProgramCell
set_option autoImplicit false

/-! ## Decoding the product against `abi.outputs` -/

/-- A Nock list of `[key value]` with atom keys. -/
def entriesOf : Noun → Option (List (Nat × Noun))
  | .atom 0 => some []
  | .cell (.cell (.atom k) v) rest => (entriesOf rest).map ((k, v) :: ·)
  | _ => none

def decodeValue : SlotType → Noun → Option Int
  | .nat, .atom n => some (.ofNat n)
  | .nat, .cell _ _ => none
  | .int, n => n.toInt?
  | .noun, n => if (Noun.jam n).length ≤ nounMaxBytes then some (.ofNat (jamAtom n)) else none

/-- **`noun_output_roundtrip`** (K-RUN-PIN): a `noun` output is written as the
jam atom of the product's noun, within the birth-source bound, and a `noun`
sample slot reading that field gets the same noun back — so one program's noun
output is the next program's (or the next segment's) noun input, unaltered. -/
theorem noun_output_roundtrip {n : Noun} {value : Int} (written : decodeValue .noun n = some value) :
    value = .ofNat (jamAtom n) ∧ (Noun.jam n).length ≤ nounMaxBytes ∧
      encodeValue .noun value = some n := by
  simp only [decodeValue] at written
  split at written
  · rename_i bound
    cases written
    exact ⟨rfl, bound, ofJamAtom_jamAtom n⟩
  · cases written

/-- A `noun` output above the bound writes nothing. -/
theorem noun_output_bounded {n : Noun} (big : nounMaxBytes < (Noun.jam n).length) :
    decodeValue .noun n = none := by
  simp [decodeValue]; omega

def decodeEntry (outputs : List OutputSlot) (entry : Nat × Noun) : Option FieldWrite :=
  match outputs.find? (fun o => cordValue o.key.toUTF8.toList == entry.1) with
  | none => none
  | some o => (decodeValue o.type entry.2).map fun value => ⟨o.target, o.field, value⟩

/-- The writes a product names. Each `(target, field)` at most once. -/
def decodeWrites (abi : Abi) (out : Noun) : Option (List FieldWrite) := do
  let entries ← entriesOf out
  let writes ← entries.mapM (decodeEntry abi.outputs)
  if (writes.map fun w => (w.target, w.field)).Nodup then some writes else none

/-! ## The subject and formula (N16) -/

/-- `[L₁ [L₂ … Lₖ]]`. -/
def libraryNoun : List Noun → Noun
  | [] => .atom 0
  | [l] => l
  | l :: rest => .cell l (libraryNoun rest)

/-- `[7 [[2 [0 2] 0 6] 0 7] slam]`: build `[*[lib P] sample]`, then slam it. -/
def libraryFormula (arm : Nat) : Noun :=
  Nock.op 7 (.cell (.cell (Nock.op 2 (.cell (Nock.op 0 (.atom 2)) (Nock.op 0 (.atom 6))))
    (Nock.op 0 (.atom 7))) (Nock.slam arm))

def subjectFormula (arm : Nat) (program : Noun) (libraries : List Noun) (sample : Noun) :
    Noun × Noun :=
  match libraries with
  | [] => (.cell program sample, Nock.slam arm)
  | _ => (.cell (libraryNoun libraries) (.cell program sample), libraryFormula arm)

/-! ## Which field a stale pinned claim missed -/

/-- The items of a null-terminated Nock list. -/
def listItems : Noun → Option (List Noun)
  | .atom 0 => some []
  | .cell x rest => (listItems rest).map (x :: ·)
  | _ => none

theorem listItems_nockList : ∀ (items : List Noun), listItems (nockList items) = some items
  | [] => rfl
  | x :: rest => by simp [nockList, listItems, listItems_nockList rest]

/-- The key of the first slot whose kernel entry is not the claimed entry. -/
def firstStale : List SampleSlot → List Noun → List Noun → Option String
  | slot :: rest, k :: ks, c :: cs => if k = c then firstStale rest ks cs else some slot.key
  | slot :: _, _ :: _, [] => some slot.key
  | _, _, _ => none

/-- Under `pinned`, the key of the first ABI slot whose entry in the claimed
sample differs from the kernel's `sample`, when the two agree on everything
before the slots (the context and the target entries). `none` under `live`,
where the height alone moves the sample, and when the claim differs elsewhere. -/
def staleField (abi : Abi) (sample : Noun) (claimed : List UInt8) : Option String :=
  match abi.context, sample, Noun.cue claimed with
  | .pinned, .cell kc kernelList, some (.cell cc claimedList) =>
    match listItems kernelList, listItems claimedList with
    | some ks, some cs =>
      let offset := ks.length - abi.sample.length
      if kc = cc ∧ ks.take offset = cs.take offset then
        firstStale abi.sample (ks.drop offset) (cs.drop offset)
      else none
    | _, _ => none
  | _, _, _ => none

theorem firstStale_only {read read' : Nat → String → Option Int} {slot : SampleSlot} :
    ∀ {slots : List SampleSlot} {ns ns' : List Noun},
      sampleSlots read slots = some ns → sampleSlots read' slots = some ns' →
      slot ∈ slots → read slot.target slot.slot ≠ read' slot.target slot.slot →
      (∀ s ∈ slots, s ≠ slot → read s.target s.slot = read' s.target s.slot) →
      firstStale slots ns' ns = some slot.key
  | [], _, _, _, _, member, _, _ => by cases member
  | s :: rest, ns, ns', h, h', member, changed, only => by
    obtain ⟨v, n, tail, hv, he, -, hr, rfl⟩ := sampleSlots_cons h
    obtain ⟨v', n', tail', hv', he', -, hr', rfl⟩ := sampleSlots_cons h'
    by_cases same : s = slot
    · subst same
      have differ : ¬ (Noun.cell (cord s.key) n' = Noun.cell (cord s.key) n) := by
        intro e
        simp only [Noun.cell.injEq, true_and] at e
        subst e
        exact changed (by rw [hv, hv', encodeValue_injective he he'])
      simp only [firstStale, if_neg differ]
    · obtain rfl : v = v' := Option.some.inj ((hv.symm.trans (only s (List.mem_cons_self ..) same)).trans hv')
      obtain rfl : n' = n := Option.some.inj (he'.symm.trans he)
      have m : slot ∈ rest := by
        rcases List.mem_cons.mp member with e | m
        · exact absurd e.symm same
        · exact m
      simp only [firstStale, if_pos rfl]
      exact firstStale_only hr hr' m changed (fun t mt nt => only t (List.mem_cons_of_mem _ mt) nt)

/-- **`staleField_names`** (K-RUN-PIN): two samples of a pinned program built over
reads that differ in exactly one named slot are different, and `staleField` names
that slot's key on the jam of the earlier one — the Nock instance of
`Evaluator.staleField_names`. -/
theorem staleField_names {abi : Abi} {ctx ctx' : Context} {targets : List Nat}
    {read read' : Nat → String → Option Int} {sample sample' : Noun} {slot : SampleSlot}
    (pinned : abi.context = .pinned)
    (claimed : sampleOf abi ctx targets read = some sample)
    (current : sampleOf abi ctx' targets read' = some sample')
    (named : slot ∈ abi.sample)
    (changed : read slot.target slot.slot ≠ read' slot.target slot.slot)
    (only : ∀ s ∈ abi.sample, s ≠ slot → read s.target s.slot = read' s.target s.slot) :
    sample ≠ sample' ∧ staleField abi sample' (Noun.jam sample) = some slot.key := by
  refine ⟨fun same => ?_, ?_⟩
  · subst same
    exact changed ((sampleOf_injective claimed current).2.2 slot named)
  unfold sampleOf at claimed current
  split at claimed
  · rename_i inRange
    rw [if_pos inRange] at current
    cases hs : sampleSlots read abi.sample with
    | none => rw [hs] at claimed; cases claimed
    | some ns =>
      cases hs' : sampleSlots read' abi.sample with
      | none => rw [hs'] at current; cases current
      | some ns' =>
        rw [hs] at claimed
        rw [hs'] at current
        simp only [Option.map_some, Option.some.injEq] at claimed current
        subst claimed
        subst current
        have len := sampleSlots_length hs
        have len' := sampleSlots_length hs'
        have off : (targetEntries 0 targets ++ ns').length - abi.sample.length =
            (targetEntries 0 targets).length := by
          simp only [List.length_append, len']; omega
        have takeK : (targetEntries 0 targets ++ ns').take (targetEntries 0 targets).length =
            targetEntries 0 targets := List.take_left' rfl
        have takeC : (targetEntries 0 targets ++ ns).take (targetEntries 0 targets).length =
            targetEntries 0 targets := List.take_left' rfl
        have dropK : (targetEntries 0 targets ++ ns').drop (targetEntries 0 targets).length =
            ns' := List.drop_left' rfl
        have dropC : (targetEntries 0 targets ++ ns).drop (targetEntries 0 targets).length =
            ns := List.drop_left' rfl
        unfold staleField
        rw [Noun.cue_jam, pinned]
        simp only [listItems_nockList, contextOf]
        rw [off, takeK, takeC, dropK, dropC, if_pos (by simp)]
        exact firstStale_only hs hs' named changed only
  · cases claimed

/-! ## The oracle -/

/-- One evaluation of `*[s f]` with `fuel` steps. -/
def oracle (fuel : Nat) (s f : Noun) : Ran Noun :=
  match Nock.exec fuel fuel s f with
  | .ok v r => .ok v (fuel - r)
  | .crash r => .crash (fuel - r)
  | .exhausted => .exhausted fuel

/-- **The oracle is the export.** `runJammed` (behind `@[export
minidregg_nock_run_jammed]`) answers the oracle's status and steps on `jam [s f]`,
and its output bytes are the jam of the oracle's product. -/
theorem oracle_is_export (fuel : Nat) (s f : Noun) :
    Nock.runJammed fuel (Noun.jam (.cell s f)) =
      match oracle fuel s f with
      | .ok v k => .ok k (Noun.jam v)
      | .crash k => .crash k
      | .exhausted k => .exhausted k := by
  simp only [Nock.runJammed, oracle, Noun.cue_jam]
  cases Nock.exec fuel fuel s f <;> rfl

theorem oracle_ok_step {fuel : Nat} {s f v : Noun} {k : Nat} (h : oracle fuel s f = .ok v k) :
    Nock.Step s f v ∧ Nock.run fuel s f = .ok v ∧ Nock.steps fuel s f = k := by
  unfold oracle at h
  split at h
  · rename_i v' r he
    cases h
    refine ⟨(Nock.exec_sound _ _ _ _).1 _ _ he, ?_, ?_⟩
    · unfold Nock.run; rw [he]
    · unfold Nock.steps; rw [he]
  · cases h
  · cases h

/-- A crash the oracle reports is a crash of the term (`Theory.Nock.Crash`), not of the fuel. -/
theorem oracle_crash {fuel : Nat} {s f : Noun} {k : Nat} (h : oracle fuel s f = .crash k) :
    Nock.Crash s f := by
  unfold oracle at h
  split at h
  · cases h
  · rename_i r he
    exact Nock.run_crash_iff.mp ⟨fuel, by unfold Nock.run; rw [he]⟩
  · cases h

/-- The oracle runs out of fuel only at the whole budget, and says only that. -/
theorem oracle_exhausted {fuel : Nat} {s f : Noun} {k : Nat} (h : oracle fuel s f = .exhausted k) :
    Nock.run fuel s f = .error .exhausted ∧ k = fuel := by
  unfold oracle at h
  split at h
  · cases h
  · cases h
  · rename_i he
    cases h
    exact ⟨by unfold Nock.run; rw [he], rfl⟩

end Minidregg.Kernel.NockEntry

/-- info: 'Minidregg.Kernel.NockEntry.noun_output_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.noun_output_roundtrip
/-- info: 'Minidregg.Kernel.NockEntry.noun_output_bounded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.noun_output_bounded
/-- info: 'Minidregg.Kernel.NockEntry.listItems_nockList' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.listItems_nockList
/-- info: 'Minidregg.Kernel.NockEntry.firstStale_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.firstStale_only
/-- info: 'Minidregg.Kernel.NockEntry.staleField_names' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.staleField_names
/-- info: 'Minidregg.Kernel.NockEntry.oracle_is_export' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.oracle_is_export
/-- info: 'Minidregg.Kernel.NockEntry.oracle_ok_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.oracle_ok_step
/-- info: 'Minidregg.Kernel.NockEntry.oracle_crash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.oracle_crash
/-- info: 'Minidregg.Kernel.NockEntry.oracle_exhausted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.oracle_exhausted
