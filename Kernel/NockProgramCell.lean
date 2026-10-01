/-
# Kernel.NockProgramCell — the program's sample, and the program cell's reads

`sampleOf` is NOCK §2.3's subject: the kernel, not the runner, builds the noun
a program is slammed with, from the command's projected participant slots and
the program's `Abi`. Layout (the one `nock-run --sample-json` builds, so a runner
and the kernel agree byte for byte):

    [[height caller room] ~[['target/0' id0] … ['target/n' idn] [key0 v0] … [keym vm]]]

The target entries are the command's target cell ids in the signed target
order: two sheets given to one program yield different samples
(`sampleOf_targets_injective`), which the §2.3 draft could not tell apart. The
slot entries follow `Abi.sample` in order; a missing slot, or a negative value in
a `nat` slot, refuses (`none`) rather than defaulting — absence is not zero.

The reads (`checkProgram`, `showProgram`, `sampleFor`) are what host ops 131,
118, 119 serve. The WRITE is the ordinary resource birth (`storage: "nock"`).
-/
import Compiler.NockProgramCodec
import Compiler.CanonicalCellRegistry

namespace Minidregg.Kernel.NockProgramCell

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NockProgramCodec

set_option autoImplicit false

/-! ## The sample -/

/-- What the kernel knows about a run besides the observed values. `room` is an
atom (0 = no room), as `forge.hoon`'s `room=@` and the runner read it. -/
structure Context where
  height : Nat
  caller : Nat
  room : Nat
  deriving DecidableEq, Repr

/-- Hoon `@t`: UTF-8 bytes, least significant first. -/
def cordValue : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * cordValue rest

def cord (s : String) : Noun := .atom (cordValue s.toUTF8.toList)

/-- A null-terminated Nock list. -/
def nockList : List Noun → Noun
  | [] => .atom 0
  | x :: rest => .cell x (nockList rest)

def encodeValue : SlotType → Int → Option Noun
  | .nat, .ofNat n => some (.atom n)
  | .nat, .negSucc _ => none
  | .int, z => some z.toNoun

def targetKey (i : Nat) : String := targetPrefix ++ toString i

/-- `['target/i' id]` for each command target, in command order. -/
def targetEntries : Nat → List Nat → List Noun
  | _, [] => []
  | i, id :: rest => .cell (cord (targetKey i)) (.atom id) :: targetEntries (i + 1) rest

/-- `[key value]` for each ABI sample slot, in ABI order. -/
def sampleSlots (read : Nat → String → Option Int) : List SampleSlot → Option (List Noun)
  | [] => some []
  | slot :: rest =>
    match read slot.target slot.slot with
    | none => none
    | some value =>
      match encodeValue slot.type value with
      | none => none
      | some noun => (sampleSlots read rest).map (.cell (cord slot.key) noun :: ·)

def contextNoun (ctx : Context) : Noun :=
  .cell (.atom ctx.height) (.cell (.atom ctx.caller) (.atom ctx.room))

/-- The sample. `targets` are the command's target cell ids in command order;
`read i slot` is the projected participant slot `slot` of target `i`. -/
def sampleOf (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) : Option Noun :=
  if abi.sample.all (fun slot => decide (slot.target < targets.length)) then
    (sampleSlots read abi.sample).map fun slots =>
      .cell (contextNoun ctx) (nockList (targetEntries 0 targets ++ slots))
  else none

theorem encodeValue_injective {type : SlotType} {a b : Int} {n : Noun}
    (ha : encodeValue type a = some n) (hb : encodeValue type b = some n) : a = b := by
  cases type with
  | nat =>
    cases a <;> cases b <;> simp [encodeValue] at ha hb
    subst ha; cases hb; rfl
  | int =>
    simp only [encodeValue, Option.some.injEq] at ha hb
    exact Noun.toNoun_injective (ha.trans hb.symm)

theorem sampleSlots_cons {read : Nat → String → Option Int} {slot : SampleSlot}
    {rest : List SampleSlot} {nouns : List Noun}
    (h : sampleSlots read (slot :: rest) = some nouns) :
    ∃ v n tail, read slot.target slot.slot = some v ∧ encodeValue slot.type v = some n ∧
      sampleSlots read rest = some tail ∧ nouns = .cell (cord slot.key) n :: tail := by
  simp only [sampleSlots] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · rename_i n hn
      cases hr : sampleSlots read rest with
      | none => rw [hr] at h; cases h
      | some tail =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨v, n, tail, hv, hn, rfl, h.symm⟩

theorem sampleSlots_length {read : Nat → String → Option Int} :
    ∀ {slots : List SampleSlot} {nouns : List Noun},
      sampleSlots read slots = some nouns → nouns.length = slots.length
  | [], nouns, h => by simp [sampleSlots] at h; subst h; rfl
  | slot :: rest, nouns, h => by
    obtain ⟨_, _, tail, _, _, hr, rfl⟩ := sampleSlots_cons h
    simp [sampleSlots_length hr]

theorem sampleSlots_injective {read read' : Nat → String → Option Int} :
    ∀ {slots : List SampleSlot} {nouns : List Noun},
      sampleSlots read slots = some nouns → sampleSlots read' slots = some nouns →
        ∀ slot ∈ slots, read slot.target slot.slot = read' slot.target slot.slot
  | [], _, _, _ => by simp
  | slot :: rest, nouns, h, h' => by
    obtain ⟨v, n, tail, hv, he, hr, rfl⟩ := sampleSlots_cons h
    obtain ⟨v', n', tail', hv', he', hr', same⟩ := sampleSlots_cons h'
    simp only [List.cons.injEq, Noun.cell.injEq, true_and] at same
    obtain ⟨hn, ht⟩ := same
    subst hn
    subst ht
    have hvv : v = v' := encodeValue_injective he he'
    intro s member
    rcases List.mem_cons.mp member with head | tail
    · subst head; rw [hv, hv', hvv]
    · exact sampleSlots_injective hr hr' s tail

theorem nockList_injective : ∀ {a b : List Noun}, nockList a = nockList b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [nockList] at h
  | _ :: _, [], h => by simp [nockList] at h
  | x :: xs, y :: ys, h => by
    simp only [nockList, Noun.cell.injEq] at h
    rw [h.1, nockList_injective h.2]

theorem targetEntries_length : ∀ (i : Nat) (ids : List Nat),
    (targetEntries i ids).length = ids.length
  | _, [] => rfl
  | i, _ :: rest => by simp [targetEntries, targetEntries_length (i + 1) rest]

theorem targetEntries_injective : ∀ {i : Nat} {a b : List Nat},
    targetEntries i a = targetEntries i b → a = b
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by simp [targetEntries] at h
  | _, _ :: _, [], h => by simp [targetEntries] at h
  | i, x :: xs, y :: ys, h => by
    simp only [targetEntries, List.cons.injEq, Noun.cell.injEq, Noun.atom.injEq, true_and] at h
    rw [h.1, targetEntries_injective h.2]

/-- **`sampleOf_injective`** (NOCK §3.3): one sample noun determines the
context, the target ids, and every value the ABI reads. Distinct targets or
distinct slot values give distinct nouns. -/
theorem sampleOf_injective {abi : Abi} {ctx ctx' : Context} {targets targets' : List Nat}
    {read read' : Nat → String → Option Int} {n : Noun}
    (h : sampleOf abi ctx targets read = some n) (h' : sampleOf abi ctx' targets' read' = some n) :
    ctx = ctx' ∧ targets = targets' ∧
      ∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot := by
  unfold sampleOf at h h'
  split at h
  · split at h'
    · cases hs : sampleSlots read abi.sample with
      | none => rw [hs] at h; cases h
      | some slots =>
        cases hs' : sampleSlots read' abi.sample with
        | none => rw [hs'] at h'; cases h'
        | some slots' =>
          rw [hs] at h
          rw [hs'] at h'
          simp only [Option.map_some, Option.some.injEq] at h h'
          have same := h.trans h'.symm
          simp only [contextNoun, Noun.cell.injEq, Noun.atom.injEq] at same
          obtain ⟨⟨hh, hc, hr⟩, rest⟩ := same
          have lists := nockList_injective rest
          have lens : slots.length = slots'.length := by
            rw [sampleSlots_length hs, sampleSlots_length hs']
          obtain ⟨ht, hl⟩ := List.append_inj' lists lens
          subst hl
          refine ⟨?_, targetEntries_injective ht, sampleSlots_injective hs hs'⟩
          cases ctx; cases ctx'; simp_all
    · cases h'
  · cases h

theorem sampleOf_targets_injective {abi : Abi} {ctx : Context} {targets targets' : List Nat}
    {read read' : Nat → String → Option Int} {n : Noun}
    (h : sampleOf abi ctx targets read = some n) (h' : sampleOf abi ctx targets' read' = some n) :
    targets = targets' :=
  (sampleOf_injective h h').2.1

/-- **`sampleOf_deterministic`**: the sample is a function of the context, the
target ids and the values at the ABI's slots, and of nothing else a reader
could vary. -/
theorem sampleOf_deterministic (abi : Abi) (ctx : Context) (targets : List Nat)
    {read read' : Nat → String → Option Int}
    (agree : ∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot) :
    sampleOf abi ctx targets read = sampleOf abi ctx targets read' := by
  have slots : ∀ (list : List SampleSlot),
      (∀ slot ∈ list, read slot.target slot.slot = read' slot.target slot.slot) →
        sampleSlots read list = sampleSlots read' list := by
    intro list
    induction list with
    | nil => intro _; rfl
    | cons slot rest ih =>
      intro same
      simp only [sampleSlots, same slot (List.mem_cons_self ..),
        ih (fun s m => same s (List.mem_cons_of_mem _ m))]
  unfold sampleOf
  rw [slots abi.sample agree]

theorem sampleOf_absent_refused (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) (slot : SampleSlot) (named : slot ∈ abi.sample)
    (absent : read slot.target slot.slot = none) :
    sampleOf abi ctx targets read = none := by
  have none_of : ∀ (list : List SampleSlot), slot ∈ list → sampleSlots read list = none := by
    intro list
    induction list with
    | nil => intro m; cases m
    | cons head rest ih =>
      intro m
      simp only [sampleSlots]
      rcases List.mem_cons.mp m with same | later
      · subst same; simp [absent]
      · split
        · rfl
        · split
          · rfl
          · simp [ih later]
  unfold sampleOf
  split
  · simp [none_of abi.sample named]
  · rfl

theorem sampleOf_foreign_target_refused (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) (slot : SampleSlot) (named : slot ∈ abi.sample)
    (beyond : targets.length ≤ slot.target) :
    sampleOf abi ctx targets read = none := by
  unfold sampleOf
  have : abi.sample.all (fun slot => decide (slot.target < targets.length)) = false := by
    rw [List.all_eq_false]
    exact ⟨slot, named, by simp; omega⟩
  simp [this]

/-- The sample the kernel hands a runner is canonical jam bytes. -/
theorem sample_jam_canonical (n : Noun) : Noun.canonical (Noun.jam n) = true :=
  Noun.canonical_jam n

/-! ## Reads served to the client (ops 131–133) -/

/-- Op 131: what a birth of these bytes would meet, against the live store. -/
inductive CheckVerdict where
  | malformed
  | refused (reason : Refusal)
  | admissible (program : Program) (id : Digest) (code : Digest) (cellId : Nat) (present : Bool)

def checkProgram (domain : Digest) (directory : Directory Nat CanonicalCellRegistry.registry)
    (program : Program) : CheckVerdict :=
  match check program with
  | .error reason => .refused reason
  | .ok () =>
    if CanonicalCellRegistry.librariesPresent domain directory program then
      let id := programId program
      .admissible program id (codeDigest program.jam)
        (CanonicalCellRegistry.programCellId domain program)
        (CanonicalCellRegistry.loadProgram domain directory id).isSome
    else .refused .missingLibrary

/-- Op 133: the canonical sample jam for a stored program. `values` are
`(target index, slot, value)` triples; a duplicate `(index, slot)` refuses. -/
inductive SampleVerdict where
  | missingProgram
  | ambiguousValues
  | refused
  | sample (jam : List UInt8)

def readOf (values : List (Nat × String × Int)) (i : Nat) (slot : String) : Option Int :=
  (values.find? fun v => v.1 = i ∧ v.2.1 = slot).map fun v => v.2.2

def sampleFor (domain : Digest) (directory : Directory Nat CanonicalCellRegistry.registry)
    (id : Digest) (ctx : Context) (targets : List Nat) (values : List (Nat × String × Int)) :
    SampleVerdict :=
  match CanonicalCellRegistry.loadProgram domain directory id with
  | none => .missingProgram
  | some program =>
    if (values.map fun v => (v.1, v.2.1)).Nodup then
      match sampleOf program.abi ctx targets (readOf values) with
      | none => .refused
      | some noun => .sample (Noun.jam noun)
    else .ambiguousValues

end Minidregg.Kernel.NockProgramCell

/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_injective
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_targets_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_targets_injective
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_deterministic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_deterministic
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_absent_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_absent_refused
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_foreign_target_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_foreign_target_refused
