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
import Theory.NockCost.Shape

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

/-- A sample value within its slot's declared maximum (`SampleSlot.max`, NC-2); an undeclared
slot takes any atom. -/
def withinMax (slot : SampleSlot) : Noun → Bool
  | .atom k =>
    match slot.max with
    | some m => decide (k ≤ m)
    | none => true
  | .cell _ _ => slot.max.isNone

/-- `[key value]` for each ABI sample slot, in ABI order. A value above its slot's declared
maximum refuses (`none`), as an absent one does. -/
def sampleSlots (read : Nat → String → Option Int) : List SampleSlot → Option (List Noun)
  | [] => some []
  | slot :: rest =>
    match read slot.target slot.slot with
    | none => none
    | some value =>
      match encodeValue slot.type value with
      | none => none
      | some noun =>
        if withinMax slot noun then (sampleSlots read rest).map (.cell (cord slot.key) noun :: ·)
        else none

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
      withinMax slot n = true ∧ sampleSlots read rest = some tail ∧
        nouns = .cell (cord slot.key) n :: tail := by
  simp only [sampleSlots] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · rename_i n hn
      split at h
      · rename_i hw
        cases hr : sampleSlots read rest with
        | none => rw [hr] at h; cases h
        | some tail =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          exact ⟨v, n, tail, hv, hn, hw, rfl, h.symm⟩
      · cases h

theorem sampleSlots_length {read : Nat → String → Option Int} :
    ∀ {slots : List SampleSlot} {nouns : List Noun},
      sampleSlots read slots = some nouns → nouns.length = slots.length
  | [], nouns, h => by simp [sampleSlots] at h; subst h; rfl
  | slot :: rest, nouns, h => by
    obtain ⟨_, _, tail, _, _, _, hr, rfl⟩ := sampleSlots_cons h
    simp [sampleSlots_length hr]

theorem sampleSlots_injective {read read' : Nat → String → Option Int} :
    ∀ {slots : List SampleSlot} {nouns : List Noun},
      sampleSlots read slots = some nouns → sampleSlots read' slots = some nouns →
        ∀ slot ∈ slots, read slot.target slot.slot = read' slot.target slot.slot
  | [], _, _, _ => by simp
  | slot :: rest, nouns, h, h' => by
    obtain ⟨v, n, tail, hv, he, -, hr, rfl⟩ := sampleSlots_cons h
    obtain ⟨v', n', tail', hv', he', -, hr', same⟩ := sampleSlots_cons h'
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

/-! ## The declared maximum (NC-2): a refusal by name, and the shape it buys

A program that declares `max` on its sample slots is handed only samples inside the box
`shapeOf abi`, so its step bound can be read from the box at birth
(`Theory.NockCost.Summaries.costSym`; `cost_sym_sound` makes it a price for every such sample). -/

/-- The first sample slot whose value is present, encodes, and lies above the slot's declared
maximum: what admission refuses `fieldOverMax` (before the sample is built). -/
def overMax (read : Nat → String → Option Int) : List SampleSlot → Option SampleSlot
  | [] => none
  | slot :: rest =>
    match read slot.target slot.slot with
    | none => overMax read rest
    | some value =>
      match encodeValue slot.type value with
      | none => overMax read rest
      | some noun => if withinMax slot noun then overMax read rest else some slot

theorem sampleSlots_overMax {read : Nat → String → Option Int} :
    ∀ {slots : List SampleSlot} {slot : SampleSlot}, overMax read slots = some slot →
      sampleSlots read slots = none
  | [], _, h => by simp [overMax] at h
  | head :: rest, slot, h => by
    simp only [overMax] at h
    simp only [sampleSlots]
    split
    · rfl
    · rename_i v hv
      rw [hv] at h
      simp only at h
      split
      · rfl
      · rename_i n hn
        rw [hn] at h
        simp only at h
        split_ifs at h ⊢ with hw
        · simp [sampleSlots_overMax h]
        · rfl

/-- **`sampleOf_overMax_refused`**: a value above its slot's declared maximum leaves no sample. -/
theorem sampleOf_overMax_refused (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) {slot : SampleSlot}
    (above : overMax read abi.sample = some slot) : sampleOf abi ctx targets read = none := by
  unfold sampleOf
  split
  · simp [sampleSlots_overMax above]
  · rfl

open Minidregg.Theory.NockCost (Shape fits HasShape)

/-- What a slot admits: `[0, max]` when declared, any atom otherwise. -/
def slotShape (slot : SampleSlot) : Shape :=
  match slot.max with
  | some m => .range 0 m
  | none => .atom

/-- A Nock list of exactly these element shapes. -/
def listShape : List Shape → Shape
  | [] => .exact (.atom 0)
  | sh :: rest => .cell sh (listShape rest)

/-- `['target/i' id]` for `n` targets from `i`: the key is fixed, the id any atom. -/
def targetShapes : Nat → Nat → List Shape
  | _, 0 => []
  | i, n + 1 => .cell (.exact (cord (targetKey i))) .atom :: targetShapes (i + 1) n

def contextShape : Shape := .cell .atom (.cell .atom .atom)

/-- **`shapeOf`**: the sample shape a program's ABI declares, for a command with `targets`
targets — the context, the target entries, then `[key value]` per slot with the value in
`slotShape`. -/
def shapeOf (abi : Abi) (targets : Nat) : Shape :=
  .cell contextShape (listShape (targetShapes 0 targets ++
    abi.sample.map fun slot => .cell (.exact (cord slot.key)) (slotShape slot)))

theorem encodeValue_atom {type : SlotType} {v : Int} {n : Noun} (h : encodeValue type v = some n) :
    ∃ k, n = .atom k := by
  cases type <;> cases v <;> simp [encodeValue, Int.toNoun] at h <;> exact ⟨_, h.symm⟩

theorem withinMax_fits {slot : SampleSlot} {k : Nat} (h : withinMax slot (.atom k) = true) :
    fits (.atom k) (slotShape slot) = true := by
  unfold withinMax at h; unfold slotShape
  cases hm : slot.max with
  | none => simp [fits]
  | some m => rw [hm] at h; simpa [fits] using h

theorem listShape_fits : ∀ {vs : List Noun} {shs : List Shape},
    List.Forall₂ (fun v sh => fits v sh = true) vs shs → fits (nockList vs) (listShape shs) = true
  | [], [], _ => by simp [nockList, listShape, fits]
  | _ :: _, _ :: _, .cons h rest => by simp [nockList, listShape, fits, h, listShape_fits rest]

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {a₁ : List α} {b₁ : List β} {a₂ : List α} {b₂ : List β},
      List.Forall₂ R a₁ b₁ → List.Forall₂ R a₂ b₂ → List.Forall₂ R (a₁ ++ a₂) (b₁ ++ b₂)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, .cons h t, h₂ => .cons h (forall₂_append t h₂)

theorem targetEntries_fit : ∀ (i : Nat) (ids : List Nat),
    List.Forall₂ (fun v sh => fits v sh = true) (targetEntries i ids) (targetShapes i ids.length)
  | _, [] => .nil
  | i, _ :: rest => .cons (by simp [fits]) (targetEntries_fit (i + 1) rest)

theorem sampleSlots_fit {read : Nat → String → Option Int} :
    ∀ {slots : List SampleSlot} {nouns : List Noun}, sampleSlots read slots = some nouns →
      List.Forall₂ (fun v sh => fits v sh = true) nouns
        (slots.map fun slot => .cell (.exact (cord slot.key)) (slotShape slot))
  | [], nouns, h => by simp [sampleSlots] at h; subst h; exact .nil
  | slot :: rest, nouns, h => by
    obtain ⟨_, n, tail, _, he, hw, hr, rfl⟩ := sampleSlots_cons h
    obtain ⟨k, rfl⟩ := encodeValue_atom he
    exact .cons (by simp [fits, withinMax_fits hw]) (sampleSlots_fit hr)

/-- **`declared_shape_sound`**: every sample the kernel builds lies in the box the ABI declares
(the refusals above are what make it unconditional). -/
theorem declared_shape_sound {abi : Abi} {ctx : Context} {targets : List Nat}
    {read : Nat → String → Option Int} {n : Noun} (h : sampleOf abi ctx targets read = some n) :
    HasShape n (shapeOf abi targets.length) := by
  unfold sampleOf at h
  split at h
  · cases hs : sampleSlots read abi.sample with
    | none => rw [hs] at h; cases h
    | some slots =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hl := listShape_fits (forall₂_append (targetEntries_fit 0 targets) (sampleSlots_fit hs))
      show fits _ _ = true
      simp [shapeOf, fits, contextShape, contextNoun, hl]
  · cases h

/-! Poles: forge's three inventory slots, declared `≤ 3`. -/

def poleAbi : Abi :=
  { version := abiVersion, arm := 2, fuel := 4096, libraries := [], outputs := [],
    sample := [{ target := 0, slot := "iron", key := "inv/iron", type := .nat, max := some 3 },
      { target := 0, slot := "wood", key := "inv/wood", type := .nat, max := some 3 },
      { target := 0, slot := "sword", key := "inv/sword", type := .nat, max := some 3 }] }

def poleRead (iron : Int) : Nat → String → Option Int
  | 0, "iron" => some iron
  | 0, "wood" => some 2
  | 0, "sword" => some 0
  | _, _ => none

/-- At the declared maximum: the sample is built, and it lies in the declared box. -/
theorem pole_at_max_accepted :
    (sampleOf poleAbi ⟨16, 7, 0⟩ [5] (poleRead 3)).isSome = true ∧
      overMax (poleRead 3) poleAbi.sample = none := by decide

/-- One above: refused, and `overMax` names the slot. -/
theorem pole_over_max_refused :
    sampleOf poleAbi ⟨16, 7, 0⟩ [5] (poleRead 4) = none ∧
      overMax (poleRead 4) poleAbi.sample = poleAbi.sample.head? := by decide

theorem pole_at_max_fits : ∀ n, sampleOf poleAbi ⟨16, 7, 0⟩ [5] (poleRead 3) = some n →
    HasShape n (shapeOf poleAbi 1) := fun _ h => declared_shape_sound h

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
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleSlots_overMax' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleSlots_overMax
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_overMax_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_overMax_refused
/-- info: 'Minidregg.Kernel.NockProgramCell.declared_shape_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.declared_shape_sound
/-- info: 'Minidregg.Kernel.NockProgramCell.pole_at_max_accepted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.pole_at_max_accepted
/-- info: 'Minidregg.Kernel.NockProgramCell.pole_over_max_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.pole_over_max_refused
