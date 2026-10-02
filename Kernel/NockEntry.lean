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
* **`Params`** (E3): Nock's params are the arm, as `DREGG/NOCK/PARAMS/v1 ‖ jam arm`
  (`encodeParams`; `decodeParams` accepts only its own re-encoding, `decodeParams_canonical`).
  A plain function with no proof inside, so a decided pole that decodes params keeps
  `[propext]`.
* **The door's pieces** (N11, moved here for E4): NockApp's boot `[9 2 0 1]`, the poke/peek
  slams, the job `[event [%poke wire] 0 0 0 cause]`, the product `[door [effects core']]`
  with `core' = #[6 state' door]`, and the effects as writes. `Compiler.Evaluator.nockDoor`
  assembles them into the generic door; `Kernel.NockDoor` keeps N11's names.

Nothing here is generic; the generic referee is `Kernel.Run` (`Kernel.Door` for doors).
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

/-! ## Params (E3): the arm, as a jammed atom behind a frame -/

/-- Nock's entry data: the arm the kernel slams (2 for a bare gate, hoonc's trap kicked to its
gate; NockApp's poke axis 23 for a door). -/
structure Params where
  arm : Nat
  deriving DecidableEq, Repr

/-- `DREGG/NOCK/PARAMS/v1` -/
def paramsFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 78, 79, 67, 75, 47, 80, 65, 82, 65, 77, 83, 47, 118, 49]

theorem paramsFrame_spells : paramsFrame = "DREGG/NOCK/PARAMS/v1".toUTF8.toList := by
  decide +kernel

def encodeParams (params : Params) : List UInt8 := paramsFrame ++ Noun.jam (.atom params.arm)

/-- The params, accepted only as their own re-encoding (the jam of an atom, minimal). -/
def decodeParams (bytes : List UInt8) : Option Params :=
  if bytes.take paramsFrame.length = paramsFrame then
    match Noun.cue (bytes.drop paramsFrame.length) with
    | some (.atom arm) =>
      if Noun.jam (.atom arm) = bytes.drop paramsFrame.length then some ⟨arm⟩ else none
    | _ => none
  else none

theorem decodeParams_encode (params : Params) : decodeParams (encodeParams params) = some params := by
  have take : (paramsFrame ++ Noun.jam (.atom params.arm)).take paramsFrame.length = paramsFrame :=
    List.take_left' rfl
  have drop : (paramsFrame ++ Noun.jam (.atom params.arm)).drop paramsFrame.length =
      Noun.jam (.atom params.arm) := List.drop_left' rfl
  unfold decodeParams encodeParams
  rw [if_pos take, drop, Noun.cue_jam]
  simp

/-- **`decodeParams_canonical`**: accepted params bytes are the encoding of what they decode to. -/
theorem decodeParams_canonical {bytes : List UInt8} {params : Params}
    (accepted : decodeParams bytes = some params) : encodeParams params = bytes := by
  unfold decodeParams at accepted
  split at accepted
  · rename_i framed
    split at accepted
    · rename_i arm _
      split at accepted
      · rename_i minimal
        cases accepted
        unfold encodeParams
        rw [minimal]
        have whole := List.take_append_drop paramsFrame.length bytes
        rw [framed] at whole
        exact whole
      · cases accepted
    · cases accepted
  · cases accepted

/-- Nock's birth check of its params: arm 0 is the whole subject, never a gate. -/
def checkParams (params : Params) : Option NockProgramCodec.Refusal :=
  if params.arm = 0 then some .armZero else none

/-! ## The door's pieces (N11; `Kernel.NockDoor` for the referee's names) -/

/-- `[9 2 0 1]`: NockApp's boot of the kernel trap (`form.rs:2040`). -/
def bootFormula : Noun := Nock.op 9 (.cell (.atom 2) (Nock.op 0 (.atom 1)))

/-- Over `[[trap ustate] x]`: the door — the booted trap, its axis 6 replaced
by the stored state when the instance is loaded. -/
def doorFormula : Noun :=
  let boot := Nock.op 7 (.cell (Nock.op 0 (.atom 4)) bootFormula)
  Nock.op 6 (.cell (Nock.op 3 (Nock.op 0 (.atom 5)))
    (.cell (Nock.op 10 (.cell (.cell (.atom 6) (Nock.op 0 (.atom 11))) boot)) boot))

/-- Over `[[trap ustate] job]`: `[door *[[door job] slam(poke)]]`. -/
def pokeFormula (poke : Nat) : Noun :=
  Nock.op 8 (.cell doorFormula (.cell (Nock.op 0 (.atom 2))
    (Nock.op 7 (.cell (.cell (Nock.op 0 (.atom 2)) (Nock.op 0 (.atom 7))) (Nock.slam poke)))))

/-- Over `[[trap ustate] path]`: `*[[door path] slam(peek)]`. -/
def peekFormula (peek : Nat) : Noun :=
  Nock.op 7 (.cell (.cell doorFormula (Nock.op 0 (.atom 3))) (Nock.slam peek))

/-- Over `[[trap ustate] x]`: the door's state, axis 6. -/
def stateFormula : Noun := Nock.op 7 (.cell doorFormula (Nock.op 0 (.atom 6)))

def subjectOf (trap ustate x : Noun) : Noun := .cell (.cell trap ustate) x

/-- `0` for an instance never poked (it runs on its boot state), `[0 state]` once loaded. -/
def ustateNoun : Option Noun → Noun
  | none => .atom 0
  | some state => .cell (.atom 0) state

theorem ustateNoun_injective {a b : Option Noun} (h : ustateNoun a = ustateNoun b) : a = b := by
  cases a <;> cases b <;> simp_all [ustateNoun]

/-- `%poke`. -/
def pokeTag : Nat := 1701539696

/-- NockApp's poke job `[event_num [%poke wire] eny our now cause]`
(`form.rs:2473-2493`), with `eny = our = now = 0`. -/
def job (event : Nat) (wire cause : Noun) : Noun :=
  .cell (.atom event) (.cell (.cell (.atom pokeTag) wire)
    (.cell (.atom 0) (.cell (.atom 0) (.cell (.atom 0) cause))))

/-- The claimed sample's event: its wire and cause. -/
def eventOf : Noun → Option (Noun × Noun)
  | .cell _ (.cell _ (.cell (.cell _ wire) (.cell _ (.cell _ (.cell _ cause))))) => some (wire, cause)
  | _ => none

@[simp] theorem eventOf_job (u : Noun) (event : Nat) (wire cause : Noun) :
    eventOf (.cell u (job event wire cause)) = some (wire, cause) := rfl

/-- `[door [effects core']]` with `core' = #[6 state' door]`: the door, its
effects, and its next state. -/
def pokeProduct : Noun → Option (Noun × Noun × Noun)
  | .cell door (.cell effects core) =>
    match Noun.axis 6 core with
    | some state => if Noun.edit 6 state door = some core then some (door, effects, state) else none
    | none => none
  | _ => none

theorem pokeProduct_sound {product door effects state : Noun}
    (h : pokeProduct product = some (door, effects, state)) :
    ∃ core, product = .cell door (.cell effects core) ∧ Noun.axis 6 core = some state ∧
      Noun.edit 6 state door = some core := by
  unfold pokeProduct at h
  split at h
  · rename_i door' effects' core
    split at h
    · rename_i state' hax
      split at h
      · rename_i hedit
        cases h
        exact ⟨core, rfl, hax, hedit⟩
      · cases h
    · cases h
  · cases h

/-- A Nock list. -/
def itemsOf : Noun → Option (List Noun)
  | .atom 0 => some []
  | .cell e rest => (itemsOf rest).map (e :: ·)
  | _ => none

/-- An effect that is a write: `[key value]` with an ABI output key. -/
def effectWrite (outputs : List OutputSlot) : Noun → Option FieldWrite
  | .cell (.atom k) v => decodeEntry outputs (k, v)
  | _ => none

/-- Every effect a write, in order; the first that is not refuses. -/
def effectWrites (outputs : List OutputSlot) : List Noun → Except EffectRefusal (List FieldWrite)
  | [] => .ok []
  | e :: rest =>
    match effectWrite outputs e with
    | none => .error .effectNotWrite
    | some w => (effectWrites outputs rest).map (w :: ·)

/-- The effects of a poke as writes: a Nock list (else `effectsMalformed`), every item a
write (else `effectNotWrite`). -/
def decodeEffects (outputs : List OutputSlot) (effects : Noun) :
    Except EffectRefusal (List FieldWrite) :=
  match itemsOf effects with
  | none => .error .effectsMalformed
  | some items => effectWrites outputs items

theorem effectWrites_sound {outputs : List OutputSlot} :
    ∀ {xs : List Noun} {ys : List FieldWrite}, effectWrites outputs xs = .ok ys →
      ∀ x ∈ xs, ∃ y ∈ ys, effectWrite outputs x = some y
  | [], _, _, x, hx => by cases hx
  | a :: rest, ys, h, x, hx => by
    unfold effectWrites at h
    cases ha : effectWrite outputs a with
    | none => rw [ha] at h; cases h
    | some b =>
      rw [ha] at h
      cases hr : effectWrites outputs rest with
      | error e => rw [hr] at h; cases h
      | ok bs =>
        rw [hr] at h
        simp only [Except.map, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨b, List.mem_cons_self .., ha⟩
        · obtain ⟨y, hy, hg⟩ := effectWrites_sound hr x hx
          exact ⟨y, List.mem_cons_of_mem _ hy, hg⟩

theorem effectWrites_refused {outputs : List OutputSlot} {xs : List Noun} {x : Noun}
    (hx : x ∈ xs) (hg : effectWrite outputs x = none) (ys : List FieldWrite) :
    effectWrites outputs xs ≠ .ok ys := by
  intro h
  obtain ⟨y, -, hy⟩ := effectWrites_sound h x hx
  rw [hg] at hy; cases hy

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
  rw [sampleOf_eq_slots] at claimed current
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
/-- info: 'Minidregg.Kernel.NockEntry.decodeParams_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.decodeParams_encode
/-- info: 'Minidregg.Kernel.NockEntry.decodeParams_canonical' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.decodeParams_canonical
/-- info: 'Minidregg.Kernel.NockEntry.pokeProduct_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.pokeProduct_sound
/-- info: 'Minidregg.Kernel.NockEntry.effectWrites_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockEntry.effectWrites_sound
