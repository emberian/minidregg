/-
# Kernel.NockDoor — a NockApp kernel door, refereed (NOCK §2.7)

A program whose ABI names a `door` is a NockApp kernel, run exactly as
NockApp runs it (nockchain `cbd9298f`, `crates/nockapp/src/kernel/form.rs`):

* **Boot** (`:2040`): the program's jam is the kernel *trap*; the kernel core is
  `*[trap [9 2 0 1]]`.
* **State** (`:49`, `STATE_AXIS = 6`): the kernel's state is axis 6 of the core.
  NockApp exports and persists exactly that axis (`:1170-1190`), and so do we:
  the state lives in object field `door.state` of the command's target 0 as the
  ATOM of its jam (`jamAtom`), the event number in field `door.event`. An
  instance with neither field has never been poked: it runs on its boot state.
* **Poke** (`:52`, `POKE_AXIS = 23`; `:2211-2240` `do_poke`): the slam
  `[8 [9 23 0 2] 9 2 10 [6 0 7] 0 2]` (`crates/nockapp/src/noun/ops.rs:23-36`,
  which is `Theory.Nock.slam`) on `[core job]`, where the job is NockApp's
  `[event_num [%poke wire] eny our now cause]` (`form.rs:2473-2493`). The
  product is `[effects core']`; core' is the next core.
* **Peek** (`:51`, `PEEK_AXIS = 22`; `:2132-2143`): the same slam at 22 on a
  path; the product is `(unit (unit *))`. A read: it takes no Store and returns
  no writes.

What a refereed kernel cannot have, it gets as constants: `eny = our = now = 0`
(NockApp's `our` is already 0; a kernel that needs time or entropy reads it from
its event). The event number is the instance's own count, `event + 1`.

**Only the state persists**, as in NockApp. The kernel therefore checks that the
poke kept the door's battery and context: `core' = #[6 state' core]` (else
`doorShape`). Under that check, re-installing the stored state into the booted
core IS the core NockApp holds in memory after the poke.

**Effects are writes** (ember, v1): every effect must be `[key value]` with a
key of an ABI output slot; anything else (`%exit`, I/O) refuses
`effectNotWrite`.

**Generic since E4.** The referee is `Kernel.Door.checkPoke` on `Machine.nock` with N11's
pieces as Nock's `EvalDoor` (`Compiler.Evaluator.nockDoor`, built from `Kernel.NockEntry`);
the poke arm is the record's params (`Kernel.NockEntry.Params.arm`, E3), no longer an ABI
field. This file keeps N11's names: `checkPoke`, `peek`, `stateNow`, `dryPoke`, and the seven
theorems, each the generic one at Nock.

The claim is K-RAN's `RunClaim` unchanged: `sampleJam` = jam of
`[ustate job]` (`ustate` = `0` unloaded, `[0 state]` loaded); `outputJam` = jam
of `[effects state']`; `steps` = the oracle's count of the whole run, boot
included. A claim over another state or event number refuses `sampleStale`:
concurrent pokes serialise.
-/
import Kernel.Door

namespace Minidregg.Kernel.NockDoor
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Compiler.NockProgramCodec
open Minidregg.Kernel.NockProgramCell
open Minidregg.Kernel.Run
open Minidregg.Kernel.NockEntry
open Minidregg.Kernel.Door (View loadedState)
open Minidregg.Theory.Eval
set_option autoImplicit false

-- `natBytes`, `jamAtom`, `ofJamAtom` (+ `ofJamAtom_sound`, `ofJamAtom_jamAtom`) live in
-- `Kernel.NockProgramCell`; the formulas, the job, `pokeProduct` and the effects in
-- `Kernel.NockEntry`; the view and the referee in `Kernel.Door`.

theorem pokeTag_cord : pokeTag = cordValue "poke".toUTF8.toList := by decide +kernel

/-- `0` for an unloaded instance (it runs on its boot state), `[0 state]` once loaded. -/
def ustateOf (view : View) : Except Run.Refusal Noun :=
  (loadedState nockDoor view).map ustateNoun

/-- The two writes every accepted poke makes on target 0: the new state's jam atom and the
next event number. -/
def stateWrites (door : Door) (view : View) (state : Noun) : List FieldWrite :=
  Kernel.Door.stateWrites door view (jamAtom state)

/-! ## The decision and the reads: the generic referee on Nock -/

/-- **`checkPoke`** (N11): `Kernel.Door.checkPoke` on Nock's machine and door. -/
def checkPoke (program : Program) (door : Door) (view : View) (claim : RunClaim)
    (writes : List FieldWrite) : Except Run.Refusal (Verdict Noun) :=
  Kernel.Door.checkPoke Machine.nock nockDoor program door view claim writes

/-- **Peek** (N11): the peek arm slammed on `path` over the stored state, at the ABI fuel. -/
def peek (program : Program) (door : Door) (view : View) (path : Noun) :
    Except Run.Refusal (Ran Noun) :=
  Kernel.Door.peek Machine.nock nockDoor program door view path

/-- **Load** (N11): the stored state, or the booted trap's own axis 6. -/
def stateNow (program : Program) (view : View) : Except Run.Refusal (Ran Noun) :=
  Kernel.Door.stateNow Machine.nock nockDoor program view

/-- Op 135, the runner's dry run of a poke: the sample to claim, the oracle at
the ABI fuel, and (when it ran) the product's decomposition and the writes it
names. -/
inductive DryPoke where
  | refused (reason : Run.Refusal)
  | ran (sample : Noun) (subject formula : Noun) (result : Ran Noun)
      (decoded : Option (Noun × Noun × Except Run.Refusal (List FieldWrite)))

def dryPoke (program : Program) (door : Door) (view : View) (wire cause : Noun) : DryPoke :=
  match Noun.cue program.jam, ustateOf view, decodeParams program.params with
  | none, _, _ => .refused .programMalformed
  | _, .error e, _ => .refused e
  | _, _, none => .refused .paramsMalformed
  | some trap, .ok ustate, some params =>
    let input := job (view.event + 1) wire cause
    let s := subjectOf trap ustate input
    let f := pokeFormula params.arm
    let result := oracle program.abi.fuel s f
    .ran (.cell ustate input) s f result
      (match result with
       | .ok product _ =>
         (pokeProduct product).map fun (_, effects, state) =>
           (effects, state, ((decodeEffects program.abi.outputs effects).mapError
             Kernel.Door.effectRefusal).map (stateWrites door view state ++ ·))
       | _ => none)

/-! ## N11's theorems, at Nock -/

theorem ustateOf_loaded {view : View} {ustate : Noun} (h : ustateOf view = .ok ustate) :
    ∃ stored, loadedState nockDoor view = .ok stored ∧ ustate = ustateNoun stored := by
  unfold ustateOf at h
  cases hl : loadedState nockDoor view with
  | error e => rw [hl] at h; cases h
  | ok stored =>
    rw [hl] at h
    simp only [Except.map, Except.ok.injEq] at h
    exact ⟨stored, rfl, h.symm⟩

theorem ustateOf_of_loaded {view : View} {stored : Option Noun}
    (h : loadedState nockDoor view = .ok stored) : ustateOf view = .ok (ustateNoun stored) := by
  unfold ustateOf; rw [h]; rfl

/-- **`door_poke_sound`** (N11; `Kernel.Door.door_poke_sound` at Nock): an accepted poke ran
the door's poke arm — the record's params' arm — on the instance's OWN state and event
number (`ustateOf view`, `view.event + 1`); the product is `[door [effects core']]` with
`core' = #[6 state' door]`; the claim names exactly `[effects state']`; and the command
writes exactly the jam atom of `state'` to the state field — no other state value — plus
the next event number and the effects' writes. -/
theorem door_poke_sound {program : Program} {door : Door} {view : View} {claim : RunClaim}
    {writes : List FieldWrite} {verdict : Verdict Noun}
    (accepted : checkPoke program door view claim writes = .ok verdict) :
    ∃ trap params ustate wire cause doorCore effects core state,
      Noun.cue program.jam = some trap ∧ decodeParams program.params = some params ∧
      ustateOf view = .ok ustate ∧
      claim.sampleJam = Noun.jam (.cell ustate (job (view.event + 1) wire cause)) ∧
      Nock.Step (subjectOf trap ustate (job (view.event + 1) wire cause))
        (pokeFormula params.arm) (.cell doorCore (.cell effects core)) ∧
      Noun.axis 6 core = some state ∧ Noun.edit 6 state doorCore = some core ∧
      verdict.output = .cell effects state ∧ claim.outputJam = Noun.jam verdict.output ∧
      (⟨0, door.state, jamAtom state⟩ : FieldWrite) ∈ writes ∧
      (⟨0, door.event, view.event + 1⟩ : FieldWrite) ∈ writes ∧
      (∀ w ∈ writes, w.target = 0 → w.field = door.state → w.value = jamAtom state) ∧
      (∀ w, w ∈ writes ↔ w ∈ verdict.writes) ∧
      (∃ decoded, decodeEffects program.abi.outputs effects = .ok decoded ∧
        verdict.writes = stateWrites door view state ++ decoded) ∧
      verdict.steps = claim.steps ∧ claim.steps ≤ program.abi.fuel := by
  obtain ⟨trap, stored, ev, params, product, effects, state, decoded, hc, hl, -, hs, hp, -,
    hspec, hprod, hout, hjam, hdec, hw, hnodup, hiff, hsteps, hfuel⟩ :=
    Kernel.Door.door_poke_sound (E := Evaluator.nock) (d := nockDoor) accepted
  obtain ⟨⟨doorCore, effects', state'⟩, hpp, heq⟩ := Option.map_eq_some_iff.mp hprod
  have h1 : effects' = effects := congrArg Prod.fst heq
  have h2 : state' = state := congrArg Prod.snd heq
  rw [h1, h2] at hpp
  obtain ⟨core, rfl, hax, hedit⟩ := pokeProduct_sound hpp
  have hu : ustateOf view = .ok (ustateNoun stored) := ustateOf_of_loaded hl
  have mem : ∀ w, w ∈ stateWrites door view state ++ decoded → w ∈ writes := fun w m =>
    (hiff w).2 (hw ▸ m)
  refine ⟨trap, params, ustateNoun stored, ev.1, ev.2, doorCore, effects, core, state, hc, hp, hu,
    hs, hspec, hax, hedit, hout, hjam, mem _ (by simp [stateWrites, Kernel.Door.stateWrites]),
    mem _ (by simp [stateWrites, Kernel.Door.stateWrites]), ?_, hiff, ⟨decoded, hdec, hw⟩, hsteps,
    hfuel⟩
  intro w hw' ht hf
  exact Kernel.Door.keys_unique hnodup (hw ▸ (hiff w).1 hw') ⟨ht, hf⟩

/-- **`door_state_stale_refused`** (N11; `Kernel.Door.door_state_stale_refused` at Nock): a
claim computed over any other state or event number than the instance's own refuses
`sampleStale` — whatever it claims as output, steps or writes. Two concurrent pokes of one
instance therefore serialise: once one lands, the other's sample is stale. -/
theorem door_state_stale_refused {program : Program} {door : Door} {view : View}
    {claim : RunClaim} {writes : List FieldWrite} {trap ustate ustate' wire cause : Noun}
    {event : Nat} (cued : Noun.cue program.jam = some trap) (loaded : ustateOf view = .ok ustate)
    (claimed : claim.sampleJam = Noun.jam (.cell ustate' (job event wire cause)))
    (stale : ustate' ≠ ustate ∨ event ≠ view.event + 1) :
    checkPoke program door view claim writes = .error (.sampleStale none) := by
  obtain ⟨stored, hl, rfl⟩ := ustateOf_loaded loaded
  apply Kernel.Door.door_state_stale_refused (M := Machine.nock) (d := nockDoor) (ev := (wire, cause))
    cued hl
  · show (Noun.cue claim.sampleJam).bind eventOf = some (wire, cause)
    rw [claimed, Noun.cue_jam]; rfl
  · rw [claimed]
    intro h
    have h' := Noun.jam_injective h
    simp only [nockDoor, job, Noun.cell.injEq, Noun.atom.injEq] at h'
    rcases stale with s | s
    · exact s h'.1
    · exact s h'.2.1

/-- **`door_effects_are_writes`**: in an accepted poke, the effects are a Nock
list and EVERY effect is a write the command makes. -/
theorem door_effects_are_writes {program : Program} {door : Door} {view : View}
    {claim : RunClaim} {writes : List FieldWrite} {verdict : Verdict Noun}
    (accepted : checkPoke program door view claim writes = .ok verdict) :
    ∃ effects state items, verdict.output = .cell effects state ∧ itemsOf effects = some items ∧
      ∀ e ∈ items, ∃ w, effectWrite program.abi.outputs e = some w ∧ w ∈ writes := by
  obtain ⟨-, -, -, -, -, -, effects, -, state, -, -, -, -, -, -, -, hout, -, -, -, -, same,
    ⟨decoded, hdec, hwrites⟩, -⟩ := door_poke_sound accepted
  unfold decodeEffects at hdec
  split at hdec
  · cases hdec
  rename_i items hitems
  refine ⟨effects, state, items, hout, hitems, fun e he => ?_⟩
  obtain ⟨w, hw, hg⟩ := effectWrites_sound hdec e he
  exact ⟨w, hg, (same w).2 (hwrites ▸ List.mem_append_right _ hw)⟩

/-- **`door_effect_not_write_refused`**: if the door's actual product names an
effect that is not a write, no claim is accepted — whatever it asserts. -/
theorem door_effect_not_write_refused {program : Program} {door : Door} {view : View}
    {params : Params} {trap ustate wire cause doorCore effects core : Noun} {items : List Noun}
    {e : Noun} (cued : Noun.cue program.jam = some trap)
    (decodedParams : decodeParams program.params = some params) (loaded : ustateOf view = .ok ustate)
    (derives : Nock.Step (subjectOf trap ustate (job (view.event + 1) wire cause))
      (pokeFormula params.arm) (.cell doorCore (.cell effects core)))
    (listed : itemsOf effects = some items) (member : e ∈ items)
    (notWrite : effectWrite program.abi.outputs e = none)
    (claim : RunClaim) (writes : List FieldWrite) (verdict : Verdict Noun)
    (named : ∃ u event, claim.sampleJam = Noun.jam (.cell u (job event wire cause))) :
    checkPoke program door view claim writes ≠ .ok verdict := by
  intro accepted
  obtain ⟨trap', params', ustate', wire', cause', doorCore', effects', core', state', cued',
    params'', loaded', sample', step', -, -, -, -, -, -, -, -, ⟨decoded, hdec, -⟩, -⟩ :=
    door_poke_sound accepted
  rw [cued] at cued'; cases cued'
  rw [decodedParams] at params''; cases params''
  rw [loaded] at loaded'; cases loaded'
  obtain ⟨u, event, hnamed⟩ := named
  rw [sample'] at hnamed
  have hs := Noun.jam_injective hnamed
  simp only [job, Noun.cell.injEq, true_and] at hs
  obtain ⟨-, -, rfl, rfl⟩ := hs
  have same := Nock.step_deterministic step' derives
  simp only [Noun.cell.injEq] at same
  obtain ⟨-, rfl, -⟩ := same
  unfold decodeEffects at hdec
  rw [listed] at hdec
  exact effectWrites_refused member notWrite _ hdec

/-- **`door_poke_deterministic`** (N11; `Kernel.Door.door_poke_deterministic` at Nock): two
accepted pokes of one instance with one event agree on the product and the writes —
whatever fuel each runner brought. `audit` replays pokes in order and gets the same states. -/
theorem door_poke_deterministic {program : Program} {door : Door} {view : View}
    {claim claim' : RunClaim} {writes writes' : List FieldWrite} {verdict verdict' : Verdict Noun}
    (accepted : checkPoke program door view claim writes = .ok verdict)
    (accepted' : checkPoke program door view claim' writes' = .ok verdict')
    (sameEvent : claim.sampleJam = claim'.sampleJam) :
    verdict.output = verdict'.output ∧ verdict.writes = verdict'.writes :=
  Kernel.Door.door_poke_deterministic (E := Evaluator.nock) (d := nockDoor) accepted accepted'
    sameEvent

/-- **`door_peek_pure`** (N11; `Kernel.Door.door_peek_pure` at Nock): a peek is the peek arm
slammed on the path over the instance's stored state — the core a poke would run on — at
the ABI fuel. It takes no Store and names no write. -/
theorem door_peek_pure {program : Program} {door : Door} {view : View} {path out : Noun}
    {k : Nat} (answered : peek program door view path = .ok (.ok out k)) :
    ∃ trap ustate, Noun.cue program.jam = some trap ∧ ustateOf view = .ok ustate ∧
      Nock.Step (subjectOf trap ustate path) (peekFormula door.peek) out ∧
      Nock.steps program.abi.fuel (subjectOf trap ustate path) (peekFormula door.peek) = k := by
  obtain ⟨trap, stored, hc, hl, hspec, hsteps⟩ :=
    Kernel.Door.door_peek_pure (E := Evaluator.nock) (d := nockDoor) answered
  exact ⟨trap, ustateNoun stored, hc, ustateOf_of_loaded hl, hspec, hsteps⟩

/-- **`door_load_deterministic`** (N11; `Kernel.Door.door_load_deterministic` at Nock): the
state an instance holds — its stored state, or its booted trap's own axis 6 when never
poked — is a Nock derivation from the program and the stored view alone, and unique. -/
theorem door_load_deterministic {program : Program} {view : View} {state state' : Noun}
    {k : Nat} (loaded : stateNow program view = .ok (.ok state k))
    (other : ∃ trap ustate, Noun.cue program.jam = some trap ∧ ustateOf view = .ok ustate ∧
      Nock.Step (subjectOf trap ustate (.atom 0)) stateFormula state') :
    state' = state := by
  obtain ⟨trap, ustate, cued, u, step'⟩ := other
  obtain ⟨stored, hl, rfl⟩ := ustateOf_loaded u
  exact Kernel.Door.door_load_deterministic (E := Evaluator.nock) (d := nockDoor) loaded
    ⟨trap, stored, cued, hl, step'⟩

-- Concrete counter fixtures and kernel-decided poles are checked in
-- `Assurance.NockDoorAudit`, required by both Deployed and Assurance.

/-- info: 'Minidregg.Kernel.NockDoor.door_poke_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms door_poke_sound
/-- info: 'Minidregg.Kernel.NockDoor.door_state_stale_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms door_state_stale_refused
/-- info: 'Minidregg.Kernel.NockDoor.door_effects_are_writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms door_effects_are_writes
/-- info: 'Minidregg.Kernel.NockDoor.door_effect_not_write_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms door_effect_not_write_refused
/-- info: 'Minidregg.Kernel.NockDoor.door_poke_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms door_poke_deterministic
/-- info: 'Minidregg.Kernel.NockDoor.door_peek_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms door_peek_pure
/-- info: 'Minidregg.Kernel.NockDoor.door_load_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms door_load_deterministic
/-- info: 'Minidregg.Kernel.NockDoor.pokeTag_cord' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pokeTag_cord

end Minidregg.Kernel.NockDoor
