/-
# Kernel.Door — a program whose state lives in a cell, refereed on any evaluator (EVAL §4, E4)

N11 built the NockApp door (`Kernel.NockDoor`); this is its referee with Nock taken out. An
**instance** is an ordinary declared object holding the door's state (as the field value
`EvalDoor.encodeState` gives it) and its event number, in the two fields the ABI's door
record names, on the command's target 0. A **poke** is one invocation carrying a
`RunClaim`: its sample is the evaluator's `pokeInput` of (stored state, event + 1, event)
and its output the evaluator's `claimOutput` of (effects, next state). The kernel decodes
the stored state (`decodeState`; `stateMalformed`), reads the claim's event off its bytes
(`eventOf`; `eventMalformed`), compares the claimed sample with its own (`sampleStale`),
holds the steps to the ABI fuel, decodes the record's params (`paramsMalformed`), runs
`poke` in exactly the claimed steps, splits the product into effects and next state
(`product`; `doorShape`), compares the claimed output, reads the effects as writes
(`effects`), and admits exactly the writes: the next state, the next event number, and
the effects'.

The evaluator brings three terms (EVAL §4): **boot + poke** (`EvalDoor.poke`), **peek**
(`EvalDoor.peek`, a read at the ABI's peek arm on a path) and **load** (`EvalDoor.load`,
the state now), plus the state codec, whose round trip is an `Evaluator` fact
(`door_decode_encode`; at Nock N11's `ofJamAtom_jamAtom`).

Generic here: `door_poke_sound`, `door_state_stale_refused` (the claim's bytes are not the
kernel's sample), `door_other_state_stale` (a claim made on another state or event number),
`door_poke_deterministic`, `door_peek_pure`, `door_load_deterministic`. `Kernel.NockDoor`
instantiates them at Nock under N11's names.
-/
import Kernel.Run
import Kernel.DeclaredResourceProjection

namespace Minidregg.Kernel.Door
open Minidregg.Theory
open Minidregg.Theory.Eval
open Minidregg.Compiler
open Minidregg.Compiler.NockProgramCodec
open Minidregg.Kernel.Run
set_option autoImplicit false

/-! ## What the kernel reads off the instance -/

/-- Target 0's stored state (its field value), when loaded, and its event number. -/
structure View where
  state : Option Nat
  event : Nat
  deriving DecidableEq, Repr

def readField (read : Nat → String → Option Int) (field : Nat) : Except Run.Refusal (Option Nat) :=
  match read 0 (DeclaredResourceProjection.fieldName field "before") with
  | none => .ok none
  | some (.ofNat n) => .ok (some n)
  | some (.negSucc _) => .error .stateMalformed

/-- The instance's view: both fields absent (never poked), or both present. -/
def viewOf (door : NockProgramCodec.Door) (read : Nat → String → Option Int) :
    Except Run.Refusal View :=
  match readField read door.state, readField read door.event with
  | .ok none, .ok none => .ok ⟨none, 0⟩
  | .ok (some s), .ok (some e) => .ok ⟨some s, e⟩
  | .error e, _ => .error e
  | _, .error e => .error e
  | _, _ => .error .stateMalformed

variable {Params Code Input Output Term : Type}

/-- The stored state, decoded: `none` for an instance never poked; refused `stateMalformed`
when the field holds no state's encoding. -/
def loadedState (d : EvalDoor Params Code Input Output Term) (view : View) :
    Except Run.Refusal (Option Output) :=
  match view.state with
  | none => .ok none
  | some a =>
    match d.decodeState a with
    | some state => .ok (some state)
    | none => .error .stateMalformed

/-- **`loadedState_stored`**: a state a poke wrote reads back (`door_decode_encode`). -/
theorem loadedState_stored {E : Evaluator} {d : EvalDoor E.Params E.Code E.Input E.Output E.Term}
    (member : d ∈ E.door) (state : E.Output) (event : Nat) :
    loadedState d ⟨some (d.encodeState state), event⟩ = .ok (some state) := by
  simp [loadedState, E.door_decode_encode d member state]

/-- The two writes every accepted poke makes on target 0: the next state's field value and
the next event number. -/
def stateWrites (door : NockProgramCodec.Door) (view : View) (encoded : Nat) : List FieldWrite :=
  [⟨0, door.state, encoded⟩, ⟨0, door.event, view.event + 1⟩]

def effectRefusal : EffectRefusal → Run.Refusal
  | .effectsMalformed => .outputMalformed
  | .effectNotWrite => .effectNotWrite

/-! ## The decision -/

/-- **`checkPoke`**: re-execute the door's poke on the instance's own state and event
number, on evaluator `M`, and decide `claim` against the command's `writes`. -/
def checkPoke (M : Machine) (d : EvalDoor M.Params M.Code M.Input M.Output M.Term)
    (program : Program) (door : NockProgramCodec.Door) (view : View) (claim : RunClaim)
    (writes : List FieldWrite) : Except Run.Refusal (Verdict M.Output) :=
  match M.decode program.jam with
  | none => .error .programMalformed
  | some code =>
  match loadedState d view with
  | .error e => .error e
  | .ok stored =>
  match d.eventOf claim.sampleJam with
  | none => .error .eventMalformed
  | some ev =>
  if claim.sampleJam ≠ M.encodeInput (d.pokeInput stored (view.event + 1) ev) then
    .error (.sampleStale none)
  else if program.abi.fuel < claim.steps then .error .fuelExceeded
  else
  match M.decodeParams program.params with
  | none => .error .paramsMalformed
  | some params =>
  match M.oracle claim.steps (d.poke params code stored (view.event + 1) ev) with
  | .crash k => .error (.crash k)
  | .exhausted k => .error (.exhausted k)
  | .ok product k =>
  if k ≠ claim.steps then .error (.stepsMismatch k)
  else
  match d.product product with
  | none => .error .doorShape
  | some (effects, state) =>
  if M.encodeOutput (d.claimOutput effects state) ≠ claim.outputJam then .error .outputMismatch
  else
  match d.effects program.abi.outputs effects with
  | .error e => .error (effectRefusal e)
  | .ok decoded =>
  if ¬ ((stateWrites door view (d.encodeState state) ++ decoded).map
      fun w => (w.target, w.field)).Nodup then
    .error .outputMalformed
  else if !writes.all (· ∈ stateWrites door view (d.encodeState state) ++ decoded) then
    .error .writeNotInOutput
  else if !(stateWrites door view (d.encodeState state) ++ decoded).all (· ∈ writes) then
    .error .outputNotWritten
  else .ok ⟨d.claimOutput effects state, k, stateWrites door view (d.encodeState state) ++ decoded⟩

/-! ## Reads: peek, and the state now -/

/-- **Peek**: the door's peek on `path` over the stored state, at the ABI fuel. Takes no
Store and names no write. -/
def peek (M : Machine) (d : EvalDoor M.Params M.Code M.Input M.Output M.Term) (program : Program)
    (door : NockProgramCodec.Door) (view : View) (path : M.Input) : Except Run.Refusal (Ran M.Output) :=
  match M.decode program.jam with
  | none => .error .programMalformed
  | some code =>
    match loadedState d view with
    | .error e => .error e
    | .ok stored => .ok (M.oracle program.abi.fuel (d.peek code stored door.peek path))

/-- **Load**: the instance's state — the stored one, or the booted program's own for an
instance never poked. -/
def stateNow (M : Machine) (d : EvalDoor M.Params M.Code M.Input M.Output M.Term)
    (program : Program) (view : View) : Except Run.Refusal (Ran M.Output) :=
  match M.decode program.jam with
  | none => .error .programMalformed
  | some code =>
    match loadedState d view with
    | .error e => .error e
    | .ok stored => .ok (M.oracle program.abi.fuel (d.load code stored))

/-! ## Theorems, once for every evaluator -/

theorem keys_unique {door : NockProgramCodec.Door} {view : View} {encoded : Nat}
    {decoded : List FieldWrite}
    (nodup : ((stateWrites door view encoded ++ decoded).map fun w => (w.target, w.field)).Nodup)
    {w : FieldWrite} (mem : w ∈ stateWrites door view encoded ++ decoded)
    (key : w.target = 0 ∧ w.field = door.state) : w.value = encoded := by
  simp only [stateWrites, List.cons_append, List.map_cons, List.nodup_cons] at nodup mem
  obtain ⟨fresh, -⟩ := nodup
  rcases List.mem_cons.1 mem with rfl | rest
  · rfl
  · exfalso
    have hk : (w.target, w.field) = (0, door.state) := by rw [key.1, key.2]
    exact fresh (hk ▸ List.mem_map_of_mem (f := fun w : FieldWrite => (w.target, w.field)) rest)

/-- **`door_poke_sound`** (N11's, on any evaluator): an accepted poke decoded the program and
the instance's OWN stored state, read the claim's event off its bytes, and ran the door's
poke on (that state, event number + 1, that event) to a derivation (`E.Spec`) of a product
whose split is (effects, next state); the claim names exactly that sample and that output;
the command writes exactly the next state's encoding, the next event number and the
effects' writes. -/
theorem door_poke_sound {E : Evaluator} {d : EvalDoor E.Params E.Code E.Input E.Output E.Term}
    {program : Program} {door : NockProgramCodec.Door} {view : View} {claim : RunClaim}
    {writes : List FieldWrite} {verdict : Verdict E.Output}
    (accepted : checkPoke E.toMachine d program door view claim writes = .ok verdict) :
    ∃ code stored ev params product effects state decoded,
      E.decode program.jam = some code ∧ loadedState d view = .ok stored ∧
      d.eventOf claim.sampleJam = some ev ∧
      claim.sampleJam = E.encodeInput (d.pokeInput stored (view.event + 1) ev) ∧
      E.decodeParams program.params = some params ∧
      E.oracle claim.steps (d.poke params code stored (view.event + 1) ev) = .ok product claim.steps ∧
      E.Spec (d.poke params code stored (view.event + 1) ev) product ∧
      d.product product = some (effects, state) ∧
      verdict.output = d.claimOutput effects state ∧ claim.outputJam = E.encodeOutput verdict.output ∧
      d.effects program.abi.outputs effects = .ok decoded ∧
      verdict.writes = stateWrites door view (d.encodeState state) ++ decoded ∧
      ((stateWrites door view (d.encodeState state) ++ decoded).map
        fun w => (w.target, w.field)).Nodup ∧
      (∀ w, w ∈ writes ↔ w ∈ verdict.writes) ∧
      verdict.steps = claim.steps ∧ claim.steps ≤ program.abi.fuel := by
  unfold checkPoke at accepted
  split at accepted
  · cases accepted
  rename_i code hcode
  split at accepted
  · cases accepted
  rename_i stored hstored
  split at accepted
  · cases accepted
  rename_i ev hev
  split at accepted
  · cases accepted
  rename_i hsample
  split at accepted
  · cases accepted
  rename_i hfuel
  split at accepted
  · cases accepted
  rename_i params hparams
  split at accepted
  · cases accepted
  · cases accepted
  rename_i product k horacle
  split at accepted
  · cases accepted
  rename_i hk
  split at accepted
  · cases accepted
  rename_i effects state hprod
  split at accepted
  · cases accepted
  rename_i hout
  split at accepted
  · cases accepted
  rename_i decoded hdec
  split at accepted
  · cases accepted
  rename_i hnodup
  split at accepted
  · cases accepted
  rename_i hwr
  split at accepted
  · cases accepted
  rename_i hdw
  cases accepted
  have hk' : k = claim.steps := Classical.byContradiction hk
  subst hk'
  obtain ⟨hrun, -⟩ := E.oracle_ok horacle
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hwr hdw
  exact ⟨code, stored, ev, params, product, effects, state, decoded, hcode, hstored, hev,
    Classical.byContradiction hsample, hparams, horacle, E.run_sound hrun, hprod, rfl,
    (Classical.byContradiction hout).symm, hdec, rfl, Classical.not_not.1 hnodup,
    fun w => ⟨fun m => by simpa using hwr w m, fun m => by simpa using hdw w m⟩, rfl,
    by omega⟩

/-- **`door_state_stale_refused`** (generic, the claim's bytes): when the claimed sample is
not the kernel's — the instance's own stored state and next event number, with the event
the claim carries — the poke is refused `sampleStale`, whatever output, steps or writes the
claim asserts. Two concurrent pokes of one instance serialise. -/
theorem door_state_stale_refused {M : Machine} {d : EvalDoor M.Params M.Code M.Input M.Output M.Term}
    {program : Program} {door : NockProgramCodec.Door} {view : View} {claim : RunClaim}
    {writes : List FieldWrite} {code : M.Code} {stored : Option M.Output} {ev : d.Event}
    (cued : M.decode program.jam = some code) (loaded : loadedState d view = .ok stored)
    (event : d.eventOf claim.sampleJam = some ev)
    (stale : claim.sampleJam ≠ M.encodeInput (d.pokeInput stored (view.event + 1) ev)) :
    checkPoke M d program door view claim writes = .error (.sampleStale none) := by
  unfold checkPoke
  simp only [cued, loaded, event]
  exact if_pos stale

/-- **`door_other_state_stale`** (N11's statement, generic): a claim computed on any other
stored state or event number than the instance's own refuses `sampleStale`. -/
theorem door_other_state_stale {E : Evaluator} {d : EvalDoor E.Params E.Code E.Input E.Output E.Term}
    (member : d ∈ E.door) {program : Program} {door : NockProgramCodec.Door} {view : View}
    {claim : RunClaim} {writes : List FieldWrite} {code : E.Code} {stored stored' : Option E.Output}
    {event : Nat} {ev : d.Event}
    (cued : E.decode program.jam = some code) (loaded : loadedState d view = .ok stored)
    (claimed : claim.sampleJam = E.encodeInput (d.pokeInput stored' event ev))
    (stale : stored' ≠ stored ∨ event ≠ view.event + 1) :
    checkPoke E.toMachine d program door view claim writes = .error (.sampleStale none) := by
  apply door_state_stale_refused cued loaded (by rw [claimed]; exact E.door_eventOf d member _ _ _)
  rw [claimed]
  intro same
  obtain ⟨hs, he, -⟩ := E.door_pokeInput_injective d member (E.encodeInput_injective same)
  rcases stale with s | s
  · exact s hs
  · exact s he

/-- **`door_poke_deterministic`** (N11's, on any evaluator): two accepted pokes of one
instance on one claimed sample agree on the product and the writes — whatever fuel each
runner brought. `audit` replays pokes in order and gets the same states. -/
theorem door_poke_deterministic {E : Evaluator} {d : EvalDoor E.Params E.Code E.Input E.Output E.Term}
    {program : Program} {door : NockProgramCodec.Door} {view : View} {claim claim' : RunClaim}
    {writes writes' : List FieldWrite} {verdict verdict' : Verdict E.Output}
    (accepted : checkPoke E.toMachine d program door view claim writes = .ok verdict)
    (accepted' : checkPoke E.toMachine d program door view claim' writes' = .ok verdict')
    (sameEvent : claim.sampleJam = claim'.sampleJam) :
    verdict.output = verdict'.output ∧ verdict.writes = verdict'.writes := by
  obtain ⟨code, stored, ev, params, product, effects, state, decoded, hc, hl, he, -, hp, -, hs,
    hprod, hout, -, hdec, hw, -⟩ := door_poke_sound accepted
  obtain ⟨code', stored', ev', params', product', effects', state', decoded', hc', hl', he', -,
    hp', -, hs', hprod', hout', -, hdec', hw', -⟩ := door_poke_sound accepted'
  rw [hc] at hc'; cases hc'
  rw [hl] at hl'; cases hl'
  rw [← sameEvent, he] at he'; cases he'
  rw [hp] at hp'; cases hp'
  have same := E.spec_deterministic hs hs'
  subst same
  rw [hprod] at hprod'; cases hprod'
  rw [hdec] at hdec'; cases hdec'
  exact ⟨by rw [hout, hout'], by rw [hw, hw']⟩

/-- **`door_peek_pure`** (generic): a peek is the door's peek term over the stored state at
the ABI fuel — a function of the program, the stored view and the path. -/
theorem door_peek_pure {E : Evaluator} {d : EvalDoor E.Params E.Code E.Input E.Output E.Term}
    {program : Program} {door : NockProgramCodec.Door} {view : View} {path : E.Input}
    {out : E.Output} {k : Nat}
    (answered : peek E.toMachine d program door view path = .ok (.ok out k)) :
    ∃ code stored, E.decode program.jam = some code ∧ loadedState d view = .ok stored ∧
      E.Spec (d.peek code stored door.peek path) out ∧
      E.steps program.abi.fuel (d.peek code stored door.peek path) = k := by
  unfold peek at answered
  cases hcode : E.decode program.jam with
  | none => simp [hcode] at answered
  | some code =>
    cases hs : loadedState d view with
    | error e => simp [hcode, hs] at answered
    | ok stored =>
      simp only [hcode, hs, Except.ok.injEq] at answered
      obtain ⟨hrun, hsteps⟩ := E.oracle_ok answered
      exact ⟨code, stored, rfl, rfl, E.run_sound hrun, hsteps⟩

/-- **`door_load_deterministic`** (generic): the state an instance holds is a derivation
from the program and the stored view alone, and unique. -/
theorem door_load_deterministic {E : Evaluator} {d : EvalDoor E.Params E.Code E.Input E.Output E.Term}
    {program : Program} {view : View} {state state' : E.Output} {k : Nat}
    (loaded : stateNow E.toMachine d program view = .ok (.ok state k))
    (other : ∃ code stored, E.decode program.jam = some code ∧ loadedState d view = .ok stored ∧
      E.Spec (d.load code stored) state') :
    state' = state := by
  obtain ⟨code, stored, cued, u, spec'⟩ := other
  unfold stateNow at loaded
  simp only [cued, u, Except.ok.injEq] at loaded
  obtain ⟨hrun, -⟩ := E.oracle_ok loaded
  exact E.spec_deterministic spec' (E.run_sound hrun)

end Minidregg.Kernel.Door

/-- info: 'Minidregg.Kernel.Door.keys_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Door.keys_unique
/-- info: 'Minidregg.Kernel.Door.door_poke_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Door.door_poke_sound
/-- info: 'Minidregg.Kernel.Door.door_state_stale_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Door.door_state_stale_refused
/-- info: 'Minidregg.Kernel.Door.door_other_state_stale' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Door.door_other_state_stale
/-- info: 'Minidregg.Kernel.Door.door_poke_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Door.door_poke_deterministic
/-- info: 'Minidregg.Kernel.Door.door_peek_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Door.door_peek_pure
/-- info: 'Minidregg.Kernel.Door.door_load_deterministic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.Door.door_load_deterministic
