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

The claim is K-RAN's `RunClaim` unchanged: `sampleJam` = jam of
`[ustate job]` (`ustate` = `0` unloaded, `[0 state]` loaded); `outputJam` = jam
of `[effects state']`; `steps` = the oracle's count of the whole run, boot
included. A claim over another state or event number refuses `sampleStale`:
concurrent pokes serialise.
-/
import Kernel.NockRun
import Kernel.DeclaredResourceProjection

namespace Minidregg.Kernel.NockDoor
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Compiler.NockProgramCodec
open Minidregg.Kernel.NockProgramCell
open Minidregg.Kernel.NockRun
set_option autoImplicit false

/-! ## The state as an atom -/

def natBytesAux : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else (n % 256).toUInt8 :: natBytesAux fuel (n / 256)

/-- Little-endian minimal bytes of an atom. -/
def natBytes (n : Nat) : List UInt8 := natBytesAux n n

/-- The jam of a noun as an atom (Urbit's `jam` is an atom). -/
def jamAtom (n : Noun) : Nat := cordValue (Noun.jam n)

/-- The noun whose jam is the atom `a`, refused unless re-jamming gives `a` back. -/
def ofJamAtom (a : Nat) : Option Noun :=
  match Noun.cue (natBytes a) with
  | some n => if jamAtom n = a then some n else none
  | none => none

theorem ofJamAtom_sound {a : Nat} {n : Noun} (h : ofJamAtom a = some n) : jamAtom n = a := by
  unfold ofJamAtom at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-! ## What the kernel reads off the instance -/

/-- Target 0's stored state (a jam atom), when loaded, and its event number. -/
structure View where
  state : Option Nat
  event : Nat
  deriving DecidableEq, Repr

def readField (read : Nat → String → Option Int) (field : Nat) : Except NockRun.Refusal (Option Nat) :=
  match read 0 (DeclaredResourceProjection.fieldName field "before") with
  | none => .ok none
  | some (.ofNat n) => .ok (some n)
  | some (.negSucc _) => .error .stateMalformed

/-- The instance's view: both fields absent (never poked), or both present. -/
def viewOf (door : Door) (read : Nat → String → Option Int) : Except NockRun.Refusal View :=
  match readField read door.state, readField read door.event with
  | .ok none, .ok none => .ok ⟨none, 0⟩
  | .ok (some s), .ok (some e) => .ok ⟨some s, e⟩
  | .error e, _ => .error e
  | _, .error e => .error e
  | _, _ => .error .stateMalformed

/-- `0` for an unloaded instance (it runs on its boot state), `[0 state]` once loaded. -/
def ustateOf (view : View) : Except NockRun.Refusal Noun :=
  match view.state with
  | none => .ok (.atom 0)
  | some a =>
    match ofJamAtom a with
    | some n => .ok (.cell (.atom 0) n)
    | none => .error .stateMalformed

/-! ## Subject, job, formulas -/

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

/-- `%poke`. -/
def pokeTag : Nat := 1701539696

theorem pokeTag_cord : pokeTag = cordValue "poke".toUTF8.toList := by decide +kernel

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

/-! ## Effects -/

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
def effectWrites (outputs : List OutputSlot) : List Noun → Except NockRun.Refusal (List FieldWrite)
  | [] => .ok []
  | e :: rest =>
    match effectWrite outputs e with
    | none => .error .effectNotWrite
    | some w => (effectWrites outputs rest).map (w :: ·)

def decodeEffects (abi : Abi) (effects : Noun) : Except NockRun.Refusal (List FieldWrite) :=
  match itemsOf effects with
  | none => .error .outputMalformed
  | some items => effectWrites abi.outputs items

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

/-! ## The decision -/

/-- The two writes every accepted poke makes on target 0: the new state's jam
atom and the next event number. -/
def stateWrites (door : Door) (view : View) (state : Noun) : List FieldWrite :=
  [⟨0, door.state, jamAtom state⟩, ⟨0, door.event, view.event + 1⟩]

/-- **`checkPoke`**: re-execute the door's poke on the instance's own state and
event number and decide `claim` against the command's `writes`. -/
def checkPoke (program : Program) (door : Door) (view : View) (claim : RunClaim)
    (writes : List FieldWrite) : Except NockRun.Refusal Verdict :=
  match Noun.cue program.jam with
  | none => .error .programMalformed
  | some trap =>
  match ustateOf view with
  | .error e => .error e
  | .ok ustate =>
  match Noun.cue claim.sampleJam with
  | none => .error .eventMalformed
  | some claimed =>
  match eventOf claimed with
  | none => .error .eventMalformed
  | some (wire, cause) =>
  if claim.sampleJam ≠ Noun.jam (.cell ustate (job (view.event + 1) wire cause)) then
    .error .sampleStale
  else if program.abi.fuel < claim.steps then .error .fuelExceeded
  else
  match oracle claim.steps (subjectOf trap ustate (job (view.event + 1) wire cause))
      (pokeFormula program.abi.arm) with
  | .crash k => .error (.crash k)
  | .exhausted k => .error (.exhausted k)
  | .ok product k =>
  if k ≠ claim.steps then .error (.stepsMismatch k)
  else
  match pokeProduct product with
  | none => .error .doorShape
  | some (_, effects, state) =>
  if Noun.jam (.cell effects state) ≠ claim.outputJam then .error .outputMismatch
  else
  match decodeEffects program.abi effects with
  | .error e => .error e
  | .ok decoded =>
  if ¬ ((stateWrites door view state ++ decoded).map fun w => (w.target, w.field)).Nodup then
    .error .outputMalformed
  else if !writes.all (· ∈ stateWrites door view state ++ decoded) then .error .writeNotInOutput
  else if !(stateWrites door view state ++ decoded).all (· ∈ writes) then .error .outputNotWritten
  else .ok ⟨.cell effects state, k, stateWrites door view state ++ decoded⟩

/-! ## Reads: peek, and the state now -/

/-- **Peek**: the peek arm slammed on `path` over the instance's stored state,
at the ABI fuel. Takes no Store, returns no writes. -/
def peek (program : Program) (door : Door) (view : View) (path : Noun) : Except NockRun.Refusal Ran :=
  match Noun.cue program.jam with
  | none => .error .programMalformed
  | some trap =>
    match ustateOf view with
    | .error e => .error e
    | .ok ustate => .ok (oracle program.abi.fuel (subjectOf trap ustate path) (peekFormula door.peek))

/-- **Load**: the instance's state — the stored one, or the booted trap's own
axis 6 for an instance never poked. -/
def stateNow (program : Program) (view : View) : Except NockRun.Refusal Ran :=
  match Noun.cue program.jam with
  | none => .error .programMalformed
  | some trap =>
    match ustateOf view with
    | .error e => .error e
    | .ok ustate => .ok (oracle program.abi.fuel (subjectOf trap ustate (.atom 0)) stateFormula)

/-- Op 135, the runner's dry run of a poke: the sample to claim, the oracle at
the ABI fuel, and (when it ran) the product's decomposition and the writes it
names. -/
inductive DryPoke where
  | refused (reason : NockRun.Refusal)
  | ran (sample : Noun) (subject formula : Noun) (result : Ran)
      (decoded : Option (Noun × Noun × Except NockRun.Refusal (List FieldWrite)))

def dryPoke (program : Program) (door : Door) (view : View) (wire cause : Noun) : DryPoke :=
  match Noun.cue program.jam, ustateOf view with
  | none, _ => .refused .programMalformed
  | _, .error e => .refused e
  | some trap, .ok ustate =>
    let input := job (view.event + 1) wire cause
    let s := subjectOf trap ustate input
    let f := pokeFormula program.abi.arm
    let result := oracle program.abi.fuel s f
    .ran (.cell ustate input) s f result
      (match result with
       | .ok product _ =>
         (pokeProduct product).map fun (_, effects, state) =>
           (effects, state, (decodeEffects program.abi effects).map (stateWrites door view state ++ ·))
       | _ => none)

/-! ## Theorems -/

theorem keys_unique {door : Door} {view : View} {state : Noun} {decoded : List FieldWrite}
    (nodup : ((stateWrites door view state ++ decoded).map fun w => (w.target, w.field)).Nodup)
    {w : FieldWrite} (mem : w ∈ stateWrites door view state ++ decoded)
    (key : w.target = 0 ∧ w.field = door.state) : w.value = jamAtom state := by
  simp only [stateWrites, List.cons_append, List.map_cons, List.nodup_cons] at nodup mem
  obtain ⟨fresh, -⟩ := nodup
  rcases List.mem_cons.1 mem with rfl | rest
  · rfl
  · exfalso
    have hk : (w.target, w.field) = (0, door.state) := by rw [key.1, key.2]
    exact fresh (hk ▸ List.mem_map_of_mem (f := fun w : FieldWrite => (w.target, w.field)) rest)

/-- **`door_poke_sound`**: an accepted poke ran the door's poke arm on the
instance's OWN state and event number (`ustateOf view`, `view.event + 1`); the
product is `[door [effects core']]` with `core' = #[6 state' door]`; the claim
names exactly `[effects state']`; and the command writes exactly the jam atom
of `state'` to the state field — no other state value — plus the next event
number and the effects' writes. -/
theorem door_poke_sound {program : Program} {door : Door} {view : View} {claim : RunClaim}
    {writes : List FieldWrite} {verdict : Verdict}
    (accepted : checkPoke program door view claim writes = .ok verdict) :
    ∃ trap ustate wire cause doorCore effects core state,
      Noun.cue program.jam = some trap ∧ ustateOf view = .ok ustate ∧
      claim.sampleJam = Noun.jam (.cell ustate (job (view.event + 1) wire cause)) ∧
      Nock.Step (subjectOf trap ustate (job (view.event + 1) wire cause))
        (pokeFormula program.abi.arm) (.cell doorCore (.cell effects core)) ∧
      Noun.axis 6 core = some state ∧ Noun.edit 6 state doorCore = some core ∧
      verdict.output = .cell effects state ∧ claim.outputJam = Noun.jam verdict.output ∧
      (⟨0, door.state, jamAtom state⟩ : FieldWrite) ∈ writes ∧
      (⟨0, door.event, view.event + 1⟩ : FieldWrite) ∈ writes ∧
      (∀ w ∈ writes, w.target = 0 → w.field = door.state → w.value = jamAtom state) ∧
      (∀ w, w ∈ writes ↔ w ∈ verdict.writes) ∧
      (∃ decoded, decodeEffects program.abi effects = .ok decoded ∧
        verdict.writes = stateWrites door view state ++ decoded) ∧
      verdict.steps = claim.steps ∧ claim.steps ≤ program.abi.fuel := by
  unfold checkPoke at accepted
  split at accepted
  · cases accepted
  rename_i trap htrap
  split at accepted
  · cases accepted
  rename_i ustate hu
  split at accepted
  · cases accepted
  rename_i claimed hclaimed
  split at accepted
  · cases accepted
  rename_i wire cause hev
  split at accepted
  · cases accepted
  rename_i hsample
  split at accepted
  · cases accepted
  rename_i hfuel
  split at accepted
  · cases accepted
  · cases accepted
  rename_i product k horacle
  split at accepted
  · cases accepted
  rename_i hk
  split at accepted
  · cases accepted
  rename_i doorCore effects state hprod
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
  obtain ⟨hstep, -, -⟩ := oracle_ok_step horacle
  obtain ⟨core, rfl, hax, hedit⟩ := pokeProduct_sound hprod
  have hnodup' := Classical.not_not.1 hnodup
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hwr hdw
  have hk' : k = claim.steps := Classical.byContradiction hk
  refine ⟨trap, ustate, wire, cause, doorCore, effects, core, state, htrap, hu,
    Classical.byContradiction hsample, hstep, hax, hedit, rfl,
    (Classical.byContradiction hout).symm, ?_, ?_, ?_, ?_, ?_, hk', by omega⟩
  · exact by simpa using hdw ⟨0, door.state, jamAtom state⟩ (by simp [stateWrites])
  · exact by simpa using hdw ⟨0, door.event, view.event + 1⟩ (by simp [stateWrites])
  · intro w hw ht hf
    exact keys_unique hnodup' (by simpa using hwr w hw) ⟨ht, hf⟩
  · intro w
    exact ⟨fun m => by simpa using hwr w m, fun m => by simpa using hdw w m⟩
  · exact ⟨decoded, hdec, rfl⟩

/-- **`door_state_stale_refused`**: a claim computed over any other state or
event number than the instance's own refuses `sampleStale` — whatever it
claims as output, steps or writes. Two concurrent pokes of one instance
therefore serialise: once one lands, the other's sample is stale. -/
theorem door_state_stale_refused {program : Program} {door : Door} {view : View}
    {claim : RunClaim} {writes : List FieldWrite} {trap ustate ustate' wire cause : Noun}
    {event : Nat} (cued : Noun.cue program.jam = some trap) (loaded : ustateOf view = .ok ustate)
    (claimed : claim.sampleJam = Noun.jam (.cell ustate' (job event wire cause)))
    (stale : ustate' ≠ ustate ∨ event ≠ view.event + 1) :
    checkPoke program door view claim writes = .error .sampleStale := by
  have hc : Noun.cue claim.sampleJam = some (.cell ustate' (job event wire cause)) := by
    rw [claimed, Noun.cue_jam]
  have hne : claim.sampleJam ≠ Noun.jam (.cell ustate (job (view.event + 1) wire cause)) := by
    rw [claimed]
    intro h
    have h' := Noun.jam_injective h
    simp only [job, Noun.cell.injEq, Noun.atom.injEq] at h'
    rcases stale with s | s
    · exact s h'.1
    · exact s h'.2.1
  unfold checkPoke
  simp only [cued, loaded, hc, eventOf_job]
  exact if_pos hne

/-- **`door_effects_are_writes`**: in an accepted poke, the effects are a Nock
list and EVERY effect is a write the command makes. -/
theorem door_effects_are_writes {program : Program} {door : Door} {view : View}
    {claim : RunClaim} {writes : List FieldWrite} {verdict : Verdict}
    (accepted : checkPoke program door view claim writes = .ok verdict) :
    ∃ effects state items, verdict.output = .cell effects state ∧ itemsOf effects = some items ∧
      ∀ e ∈ items, ∃ w, effectWrite program.abi.outputs e = some w ∧ w ∈ writes := by
  obtain ⟨-, -, -, -, -, effects, -, state, -, -, -, -, -, -, hout, -, -, -, -, same,
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
    {trap ustate wire cause doorCore effects core : Noun} {items : List Noun} {e : Noun}
    (cued : Noun.cue program.jam = some trap) (loaded : ustateOf view = .ok ustate)
    (derives : Nock.Step (subjectOf trap ustate (job (view.event + 1) wire cause))
      (pokeFormula program.abi.arm) (.cell doorCore (.cell effects core)))
    (listed : itemsOf effects = some items) (member : e ∈ items)
    (notWrite : effectWrite program.abi.outputs e = none)
    (claim : RunClaim) (writes : List FieldWrite) (verdict : Verdict)
    (named : ∃ u event, claim.sampleJam = Noun.jam (.cell u (job event wire cause))) :
    checkPoke program door view claim writes ≠ .ok verdict := by
  intro accepted
  obtain ⟨trap', ustate', wire', cause', doorCore', effects', core', state', cued', loaded',
    sample', step', -, -, -, -, -, -, -, -, ⟨decoded, hdec, -⟩, -⟩ := door_poke_sound accepted
  rw [cued] at cued'; cases cued'
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

/-- **`door_poke_deterministic`**: two accepted pokes of one instance with one
event agree on the product, the written state, the writes and the steps —
whatever fuel each runner brought. `audit` replays pokes in order and gets the
same states (with `door_poke_sound`). -/
theorem door_poke_deterministic {program : Program} {door : Door} {view : View}
    {claim claim' : RunClaim} {writes writes' : List FieldWrite} {verdict verdict' : Verdict}
    (accepted : checkPoke program door view claim writes = .ok verdict)
    (accepted' : checkPoke program door view claim' writes' = .ok verdict')
    (sameEvent : claim.sampleJam = claim'.sampleJam) :
    verdict.output = verdict'.output ∧ verdict.writes = verdict'.writes := by
  obtain ⟨trap, ustate, wire, cause, d, effects, core, state, cued, loaded, sample, step, hax,
    -, hout, -, -, -, -, -, ⟨decoded, hdec, hw⟩, -⟩ := door_poke_sound accepted
  obtain ⟨trap', ustate', wire', cause', d', effects', core', state', cued', loaded', sample',
    step', hax', -, hout', -, -, -, -, -, ⟨decoded', hdec', hw'⟩, -⟩ := door_poke_sound accepted'
  rw [cued] at cued'; cases cued'
  rw [loaded] at loaded'; cases loaded'
  rw [sameEvent, sample'] at sample
  have hs := Noun.jam_injective sample
  simp only [job, Noun.cell.injEq, true_and] at hs
  obtain ⟨rfl, rfl⟩ := hs
  have same := Nock.step_deterministic step step'
  simp only [Noun.cell.injEq] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  rw [hax] at hax'; cases hax'
  rw [hdec] at hdec'; cases hdec'
  exact ⟨by rw [hout, hout'], by rw [hw, hw']⟩

/-- **`door_peek_pure`**: a peek is the peek arm slammed on the path over the
instance's stored state — the core a poke would run on — at the ABI fuel. It is
a function of the program, the stored view and the path: it takes no Store and
names no write. -/
theorem door_peek_pure {program : Program} {door : Door} {view : View} {path out : Noun}
    {k : Nat} (answered : peek program door view path = .ok (.ok out k)) :
    ∃ trap ustate, Noun.cue program.jam = some trap ∧ ustateOf view = .ok ustate ∧
      Nock.Step (subjectOf trap ustate path) (peekFormula door.peek) out ∧
      Nock.steps program.abi.fuel (subjectOf trap ustate path) (peekFormula door.peek) = k := by
  unfold peek at answered
  cases hcue : Noun.cue program.jam with
  | none => simp [hcue] at answered
  | some trap =>
    cases hu : ustateOf view with
    | error e => simp [hcue, hu] at answered
    | ok ustate =>
      simp only [hcue, hu, Except.ok.injEq] at answered
      obtain ⟨hstep, -, hsteps⟩ := oracle_ok_step answered
      exact ⟨trap, ustate, rfl, rfl, hstep, hsteps⟩

/-- **`door_load_deterministic`**: the state an instance holds — its stored
state, or its booted trap's own axis 6 when never poked — is a Nock derivation
from the program and the stored view alone, and unique. -/
theorem door_load_deterministic {program : Program} {view : View} {state state' : Noun}
    {k : Nat} (loaded : stateNow program view = .ok (.ok state k))
    (other : ∃ trap ustate, Noun.cue program.jam = some trap ∧ ustateOf view = .ok ustate ∧
      Nock.Step (subjectOf trap ustate (.atom 0)) stateFormula state') :
    state' = state := by
  obtain ⟨trap, ustate, cued, u, step'⟩ := other
  unfold stateNow at loaded
  simp only [cued, u, Except.ok.injEq] at loaded
  obtain ⟨step, -, -⟩ := oracle_ok_step loaded
  exact Nock.step_deterministic step' step

/-! ## Poles: a counter kernel, decided by the kernel

`counterTrap` is a NockApp-shaped kernel written as a raw noun: the trap
`[[1 door] 0]` boots to the door `[battery [state=0 ctx=0]]` whose battery holds
a load arm at 4, a peek arm at 22 and a poke arm at 23 (NockApp's axes). The
poke gate increments the state and emits the write effect `~[['count' state']]`;
on the cause `%exit` it emits `~[[%exit 0]]` instead, which is not a write. The
peek gate answers `[~ ~ state]`. -/

/-- `'count'`, `%exit`. -/
def countKey : Nat := 500069396323
def exitTag : Nat := 1953069157

theorem countKey_cord : countKey = cordValue "count".toUTF8.toList := by decide +kernel
theorem exitTag_cord : exitTag = cordValue "exit".toUTF8.toList := by decide +kernel

/-- A gate `[battery [0 door]]` built by an arm of the door. -/
def gateArm (battery : Noun) : Noun :=
  .cell (Nock.op 1 battery) (.cell (Nock.op 1 (.atom 0)) (Nock.op 0 (.atom 1)))

/-- Over the gate `[battery [ovum door]]`: the door with state `+(state)`. -/
def counterNext : Noun :=
  Nock.op 10 (.cell (.cell (.atom 6) (Nock.op 4 (Nock.op 0 (.atom 30)))) (Nock.op 0 (.atom 7)))

/-- The poke gate's battery: cause (axis 223 of the gate) `%exit` → a non-write
effect; otherwise the write `['count' +(state)]`. -/
def counterPoke : Noun :=
  let isExit := Nock.op 5 (.cell (Nock.op 0 (.atom 223)) (Nock.op 1 (.atom exitTag)))
  let exitEffects := Nock.op 1 (.cell (.cell (.atom exitTag) (.atom 0)) (.atom 0))
  let countEntry := Noun.cell (Nock.op 1 (.atom countKey)) (Nock.op 4 (Nock.op 0 (.atom 30)))
  let countEffects := Noun.cell countEntry (Nock.op 1 (.atom 0))
  Nock.op 6 (.cell isExit (.cell (.cell exitEffects counterNext) (.cell countEffects counterNext)))

/-- The peek gate's battery: `[~ ~ state]`. -/
def counterPeek : Noun :=
  .cell (Nock.op 1 (.atom 0)) (.cell (Nock.op 1 (.atom 0)) (Nock.op 0 (.atom 30)))

/-- The load gate's battery: the door with the sample as its state. -/
def counterLoad : Noun :=
  Nock.op 10 (.cell (.cell (.atom 6) (Nock.op 0 (.atom 6))) (Nock.op 0 (.atom 7)))

def counterDoor : Noun :=
  .cell (.cell (gateArm counterLoad) (.cell (Nock.op 0 (.atom 0))
    (.cell (gateArm counterPeek) (gateArm counterPoke)))) (.cell (.atom 0) (.atom 0))

def counterTrap : Noun := .cell (Nock.op 1 counterDoor) (.atom 0)

def counterDoorAbi : Door := ⟨22, 2, 3⟩

def counter : Program :=
  ⟨Noun.jam counterTrap,
    { version := abiVersion, arm := 23, sample := [], libraries := [], fuel := 10000,
      outputs := [{ key := "count", target := 0, field := 4, type := .nat }],
      door := some counterDoorAbi }⟩

theorem counter_admissible : NockProgramCodec.check counter = .ok () := by decide +kernel

def wire0 : Noun := .atom 0
def unloaded : View := ⟨none, 0⟩
def loadedAt (n event : Nat) : View := ⟨some (jamAtom (.atom n)), event⟩

/-- The sample and output a runner claims for one counter poke. -/
def pokeClaim (ustate : Noun) (event : Nat) (cause : Noun) (effects state : Noun) (steps : Nat) :
    RunClaim :=
  ⟨⟨0⟩, Noun.jam (.cell ustate (job event wire0 cause)), Noun.jam (.cell effects state), steps⟩

def countEffects (n : Nat) : Noun := .cell (.cell (.atom countKey) (.atom n)) (.atom 0)

def counterWrites (n event : Nat) : List FieldWrite :=
  [⟨0, 2, jamAtom (.atom n)⟩, ⟨0, 3, event⟩, ⟨0, 4, n⟩]

def ranOf : Except NockRun.Refusal Ran → Option Ran
  | .ok r => some r
  | .error _ => none

set_option maxRecDepth 100000

/-- Load: an instance never poked holds the booted trap's state, `0`, in 10 steps. -/
theorem pole_door_load : ranOf (stateNow counter unloaded) = some (.ok (.atom 0) 10) := by
  decide +kernel
/-- poke 1 on the unloaded instance: state `1`, event 1, the effect `count := 1`; 42 steps
(boot included). -/
theorem pole_door_poke_first :
    writesOf (checkPoke counter counterDoorAbi unloaded
      (pokeClaim (.atom 0) 1 (.atom 1) (countEffects 1) (.atom 1) 42) (counterWrites 1 1)) =
      some (counterWrites 1 1) := by decide +kernel
/-- poke 1 again, on the stored state `1`: state `2`, event 2, `count := 2`; 44 steps. -/
theorem pole_door_poke_second :
    writesOf (checkPoke counter counterDoorAbi (loadedAt 1 1)
      (pokeClaim (.cell (.atom 0) (.atom 1)) 2 (.atom 1) (countEffects 2) (.atom 2) 44)
      (counterWrites 2 2)) = some (counterWrites 2 2) := by decide +kernel
/-- The first poke's claim, replayed once the state is `2`: stale. -/
theorem pole_door_stale :
    refusalOf (checkPoke counter counterDoorAbi (loadedAt 2 2)
      (pokeClaim (.atom 0) 1 (.atom 1) (countEffects 1) (.atom 1) 42) (counterWrites 1 1)) =
      some .sampleStale := by decide +kernel
/-- A claim on the stored state `1` whose stateOut is `1` (the door's is `2`). -/
theorem pole_door_outputMismatch :
    refusalOf (checkPoke counter counterDoorAbi (loadedAt 1 1)
      (pokeClaim (.cell (.atom 0) (.atom 1)) 2 (.atom 1) (countEffects 1) (.atom 1) 44)
      (counterWrites 1 2)) = some .outputMismatch := by decide +kernel
/-- The cause `%exit`: the door's effect `[%exit 0]` is not a write. -/
theorem pole_door_effectNotWrite :
    refusalOf (checkPoke counter counterDoorAbi (loadedAt 1 1)
      (pokeClaim (.cell (.atom 0) (.atom 1)) 2 (.atom exitTag)
        (.cell (.cell (.atom exitTag) (.atom 0)) (.atom 0)) (.atom 2) 39)
      [⟨0, 2, jamAtom (.atom 2)⟩, ⟨0, 3, 2⟩]) = some .effectNotWrite := by decide +kernel
/-- A poke's writes without the state write: refused. -/
theorem pole_door_outputNotWritten :
    refusalOf (checkPoke counter counterDoorAbi unloaded
      (pokeClaim (.atom 0) 1 (.atom 1) (countEffects 1) (.atom 1) 42) [⟨0, 3, 1⟩, ⟨0, 4, 1⟩]) =
      some .outputNotWritten := by decide +kernel
/-- Peek on the stored state `2`: `[~ ~ 2]` in 30 steps. -/
theorem pole_door_peek :
    ranOf (peek counter counterDoorAbi (loadedAt 2 2) (.atom 0)) =
      some (.ok (.cell (.atom 0) (.cell (.atom 0) (.atom 2))) 30) := by decide +kernel
/-- The stored state round-trips through its jam atom. -/
theorem pole_state_roundtrip : ofJamAtom (jamAtom (.atom 2)) = some (.atom 2) := by decide +kernel

/-- info: 'Minidregg.Kernel.NockDoor.ofJamAtom_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ofJamAtom_sound
/-- info: 'Minidregg.Kernel.NockDoor.pokeProduct_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pokeProduct_sound
/-- info: 'Minidregg.Kernel.NockDoor.effectWrites_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms effectWrites_sound
/-- info: 'Minidregg.Kernel.NockDoor.keys_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keys_unique
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
/-- info: 'Minidregg.Kernel.NockDoor.counter_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms counter_admissible
/-- info: 'Minidregg.Kernel.NockDoor.pole_door_load' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_door_load
/-- info: 'Minidregg.Kernel.NockDoor.pole_door_poke_first' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_door_poke_first
/-- info: 'Minidregg.Kernel.NockDoor.pole_door_poke_second' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_door_poke_second
/-- info: 'Minidregg.Kernel.NockDoor.pole_door_stale' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_door_stale
/-- info: 'Minidregg.Kernel.NockDoor.pole_door_outputMismatch' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_door_outputMismatch
/-- info: 'Minidregg.Kernel.NockDoor.pole_door_effectNotWrite' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_door_effectNotWrite
/-- info: 'Minidregg.Kernel.NockDoor.pole_door_outputNotWritten' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_door_outputNotWritten
/-- info: 'Minidregg.Kernel.NockDoor.pole_door_peek' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_door_peek
/-- info: 'Minidregg.Kernel.NockDoor.pole_state_roundtrip' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_state_roundtrip

end Minidregg.Kernel.NockDoor
