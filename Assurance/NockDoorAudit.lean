/-
# Assurance.NockDoorAudit — concrete counter checks for the deployed Nock door

The runtime API and general soundness theorems live in `Kernel.NockDoor`.
These counter fixtures and kernel-decided poles retain their original namespace
and statements. Both `Deployed` and the research `Assurance` umbrella import
this module, so the full checks remain mandatory without forcing them into
Host's runtime import closure.
-/
import Kernel.NockDoor

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
  ⟨Run.fixtureEvaluator, Noun.jam counterTrap,
    { version := abiVersion, sample := [], libraries := [], fuel := 10000,
      outputs := [{ key := "count", target := 0, field := 4, type := .nat }],
      door := some counterDoorAbi }, encodeParams ⟨23⟩⟩

/-- The counter is admitted at birth on Nock, with params arm 23 (NockApp's poke axis). -/
theorem counter_admissible : (Machine.nock.admit counter).toOption = some ⟨23⟩ := by decide +kernel

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

def ranOf : Except Run.Refusal (Ran Noun) → Option (Ran Noun)
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
      some (.sampleStale none) := by decide +kernel
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

end Minidregg.Kernel.NockDoor
