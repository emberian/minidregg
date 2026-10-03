/- Executable native-Nock constructor probes. General byte/definition and
complete native admission results live in the imported source modules. -/
import Kernel.WorldPrototypeConstruction
import Kernel.NockEntry
import Theory.AssertAxioms

namespace Minidregg.Assurance.WorldPrototypeConstructionChecks
open Minidregg.Theory
open Minidregg.Kernel
open Minidregg.Kernel.WorldPrototypeConstruction

set_option autoImplicit false

def quote (value : Noun) : Noun := .cell (.atom 1) value
def slot (axis : Nat) : Noun := .cell (.atom 0) (.atom axis)
def select (value : Noun) (axis : Nat) : Noun :=
  .cell (.atom 2) (.cell value (quote (slot axis)))

def parentBytes : List UInt8 := [7, 255, 1, 255, 42, 0]
def successorBytes : List UInt8 := [9, 255, 2, 255, 42, 0]

/-- Same two-target parent sample coordinate used by jworld-construction. -/
def nativeSample : Noun := .cell (.cell (.atom 0) (.cell (.atom 0) (.atom 0)))
  (NockProgramCell.nockList [
    .cell (NockProgramCell.cord "target/0") (.atom 9),
    .cell (NockProgramCell.cord "target/1") (.atom 7),
    .cell (NockProgramCell.cord "parent") (byteNoun parentBytes)])

def patched : Noun :=
  .cell (quote (.atom 9))
    (.cell (quote (.atom 255))
      (.cell (quote (.atom 2))
        (.cell (quote (.atom 255))
          (select (select (select (select (slot 221) 3) 3) 3) 3))))

def outputFormula : Noun :=
  .cell (.cell (quote (NockProgramCell.cord "definition")) patched) (quote (.atom 0))

def nativeCore : Noun :=
  .cell (quote (.cell outputFormula (.cell (.atom 0) (.atom 0)))) (.atom 0)

def nativeEntry := NockEntry.subjectFormula 2 nativeCore [] nativeSample

def nativeResult := NockEntry.oracle 1000 nativeEntry.1 nativeEntry.2

def expected : Noun := NockProgramCell.nockList
  [.cell (NockProgramCell.cord "definition") (byteNoun successorBytes)]

theorem actual_native_constructor_output :
    (match nativeResult with
     | .ok value _ => value == expected
     | _ => false) = true := by decide +kernel

theorem terminal_zero_retained : bytesOfNoun (byteNoun successorBytes) = some successorBytes := by
  decide +kernel

theorem improper_byte_list_refused : bytesOfNoun (.cell (.atom 1) (.atom 2)) = none := by
  decide +kernel

theorem overwide_byte_refused : bytesOfNoun (.cell (.atom 256) (.atom 0)) = none := by
  decide +kernel

#assert_axioms actual_native_constructor_output
#assert_axioms terminal_zero_retained
#assert_axioms improper_byte_list_refused
#assert_axioms overwide_byte_refused

end Minidregg.Assurance.WorldPrototypeConstructionChecks
