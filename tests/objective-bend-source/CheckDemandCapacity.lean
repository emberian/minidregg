import Theory.ObjectiveBendDemandCapacity
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Theory.ObjectiveBendDemandCapacity
private def limits : Limits := ⟨4096,1024⟩
private def term : Term := .binary .multiply (.binary .multiply (.nat 9) (.nat 9))
  (.binary .multiply (.nat 9) (.nat 9))
def main : IO Unit := do
  let (outcome,leftTicks) := forceWith (allows ⟨8⟩) limits 100 (initial term)
  let .suspended .capacity retained := outcome
    | throw (IO.userError "arithmetic scalar bound did not suspend")
  let .returned (.natural 81) := retained.control
    | throw (IO.userError "guard lost pre-arithmetic right operand")
  let .binaryRight .multiply (.natural 81)::_ := retained.stack
    | throw (IO.userError "guard lost pre-arithmetic left operand/continuation")
  let (resumed,_) := forceWith (allows ⟨16⟩) limits leftTicks retained
  let .finished (.natural 6561) _ := resumed
    | throw (IO.userError "exact retained state could not resume with larger declared scalar cap")
  let .finished (.natural 6561) _ := runBounded limits 100 (initial term)
    | throw (IO.userError "raw Core4 semantics changed")
  let .error (.suspended,_) := executeWith (allows ⟨8⟩) limits ⟨100,100,4096⟩ (.record [("deep",term)])
    | throw (IO.userError "record field forcing bypassed scalar capacity")
  let .error .capacity := decodeNatural ⟨8⟩ (String.ofList (List.replicate 10000 '9'))
    | throw (IO.userError "textual pre-parse cap missing")
  let .error .capacity := decodeNatural ⟨8⟩ "256"
    | throw (IO.userError "exact input bit cap missing")
  let .error .noncanonical := decodeNatural ⟨8⟩ "0001"
    | throw (IO.userError "noncanonical input accepted")
  let .ok 255 := decodeNatural ⟨8⟩ "255"
    | throw (IO.userError "valid bounded input refused")
  IO.println "NATIVE PRE-ARITHMETIC CAP, EXACT STATE RESUMPTION, GUARDED FIELD FORCING, INPUT PREPARSE/BIT CAPS PASS; RAW LANGUAGE UNCHANGED"
