import Theory.ObjectiveBendDemandData
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandData
private def limits : Limits := ⟨4096,1024⟩
private def full : Budget := ⟨4096,4096,65536⟩
private def runData (term : Term) (budget : Budget := full) :=
  complete limits budget (run limits 4096 (initial term))
def main : IO Unit := do
  let term := Term.app (.lam (.record [("after",.binary .add (.bound 0) (.nat 1)),("flag",.boolean true),("text",.label "true")])) (.nat 7)
  let .ok result := runData term | throw (IO.userError "full graph forcing failed")
  let .record [("after",.natural 8),("flag",.boolean true),("text",.label "true")] := result.value
    | throw (IO.userError "source computed data/Boolean/String collision")
  if result.remaining.ticks ≥ full.ticks then throw (IO.userError "forcing unmetered")
  let .error (.suspended,_) := runData term {full with ticks:=1}
    | throw (IO.userError "shared ticks not bounded")
  let .error (.budget,_) := runData term {full with nodes:=2}
    | throw (IO.userError "global nodes not bounded")
  let .error (.budget,_) := runData term {full with bytes:=2}
    | throw (IO.userError "global output bytes not bounded")
  let .error (.executableValue,_) := runData (.record [("body",.lam (.bound 0))])
    | throw (IO.userError "closure leaked into data")
  let .error (.duplicateField,_) := runData (.record [("a",.nat 1),("a",.nat 2)])
    | throw (IO.userError "duplicate projection silently changed Plan")
  let cyclic := Term.fix (.lam (.lam (.record [("self",.bound 1)]))) (.record [])
  let .error (.budget,_) := runData cyclic {full with nodes:=8}
    | throw (IO.userError "cyclic materialization not bounded")
  IO.println "CORE4 SAME-MACHINE FULL DATA, BOOL/STRING, GLOBAL TICK/NODE/BYTE, CLOSURE/DUP/CYCLE PASS"
