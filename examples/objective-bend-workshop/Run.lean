import Compiler.ObjectiveBendWorkshop
def main (args : List String) : IO Unit := do
  match args with
  | [path] => Minidregg.Compiler.ObjectiveBendWorkshop.run path
  | _ => throw (IO.userError "expected exact emitted Book path")
