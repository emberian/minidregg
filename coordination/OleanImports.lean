import Lean
open Lean
unsafe def main (args : List String) : IO Unit := do
  for arg in args do
    let (data, _) ← readModuleData (System.FilePath.mk arg)
    let imports := data.imports.toList.map fun i => Json.str i.module.toString
    IO.println (Json.mkObj [("path", Json.str arg), ("imports", toJson imports)]).compress
