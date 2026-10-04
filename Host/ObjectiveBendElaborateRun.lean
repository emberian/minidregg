/- Batch driver for the Lean Objective Bend elaborator: reads a JSON array of
jobs `{name, modules:[{name, imports:[{alias, moduleName}], ast}], entryModule,
entryDefinition, arguments, mode}` and writes one result per job: the Core4
term, the typing proposal (or why it is unsupported), and whether the term
erases to the current Core4 `Term`. Consumed by
native/bend-source/objective-elaborate-tv.ts (translation validation). -/
import Compiler.ObjectiveBendElaborate

def main (arguments : List String) : IO UInt32 := do
  let [jobsPath, outputPath] := arguments | do
    IO.eprintln "usage: ObjectiveBendElaborate JOBS_JSON OUTPUT_JSON"; return 2
  let text ← IO.FS.readFile jobsPath
  match Lean.Json.parse text >>= (·.getArr?) with
  | .error e => IO.eprintln e; return 2
  | .ok jobs =>
    let results := jobs.map Minidregg.Compiler.ObjectiveBendElaborate.runJob
    IO.FS.writeFile outputPath ((Lean.Json.arr results).compress ++ "\n")
    return 0
