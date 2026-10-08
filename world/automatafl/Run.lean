/- Batch source cross-check driver. Calls the existing front end, proof-producing
checker and demand preview; contains no Automatafl semantics. -/
import Host.ObjectiveBendFrontEnd
open Lean
open Minidregg.Compiler.ObjectiveBendFrontEnd

def main (args : List String) : IO UInt32 := do
  let [sourcePath, jobsPath, outputPath] := args
    | IO.eprintln "usage: Run.lean SOURCE JOBS OUTPUT"; return 64
  let source ← IO.FS.readFile sourcePath
  let module : SourceModule := ⟨"Automatafl", source, Minidregg.Compiler.Sha256.hexString source, []⟩
  let decoded ← match parseModule module with
    | .ok d => pure d
    | .error e => IO.eprintln e.json.compress; return 2
  let jobsText ← IO.FS.readFile jobsPath
  let .ok jobs := Json.parse jobsText >>= Json.getArr?
    | IO.eprintln "invalid jobs"; return 2
  let limits := Json.mkObj [("ticks", toJson "100000"), ("heap", toJson "100000"),
    ("stack", toJson "10000"), ("typeFuel", toJson "16384")]
  let out ← IO.FS.Handle.mk outputPath .write
  for job in jobs do
    let id := (job.getObjVal? "id").toOption.getD Json.null
    let entry := (job.getObjValAs? String "entry").toOption.getD "play"
    let arguments := (job.getObjVal? "arguments").toOption.getD (Json.arr #[])
    let result : Except String Json := do
      let lowered ← (lowerDecoded [module] [decoded] 0 entry arguments (Json.arr #[]) limits "application").mapError (fun (d : Diagnostic) => d.json.compress)
      Minidregg.Host.ObjectiveBendPreview.preview lowered.packet limits
    let fields := match result with
      | .ok r => [("result", r)]
      | .error e => [("error", toJson e)]
    out.putStrLn (Json.mkObj (("id",id) :: fields)).compress
    out.flush
  return 0
