/- The Objective Bend front end as a command: every tool that turns `.obend`
source into checked typed core goes through here, and through nothing else.

  identity                                   the compiled-in front-end identity and its manifest
  parse SOURCE.obend                         the module AST (dregg.objective-bend.module.v1)
  capture PACKAGE_SPEC NEW_DIR [--objective-edition-1]
                                             lock sources: NEW_DIR/source/<i>.obend + objective.json
  elaborate CAPTURE PREFIX [ARGS] [PROJECTIONS] [LIMITS] [application|definition]
                                             PREFIX.core.json and PREFIX.typed.json
  preview REQUEST NEW_DIR                    capture → elaborate → check → run, NEW_DIR/preview.json
  batch JOBS OUT                             in-memory jobs (tests): parse/elaborate/check results

Run with `lean --run Host/ObjectiveBendFrontEndMain.lean ...` against built oleans, or as
`minidregg-host /dev/null objective-front ...` (the same code, compiled). A refusal is a
`dregg.bend.compiler-diagnostic.v1` on stderr (and in NEW_DIR/diagnostic.json) with exit 2;
`elaborate` exits 1, as its predecessor did. -/
import Compiler.ObjectiveBendFrontEndIdentity
import Host.ObjectiveBendPreview
namespace Minidregg.Host.ObjectiveBendFrontEnd
open Lean
open Minidregg.Compiler
open Minidregg.Compiler.ObjectiveBendFrontEnd
set_option autoImplicit false

def identity : String := ObjectiveBendFrontEndIdentity.identity

abbrev FE := ExceptT Diagnostic IO

def captureStage : String := "objective-package-capture"
def refuse {α : Type} (message : String) (stage : String := captureStage) : FE α :=
  throw { stage, message }
def liftFE {α : Type} (x : Except Diagnostic α) : FE α := ExceptT.mk (pure x)

def sha (bytes : ByteArray) : String := Sha256.hex bytes

def isIdentifier (s : String) : Bool := ObjectiveBendParse.isIdent s.toList

def canonicalDecimal (s : String) : Bool :=
  s == "0" || (match s.toList with
    | d :: rest => d != '0' && d.isDigit && rest.all Char.isDigit
    | [] => false)

def utf8Text (bytes : ByteArray) (what : String) : FE String :=
  match ObjectiveBendParse.decodeSource bytes with
  | some text => pure text
  | none => refuse ("TypeError: " ++ what ++ " is not valid UTF-8")

def readBytes (path : String) : FE ByteArray := do
  match ← (IO.FS.readBinFile path).toBaseIO with
  | .ok bytes => pure bytes
  | .error e => refuse ("Error: " ++ toString e)

def readJson (path : String) : FE (ByteArray × Json) := do
  let bytes ← readBytes path
  let text ← utf8Text bytes path
  match Json.parse text with
  | .ok json => pure (bytes, json)
  | .error e => refuse ("SyntaxError: " ++ path ++ ": " ++ e)

def text (j : Json) (key : String) : Option String := (j.getObjValAs? String key).toOption

def pretty (j : Json) : String := j.pretty ++ "\n"

/-- Write a file that must not exist (`flag: "wx"`). -/
def writeNew (path : System.FilePath) (contents : String) : FE Unit := do
  if ← path.pathExists then refuse ("Error: EEXIST: file already exists, " ++ path.toString)
  IO.FS.writeFile path contents

/-! ## Capture: one module, in memory -/

/-- A module's import lock as written in a package spec. -/
structure Lock where
  importAlias : Option String
  path : Option String
  target : Json
  sha256 : Option String

def Lock.ofJson (j : Json) : Lock :=
  ⟨text j "alias", text j "path", (j.getObjVal? "module").toOption.getD .null, text j "sha256"⟩

def importIndex (value : Json) (label : String) : FE Nat :=
  match value.getStr? with
  | .ok s => if canonicalDecimal s then pure s.toNat! else refuse ("Error: " ++ label ++ ": canonical decimal index required")
  | .error _ => refuse ("Error: " ++ label ++ ": canonical decimal index required")

def sealedPath (p : String) : Bool :=
  match p.toList with
  | '.' :: '/' :: rest =>
    let stem := rest.take (rest.length - 6)
    ObjectiveBendParse.endsWith rest ".obend" && ObjectiveBendParse.isIdent stem
  | _ => false

def notUtf8 (name : String) : Diagnostic :=
  ⟨"objective-source-parse", "TypeError: The encoded data was not valid for encoding utf-8", none, some name⟩

/-- Capture module `name` (the next after `prior`): fingerprint, strict decode, parse, distinct
declarations, and every import edge checked against its lock. Returns the module and its
declaration names. -/
def captureModule (prior : Array SourceModule) (name : String) (bytes : ByteArray)
    (expected : Option String) (locks : List Lock) (adopted : Bool) : FE (SourceModule × List String) := do
  let sha256 := sha bytes
  if let some e := expected then
    if e != sha256 then refuse ("Error: changed module bytes: " ++ name)
  let some source := ObjectiveBendParse.decodeSource bytes | throw (notUtf8 name)
  let ast ← match ObjectiveBendParse.parseObjective source with
    | .ok ast => pure ast
    | .error d => throw ⟨"objective-source-parse", d.message, d.span, some name⟩
  let decls := ((ast.getObjVal? "declarations").bind Json.getArr?).toOption.getD #[]
  let names := decls.toList.map declarationName
  if names.eraseDups.length != names.length then refuse ("Error: duplicate declaration in " ++ name)
  let edges := ((ast.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
  if edges.size != locks.length then refuse ("Error: import count differs: " ++ name)
  let aliases := edges.toList.map (fun e => (text e "alias").getD "")
  if aliases.eraseDups.length != aliases.length then refuse ("Error: duplicate import alias in " ++ name)
  let mut imports : List LockedImport := []
  for (edge, lock) in edges.toList.zip locks do
    let target ← importIndex lock.target "import module"
    if target ≥ prior.size then refuse "Error: imports must reference an earlier sealed module"
    let edgeAlias := (text edge "alias").getD ""
    let edgePath := (text edge "path").getD ""
    if lock.importAlias != some edgeAlias || ((!adopted || lock.path.isSome) && lock.path != some edgePath) then
      refuse ("Error: source import path/alias differs: " ++ name)
    if !sealedPath edgePath then
      refuse "Error: Objective edition 1 imports require sealed ./NAME.obend paths (Gen-1 ./NAME.bend is retired)"
    let targetModule := prior[target]!
    if edgePath != "./" ++ targetModule.name ++ ".obend" then refuse ("Error: source import target differs: " ++ name)
    if let some s := lock.sha256 then
      if s != targetModule.sha256 then refuse ("Error: changed imported bytes: " ++ name)
    imports := imports ++ [⟨edgePath, edgeAlias, (edge.getObjVal? "span").toOption.getD .null, target,
      targetModule.name, targetModule.sha256⟩]
  return (⟨name, source, sha256, imports⟩, names)

/-! ## Capture: a package spec -/

structure Captured where
  modules : Array SourceModule
  bytes : Array ByteArray
  entryModule : Nat
  entryDefinition : String
  requestSha256 : String
  requestSchema : String
  adopted : Bool

/-- `dregg.objective-bend.package-input.v1` (or, with `adopt`, a `dregg.bend.package-input.v1`
Studio capture of `.obend` modules): read and lock every module source. -/
def captureSpec (specPath : String) (adopt : Bool) : FE Captured := do
  let (requestBytes, request) ← readJson specPath
  let schema := (text request "schema").getD ""
  let adopted := adopt && schema == "dregg.bend.package-input.v1"
  if !adopted && (schema != "dregg.objective-bend.package-input.v1" || text request "edition" != some "objective-bend-1") then
    refuse "Error: Objective package schema/edition required"
  let modules := ((request.getObjVal? "modules").bind Json.getArr?).toOption.getD #[]
  if modules.isEmpty || modules.size > 256 then refuse "Error: module capacity"
  let mut names : List String := []
  for m in modules do
    let some n := text m "name" | refuse "Error: module name: identifier required"
    if !isIdentifier n then refuse "Error: module name: identifier required"
    names := names ++ [n]
  if names.eraseDups.length != names.length then refuse "Error: duplicate module name"
  let entryModule ← importIndex ((request.getObjVal? "entryModule").toOption.getD .null) "entry module"
  let some entryDefinition := text request "entryDefinition" | refuse "Error: entry definition: identifier required"
  if !isIdentifier entryDefinition then refuse "Error: entry definition: identifier required"
  if entryModule ≥ modules.size then refuse "Error: entry module absent"
  let mut captured : Array SourceModule := #[]
  let mut sources : Array ByteArray := #[]
  let mut declared : Array (List String) := #[]
  let mut total := 0
  for (m, name) in modules.toList.zip names do
    let some sourcePath := text m "sourcePath" | refuse "Error: invalid module record"
    let some locks := ((m.getObjVal? "imports").bind Json.getArr?).toOption | refuse "Error: invalid module record"
    let bytes ← readBytes sourcePath
    total := total + bytes.size
    if total > 4194304 then refuse "Error: source byte capacity"
    let (module, decls) ← captureModule captured name bytes (text m "sha256") (locks.toList.map Lock.ofJson) adopted
    captured := captured.push module
    sources := sources.push bytes
    declared := declared.push decls
  if !(declared[entryModule]!.contains entryDefinition) then refuse "Error: entry declaration absent"
  return ⟨captured, sources, entryModule, entryDefinition, sha requestBytes, schema, adopted⟩

def captureSchema : String := "dregg.objective-bend.captured-package.v2"

def captureJson (c : Captured) (paths : Array String) : Json :=
  Json.mkObj [("schema", toJson captureSchema), ("edition", toJson "objective-bend-1"),
    ("frontEnd", toJson identity), ("requestSha256", toJson c.requestSha256), ("requestSchema", toJson c.requestSchema),
    ("editionSelection", toJson (if c.adopted then "explicit-caller-adoption" else "declared-request")),
    ("modules", Json.arr ((c.modules.zip paths).map fun (m, path) => Json.mkObj [("name", toJson m.name),
      ("sourcePath", toJson path), ("sha256", toJson m.sha256),
      ("imports", Json.arr (m.imports.map LockedImport.json).toArray)])),
    ("entryModule", toJson (toString c.entryModule)), ("entryDefinition", toJson c.entryDefinition),
    ("sourceEntry", toJson (c.modules[c.entryModule]!.name ++ "." ++ c.entryDefinition)),
    ("sourceStatus", toJson "exact locked source"),
    ("semanticStatus", toJson "requires Objective elaboration and execution receipt"),
    ("theoremScope", toJson "no typing or totality theorem asserted")]

/-- Write the locked snapshot: `dir/source/<i>.obend` and `dir/objective.json`. -/
def writeCapture (c : Captured) (dir : System.FilePath) : FE Json := do
  IO.FS.createDirAll (dir / "source")
  let root ← IO.FS.realPath dir
  let mut paths : Array String := #[]
  for i in [0:c.bytes.size] do
    let path := root / "source" / s!"{i}.obend"
    if ← path.pathExists then refuse ("Error: EEXIST: file already exists, " ++ path.toString)
    IO.FS.writeBinFile path c.bytes[i]!
    paths := paths.push path.toString
  let json := captureJson c paths
  writeNew (dir / "objective.json") (pretty json)
  return json

/-! ## Loading a capture -/

structure Loaded where
  bytes : ByteArray
  json : Json
  modules : List SourceModule
  entryModule : Nat
  entryDefinition : String

/-- Re-read a capture: its schema and front end, every source against its fingerprint, every
lock against the module it names. -/
def loadCapture (path : String) : FE Loaded := do
  let (bytes, capture) ← readJson path
  if text capture "schema" != some captureSchema || text capture "edition" != some "objective-bend-1" then
    refuse "Error: unsupported captured edition" "objective-core-elaboration"
  if text capture "frontEnd" != some identity then
    refuse ("Error: capture was produced by another front end (" ++ (text capture "frontEnd").getD "none" ++
      ") than this one (" ++ identity ++ ")") "objective-core-elaboration"
  let rows := ((capture.getObjVal? "modules").bind Json.getArr?).toOption.getD #[]
  if rows.size > 64 then refuse "Error: preview module capacity refused" "objective-core-elaboration"
  let mut modules : Array SourceModule := #[]
  for row in rows do
    let some sourcePath := text row "sourcePath" | refuse "Error: invalid captured module" "objective-core-elaboration"
    let name := (text row "name").getD ""
    let source ← readBytes sourcePath
    if source.size > 2097152 then refuse "Error: preview source capacity refused" "objective-core-elaboration"
    if some (sha source) != text row "sha256" then
      refuse ("Error: captured source hash mismatch " ++ name) "objective-core-elaboration"
    let some decoded := ObjectiveBendParse.decodeSource source
      | refuse ("Error: captured source is not UTF-8 " ++ name) "objective-core-elaboration"
    let edges := ((row.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]
    let mut imports : List LockedImport := []
    for edge in edges do
      let index := (text edge "module").getD ""
      let target := index.toNat!
      if !canonicalDecimal index || target ≥ modules.size || some modules[target]!.name != text edge "moduleName" ||
          some modules[target]!.sha256 != text edge "sha256" then
        refuse "Error: invalid locked import" "objective-core-elaboration"
      imports := imports ++ [⟨(text edge "path").getD "", (text edge "alias").getD "",
        (edge.getObjVal? "span").toOption.getD .null, target, modules[target]!.name, modules[target]!.sha256⟩]
    modules := modules.push ⟨name, decoded, sha source, imports⟩
  let entryText := (text capture "entryModule").getD ""
  if !canonicalDecimal entryText then refuse "Error: selected module" "objective-core-elaboration"
  return ⟨bytes, capture, modules.toList, entryText.toNat!, (text capture "entryDefinition").getD ""⟩

/-! ## Commands -/

def report (dir : Option System.FilePath) (d : Diagnostic) : IO UInt32 := do
  if let some dir := dir then
    try
      IO.FS.createDirAll dir
      unless ← (dir / "diagnostic.json").pathExists do IO.FS.writeFile (dir / "diagnostic.json") (pretty d.json)
    catch _ => pure ()
  IO.eprintln d.json.compress
  return 2

def parseCommand (path : String) : IO UInt32 := do
  match ← (do
      let bytes ← readBytes path
      let source ← utf8Text bytes path
      liftFE (match ObjectiveBendParse.parseObjective source with
        | .ok ast => .ok ast
        | .error d => .error { stage := "objective-source-parse", message := d.message, span := d.span }) : FE Json).run with
  | .ok ast => IO.println ast.compress; return 0
  | .error d => report none d

def captureCommand (spec dir : String) (adopt : Bool) : IO UInt32 := do
  match ← (do writeCapture (← captureSpec spec adopt) dir : FE Json).run with
  | .ok json => IO.println json.compress; return 0
  | .error d => report (some dir) d

def elaborateCommand (capturePath prefix_ argsRaw projectionsRaw limitsRaw mode : String) : IO UInt32 := do
  let run : FE Json := do
    let loaded ← loadCapture capturePath
    let parse (raw what : String) : FE Json := match Json.parse raw with
      | .ok j => pure j
      | .error e => refuse ("SyntaxError: " ++ what ++ ": " ++ e) "objective-core-elaboration"
    let lowered ← liftFE (lower loaded.modules loaded.entryModule loaded.entryDefinition (← parse argsRaw "arguments")
      (← parse projectionsRaw "projections") (← parse limitsRaw "limits") mode)
    let core := lowered.core
    IO.FS.writeFile (prefix_ ++ ".typed.json") (pretty lowered.packet)
    IO.FS.writeFile (prefix_ ++ ".core.json") (pretty core)
    return Json.mkObj [("schema", toJson "dregg.objective-bend.core.v2"), ("sourceEntry", toJson lowered.sourceEntry),
      ("outputPrefix", toJson prefix_), ("coreSha256", toJson (Sha256.hexString core.compress)),
      ("frontEnd", toJson identity),
      ("status", (core.getObjVal? "status").toOption.getD .null)]
  match ← run.run with
  | .ok json => IO.println json.compress; return 0
  | .error d => IO.eprintln d.json.compress; return 1

/-- `^[1-9][0-9]*$` at most `cap`, kept as its decimal text. -/
def count (limits : Json) (key : String) (cap : Nat) : FE String := do
  let some v := text limits key | refuse ("Error: invalid preview capacity: " ++ key) "preview-request"
  match ObjectiveBendFrontEnd.positive (toJson v) cap with
  | some _ => pure v
  | none => refuse ("Error: invalid preview capacity: " ++ key) "preview-request"

/-- The preview: a capture-bound request, elaborated by this front end, checked by the actual
checker and run by the bounded demand machine on the same decoded term. -/
def previewCommand (requestPath dirPath : String) : IO UInt32 := do
  let dir := System.FilePath.mk dirPath
  let bindingRef ← IO.mkRef (Json.mkObj [])
  let bind (k : String) (v : Json) : IO Unit := bindingRef.modify fun b => b.setObjVal! k v
  let run : FE Json := do
    let (requestBytes, request) ← readJson requestPath
    bind "previewRequestSha256" (toJson (sha requestBytes))
    if text request "schema" != some "dregg.objective-bend.preview-input.v2" ||
        (text request "capturePath").isNone || (text request "captureSha256").isNone then
      refuse "Error: preview input schema/capture pin required" "preview-request"
    let captureBytes ← readBytes ((text request "capturePath").getD "")
    if some (sha captureBytes) != text request "captureSha256" then
      refuse "Error: captured package identity differs" "preview-request"
    let loaded ← loadCapture ((text request "capturePath").getD "")
    bind "captureSha256" (toJson (sha captureBytes))
    bind "sourceRequestSha256" ((loaded.json.getObjVal? "requestSha256").toOption.getD .null)
    bind "edition" (toJson "objective-bend-1")
    bind "frontEnd" (toJson identity)
    bind "sourceEntry" ((loaded.json.getObjVal? "sourceEntry").toOption.getD .null)
    bind "modules" (Json.arr (loaded.modules.map SourceModule.binding).toArray)
    let some arguments := (request.getObjVal? "arguments").toOption.bind (fun a => (a.getArr?).toOption)
      | refuse "Error: arguments/projections arrays required" "preview-request"
    let some projections := (request.getObjVal? "projections").toOption.bind (fun a => (a.getArr?).toOption)
      | refuse "Error: arguments/projections arrays required" "preview-request"
    let encoding := (text request "argumentEncoding").getD "legacy-values-v1"
    if encoding != "legacy-values-v1" && encoding != "typed-values-v1" then
      refuse "Error: unknown preview argument encoding" "preview-request"
    let wire := if encoding == "typed-values-v1" then
        Json.mkObj [("schema", toJson "dregg.objective-bend.argument-values.v1"), ("values", Json.arr arguments)]
      else Json.arr arguments
    bind "argumentEncoding" (toJson encoding)
    let limitsIn := (request.getObjVal? "limits").toOption.getD (Json.mkObj [])
    let ticks ← count limitsIn "ticks" 100000
    let heap ← count limitsIn "heap" 100000
    let stack ← count limitsIn "stack" 100000
    let typeFuel ← count limitsIn "typeFuel" 16384
    let responses := (request.getObjVal? "responses").toOption.getD (Json.arr #[])
    match responses.getArr? with
    | .ok a => if a.size > 64 then refuse "Error: preview responses must be an array of at most 64 typed data values" "preview-request"
    | .error _ => refuse "Error: preview responses must be an array of at most 64 typed data values" "preview-request"
    let limits := Json.mkObj [("ticks", toJson ticks), ("heap", toJson heap), ("stack", toJson stack)]
    bind "limits" (Json.mkObj [("ticks", toJson ticks), ("heap", toJson heap), ("stack", toJson stack),
      ("typeFuel", toJson typeFuel)])
    IO.FS.createDirAll dir
    if !(← dir.readDir).isEmpty then refuse "Error: preview output directory must be empty" "preview-request"
    writeNew (dir / "capture.json") (String.fromUTF8! captureBytes)
    let lowered ← liftFE (lower loaded.modules loaded.entryModule loaded.entryDefinition wire (Json.arr projections)
      (Json.mkObj [("ticks", toJson ticks), ("heap", toJson heap), ("stack", toJson stack), ("typeFuel", toJson typeFuel)])
      "application")
    let coreText := pretty lowered.core
    let packetText := pretty lowered.packet
    writeNew (dir / "source.core.json") coreText
    writeNew (dir / "source.typed.json") packetText
    bind "coreSha256" (toJson (Sha256.hexString coreText))
    bind "sourceEntry" (toJson lowered.sourceEntry)
    if let .error message := lowered.proposal then refuse message "objective-source-type-proposal"
    writeNew (dir / "limits.json") (pretty limits)
    let responsesText := pretty responses
    writeNew (dir / "responses.json") responsesText
    bind "typedPacketSha256" (toJson (Sha256.hexString packetText))
    bind "responsesSha256" (toJson (Sha256.hexString responsesText))
    let result ← match ObjectiveBendPreview.preview lowered.packet limits responses with
      | .ok r => pure r
      | .error message => refuse message "objective-typed-preview"
    let output := Json.mkObj [("schema", toJson "dregg.objective-bend.preview-result.v2"),
      ("status", (result.getObjVal? "status").toOption.getD .null), ("binding", ← bindingRef.get),
      ("preview", result), ("authority", toJson "none; source preview only")]
    writeNew (dir / "preview.json") (pretty output)
    return output
  match ← run.run with
  | .ok output => IO.println output.compress; return 0
  | .error d =>
    let refused := Json.mkObj [("schema", toJson "dregg.objective-bend.preview-result.v2"), ("status", toJson "refused"),
      ("binding", ← bindingRef.get), ("diagnostic", d.json), ("authority", toJson "none; source preview only")]
    try
      IO.FS.createDirAll dir
      unless ← (dir / "diagnostic.json").pathExists do IO.FS.writeFile (dir / "diagnostic.json") (pretty refused)
    catch _ => pure ()
    IO.println refused.compress
    return 2

/-! ## Batch (tests): many in-memory jobs, one process -/

/-- A job: `{name, modules:[{name, source, imports:[{alias, module}]}], entryModule,
entryDefinition, arguments, projections?, limits?, mode?}`, or `{name, parse: SOURCE}`. -/
def batchJob (job : Json) : IO Json := do
  let name := (text job "name").getD ""
  if let some source := text job "parse" then
    return match ObjectiveBendParse.parseObjective source with
      | .ok ast => Json.mkObj [("name", toJson name), ("ok", toJson true), ("ast", ast)]
      | .error d => Json.mkObj [("name", toJson name), ("ok", toJson false), ("diagnostic", d.json)]
  let run : FE Json := do
    let rows := ((job.getObjVal? "modules").bind Json.getArr?).toOption.getD #[]
    let mut modules : Array SourceModule := #[]
    for row in rows do
      let locks := (((row.getObjVal? "imports").bind Json.getArr?).toOption.getD #[]).toList.map fun l =>
        ({ importAlias := text l "alias", path := none, target := (l.getObjVal? "module").toOption.getD .null,
           sha256 := none } : Lock)
      let (m, _) ← captureModule modules ((text row "name").getD "") ((text row "source").getD "").toUTF8 none locks true
      modules := modules.push m
    let entry := match job.getObjVal? "entryModule" with
      | .ok (.str s) => s.toNat!
      | .ok j => (j.getNat?).toOption.getD (modules.size - 1)
      | .error _ => modules.size - 1
    let lowered ← liftFE (lower modules.toList entry ((text job "entryDefinition").getD "")
      ((job.getObjVal? "arguments").toOption.getD (Json.arr #[])) ((job.getObjVal? "projections").toOption.getD (Json.arr #[]))
      ((job.getObjVal? "limits").toOption.getD (Json.mkObj [("heap", toJson "100000"), ("stack", toJson "100000"),
        ("ticks", toJson "100000")]))
      ((text job "mode").getD "application"))
    let checked : Json := match accept lowered with
      | .ok a => Json.mkObj [("accepted", toJson true), ("type", reprStr a.typed.type |> toJson)]
      | .error d => Json.mkObj [("accepted", toJson false), ("diagnostic", d.json)]
    return Json.mkObj [("core", lowered.core), ("packet", lowered.packet), ("check", checked)]
  match ← run.run with
  | .ok out => return Json.mkObj [("name", toJson name), ("ok", toJson true), ("output", out)]
  | .error d => return Json.mkObj [("name", toJson name), ("ok", toJson false), ("diagnostic", d.json)]

def batchCommand (jobsPath outPath : String) : IO UInt32 := do
  let jobs ← match ← (readJson jobsPath).run with
    | .ok (_, j) => pure ((j.getArr?).toOption.getD #[])
    | .error d => return ← report none d
  let results ← jobs.mapM batchJob
  IO.FS.writeFile outPath ((Json.arr results).compress ++ "\n")
  return 0

def identityJson : Json :=
  Json.mkObj [("schema", toJson "dregg.objective-bend.front-end-identity.v1"), ("frontEnd", toJson identity),
    ("manifest", toJson ObjectiveBendFrontEndIdentity.manifest)]

def usage : String :=
  "usage: objective-front identity | parse SOURCE.obend | capture PACKAGE_SPEC NEW_DIR [--objective-edition-1] | " ++
  "elaborate CAPTURE PREFIX [ARGS] [PROJECTIONS] [LIMITS] [application|definition] | preview REQUEST NEW_DIR | batch JOBS OUT"

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["identity"] => IO.println identityJson.compress; return 0
  | ["parse", path] => parseCommand path
  | ["capture", spec, dir] => captureCommand spec dir false
  | ["capture", spec, dir, "--objective-edition-1"] => captureCommand spec dir true
  | "elaborate" :: capture :: prefix_ :: rest =>
    let args := rest.getD 0 "[]"
    let projections := rest.getD 1 "[]"
    let limits := rest.getD 2 "{\"heap\":\"100000\",\"stack\":\"100000\",\"ticks\":\"100000\"}"
    let mode := rest.getD 3 "application"
    if rest.length > 4 then IO.eprintln usage; return 2
    elaborateCommand capture prefix_ args projections limits mode
  | ["preview", request, dir] => previewCommand request dir
  | ["batch", jobs, out] => batchCommand jobs out
  | _ => IO.eprintln usage; return 2

end Minidregg.Host.ObjectiveBendFrontEnd
