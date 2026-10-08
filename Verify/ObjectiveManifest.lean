/-
# Verify/ObjectiveManifest.lean -- the scanner behind the Objective contract manifests

One scanner, two environments (scripts/check-objective-proofs.sh `proofs`):

* scripts/ObjectiveManifest.lean -- the `Theory.ObjectiveBend*` modules, in an environment with
  no Mathlib module (refused: Mathlib's delaborators re-render unchanged statements).
* scripts/ObjectiveManifestMathlib.lean -- every other module of this repository in the import
  closure of `ObjectiveProofs` (Kernel, Compiler, Pred, Selvage, the rest of Theory), in an
  environment that imports `ObjectiveProofs` and therefore Mathlib.

A run writes one file (the path in `OBJECTIVE_MANIFEST_OUT`); scripts/objective-manifest.py turns
it into the per-module manifests under scripts/gates/objective-manifest/ and ratchets them. Lines:

* `R` -- one row per covered declaration (compiler-generated names excluded): its name, the name
  it is shown under, its module, its kind, its exact axiom set (theorems, definitions, opaques)
  and its statement: the ELABORATED type, pretty-printed with full names at unbounded width,
  whitespace collapsed; a definition whose type ends in `Prop` is followed by `:= <body>`. The
  text is for the human reading a diff; what the ratchet compares are the hashes below.
* `C` -- one record per constant of the CLOSURE of the rows: the covered declarations, and every
  constant their content mentions, transitively, as long as it belongs to this repository. A
  constant's content is its type, plus its body for a definition (`def`, `abbrev`, `instance`,
  structure projections, the generated matchers and auxiliary definitions), plus the shape and
  constructor list of an inductive type, plus the parent and position of a constructor.
  A theorem's content is its type: proofs are irrelevant, the axiom set pins what they rest on.
  The CUT: a constant of a module outside this repository (Init, Lean, Std, Batteries, Mathlib,
  ...), an axiom and an opaque is a leaf hashed by kind, name, universe parameters and type;
  its body is not followed. Those modules are fixed by `lean-toolchain` and `lake-manifest.json`;
  an opaque's body is invisible to the kernel's definitional equality, so no statement can
  depend on it. A changed type of a leaf still changes every closure that reaches it.
* lower-case node lines -- the expression DAG the `C` records' types and bodies point into,
  each distinct subterm once, in dependency order (a node's children precede it; ids count the
  node lines from 0). Binder names and metadata are not part of a node (alpha-equivalent terms
  share one); universe parameters are named.

The hashes (SHA-256, Merkle over this DAG and over the strongly connected components of the
constant dependency graph) are computed by scripts/objective-manifest.py: a theorem's `closure`
hash changes when the body of any repository definition its statement reaches changes, however
deep, with the statement text byte-identical (`def Safe := True`).

The scan region is delimited by `SCAN-BEGIN`/`SCAN-END`: the gate's self-test deletes it in a
scratch copy and requires the instrument floor to fail the run.
-/
import Lean

open Lean Meta

namespace Minidregg.ObjectiveManifest

/-- What one manifest run covers and what a working scan of it must find. -/
structure Config where
  /-- Prefix of every diagnostic line (`objective-manifest`, `objective-manifest-mathlib`). -/
  label : String
  /-- The modules whose declarations this run prints. -/
  covers : Name → Bool
  /-- Declarations of the running file itself (no module) under this prefix are covered: the
  self-tests' planted declarations and scratch copies of a module. -/
  localPrefix : Option Name := none
  /-- Refuse to run with any `Mathlib` module in the environment. -/
  refuseMathlib : Bool
  /-- A working scan prints at least this many rows... -/
  scanFloor : Nat
  /-- ...and these by name. A scan that silently stopped walking lands under one of them. -/
  mustFind : List Name
  /-- Instrument failures the running script found before the scan (coverage checks). -/
  preFailures : Array String := #[]

/-- Compiler-generated or lazily realized names: their presence depends on what
some proof happened to use, not on what the module states. They get no row; they are
still in the closure of any row that mentions them. -/
def generatedTails : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "ibelow", "binductionOn",
   "noConfusion", "noConfusionType", "ndrec", "ndrecOn", "sizeOf_spec", "injEq", "inj",
   "toCtorIdx", "ctorIdx", "eq_def", "congr_simp", "induct", "mutual_induct", "fun_cases",
   "induct_unfolding", "fun_cases_unfolding", "eq_unfold", "ctorElim", "ctorElimType"]

/-- `s` is `pre` followed by an upper-case letter (`instReprCell`, `decEqTerm`),
the shape of a derived instance or its helper. -/
def upperAfter (s pre : String) : Bool :=
  s.startsWith pre && match (s.toList.drop pre.length).head? with
    | some c => c.isUpper
    | none => false

def generatedComponent (s : String) : Bool :=
  generatedTails.contains s || s.startsWith "match_" || s.startsWith "proof_"
    || s.startsWith "_" || (s.startsWith "eq_" && (s.toList.drop 3).all Char.isDigit)
    || upperAfter s "inst" || upperAfter s "decEq" || upperAfter s "repr"

def generated (name : Name) : Bool :=
  let user := (privateToUserName? name).getD name
  user.isInternalDetail || user.components.any fun c => match c with
    | .str _ s => generatedComponent s
    | _ => false

def oneLine (s : String) : String :=
  " ".intercalate ((s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty))

def ppOneLine (e : Expr) : MetaM String := do
  return oneLine (toString (← ppExpr e))

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .axiomInfo _ => "axiom"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

def endsInProp (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun _ body => return body.isProp

def shownName (name : Name) : String :=
  match privateToUserName? name with
  | some user => s!"private {user}"
  | none => toString name

/-- The statement text of one declaration (the human-readable column of its row). -/
def statementText (info : ConstantInfo) : MetaM String := do
  let mut text ← ppOneLine info.type
  if let .defnInfo d := info then
    if ← endsInProp info.type then
      text := text ++ s!" := {← ppOneLine d.value}"
  return text

/-- The exact axiom set of a theorem, definition or opaque (`-` for none); `` for other kinds. -/
def axiomField (name : Name) (info : ConstantInfo) : MetaM String := do
  let kind := kindOf info
  unless kind == "theorem" || kind == "def" || kind == "opaque" do return ""
  let axioms := (← collectAxioms name).map toString |>.qsort (· < ·)
  return if axioms.isEmpty then "-" else ",".intercalate axioms.toList

/-! ## The closure: constant records and the expression DAG -/

def levelText : Level → String
  | .zero => "0"
  | .succ l => s!"s({levelText l})"
  | .max a b => s!"m({levelText a},{levelText b})"
  | .imax a b => s!"i({levelText a},{levelText b})"
  | .param n => s!"p{n}"
  | .mvar _ => "?"

def binderText : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

structure EmitState where
  ids : Std.HashMap Expr Nat := {}
  next : Nat := 0

abbrev EmitM := StateRefT EmitState IO

/-- Emit `e`'s node (children first) and return its id. Metadata is transparent. -/
partial def node (h : IO.FS.Handle) (e : Expr) : EmitM Nat := do
  if let some i := (← get).ids[e]? then return i
  if let .mdata _ b := e then
    let i ← node h b
    modify fun st => { st with ids := st.ids.insert e i }
    return i
  let line ← match e with
    | .bvar i => pure s!"b {i}"
    | .fvar f => pure s!"F {f.name}"
    | .mvar m => pure s!"M {m.name}"
    | .sort u => pure s!"s {levelText u}"
    | .const n us => pure s!"c {",".intercalate (us.map levelText)} {n}"
    | .app f a => do
      let i ← node h f
      let j ← node h a
      pure s!"a {i} {j}"
    | .lam _ t b bi => do
      let i ← node h t
      let j ← node h b
      pure s!"l {binderText bi} {i} {j}"
    | .forallE _ t b bi => do
      let i ← node h t
      let j ← node h b
      pure s!"f {binderText bi} {i} {j}"
    | .letE _ t v b nd => do
      let i ← node h t
      let j ← node h v
      let k ← node h b
      pure s!"t {nd} {i} {j} {k}"
    | .lit (.natVal n) => pure s!"n {n}"
    | .lit (.strVal s) => pure s!"x {s.quote}"
    | .proj s i b => do
      let j ← node h b
      pure s!"p {i} {j} {s}"
    | .mdata _ _ => unreachable!
  h.putStrLn line
  -- `modifyGet` keeps the map unshared: a `get` held across the insert copies all of it
  modifyGet fun st => (st.next, { ids := st.ids.insert e st.next, next := st.next + 1 })

def safetyText : DefinitionSafety → String
  | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"

def quotText : QuotKind → String
  | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"

/-- Structure type names stored in raw projections. `Expr.forEach` uses `MonadCacheT` internally,
so shared subterms of the expression DAG are visited once. -/
private def projectionTypeNames (e : Expr) : Array Name := runST fun σ => do
  let acc ← ST.mkRef (σ := σ) #[]
  e.forEach fun
    | .proj typeName _ _ => acc.modify (·.push typeName)
    | _ => pure ()
  acc.get

/-- Everything in Lean's optimized, pointer-cached constant fold, plus the structure type stored
only in each raw `Expr.proj` (which Lean 4.30's fold omits). -/
def usedConstants (e : Expr) : Array Name := e.getUsedConstants ++ projectionTypeNames e

/-- The roots (types and bodies) of a constant's content, the extra shape it carries, and
the constants its content mentions. A leaf (`internal = false`, an axiom, an opaque) carries
its type only and mentions nothing. -/
def content (internal : Bool) (info : ConstantInfo) : Array Expr × String × Array Name :=
  let leaf := (#[info.type], "", #[])
  if !internal then leaf else
  match info with
  | .defnInfo d => (#[d.type, d.value], safetyText d.safety,
      usedConstants d.type ++ usedConstants d.value)
  | .thmInfo t => (#[t.type], "", usedConstants t.type)
  | .inductInfo i => (#[i.type],
      s!"{i.numParams} {i.numIndices} {i.isRec} {i.isUnsafe} {i.isReflexive} all={",".intercalate (i.all.map toString)} ctors={",".intercalate (i.ctors.map toString)}",
      usedConstants i.type ++ i.all.toArray ++ i.ctors.toArray)
  | .ctorInfo c => (#[c.type], s!"{c.induct} {c.cidx} {c.numParams} {c.numFields} {c.isUnsafe}",
      (usedConstants c.type).push c.induct)
  | .recInfo r => (#[r.type], s!"{r.numParams} {r.numIndices} {r.numMotives} {r.numMinors} {r.k} {r.isUnsafe}",
      usedConstants r.type)
  | .quotInfo q => (#[q.type], quotText q.kind, usedConstants q.type)
  | .axiomInfo _ => leaf
  | .opaqueInfo _ => leaf

/-- Emit the `C` records (with their nodes) of the closure of `roots`. -/
def emitClosure (h : IO.FS.Handle) (env : Environment) (internal : Name → Bool)
    (roots : Array Name) : IO Nat := do
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  let mut order : Array Name := #[]
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some info := env.find? n | continue
      order := order.push n
      let (_, _, deps) := content (internal n) info
      todo := deps.toList ++ todo
  let act : EmitM Unit := do
    for n in order do
      let some info := env.find? n | continue
      let isInternal := internal n
      let (rs, extra, deps) := content isInternal info
      let mut ids : Array String := #[]
      for r in rs do ids := ids.push (toString (← node h r))
      let deps := deps.filter (env.contains ·) |>.map toString |>.qsort (· < ·)
      let deps := deps.toList.eraseDups
      h.putStrLn ("\t".intercalate (["C", toString n, if isInternal then "I" else "E", kindOf info,
        ",".intercalate (info.levelParams.map toString), extra, " ".intercalate ids.toList] ++ deps))
  let ((), st) ← act.run {}
  return st.next

def run (cfg : Config) : MetaM Unit := do
  let env ← getEnv
  let some outPath ← IO.getEnv "OBJECTIVE_MANIFEST_OUT"
    | throwError s!"{cfg.label}: OBJECTIVE_MANIFEST_OUT is not set"
  -- a module is this repository's when its source file is under the working directory
  let mut repoModules : NameSet := {}
  for m in env.header.moduleNames do
    let file := System.mkFilePath (m.components.map toString) |>.addExtension "lean"
    if ← file.pathExists then repoModules := repoModules.insert m
  let moduleOf (n : Name) : Option Name :=
    env.getModuleIdxFor? n |>.bind fun idx => env.header.moduleNames[idx.toNat]?
  let internal (n : Name) : Bool := match moduleOf n with
    | some m => repoModules.contains m
    | none => true
  let mut rows : Array (String × String) := #[]
  let mut found : Array Name := #[]
  -- SCAN-BEGIN
  for (name, info) in env.constants.toList do
    let covered := match moduleOf name with
      | some mod => cfg.covers mod
      | none => match cfg.localPrefix with
        | some p => p.isPrefixOf ((privateToUserName? name).getD name)
        | none => false
    unless covered do continue
    if generated name then continue
    if kindOf info == "rec" then continue
    let shown := shownName name
    let module := (moduleOf name).map toString |>.getD "<local>"
    let row := "\t".intercalate ["R", toString name, shown, module, kindOf info,
      ← axiomField name info, ← statementText info]
    rows := rows.push (shown, row)
    found := found.push name
  -- SCAN-END
  let mut failures := cfg.preFailures
  if cfg.refuseMathlib && env.header.moduleNames.any (fun m => (`Mathlib).isPrefixOf m) then
    failures := failures.push "instrument: a Mathlib module is in the manifest environment; its delaborators change the rendering of unchanged statements"
  if rows.size < cfg.scanFloor then
    failures := failures.push s!"instrument: only {rows.size} declarations scanned (floor {cfg.scanFloor})"
  for n in cfg.mustFind do
    unless found.contains n do failures := failures.push s!"instrument: {n} not found"
  unless failures.isEmpty do
    for f in failures do IO.eprintln s!"{cfg.label}: {f}"
    throwError s!"{cfg.label}: {failures.size} instrument failure(s)"
  let h ← IO.FS.Handle.mk outPath .write
  let nodes ← emitClosure h env internal found
  for (_, line) in rows.qsort (fun a b => a.1 < b.1) do h.putStrLn line
  h.flush
  IO.eprintln s!"{cfg.label}: {rows.size} rows, {nodes} closure nodes -> {outPath}"

def main (cfg : Config) : MetaM Unit :=
  withOptions (fun o => o |>.set `pp.fullNames true |>.set `format.width (1000000 : Nat)
    |>.set `pp.mvars false |>.set `pp.proofs true) (run cfg)

/-- The modules of `roots`' import closure, `roots` included, as recorded in the environment
header (a root absent from the environment contributes nothing). -/
def importClosure (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let idxOf : NameMap Nat := env.header.moduleNames.size.fold (init := {}) fun i _ m =>
    m.insert env.header.moduleNames[i] i
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  while true do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      if seen.contains m then continue
      let some i := idxOf.find? m | continue
      seen := seen.insert m
      if let some data := env.header.moduleData[i]? then
        todo := data.imports.toList.map (·.module) ++ todo
  return seen

end Minidregg.ObjectiveManifest
