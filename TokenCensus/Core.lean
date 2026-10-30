/-
# TokenCensus.Core — the census instrument

Many evidence types in this tree (`CheckedSignature`, `Theory.Receiving.Vouchers`,
`Receiver.Accepted`, every receiver's `Prepared`/`Accepted`, …) state their
guarantee as "only X mints this", enforced by a `private mk`.  In Lean 4.30 that is
access control on NAMES, not on terms: outside the home module `⟨…⟩`, `{ … }` and a
named `mk` are refused, but `by constructor` (or any tactic or metaprogram that
builds the constructor application) elaborates a term naming the private
constructor directly (measured 2026-10-07, lane kn2-pay-family: a `Vouchers` forged
that way compiles).

`#assert_token_census` (run by `TokenCensus.lean` over the research umbrella and
`ObjectiveProofs`) checks, over the ELABORATED TERM of every constant:

1. **No foreign mint.**  No constant outside a private constructor's home module
   that can carry a value (anything but a theorem or a proof) mentions that
   constructor.  A forgery by tactic, by `Expr`, or by re-exporting the bare
   constructor is such a constant.
2. **No silent omission.**  Every private constructor of a package type is a row of
   `TokenCensus.Table.table`, and every row names a constructor that exists, with
   its home module.  A new private-mk type fails the build BY NAME until it has a
   reviewed row (or loses its `private`: privacy no guarantee rests on is not a token).
3. **Every row is reviewed.**  A row is `L1 <witness>` or `defect <cv task>`; there is
   no unreviewed layer.  An L1 witness is a theorem (a proof-field projection is a
   theorem) quantified over an inhabitant of the row's type whose conclusion is not
   `True`, reflexive equality, or a repeated premise, refers to the inhabitant or its
   indices, mentions every value index, and NAMES at least one value index at an
   explicit position (an index that occurs only as an implicit parameter of
   `x.field` is not something the statement says about it).  The theorem's proof is
   irrelevant: projecting the proof the type carries is the intended construction.
   A `restricted <function,…>` row is a provenance token with no proposition to carry
   (a Store identity: only the open mints one): each named function must have a
   `restrict` row (check 6), so its callers are pinned, and check 5 pins its other
   home minters.  A `defect` row is a type the review found does not carry its guarantee; the row
   names the cv task that fixes it, the census prints every defect each run, and the
   merge gate refuses a commit that ADDS one (defects only shrink).
5. **No mint that does not name the constructor**: no instance of a value-producing
   class (`Inhabited`, `Nonempty`, `Zero`, `One`, `OfNat`, `EmptyCollection`) whose
   conclusion is about a census type; no `cast`, `unsafeCast`, `Eq.mp` or `Eq.mpr`
   INTO one in a value-carrying constant outside its home; and no home-module
   definition (not a projection, not a generated auxiliary) that returns the bare
   type with no proposition and no census token among its arguments, unless the
   row's note names it under `mints:`.
6. **Restricted minting functions.**  A `restrict | function | modules | note` row
   names a public function that mints a token (a genesis head, an identity from an
   open) and the only modules that may call it; any other value-carrying caller
   fails the build.  A caller is a constant whose value uses the function at a
   computational position: not inside a type, a type former or a proof, and not as a
   parameter of the type a projection, a recursor or `casesOn`, or a matcher takes apart, nor as
   an inferred index (an implicit argument fixed by the type of a later explicit one, the `V` of
   `Receiver.intent (R : Receiver J V)`) (there it only names which instance of the type family
   the value already has, and whoever built that value chose it; under
   the module system every file elaborates its own `match_N`, so a match on
   `Receiver.Outcome … (receiverVerifier o)` mentions the function in its parameters
   without calling it).

`#assert_token_census_plants` is the instrument's self-test (check 4 and check 6's
plants): for every private constructor a forgery is planted in a scratch environment
and check 1 must flag it, and for every restriction a planted call must be flagged.
It tests the detector, not the tree, so `TokenCensus/SelfTest.lean` runs it and the
merge gate builds that module only when the instrument changes.
-/
import Lean

namespace Minidregg.TokenCensus

open Lean Elab Command Meta

/-- One census row: a private constructor, its home module, its layer (`L1 <theorem>`, or
`defect <cv task>` for a reviewed type found not to carry its guarantee) and the reason. -/
structure Row where
  ctor : Name
  home : Name
  layer : String
  note : String

/-- A restricted minting function: only the listed modules (and its home) may
name it in a value-carrying constant. -/
structure Restriction where
  function : Name
  allowed : List Name
  note : String

/-- Parse `ctor | home | layer | reason` rows and
`restrict | function | module, module | note` rows; `#` starts a comment line. -/
def parseCensus (text : String) : Except String (Array Row × Array Restriction) := do
  let mut rows := #[]
  let mut restrictions := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match (line.splitOn "|").map (·.trimAscii.toString) with
    | ["restrict", function, allowed, note] =>
        restrictions := restrictions.push
          ⟨function.toName, (allowed.splitOn ",").map (·.trimAscii.toString.toName), note⟩
    | [ctor, home, layer, note] =>
        -- `[anonymous]` is the home of a declaration elaborated outside any module (a plant)
        let home := if home == "[anonymous]" then Name.anonymous else home.toName
        rows := rows.push ⟨ctor.toName, home, layer, note⟩
    | _ => throw s!"token census: malformed row: {line}"
  return (rows, restrictions)

/-- The module a constant was declared in (the current module for a local one). -/
def moduleOf (env : Environment) (constant : Name) : Name :=
  match env.getModuleIdxFor? constant with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Every private constructor of a package type: its private name, its
user-facing name and its home module. -/
def privateCtors (env : Environment) : Array (Name × Name × Name) := Id.run do
  let mut found := #[]
  for (name, info) in env.constants.toList do
    if let .ctorInfo _ := info then
      if isPrivateName name then
        let user := (privateToUserName? name).getD name
        if (`Minidregg).isPrefixOf user then
          found := found.push (name, user, moduleOf env name)
  return found

/-- The private constructors a constant mentions, if the constant can carry a
value (a theorem, or a definition whose type is a proposition, mints nothing),
paired with the minter's module. -/
def mintsOf (privates : NameMap (Name × Name)) (name : Name) (info : ConstantInfo) :
    MetaM (Array (Name × Name)) := do
  let used := info.getUsedConstantsAsSet.toList.filterMap fun constant =>
    if constant == name then none else privates.find? constant
  if used.isEmpty then return #[]
  if info matches .thmInfo _ then return #[]
  if ← isProp info.type then return #[]
  return used.toArray

/-- Foreign mints: (minter, its module, constructor, home). -/
def foreignMints (privates : NameMap (Name × Name)) (name : Name) (info : ConstantInfo) :
    MetaM (Array (Name × Name × Name × Name)) := do
  let env ← getEnv
  let module := moduleOf env name
  let mints ← mintsOf privates name info
  return (mints.filter fun (_, home) => home != module).map fun (ctor, home) =>
    (name, module, ctor, home)


/-- Value-producing classes: an instance of one about a token mints it without
naming its constructor. -/
def mintingClasses : List Name :=
  [``Inhabited, ``Nonempty, ``Zero, ``One, ``OfNat, ``EmptyCollection]

/-- The head constant of a type's conclusion (binders stripped syntactically). -/
def conclusionHead (type : Expr) : Option Name :=
  type.getForallBody.getAppFn.constName?

/-- The `L2` census types mentioned as arguments of a type's conclusion. -/
def conclusionArgs (type : Expr) : List Name :=
  type.getForallBody.getAppArgs.toList.filterMap fun arg => arg.getAppFn.constName?

/-- The `cast`-like constants: each produces a value of a type it is told. -/
def castLike : List Name := [``cast, ``unsafeCast, ``Eq.mp, ``Eq.mpr]

/-- `cast`-like applications in an expression and the head of the type each
produces (visited once per shared subterm). -/
def castTargets (expr : Expr) : MetaM (Array Name) := do
  let found ← IO.mkRef (#[] : Array Name)
  expr.forEach fun sub => do
    let target? := match sub.getAppFn.constName?, sub.getAppArgs with
      | some ``cast, args => args[1]?
      | some ``unsafeCast, args => args[1]?
      | some ``Eq.mp, args => args[1]?
      | some ``Eq.mpr, args => args[0]?
      | _, _ => none
    if let some target := target? then
      if let some head := target.getAppFn.constName? then found.modify (·.push head)
  found.get

/-- The names a row's note justifies as bare minters (`mints: a, b`). -/
def justifiedMinters (note : String) : List Name :=
  match note.splitOn "mints:" with
  | [_, rest] => ((rest.splitOn ";").headD "").splitOn "," |>.map (·.trimAscii.toString.toName)
  | _ => []

/-- `true` when a proposition is, up to REDUCIBLE unfolding, just `True`, `x = x`, or
one of the proposition binders repeated as the conclusion.  These statements carry
no evidence about the bound token.

The test is reducible-only on purpose (the reduction-bomb class): an L1 witness is
often `x.field = f …` with `f` a deployed hash or codec (cSHAKE, Poseidon2, SHA-256,
a world root).  `whnf`/`isDefEq` at default transparency unfold such an `f` to compare
the sides -- one permutation under `whnf` is tens of GB and an hour -- and with 341 L1
rows the census elaborated for 39 h (build 3, 2026-10-14).  The vacuous statements this
rejects are syntactic; nothing deployed needs to unfold to see them. -/
def trivialConclusion (binders : Array Expr) (conclusion : Expr) : MetaM Bool :=
  withReducible do
    let conclusion ← whnfR conclusion
    if conclusion.isConstOf ``True then return true
    if conclusion.isAppOfArity ``Eq 3 then
      let args := conclusion.getAppArgs
      if ← isDefEq args[1]! args[2]! then return true
    for binder in binders do
      let type ← inferType binder
      if ← isProp type then
        if ← isDefEq type conclusion then return true
    return false

/-- A value index is a free-variable argument of the bound token type other than
a type, proposition, or instance argument.  Each such index must occur in the
witness conclusion.  The boolean records whether the conclusion mentions at
least one such index.  This deliberately checks the statement, never its proof. -/
def valueIndexCoverage (tokenType conclusion : Expr) : MetaM (Array Name × Bool) := do
  let mut missing := #[]
  let mut mentioned := false
  for arg in tokenType.getAppArgs do
    unless arg.isFVar do continue
    let decl ← getFVarLocalDecl arg
    if decl.binderInfo.isInstImplicit then continue
    let argType ← whnf decl.type
    if argType.isSort || (← isProp argType) then continue
    if conclusion.containsFVar arg.fvarId! then
      mentioned := true
    else
      missing := missing.push decl.userName
  return (missing, mentioned)

/-- The binder infos of a function's first `n` parameters, read off its type's `∀`-spine;
an unknown head, or a spine shorter than `n`, reads as explicit. -/
def binderInfosOf (fn : Expr) (n : Nat) : MetaM (Array BinderInfo) := do
  let type? ← match fn with
    | .const name _ => pure (((← getEnv).find? name).map (·.type))
    | .fvar id => pure (((← getLCtx).find? id).map (·.type))
    | _ => pure none
  let mut infos := #[]
  let mut type := type?.getD (.sort .zero)
  for _ in [0:n] do
    match type with
    | .forallE _ _ body info => infos := infos.push info; type := body
    | _ => infos := infos.push .default
  return infos

/-- The free variables an expression mentions at EXPLICIT positions: implicit, strict-implicit
and instance arguments of an application are skipped.  `x.field` elaborates to
`@T.field p₁ … pₙ x`, which mentions every parameter of `T` as an implicit argument, so
a conclusion about `x.field` alone names the indices of `x` without saying anything about
them; this sees only `x`. -/
partial def explicitFVars (e : Expr) : MetaM (Array FVarId) := do
  let ((), (_, found)) ← (visit e).run ({}, #[])
  return found
where
  /-- Each distinct subterm is visited once (`Expr` is a DAG; a tree walk of a shared
  term is exponential in its depth). -/
  visit (e : Expr) : StateT (Std.HashSet Expr × Array FVarId) MetaM Unit := do
    if (← get).1.contains e then return
    modify fun (seen, found) => (seen.insert e, found)
    match e with
    | .fvar id => modify fun (seen, found) => (seen, found.push id)
    | .mdata _ body => visit body
    | .proj _ _ struct => visit struct
    | .lam _ type body _ | .forallE _ type body _ => do visit type; visit body
    | .letE _ type value body _ => do visit type; visit value; visit body
    | .app .. =>
        let fn := e.getAppFn
        let args := e.getAppArgs
        let infos ← binderInfosOf fn args.size
        match fn with
        | .fvar id => modify fun (seen, found) => (seen, found.push id)
        | .const .. => pure ()
        | other => visit other
        for i in [0:args.size] do
          if infos[i]!.isExplicit then visit args[i]!
    | _ => pure ()

/-- The value indices of a token type (free-variable arguments other than types,
propositions and instances). -/
def valueIndices (tokenType : Expr) : MetaM (Array Expr) := do
  let mut indices := #[]
  for arg in tokenType.getAppArgs do
    unless arg.isFVar do continue
    let decl ← getFVarLocalDecl arg
    if decl.binderInfo.isInstImplicit then continue
    let argType ← whnf decl.type
    if argType.isSort || (← isProp argType) then continue
    indices := indices.push arg
  return indices

/-- Statement faults for an L1 witness.  The row type must occur as the direct
type of an inhabitant binder; mentioning it elsewhere is not enough. -/
def l1WitnessStatementFaults (structName witness : Name) (info : ConstantInfo) :
    MetaM (Array String) := do
  unless info matches .thmInfo _ do
    return #[s!"L1 witness {witness} is not a theorem or proof field"]
  let mut prefixFaults := #[]
  if (← getEnv).getProjectionFnInfo? witness |>.isSome then
    unless witness.getPrefix == structName do
      prefixFaults := prefixFaults.push s!"L1 witness {witness} is a field of {witness.getPrefix}, not of {structName}"
  forallTelescopeReducing info.type fun binders conclusion => do
    let mut faults := prefixFaults
    let mut inhabitant? : Option (Expr × Expr) := none
    for binder in binders do
      let binderType ← whnf (← inferType binder)
      if binderType.getAppFn.constName? == some structName then
        inhabitant? := some (binder, binderType)
        break
    let some (inhabitant, inhabitantType) := inhabitant?
      | return faults.push s!"L1 witness {witness} is not quantified over an inhabitant of {structName}"
    unless ← isProp conclusion do
      faults := faults.push s!"L1 witness {witness} has a data conclusion"
    if ← trivialConclusion binders conclusion then
      faults := faults.push s!"L1 witness {witness} has a trivial conclusion"
    let (missing, mentionsIndex) ← valueIndexCoverage inhabitantType conclusion
    unless missing.isEmpty do
      faults := faults.push s!"L1 witness {witness} ignores the bound token indices: {missing.toList}"
    unless conclusion.containsFVar inhabitant.fvarId! || mentionsIndex do
      faults := faults.push s!"L1 witness {witness} has a conclusion closed over the bound inhabitant and its indices"
    -- the rule's third clause: the conclusion NAMES an index, not merely the implicit
    -- parameters every projection of the inhabitant carries
    let indices ← valueIndices inhabitantType
    unless indices.isEmpty do
      let explicit ← explicitFVars conclusion
      unless indices.any (fun index => explicit.contains index.fvarId!) do
        let names ← indices.mapM fun index => return (← getFVarLocalDecl index).userName
        faults := faults.push s!"L1 witness {witness} says nothing about the token's indices {names.toList}: they occur only as implicit parameters of the inhabitant's projections"
    return faults

/-- The heartbeat budget (in `maxHeartbeats` units) for inspecting ONE witness statement. -/
def witnessHeartbeats : Nat := 400000

/-- Statement faults for an L1 witness, inspected under its own heartbeat budget: a
statement the census cannot inspect within `witnessHeartbeats` is a FAULT naming the
witness, never a hang (the reduction-bomb class; see `trivialConclusion`). -/
def l1WitnessFaults (structName witness : Name) (info : ConstantInfo) : MetaM (Array String) :=
  tryCatchRuntimeEx
    (withCurrHeartbeats <|
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := witnessHeartbeats * 1000 }) <|
        l1WitnessStatementFaults structName witness info)
    fun ex =>
      if ex.isMaxHeartbeat then
        return #[s!"L1 witness {witness}: inspecting its statement exceeded {witnessHeartbeats} heartbeats (a statement the census cannot read without unfolding deployed code is a fault)"]
      else throw ex

/-- One constant's inspection in the census scans runs under the ambient `maxHeartbeats`
from a fresh count: the scan over every constant is unbounded in total (its cost is
the size of the tree) but no single constant can hang it. -/
@[inline] def perConstant (x : MetaM α) : MetaM α := withCurrHeartbeats x

/-- The plant: a definition exporting the bare private constructor, added to the
current (scratch) environment. -/
def plantForge (ctor : Name) : MetaM Name := do
  let info ← getConstInfo ctor
  let forge := `Minidregg.TokenCensus.plantedForge ++ ((privateToUserName? ctor).getD ctor)
  addDecl <| .defnDecl
    { name := forge, levelParams := info.levelParams, type := info.type
      value := mkConst ctor (info.levelParams.map mkLevelParam)
      hints := .opaque, safety := .safe }
  return forge

/-- The census table a command names, parsed. -/
def loadCensus (table : Name) : CommandElabM (Array Row × Array Restriction) := do
  let text ← match (← getEnv).find? table with
    | some info =>
        match info.value? with
        | some (.lit (.strVal text)) => pure text
        | _ => throwError "token census: {table} is not a string literal definition"
    | none => throwError "token census: unknown table {table}"
  match parseCensus text with
  | .ok parsed => pure parsed
  | .error message => throwError message

/-- How many leading arguments of `head` are parameters of the type it takes apart: a structure
projection's, a recursor's or `casesOn`'s inductive parameters, a matcher's parameters. -/
def eliminatorParams (head : Name) : MetaM Nat := do
  let env ← getEnv
  if let some info := env.getProjectionFnInfo? head then return info.numParams
  if let some info ← getMatcherInfo? head then return info.numParams
  match env.find? head with
  | some (.recInfo info) => return info.numParams
  | _ =>
      if isCasesOnRecursor env head then
        if let some (.inductInfo info) := env.find? head.getPrefix then return info.numParams
      return 0

/-- The argument positions of `head` (among its first `count`) that are inferred indices: an
implicit or instance binder that occurs in the type of a later EXPLICIT binder and not in `head`'s
result, and `head` is not a constructor.  Such an argument is fixed by the type of the value passed
there (a `Receiver J V`'s `V` in `Receiver.intent`), so it names which member of the family that value
already is; whoever built the value chose it, and the building site is checked on its own (a
constructor's or a smart constructor's index is never skipped: `TokenCensus/SelfTest.lean` plants
both a builder, which must be flagged, and a pure consumer, which must not). -/
def inferredIndices (head : Name) (count : Nat) : MetaM (Array Nat) := do
  let some info := (← getEnv).find? head | return #[]
  -- A constructor BUILDS the value: its parameters are what the builder chooses.
  if info matches .ctorInfo _ then return #[]
  forallTelescope info.type fun xs result => do
    let mut out := #[]
    for i in [0:min count xs.size] do
      let decl ← xs[i]!.fvarId!.getDecl
      if decl.binderInfo.isExplicit then continue
      -- a function that returns a value of the family (a smart constructor) chooses its index too:
      -- only a CONSUMER, whose result does not mention the index, merely reads it off its argument
      if result.containsFVar xs[i]!.fvarId! then continue
      for j in [i+1:xs.size] do
        let later ← xs[j]!.fvarId!.getDecl
        if later.binderInfo.isExplicit && later.type.containsFVar xs[i]!.fvarId! then
          out := out.push i
          break
    return out

/-- Does `function` occur in `e` at a computational position: not inside a type, a type former
or a proof, and not as a parameter of the type an eliminator takes apart (`eliminatorParams`)? -/
partial def usesInTerm (function : Name) (e : Expr) : MetaM Bool := do
  unless (e.find? (·.isConstOf function)).isSome do return false
  if ← isProof e then return false
  if ← isTypeFormer e then return false
  match e with
  | .const name _ => return name == function
  | .app .. => e.withApp fun fn args => do
      if ← usesInTerm function fn then return true
      let skip ← match fn with
        | .const head _ => eliminatorParams head
        | _ => pure 0
      let indices ← match fn with
        | .const head _ => inferredIndices head args.size
        | _ => pure #[]
      let mut i := skip
      while i < args.size do
        unless indices.contains i do
          if ← usesInTerm function args[i]! then return true
        i := i + 1
      return false
  | .lam .. => lambdaTelescope e fun _ body => usesInTerm function body
  | .letE name type value body _ => do
      if ← usesInTerm function value then return true
      withLetDecl name type value fun x => usesInTerm function (body.instantiate1 x)
  | .mdata _ body => usesInTerm function body
  | .proj _ _ body => usesInTerm function body
  | _ => return false

/-- Is `name` a value-carrying caller of `function` outside `allowed`? -/
def restrictedCall (function : Name) (allowed : List Name) (name : Name) (info : ConstantInfo) :
    MetaM Bool := do
  if name == function then return false
  unless info.getUsedConstantsAsSet.contains function do return false
  if info matches .thmInfo _ then return false
  if ← isProp info.type then return false
  if allowed.contains (moduleOf (← getEnv) name) then return false
  let some value := info.value? | return false
  usesInTerm function value

/-- Checks 1, 2, 3, 5 and 6 over the current environment.  With `scope := some root` the
constants checked are those of the modules under `root` only (checks 1, 5, 6, and check 2 for the
private constructors those modules define), against the same table; the row checks (stale rows,
reasons, witnesses) belong to the whole-tree census and are not repeated.  The scoped form
censuses a library no whole-tree census imports (`Fixtures`, `TokenCensus/Fixtures.lean`). -/
def runTokenCensus (table : Name) (scope : Option Name) : CommandElabM Unit := do
  let (rows, restrictions) ← loadCensus table
  let inScope : Name → Bool := fun module => match scope with
    | none => true
    | some root => root.isPrefixOf module
  liftTermElabM do
    let env ← getEnv
    let present := privateCtors env
    let privates : NameMap (Name × Name) := present.foldl
      (fun map (name, user, home) => map.insert name (user, home)) {}
    let mut faults : Array String := #[]
    let mut defects : Array String := #[]
    -- 2. no silent omission, no stale row
    let rowMap : NameMap Row := rows.foldl (fun map row => map.insert row.ctor row) {}
    let ctorByUser : NameMap Name := present.foldl (fun map (name, user, _) => map.insert user name) {}
    for (_, user, home) in present.filter (fun (_, _, home) => inScope home) do
      match rowMap.find? user with
      | none => faults := faults.push s!"unlisted private constructor: {user} | {home} | L1 <theorem> | <what it states about which indices> -- or drop `private` if no guarantee rests on who builds it"
      | some row =>
          if row.home != home then
            faults := faults.push s!"{user}: census says home {row.home}, the environment says {home}"
    let presentUsers : NameSet := present.foldl (fun set (_, user, _) => set.insert user) {}
    for row in (if scope.isNone then rows else #[]) do
      unless presentUsers.contains row.ctor do
        faults := faults.push s!"stale census row: {row.ctor} (no such private constructor)"
      if row.note.trimAscii.toString.isEmpty then
        faults := faults.push s!"{row.ctor}: the row gives no reason"
      -- 3. every row is backed: an L1 witness, or a reviewed defect with its task
      match row.layer.splitOn " " with
      | ["L1", thm] =>
          -- The row names its constructor and witness by their USER names. The row's type is the
          -- inductive of the constructor itself: a `private structure`'s type and fields carry
          -- private names (`_private.<home>.0.…`), so the witness is looked up under its user name
          -- and then as a private name of the home module, and the inhabitant is matched against
          -- the real inductive, never against a name spelled from the row.
          let env ← getEnv
          let structName := match ctorByUser.find? row.ctor with
            | some ctor => match env.find? ctor with
                | some (.ctorInfo info) => info.induct
                | _ => row.ctor.getPrefix
            | none => row.ctor.getPrefix
          let witness? := match env.find? thm.toName with
            | some info => some (thm.toName, info)
            | none =>
                let hidden := mkPrivateNameCore row.home thm.toName
                (env.find? hidden).map (hidden, ·)
          match witness? with
          | none => faults := faults.push s!"{row.ctor}: L1 witness {thm} does not exist"
          | some (witness, info) =>
              for fault in ← l1WitnessFaults structName witness info do
                faults := faults.push s!"{row.ctor}: {fault}"
      | ["defect", task] => defects := defects.push s!"{row.ctor} (cv {task})"
      | ["restricted", functions] =>
          for function in functions.splitOn "," do
            unless restrictions.any (·.function == function.trimAscii.toString.toName) do
              faults := faults.push s!"{row.ctor}: restricted by {function}, which has no `restrict` row"
      | _ => faults := faults.push s!"{row.ctor}: layer must be `L1 <theorem>`, `restricted <function,…>` or `defect <cv task>`, not `{row.layer}` (there is no unreviewed layer)"
    -- 1. no foreign mint
    let mut homeUses : NameSet := {}
    for (name, info) in env.constants.toList do
      unless inScope (moduleOf env name) do continue
      for (ctor, home) in ← perConstant (mintsOf privates name info) do
        if moduleOf env name == home then homeUses := homeUses.insert ctor
      for (minter, module, ctor, home) in ← perConstant (foreignMints privates name info) do
        faults := faults.push s!"{ctor} (home {home}) is minted by {minter} in {module}"
    -- 5. no mint that does not name the constructor (every census type is evidence)
    let evidenceTypes : NameMap Row := present.foldl (fun map (name, user, _) =>
      match rowMap.find? user, env.find? name with
      | some row, some (.ctorInfo ctor) => map.insert ctor.induct row
      | _, _ => map) {}
    let evidenceHome : Name → Option Name := fun type => (evidenceTypes.find? type).map (·.home)
    let tokenTypes : NameMap Unit := present.foldl (fun map (name, _, _) =>
      match env.find? name with
      | some (.ctorInfo ctor) => map.insert ctor.induct ()
      | _ => map) {}
    for (name, info) in env.constants.toList do
      if name.isInternal && !(isPrivateName name) then continue
      let module := moduleOf env name
      unless inScope module do continue
      -- minting instances
      if isInstanceCore env name then
        if let some cls := conclusionHead info.type then
          if mintingClasses.contains cls then
            for type in conclusionArgs info.type do
              if (evidenceTypes.find? type).isSome then
                faults := faults.push s!"{name} in {module}: a {cls} instance mints the evidence token {type} without its constructor"
      -- casts into an evidence type
      if let some value := info.value? then
        let used := info.getUsedConstantsAsSet
        if castLike.any used.contains && (used.toList.any fun c => (evidenceTypes.find? c).isSome) then
          let targets := (← perConstant (castTargets value)).toList.filter fun type => (evidenceTypes.find? type).isSome
          unless targets.isEmpty do
            unless info matches .thmInfo _ do
              unless ← perConstant (isProp info.type) do
                for type in targets.eraseDups do
                  if evidenceHome type != some module then
                    faults := faults.push s!"{name} in {module} casts into the evidence token {type}"
      -- bare minters at home
      -- (a projection reads a token another value holds; an argument that is itself a census
      -- token, or a proposition, is the verification step a derivation needs)
      if let .defnInfo _ := info then
        unless isInstanceCore env name || (env.getProjectionFnInfo? name).isSome ||
            name.components.any (fun part => part.toString.startsWith "_") do
          if let some type := conclusionHead info.type then
            if let some row := evidenceTypes.find? type then
              if row.home == module then
                let bare ← perConstant <| forallTelescopeReducing info.type fun binders _ => do
                  for binder in binders do
                    let binderType ← inferType binder
                    if ← isProp binderType then return false
                    if let some head := conclusionHead binderType then
                      if (tokenTypes.find? head).isSome then return false
                  return true
                let user := (privateToUserName? name).getD name
                if bare && !((justifiedMinters row.note).any fun listed => listed.isSuffixOf user) then
                  faults := faults.push s!"{name} in {module} returns the bare evidence token {type} with no proposition among its arguments (justify it under `mints:` in the row's note)"
    -- 6. restricted minting functions are called only where the census allows
    for restriction in restrictions do
      match env.find? restriction.function with
      | none => faults := faults.push s!"stale restriction: {restriction.function} does not exist"
      | some _ =>
          let allowed := moduleOf env restriction.function :: restriction.allowed
          for (name, info) in env.constants.toList do
            unless inScope (moduleOf env name) do continue
            if ← perConstant (restrictedCall restriction.function allowed name info) then
              faults := faults.push s!"restricted {restriction.function} is called by {name} in {moduleOf env name} (allowed: {allowed})"
    unless faults.isEmpty do
      throwError m!"token census failed ({faults.size}):\n{String.intercalate "\n" faults.toList}"
    let l1 := rows.size - defects.size
    let scopeNote := match scope with | none => "" | some root => s!" (scope {root}: its modules only)"
    logInfo m!"token census{scopeNote}: {present.size} private constructors, all listed, none minted \
      abroad; {l1} L1 rows backed by their witness; {defects.size} reviewed defects: \
      {String.intercalate ", " defects.toList}; {homeUses.size} constructors used at home; \
      {restrictions.size} restricted minting functions"

elab "#assert_token_census " table:ident : command => runTokenCensus table.getId none

/-- The census over the modules under `root` only (see `runTokenCensus`). -/
elab "#assert_token_census_within " table:ident root:ident : command =>
  runTokenCensus table.getId (some root.getId)

/-- Check 4 and check 6's plants: the instrument's self-test.  For EVERY private
constructor a forgery is added to a scratch copy of the environment and the foreign-mint
check must flag it; for every restriction a planted call must be flagged.  It tests the
detector, not the tree, so it runs when the instrument changes (TokenCensus/SelfTest.lean). -/
elab "#assert_token_census_plants " table:ident : command => do
  let (_, restrictions) ← loadCensus table.getId
  liftTermElabM do
    let env ← getEnv
    let present := privateCtors env
    let privates : NameMap (Name × Name) := present.foldl
      (fun map (name, user, home) => map.insert name (user, home)) {}
    let mut faults : Array String := #[]
    for restriction in restrictions do
      if let some _ := env.find? restriction.function then
        let allowed := moduleOf env restriction.function :: restriction.allowed
        let detected ← perConstant <| withoutModifyingEnv do
          let fnInfo ← getConstInfo restriction.function
          let forge := `Minidregg.TokenCensus.plantedCall ++ restriction.function
          addDecl <| .defnDecl
            { name := forge, levelParams := fnInfo.levelParams, type := fnInfo.type
              value := mkConst restriction.function (fnInfo.levelParams.map mkLevelParam)
              hints := .opaque, safety := .safe }
          restrictedCall restriction.function allowed forge (← getConstInfo forge)
        unless detected do
          faults := faults.push s!"restricted {restriction.function}: a planted call was NOT detected"
        -- teeth the other way: a value naming the function only inside a binder's type calls nothing
        let flagged ← perConstant <| withoutModifyingEnv do
          let fnInfo ← getConstInfo restriction.function
          let fnConst := mkConst restriction.function (fnInfo.levelParams.map mkLevelParam)
          let unit := mkConst ``Unit
          let mention := mkApp (mkLambda `f .default fnInfo.type unit) fnConst
          let forge := `Minidregg.TokenCensus.plantedTypeMention ++ restriction.function
          addDecl <| .defnDecl
            { name := forge, levelParams := fnInfo.levelParams, type := mkForall `x .default mention unit
              value := mkLambda `x .default mention (mkConst ``Unit.unit)
              hints := .opaque, safety := .safe }
          restrictedCall restriction.function allowed forge (← getConstInfo forge)
        if flagged then
          faults := faults.push s!"restricted {restriction.function}: a planted type-only mention WAS flagged"
    let mut planted := 0
    for (name, user, _) in present do
      let info ← getConstInfo name
      if ← isProp info.type then continue
      let detected ← perConstant <| withoutModifyingEnv do
        let forge ← plantForge name
        let forgeInfo ← getConstInfo forge
        let flagged ← foreignMints privates forge forgeInfo
        return flagged.any fun (minter, _, ctor, _) => minter == forge && ctor == user
      if detected then planted := planted + 1
      else faults := faults.push s!"{user}: a planted forgery was NOT detected"
    unless faults.isEmpty do
      throwError m!"token census self-test failed ({faults.size}):\n{String.intercalate "\n" faults.toList}"
    logInfo m!"token census self-test: {planted} planted forgeries detected; \
      {restrictions.size} planted restricted calls detected"

end Minidregg.TokenCensus
