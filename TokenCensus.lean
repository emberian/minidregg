/-
# TokenCensus — every private constructor, minted only at home

Many evidence types in this tree (`CheckedSignature`, `Theory.Receiving.Vouchers`,
`Receiver.Accepted`, every receiver's `Prepared`/`Accepted`, …) state their
guarantee as "only X mints this", enforced by a `private mk`.  In Lean 4.30 that is
access control on NAMES, not on terms: outside the home module `⟨…⟩`, `{ … }` and a
named `mk` are refused, but `by constructor` (or any tactic or metaprogram that
builds the constructor application) elaborates a term naming the private
constructor directly (measured 2026-10-07, lane kn2-pay-family: a `Vouchers` forged
that way compiles).

This module is the guarantee that `private mk` is not.  It imports the research
umbrella (`Minidregg`: every library module, including Host, Selvage and Assurance)
-- the census imports `AxiomCensusResearch` (Minidregg and every Host module but the
other exe roots) and `ObjectiveProofs` -- and `#assert_token_census` checks, over the
ELABORATED TERM of every constant:

1. **No foreign mint.**  No constant outside a private constructor's home module
   that can carry a value (anything but a theorem or a proof) mentions that
   constructor.  A forgery by tactic, by `Expr`, or by re-exporting the bare
   constructor is such a constant.
2. **No silent omission.**  Every private constructor of a package type is a row of
   `TokenCensus.Table.table`, and every row names a constructor that exists, with
   its home module.  A new private-mk type fails the build until it is classified.
3. **Layer-1 rows are backed.**  A row marked `L1 <witness>` names either a PROOF
   FIELD of the type (the type carries the proposition it asserts) or a theorem that
   states the guarantee for every inhabitant; a theorem whose body is a bare
   projection (a field renamed) is refused, and so is a data field.
5. **No mint that does not name the constructor**, for an `L2` evidence type: no instance of
   a value-producing class (`Inhabited`, `Nonempty`, `Zero`, `One`, `OfNat`,
   `EmptyCollection`) whose conclusion is about the type (a foreign module could mint
   with `default` or `Classical.choice`); no `cast`, `unsafeCast`, `Eq.mp` or
   `Eq.mpr` INTO the type in a value-carrying constant outside its home; and no
   home-module definition (not a projection, not a generated auxiliary) that returns
   the bare type with no proposition and no census token among its arguments (no
   verification step, no evidence it derives from), unless the row's note names it
   under `mints:`.
6. **Restricted minting functions.**  A `restrict | function | modules | note` row
   names a public function that mints a token (a genesis head, an identity from an
   open) and the only modules that may call it; any other value-carrying caller
   fails the build, and a planted call is required to be detected.
4. **The detector detects (a plant per row).**  For EVERY row, a forgery (a
   definition exporting the bare private constructor) is added to a scratch copy of
   the environment and the foreign-mint check must flag it; the scratch environment
   is discarded.  A check that cannot see a planted forgery of some type fails the
   build naming the type.

The census rows' `layer` says which layer protects the type: `L1 <theorem>` (the
type's guarantee is a proposition every inhabitant carries; forging it means
proving it) or `L2` (the guarantee rests on a runtime fact no proof can express,
an oracle or IO verdict, or is not yet stated as one: it is opaque and protected
by check 1 alone).
-/
import AxiomCensusResearch
import ObjectiveProofs
import TokenCensus.Table
import Lean

namespace Minidregg.TokenCensus

open Lean Elab Command Meta

/-- One census row. -/
structure Row where
  ctor : Name
  home : Name
  kind : String
  layer : String
  note : String

/-- A restricted minting function: only the listed modules (and its home) may
name it in a value-carrying constant. -/
structure Restriction where
  function : Name
  allowed : List Name
  note : String

/-- Parse `ctor | home | kind | layer | note` rows and
`restrict | function | module, module | note` rows; `#` starts a comment line. -/
def parseCensus (text : String) : Except String (Array Row × Array Restriction) := do
  let mut rows := #[]
  let mut restrictions := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trim
    if line.isEmpty || line.startsWith "#" then continue
    match (line.splitOn "|").map String.trim with
    | ["restrict", function, allowed, note] =>
        restrictions := restrictions.push
          ⟨function.toName, (allowed.splitOn ",").map (·.trim.toName), note⟩
    | [ctor, home, kind, layer, note] =>
        -- `[anonymous]` is the home of a declaration elaborated outside any module (a plant)
        let home := if home == "[anonymous]" then Name.anonymous else home.toName
        rows := rows.push ⟨ctor.toName, home, kind, layer, note⟩
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
  | [_, rest] => ((rest.splitOn ";").headD "").splitOn "," |>.map (·.trim.toName)
  | _ => []

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

elab "#assert_token_census " table:ident : command => do
  let text ← match (← getEnv).find? table.getId with
    | some info =>
        match info.value? with
        | some (.lit (.strVal text)) => pure text
        | _ => throwError "token census: {table.getId} is not a string literal definition"
    | none => throwError "token census: unknown table {table.getId}"
  let (rows, restrictions) ← match parseCensus text with
    | .ok parsed => pure parsed
    | .error message => throwError message
  liftTermElabM do
    let env ← getEnv
    let present := privateCtors env
    let privates : NameMap (Name × Name) := present.foldl
      (fun map (name, user, home) => map.insert name (user, home)) {}
    let mut faults : Array String := #[]
    -- 2. no silent omission, no stale row
    let rowMap : NameMap Row := rows.foldl (fun map row => map.insert row.ctor row) {}
    for (_, user, home) in present do
      match rowMap.find? user with
      | none => faults := faults.push s!"unlisted private constructor: {user} | {home} | evidence | L2 | (classify)"
      | some row =>
          if row.home != home then
            faults := faults.push s!"{user}: census says home {row.home}, the environment says {home}"
    let presentUsers : NameSet := present.foldl (fun set (_, user, _) => set.insert user) {}
    for row in rows do
      unless presentUsers.contains row.ctor do
        faults := faults.push s!"stale census row: {row.ctor} (no such private constructor)"
      -- 3. layer-1 rows are backed
      match row.layer.splitOn " " with
      | ["L2"] => pure ()
      | ["L1", thm] =>
          match (← getEnv).find? thm.toName with
          | none => faults := faults.push s!"{row.ctor}: L1 witness {thm} does not exist"
          | some info =>
              -- a PROOF FIELD of the type is the witness itself (the type carries the
              -- proposition); a theorem must not be a renamed projection of one
              let structName := row.ctor.getPrefix
              if (← getEnv).getProjectionFnInfo? thm.toName |>.isSome then
                unless thm.toName.getPrefix == structName do
                  faults := faults.push s!"{row.ctor}: L1 witness {thm} is a field of {thm.toName.getPrefix}, not of {structName}"
                let proofField ← forallTelescopeReducing info.type fun _ body => isProp body
                unless proofField do
                  faults := faults.push s!"{row.ctor}: L1 witness {thm} is a data field, not a proof field"
              else
                -- a theorem: about this type, and not a projection under binders
                unless info.type.getUsedConstants.contains structName do
                  faults := faults.push s!"{row.ctor}: L1 theorem {thm} does not mention {structName}"
                -- `ConstantInfo.value?` answers `none` for a theorem whose proof is still
                -- elaborating; read the declared value directly
                let declared? : Option Expr := match info with
                  | .thmInfo proved => some proved.value
                  | .defnInfo definition => some definition.value
                  | _ => none
                if let some value := declared? then
                  let renamed ← lambdaTelescope value fun _ body => do
                    match body.consumeMData with
                    | .proj .. => pure true
                    | body =>
                        match body.getAppFn.constName? with
                        | some head => pure ((← getEnv).getProjectionFnInfo? head).isSome
                        | none => pure false
                  if renamed then
                    faults := faults.push s!"{row.ctor}: L1 theorem {thm} is a renamed projection; name the proof field instead"
      | _ => faults := faults.push s!"{row.ctor}: layer must be `L2` or `L1 <theorem>`, not `{row.layer}`"
    -- 1. no foreign mint
    let mut homeUses : NameSet := {}
    for (name, info) in env.constants.toList do
      for (ctor, home) in ← mintsOf privates name info do
        if moduleOf env name == home then homeUses := homeUses.insert ctor
      for (minter, module, ctor, home) in ← foreignMints privates name info do
        faults := faults.push s!"{ctor} (home {home}) is minted by {minter} in {module}"
    -- 5. no mint that does not name the constructor (L2 types)
    let l2Types : NameMap Row := present.foldl (fun map (name, user, _) =>
      match rowMap.find? user, env.find? name with
      | some row, some (.ctorInfo ctor) =>
          if row.layer == "L2" && row.kind == "evidence" then map.insert ctor.induct row else map
      | _, _ => map) {}
    let l2Home : Name → Option Name := fun type => (l2Types.find? type).map (·.home)
    let tokenTypes : NameMap Unit := present.foldl (fun map (name, _, _) =>
      match env.find? name with
      | some (.ctorInfo ctor) => map.insert ctor.induct ()
      | _ => map) {}
    for (name, info) in env.constants.toList do
      if name.isInternal && !(isPrivateName name) then continue
      let module := moduleOf env name
      -- minting instances
      if isInstanceCore env name then
        if let some cls := conclusionHead info.type then
          if mintingClasses.contains cls then
            for type in conclusionArgs info.type do
              if (l2Types.find? type).isSome then
                faults := faults.push s!"{name} in {module}: a {cls} instance mints the L2 token {type} without its constructor"
      -- casts into an L2 type
      if let some value := info.value? then
        let used := info.getUsedConstantsAsSet
        if castLike.any used.contains && (used.toList.any fun c => (l2Types.find? c).isSome) then
          let targets := (← castTargets value).toList.filter fun type => (l2Types.find? type).isSome
          unless targets.isEmpty do
            unless info matches .thmInfo _ do
              unless ← isProp info.type do
                for type in targets.eraseDups do
                  if l2Home type != some module then
                    faults := faults.push s!"{name} in {module} casts into the L2 token {type}"
      -- bare minters at home
      -- (a projection reads a token another value holds; an argument that is itself a census
      -- token, or a proposition, is the verification step a derivation needs)
      if let .defnInfo _ := info then
        unless isInstanceCore env name || (env.getProjectionFnInfo? name).isSome ||
            name.components.any (fun part => part.toString.startsWith "_") do
          if let some type := conclusionHead info.type then
            if let some row := l2Types.find? type then
              if row.home == module then
                let bare ← forallTelescopeReducing info.type fun binders _ => do
                  for binder in binders do
                    let binderType ← inferType binder
                    if ← isProp binderType then return false
                    if let some head := conclusionHead binderType then
                      if (tokenTypes.find? head).isSome then return false
                  return true
                let user := (privateToUserName? name).getD name
                if bare && !((justifiedMinters row.note).any fun listed => listed.isSuffixOf user) then
                  faults := faults.push s!"{name} in {module} returns the bare L2 token {type} with no proposition among its arguments (justify it under `mints:` in the row's note)"
    -- 6. restricted minting functions are called only where the census allows
    for restriction in restrictions do
      match env.find? restriction.function with
      | none => faults := faults.push s!"stale restriction: {restriction.function} does not exist"
      | some _ =>
          let home := moduleOf env restriction.function
          let allowed := home :: restriction.allowed
          let check (name : Name) (info : ConstantInfo) : MetaM Bool := do
            if name == restriction.function then return false
            unless info.getUsedConstantsAsSet.contains restriction.function do return false
            if info matches .thmInfo _ then return false
            if ← isProp info.type then return false
            return !allowed.contains (moduleOf (← getEnv) name)
          for (name, info) in env.constants.toList do
            if ← check name info then
              faults := faults.push s!"restricted {restriction.function} is called by {name} in {moduleOf env name} (allowed: {allowed})"
          -- its plant
          let detected ← withoutModifyingEnv do
            let fnInfo ← getConstInfo restriction.function
            let forge := `Minidregg.TokenCensus.plantedCall ++ restriction.function
            addDecl <| .defnDecl
              { name := forge, levelParams := fnInfo.levelParams, type := fnInfo.type
                value := mkConst restriction.function (fnInfo.levelParams.map mkLevelParam)
                hints := .opaque, safety := .safe }
            check forge (← getConstInfo forge)
          unless detected do
            faults := faults.push s!"restricted {restriction.function}: a planted call was NOT detected"
    -- 4. the detector detects: a plant per row
    let mut planted := 0
    for (name, user, _) in present do
      let info ← getConstInfo name
      if ← isProp info.type then continue
      let detected ← withoutModifyingEnv do
        let forge ← plantForge name
        let forgeInfo ← getConstInfo forge
        let flagged ← foreignMints privates forge forgeInfo
        return flagged.any fun (minter, _, ctor, _) => minter == forge && ctor == user
      if detected then planted := planted + 1
      else faults := faults.push s!"{user}: a planted forgery was NOT detected"
    unless faults.isEmpty do
      throwError m!"token census failed ({faults.size}):\n{String.intercalate "\n" faults.toList}"
    logInfo m!"token census: {present.size} private constructors, all listed, none minted \
      abroad; {planted} planted forgeries detected; {homeUses.size} constructors used at home; \
      {restrictions.size} restricted minting functions"

-- A scan of every constant: its cost is the size of the tree, not a proof search.
set_option maxHeartbeats 0 in
#assert_token_census Minidregg.TokenCensus.table

end Minidregg.TokenCensus
