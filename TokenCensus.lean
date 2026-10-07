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
and `#assert_token_census` checks, over the ELABORATED TERM of every constant:

1. **No foreign mint.**  No constant outside a private constructor's home module
   that can carry a value (anything but a theorem or a proof) mentions that
   constructor.  A forgery by tactic, by `Expr`, or by re-exporting the bare
   constructor is such a constant.
2. **No silent omission.**  Every private constructor of a package type is a row of
   `TokenCensus.Table.table`, and every row names a constructor that exists, with
   its home module.  A new private-mk type fails the build until it is classified.
3. **Layer-1 rows are backed.**  A row marked `L1 <theorem>` (the type carries the
   proposition it asserts, and the named theorem states the guarantee for every
   inhabitant) names a theorem that exists.
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
import Minidregg
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

/-- Parse `ctor | home | kind | layer | note` lines; `#` starts a comment line. -/
def parseCensus (text : String) : Except String (Array Row) := do
  let mut rows := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trim
    if line.isEmpty || line.startsWith "#" then continue
    match (line.splitOn "|").map String.trim with
    | [ctor, home, kind, layer, note] =>
        rows := rows.push ⟨ctor.toName, home.toName, kind, layer, note⟩
    | _ => throw s!"token census: malformed row: {line}"
  return rows

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
  let rows ← match parseCensus text with
    | .ok rows => pure rows
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
          unless (← getEnv).contains thm.toName do
            faults := faults.push s!"{row.ctor}: L1 theorem {thm} does not exist"
      | _ => faults := faults.push s!"{row.ctor}: layer must be `L2` or `L1 <theorem>`, not `{row.layer}`"
    -- 1. no foreign mint
    let mut homeUses : NameSet := {}
    for (name, info) in env.constants.toList do
      for (ctor, home) in ← mintsOf privates name info do
        if moduleOf env name == home then homeUses := homeUses.insert ctor
      for (minter, module, ctor, home) in ← foreignMints privates name info do
        faults := faults.push s!"{ctor} (home {home}) is minted by {minter} in {module}"
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
      abroad; {planted} planted forgeries detected; {homeUses.size} constructors used at home"

-- A scan of every constant: its cost is the size of the tree, not a proof search.
set_option maxHeartbeats 0 in
#assert_token_census Minidregg.TokenCensus.table

end Minidregg.TokenCensus
