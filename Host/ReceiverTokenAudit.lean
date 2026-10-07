/-
# Host.ReceiverTokenAudit -- receiver tokens are minted only at home

A signature verdict reaches a family's `prepare` as a token
(`Theory.Receiving.Vouchers`, and from it `CredentialSignatureAdmission.
ReceiverSignature` and `CheckedSignature`).  Each has a `private mk`, which stops
`⟨…⟩`, `{ … }` and a named `mk` outside its module -- but NOT the `constructor`
tactic, which elaborates a term naming the private constructor directly
(measured: `plants/PlantForgeTactic.lean` builds a `Vouchers` that way).  So the
constructor's privacy is not the guarantee.  This audit is: it reads the
ELABORATED TERM of every constant in the host's closure (`Host.Main` imports
every receiving family) and refuses if any constant outside a token's home
module mentions its constructor.  It also requires each constructor to be used
at home at least once, so the audit cannot pass by failing to find the
constructor at all.

It runs while this module elaborates: a forged token anywhere in the closure
fails `lake build Host`.
-/
import Host.Main
import Lean

namespace Minidregg.Host.ReceiverTokenAudit

open Lean Elab Command

/-- Each token constructor (by its user-facing name) and the one module allowed
to mention it. -/
def tokenMints : List (Name × Name) :=
  [(`Minidregg.Theory.Receiving.Vouchers.mk, `Theory.Receiving),
   (`Minidregg.Compiler.CredentialSignatureAdmission.ReceiverSignature.mk,
     `Compiler.CredentialSignatureAdmission),
   (`Minidregg.Compiler.CredentialSignatureAdmission.CheckedSignature.mk,
     `Compiler.CredentialSignatureAdmission)]

/-- The module a constant was declared in (the current module for a local one). -/
def moduleOf (env : Environment) (constant : Name) : Name :=
  match env.getModuleIdxFor? constant with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- The user-facing name of a (possibly private) constant. -/
def userName (constant : Name) : Name :=
  (privateToUserName? constant).getD constant

/-- For every token constructor: the constants that mention it, with their modules. -/
def mintUses (env : Environment) : Std.HashMap Name (Array (Name × Name)) := Id.run do
  let ctors := tokenMints.map Prod.fst
  let mut uses : Std.HashMap Name (Array (Name × Name)) := {}
  for (name, info) in env.constants.toList do
    for used in info.getUsedConstantsAsSet do
      let user := userName used
      if ctors.contains user && userName name != user then
        uses := uses.insert user ((uses.getD user #[]).push (name, moduleOf env name))
  return uses

/-- **The audit.**  Refuses a foreign mention of a token constructor, and a
constructor never used at home. -/
elab "#assert_tokens_minted_at_home" : command => do
  let env ← getEnv
  let uses := mintUses env
  let mut faults : Array String := #[]
  for (ctor, home) in tokenMints do
    let found := uses.getD ctor #[]
    let foreign := found.filter fun (_, mod) => mod != home
    for (name, mod) in foreign do
      faults := faults.push s!"{ctor} is minted by {name} in {mod} (home: {home})"
    if (found.filter fun (_, mod) => mod == home).isEmpty then
      faults := faults.push s!"{ctor} has no use at home in {home}: the audit sees nothing"
  unless faults.isEmpty do
    throwError m!"receiver token audit failed:\n{String.intercalate "\n" faults.toList}"
  logInfo m!"receiver token audit: {tokenMints.length} constructors, minted only at home"

#assert_tokens_minted_at_home

end Minidregg.Host.ReceiverTokenAudit
