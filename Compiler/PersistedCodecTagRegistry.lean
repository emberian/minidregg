/- Collect source-owned persisted identities for the Store epoch. -/
module

public import Lean
meta import Lean

@[expose] public section

namespace Minidregg.Compiler.PersistedCodecTags
open Lean Elab Command

initialize tagAttribute : TagAttribute ←
  registerTagAttribute `persisted_codec_tag "Source-owned persisted codec identity"

structure Entry where
  name : String
  bytes : List UInt8
  deriving Repr, DecidableEq

/-- Lexicographic order on bytes, independent of declaration names. -/
def bytesLE : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then bytesLE as bs else a.toNat < b.toNat

/-- A canonical set: deduplicated, byte-lexicographically ordered identities. -/
def canonicalSet (values : List (List UInt8)) : List (List UInt8) :=
  values.eraseDups.mergeSort bytesLE

/-- Every definition this module declares in the corpus namespace carries the tag. -/
meta def checkTagged : CommandElabM Unit := do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone &&
        name.toString.startsWith "Minidregg.Compiler.PersistedCodecTags." then
      if let .defnInfo _ := info then
        unless tagAttribute.hasTag env name do
          throwError m!"codec corpus declaration lacks @[persisted_codec_tag]: {name}"

/-- The check alone, for a corpus file that is not the manifest's (the owner leaf). -/
elab "check_persisted_codec_tags" : command => checkTagged

/-- The manifest: every tagged identity in the environment (this module's and every
imported corpus file's), ordered by name. -/
elab "make_persisted_codec_manifest" : command => do
  checkTagged
  let env ← getEnv
  let names := (env.constants.toList.filterMap (fun (n, _) => if tagAttribute.hasTag env n then some n else none)).mergeSort (fun a b => a.toString ≤ b.toString)
  if names.isEmpty then throwError "persisted codec corpus must not be empty"
  let mut terms : Array (TSyntax `term) := #[]
  for name in names do
    let id := mkIdent name
    let label := Syntax.mkStrLit name.toString
    let info ← liftCoreM <| getConstInfo name
    if info.type.isConstOf ``String then
      terms := terms.push (← `(term| (⟨$label, ($id).toUTF8.toList⟩ : Entry)))
    else if info.type.isConstOf ``Nat then
      terms := terms.push (← `(term| (⟨$label, (toString $id).toUTF8.toList⟩ : Entry)))
    else if info.type.isAppOfArity ``List 1 && info.type.appArg!.isConstOf ``UInt8 then
      terms := terms.push (← `(term| (⟨$label, $id⟩ : Entry)))
    else
      throwError m!"persisted codec identity must be String, Nat or List UInt8: {name}"
  let manifest := mkIdent `entries
  elabCommand (← `(command| def $manifest : List Entry := [ $[$terms],* ]))


end Minidregg.Compiler.PersistedCodecTags
