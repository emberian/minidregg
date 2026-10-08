/- Source-owned persisted codec tags. This module imports no Mini codecs.
Every tag declaration is a registry entry; the manifest is generated from the
attribute, so an added declaration cannot be omitted from the Store epoch.
Binary version suffixes live here together with their frame, not at callers.
The late PersistedCodecTagCensus rejects inline codec-tag literals elsewhere. -/
import Lean

namespace Minidregg.Theory.PersistedCodecTags
open Lean Elab Command

initialize tagAttribute : TagAttribute ←
  registerTagAttribute `persisted_codec_tag "Source-owned persisted codec identity"

structure Entry where
  name : String
  bytes : List UInt8
  deriving Repr, DecidableEq

elab "make_persisted_codec_manifest" : command => do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone &&
        name.toString.startsWith "Minidregg.Theory.PersistedCodecTags." then
      if let .defnInfo _ := info then
        unless tagAttribute.hasTag env name do
          throwError m!"codec corpus declaration lacks @[persisted_codec_tag]: {name}"
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


end Minidregg.Theory.PersistedCodecTags
