/-
# `Kernel/ResourcePayloadJson.lean` — a target's payload read from its JSON, once

`payloadOfJson refuses` is the one reader of a target payload's JSON. A `type` a declaration
bears is read by that declaration's own face (`Effect.ofJson`), and no other type is read.

Which payloads a reader admits is its PARAMETER, not an accident of which copy it holds:
`refuses` names the types this reader does not admit, and such a type is refused by name before
anything of it is read. The Host admits every payload (`hostRefuses = []`); a source agreement
does not carry a money consent (`agreementRefuses`). Executed in
`Assurance/RegistryRefusalPoles.lean`.
-/
module

public import Kernel.ResourceGrammarJson
public import Kernel.ResourceTransaction

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.Range.Basic

@[expose] public section

namespace Minidregg.Kernel.ResourcePayloadJson
open Lean
open Minidregg
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController.EffectJson
open Minidregg.Kernel.ContentJson (failAt tagged decodeHex)
set_option autoImplicit false

abbrev Result := Except String

def array (path : String) (json : Lean.Json) : Result (Array Lean.Json) :=
  json.getArr?.mapError (fun _ => s!"{path}: array expected")
open Minidregg.Kernel.ResourceGrammarJson

/-- The Host's request decoder admits every payload. -/
def hostRefuses : List String := []

/-- A source agreement admits no money consent. -/
def agreementRefuses : List String := ["moneyConsent"]

/-- A registered effect's payload, read by its declaration's own JSON face (`Effect.ofJson`);
a `type` no declaration bears is refused naming what the registry binds. -/
def registeredOfJson (path tag : String) (json : Lean.Json) :
    Result DeclaredResourceController.Payload :=
  match DeclaredResourceController.effectNamed tag with
  | some code =>
      ((DeclaredResourceController.effectAt code.toNat).ofJson path json).map fun op =>
        DeclaredResourceController.Payload.registered code op
  | none => failAt (path ++ ".type")
      s!"expected a registered effect ({", ".intercalate DeclaredResourceController.effectNames})"

/-- **A target's payload, from its JSON.** `refuses`: the types this reader does not admit. -/
def payloadOfJson (refuses : List String) (path : String) (json : Lean.Json) :
    Result DeclaredResourceController.Payload := do
  let (tag, _) ← tagged path json
  if refuses.contains tag then
    failAt (path ++ ".type") s!"{tag} is not admitted by this reader"
  else
  registeredOfJson path tag json

end Minidregg.Kernel.ResourcePayloadJson
