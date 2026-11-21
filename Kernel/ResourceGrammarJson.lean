/-
# `Kernel/ResourceGrammarJson.lean` — the request grammar of the scalar, world and money payloads, once

The JSON grammar of a scalar action, a stream reference, a world descriptor, definition and
action, and a money batch: what a `scalar`, `append`, `world`, `kindDefinition` or
`moneyConsent` payload is written in (`kindDefinition` is a registered effect and reads
`worldDefinition` as its declaration's face). The Host's request decoder (`Host/Json.lean`) and the
source agreement's (`Host/SourceAgreementJson.lean`) each held a copy; both read this one. It
sits upstream of the effect registry so that a declaration's JSON face (`Effect.ofJson`) can be
one of these decoders when its code is bound. The strict helpers are `EffectJson`'s and
`ContentJson`'s.
-/
module

public import Kernel.ContentJson
public import Kernel.WorldKindMethods
public import Kernel.WorldPrototypeConstruction
public import Kernel.ResourceMoneyReceiver
public import Lean.Data.Json

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

namespace Minidregg.Kernel.ResourceGrammarJson
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

def action (path : String) (json : Lean.Json) : Result Action := do
  let (tag, _) ← tagged path json
  match tag with
  | "create" | "write" =>
      let names := if tag = "create" then ["type", "key", "value"]
        else ["type", "key", "expected", "value"]
      let obj ← exactObject path names json
      let keyObj ← exactObject (path ++ ".key") ["type", "resource", "field"]
        (← field path "key" obj)
      let keyType ← string (path ++ ".key.type") (← field (path ++ ".key") "type" keyObj)
      let resource ← nat (path ++ ".key.resource") (← field (path ++ ".key") "resource" keyObj)
      let fieldId ← nat (path ++ ".key.field") (← field (path ++ ".key") "field" keyObj)
      let key := match keyType with
        | "object" => Minidregg.Theory.EffectDeclaration.StateKey.objectField ⟨resource⟩ ⟨fieldId⟩
        | "program" => Minidregg.Theory.EffectDeclaration.StateKey.programCode ⟨resource⟩
        | _ => Minidregg.Theory.EffectDeclaration.StateKey.objectField ⟨resource⟩ ⟨fieldId⟩
      unless keyType = "object" ∨ keyType = "program" do
        throw s!"{path}.key.type: expected object or program"
      let value ← int (path ++ ".value") (← field path "value" obj)
      if tag = "create" then pure (.create key value)
      else pure (.write key (← optional (path ++ ".expected") int
        (← field path "expected" obj)) value)
  | "move" =>
      let obj ← exactObject path ["type", "source", "destination", "resource",
        "sourceExpected", "destinationExpected", "amount"] json
      pure (.move ⟨← nat (path ++ ".source") (← field path "source" obj)⟩
        ⟨← nat (path ++ ".destination") (← field path "destination" obj)⟩
        ⟨← nat (path ++ ".resource") (← field path "resource" obj)⟩
        (← optional (path ++ ".sourceExpected") int (← field path "sourceExpected" obj))
        (← optional (path ++ ".destinationExpected") int (← field path "destinationExpected" obj))
        (← int (path ++ ".amount") (← field path "amount" obj)))
  | _ => failAt (path ++ ".type") "unknown action constructor"

def streamRef (path : String) (json : Lean.Json) : Result (Nat × Nat) := do
  let obj ← exactObject path ["cell", "sequence"] json
  pure (← nat (path ++ ".cell") (← field path "cell" obj),
    ← nat (path ++ ".sequence") (← field path "sequence" obj))

def worldScalarCodec (path : String) (json : Lean.Json) :
    Result WorldKindDescriptor.ScalarCodec := do
  match ← string path json with
  | "nat" => pure .natural
  | "int" => pure .integer
  | "bytes" => pure .bytes
  | _ => failAt path "expected nat, int or bytes"

def worldDiscipline (path : String) (json : Lean.Json) :
    Result Store.Discipline := do
  match ← string path json with
  | "rom" => pure .rom
  | "ram" => pure .ram
  | "append" => pure .appendOnly
  | _ => failAt path "expected rom, ram or append"

def worldField (path : String) (json : Lean.Json) : Result WorldKindDescriptor.Field := do
  let obj ← exactObject path ["id", "name", "meaning", "codec", "discipline"] json
  pure ⟨← nat (path ++ ".id") (← field path "id" obj),
    ← string (path ++ ".name") (← field path "name" obj),
    ← string (path ++ ".meaning") (← field path "meaning" obj),
    ← worldScalarCodec (path ++ ".codec") (← field path "codec" obj),
    ← worldDiscipline (path ++ ".discipline") (← field path "discipline" obj)⟩

def worldDescriptor (path : String) (json : Lean.Json) :
    Result WorldKindDescriptor.Descriptor := do
  let obj ← exactObject path ["kind", "revision", "fields"] json
  let descriptor : WorldKindDescriptor.Descriptor :=
    ⟨← nat (path ++ ".kind") (← field path "kind" obj),
      ← nat (path ++ ".revision") (← field path "revision" obj),
      ← list (path ++ ".fields") worldField (← field path "fields" obj)⟩
  unless descriptor.Valid do
    failAt path "descriptor needs unique field ids/names and nonempty names/meanings"
  pure descriptor

def worldValue : (codec : WorldKindDescriptor.ScalarCodec) →
    String → Lean.Json → Result codec.Value
  | .natural, path, json => nat path json
  | .integer, path, json => int path json
  | .bytes, path, json => decodeHex path json

def worldMethodOutput (path : String) (json : Lean.Json) :
    Result WorldKindMethods.OutputBinding := do
  let obj ← exactObject path ["output", "field", "key"] json
  pure ⟨← nat (path ++ ".output") (← field path "output" obj),
    ← nat (path ++ ".field") (← field path "field" obj),
    ← nat (path ++ ".key") (← field path "key" obj)⟩

def worldMethod (path : String) (json : Lean.Json) : Result WorldKindMethods.Method := do
  let obj ← exactObject path ["name", "program", "outputs"] json
  pure ⟨← string (path ++ ".name") (← field path "name" obj),
    ⟨← nat (path ++ ".program") (← field path "program" obj)⟩,
    ← list (path ++ ".outputs") worldMethodOutput (← field path "outputs" obj)⟩

def worldDefinition (path : String) (json : Lean.Json) :
    Result WorldKindCell.Definition := do
  let obj ← exactObject path ["descriptor", "defaults"] json
  let descriptor ← worldDescriptor (path ++ ".descriptor") (← field path "descriptor" obj)
  let defaults ← array (path ++ ".defaults") (← field path "defaults" obj)
  let mut store : Store.Store (WorldKindDescriptor.layout descriptor) := 0
  for i in [:defaults.size] do
    let entryPath := s!"{path}.defaults[{i}]"
    let entry ← exactObject entryPath ["field", "key", "value"] defaults[i]!
    let id ← nat (entryPath ++ ".field") (← field entryPath "field" entry)
    let space ← match WorldKindInstance.findField descriptor id with
      | some space => pure space
      | none => failAt (entryPath ++ ".field") "unknown descriptor field"
    let key ← nat (entryPath ++ ".key") (← field entryPath "key" entry)
    let address : Store.Address (WorldKindDescriptor.layout descriptor) := ⟨space, key⟩
    if (store address).isSome then failAt entryPath "duplicate default field/key"
    let raw ← field entryPath "value" entry
    let definition := descriptor.fields.get space
    let value ← if definition.meaning == WorldKindMethods.tableMeaning && raw.getArr?.isOk then do
        unless definition.codec = .bytes ∧ definition.discipline = .rom ∧ key = 0 do
          failAt entryPath "method table must be ROM bytes at key zero"
        let methods ← list (entryPath ++ ".value") worldMethod raw
        unless WorldKindMethods.valid descriptor methods do
          failAt entryPath "ambiguous or invalid method output bindings"
        match WorldKindInstance.decodeValue descriptor space
            (WorldKindDescriptor.ScalarCodec.bytes.stream.encode (WorldKindMethods.encode methods)) with
        | some value => pure value
        | none => failAt entryPath "method table field is not bytes"
      else worldValue definition.codec (entryPath ++ ".value") raw
    store := store.set address (some value)
  let definition : WorldKindCell.Definition :=
    ⟨descriptor, StoreCodec.encode (WorldKindDescriptor.wire descriptor) store⟩
  if descriptor.fields.any (fun field => field.meaning == WorldKindMethods.tableMeaning) then
    let value ← match definition.instantiate with
      | some value => pure value
      | none => failAt path "invalid method-bearing definition"
    if (WorldKindMethods.tableOf value).isNone then
      failAt path "method table requires one canonical ROM bytes slot and unambiguous bindings"
  pure definition

def worldAction (descriptor : WorldKindDescriptor.Descriptor)
    (path : String) (json : Lean.Json) : Result WorldKindInstance.Action := do
  let (tag, _) ← tagged path json
  let keys ← match tag with
    | "read" => pure ["type", "field", "key", "expected"]
    | "create" => pure ["type", "field", "key", "value"]
    | "write" => pure ["type", "field", "key", "before", "after"]
    | "erase" => pure ["type", "field", "key", "before"]
    | _ => failAt (path ++ ".type") "expected read, create, write or erase"
  let obj ← exactObject path keys json
  let id ← nat (path ++ ".field") (← field path "field" obj)
  let key ← nat (path ++ ".key") (← field path "key" obj)
  let space ← match WorldKindInstance.findField descriptor id with
    | some space => pure space
    | none => failAt (path ++ ".field") "unknown descriptor field"
  let codec := (descriptor.fields.get space).codec
  let value (key : String) : Result (List UInt8) := do
    pure (codec.stream.encode (← worldValue codec (path ++ "." ++ key) (← field path key obj)))
  match tag with
  | "read" =>
      let raw ← field path "expected" obj
      let expected ← if raw.isNull then pure none else some <$> value "expected"
      pure (.read id key expected)
  | "create" => pure (.create id key (← value "value"))
  | "write" => pure (.write id key (← value "before") (← value "after"))
  | "erase" => pure (.erase id key (← value "before"))
  | _ => failAt (path ++ ".type") "unknown world action"

def moneyOperation (path : String) (json : Lean.Json) :
    Result Minidregg.Theory.CanonicalResourceKernel.Operation := do
  let (tag, _) ← tagged path json
  match tag with
  | "transfer" | "fee" =>
      let obj ← exactObject path ["type", "source", "destination", "asset", "amount"] json
      let source ← nat (path ++ ".source") (← field path "source" obj)
      let destination ← nat (path ++ ".destination") (← field path "destination" obj)
      let asset ← nat (path ++ ".asset") (← field path "asset" obj)
      let amount ← nat (path ++ ".amount") (← field path "amount" obj)
      pure (if tag = "transfer" then .transfer source destination asset amount
        else .fee source destination asset amount)
  | "mint" =>
      let obj ← exactObject path ["type", "asset", "destination", "amount"] json
      pure (.mint (← nat (path ++ ".asset") (← field path "asset" obj))
        (← nat (path ++ ".destination") (← field path "destination" obj))
        (← nat (path ++ ".amount") (← field path "amount" obj)))
  | "burn" =>
      let obj ← exactObject path ["type", "source", "asset", "amount"] json
      pure (.burn (← nat (path ++ ".source") (← field path "source" obj))
        (← nat (path ++ ".asset") (← field path "asset" obj))
        (← nat (path ++ ".amount") (← field path "amount" obj)))
  | "lease" =>
      let obj ← exactObject path
        ["type", "leaseId", "holder", "lessor", "asset", "rate", "epochs", "startsAt"] json
      pure (.lease (← nat (path ++ ".leaseId") (← field path "leaseId" obj))
        (← nat (path ++ ".holder") (← field path "holder" obj))
        (← nat (path ++ ".lessor") (← field path "lessor" obj))
        (← nat (path ++ ".asset") (← field path "asset" obj))
        (← nat (path ++ ".rate") (← field path "rate" obj))
        (← nat (path ++ ".epochs") (← field path "epochs" obj))
        (← nat (path ++ ".startsAt") (← field path "startsAt" obj)))
  | "setFloor" =>
      let obj ← exactObject path ["type", "asset", "account", "floor"] json
      pure (.setFloor (← nat (path ++ ".asset") (← field path "asset" obj))
        (← nat (path ++ ".account") (← field path "account" obj))
        (← nat (path ++ ".floor") (← field path "floor" obj)))
  | "sweep" =>
      let obj ← exactObject path
        ["type", "holder", "commons", "asset", "permille", "epochs", "amount"] json
      pure (.sweep (← nat (path ++ ".holder") (← field path "holder" obj))
        (← nat (path ++ ".commons") (← field path "commons" obj))
        (← nat (path ++ ".asset") (← field path "asset" obj))
        (← nat (path ++ ".permille") (← field path "permille" obj))
        (← nat (path ++ ".epochs") (← field path "epochs" obj))
        (← nat (path ++ ".amount") (← field path "amount" obj)))
  | _ => failAt (path ++ ".type") "expected transfer, mint, burn, fee, lease, setFloor or sweep"

def moneyFunding (path : String) (json : Lean.Json) :
    Result Minidregg.Kernel.ResourceMoneyWire.FundingConsent := do
  let obj ← exactObject path ["asset", "credits", "expectedPayerBalance", "expectedBookRoot"] json
  pure ⟨← nat (path ++ ".asset") (← field path "asset" obj),
    ← nat (path ++ ".credits") (← field path "credits" obj),
    ← int (path ++ ".expectedPayerBalance") (← field path "expectedPayerBalance" obj),
    ⟨← nat (path ++ ".expectedBookRoot") (← field path "expectedBookRoot" obj)⟩⟩

def moneyBatch (path : String) (json : Lean.Json) :
    Result Minidregg.Kernel.ResourceMoneyWire.ApplicationBatch := do
  let obj ← exactObject path ["expectedBookRoot", "operations"] json
  pure ⟨⟨← nat (path ++ ".expectedBookRoot") (← field path "expectedBookRoot" obj)⟩,
    ← list (path ++ ".operations") moneyOperation (← field path "operations" obj)⟩

end Minidregg.Kernel.ResourceGrammarJson
