/- Bounded strict ingress for the physical owner's public manifest.
Pure JSON notation constructs BendKeyRecord.PublicMaterial; it is not native
registration authority, an epoch/key relation proof, or input/noise admission.
The current source-owned physical checker inspects crypto/profile facts later.
Reuse Host.Json's decoded duplicate-field scan and existing hex codec. -/
import Compiler.BendKeyRecord
import Host.Json

namespace Minidregg.Host.BendOwnerManifestJson
open Lean
open Minidregg.Compiler.BendKeyRecord
set_option autoImplicit false

def schema : String := "dregg.fhe-bend.owner-public-material.v1"
def maxSourceBytes : Nat := 2000000
def maxKeyBytes : Nat := 1000000
def literalProfile : String :=
  "bfv-fhe011-degree4096-t1032193-public-literal-enum-depth0-v1"
def preludeProfile : String :=
  "bfv-fhe011-degree4096-t1032193-public-prelude-bool-case-depth0-v1"
def muxProfile : String :=
  "bfv-fhe011-degree4096-t1032193-public-core-enum-mux-plan-depth1-lifetime2-v1"

def preludeMuxProfile : String :=
  "bfv-fhe011-degree4096-t1032193-public-prelude-bool-mux-plan-depth1-lifetime2-v1"

def lowercaseHex (source : String) : Bool :=
  source.toUTF8.data.all fun byte =>
    decide ((48 ≤ byte.toNat ∧ byte.toNat ≤ 57) ∨
      (97 ≤ byte.toNat ∧ byte.toNat ≤ 102))
def sha256Shape (source : String) : Bool :=
  decide (source.toUTF8.size = 64) && lowercaseHex source

/-- Shape has exact byte width; no SHA equality or epoch validity is inferred. -/
theorem sha256_shape_width {source : String} (accepted : sha256Shape source = true) :
    source.toUTF8.size = 64 := by
  simp only [sha256Shape, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact accepted.1

#assert_axioms sha256_shape_width

private def stringField (value : Json) (name : String) : Except String String := do
  (← value.getObjVal? name).getStr?.mapError (fun _ => s!"{name} must be a string")

private def digestField (value : Json) (name : String) : Except String String := do
  let source ← stringField value name
  unless sha256Shape source do
    throw s!"{name} must be exactly 64 lowercase hexadecimal characters"
  pure source

private def keyField (value : Json) (name : String) : Except String (List UInt8) := do
  let source ← stringField value name
  unless 0 < source.toUTF8.size ∧ source.toUTF8.size ≤ 2 * maxKeyBytes ∧
      source.toUTF8.size % 2 = 0 do
    throw s!"{name} has empty, oversized or odd-width encoding"
  unless lowercaseHex source do
    throw s!"{name} must be canonical lowercase hexadecimal"
  Minidregg.Host.Json.decodeHex name (.str source)

private def parseValue (value : Json) : Except String PublicMaterial := do
  let object ← value.getObj?.mapError (fun _ => "public material must be an object")
  let profile ← stringField value "profile"
  let needsRelinearization ←
    if profile = literalProfile ∨ profile = preludeProfile then pure false
    else if profile = muxProfile ∨ profile = preludeMuxProfile then pure true
    else throw "unsupported physical public-material profile"
  let expected := ["schema", "profile", "parameters_sha256", "transformer_sha256",
    "public_key", "key_epoch"] ++
    (if needsRelinearization then ["relinearization_key"] else [])
  let names := object.foldl (init := []) (fun keys key _ => key :: keys)
  unless names.length == expected.length && names.all expected.contains do
    throw "public material has missing or unknown fields"
  unless (← stringField value "schema") = schema do
    throw "unsupported owner public-material schema"
  let parameters ← digestField value "parameters_sha256"
  let transformer ← digestField value "transformer_sha256"
  let epoch ← digestField value "key_epoch"
  let publicKey ← keyField value "public_key"
  let relinearizationKey ←
    if needsRelinearization then some <$> keyField value "relinearization_key"
    else pure none
  pure ⟨profile, parameters, transformer, epoch, publicKey, relinearizationKey⟩

/-- Capacity is checked before either raw parser sees text; duplicate decoded
keys are refused by Host.Json, including escaped aliases. Optional relin is
omitted for the two depth0 literal profiles and mandatory for dynamic mux. -/
def parse (source : String) : Except String PublicMaterial := do
  unless source.toUTF8.size ≤ maxSourceBytes do
    throw "owner public-material JSON exceeds public capacity"
  parseValue (← Minidregg.Host.Json.parse source)

end Minidregg.Host.BendOwnerManifestJson
