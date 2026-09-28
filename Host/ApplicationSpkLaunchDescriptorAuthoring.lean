/-
Strict source-owned JSON author/inspect for the reusable signed-SPK launch
descriptor (legacy v2 or new API-prefix v3). The physical adapter must obtain all fields from one verified SPK
parse and compare the complete ordered command bytes; this helper only forms
and inspects the canonical Mini commitment. Duplicate JSON keys are refused
by Host.Json.parse before this module is called.
-/
import Kernel.ApplicationSpkLaunchDescriptor
import Lean.Data.Json

namespace Minidregg.Host.ApplicationSpkLaunchDescriptorAuthoring

open Lean
open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationSpkLaunchDescriptor

set_option autoImplicit false

abbrev Result := Except String

private def exactObject (path : String) (fields : List String) (json : Json) :
    Result (Std.TreeMap.Raw String Json compare) := do
  let obj ← json.getObj?.mapError (fun _ => s!"{path}: object expected")
  let actual := obj.foldl (init := []) (fun keys key _ => key :: keys)
  for key in fields do
    unless actual.contains key do throw s!"{path}: missing {key}"
  for key in actual do
    unless fields.contains key do throw s!"{path}: unexpected {key}"
  pure obj

private def field (path key : String)
    (obj : Std.TreeMap.Raw String Json compare) : Result Json :=
  match obj.get? key with
  | some value => .ok value
  | none => .error s!"{path}: missing {key}"

private def array (path : String) (limit : Nat) (json : Json) : Result (Array Json) := do
  let values ← json.getArr?.mapError (fun _ => s!"{path}: array expected")
  if values.size > limit then throw s!"{path}: exceeds bound"
  pure values

private def nibble (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 97 + 10)
  else none

private def hex (path : String) (limit : Nat) (json : Json) : Result (List UInt8) := do
  let source ← json.getStr?.mapError (fun _ => s!"{path}: hex string expected")
  let input := source.toUTF8
  unless input.size % 2 == 0 && decide (input.size / 2 ≤ limit) do
    throw s!"{path}: invalid hex length"
  let mut output := ByteArray.empty
  for i in [:input.size / 2] do
    match nibble input[2*i]!, nibble input[2*i+1]! with
    | some hi, some lo => output := output.push (UInt8.ofNat (16*hi+lo))
    | _, _ => throw s!"{path}: lowercase hexadecimal expected"
  pure output.toList

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48+n else 97+n-10)

private def encodeHex (bytes : List UInt8) : String :=
  String.ofList <| bytes.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

private def hexJson (bytes : List UInt8) : Json := .str (encodeHex bytes)
private def decimal (value : Nat) : Json := .str (toString value)

private def command (path : String) (json : Json) :
    Result ApplicationSpkLaunchDescriptor.Command := do
  let obj ← exactObject path ["argvHex", "environHex"] json
  let rawArgv ← array (path ++ ".argvHex") 64
    (← field path "argvHex" obj)
  let mut argv := []
  for i in [:rawArgv.size] do
    argv := argv ++ [← hex s!"{path}.argvHex[{i}]" 4096 rawArgv[i]!]
  let rawEnv ← array (path ++ ".environHex") 128
    (← field path "environHex" obj)
  let mut environ := []
  for i in [:rawEnv.size] do
    let envPath := s!"{path}.environHex[{i}]"
    let env ← exactObject envPath ["keyHex", "valueHex"] rawEnv[i]!
    let key ← hex (envPath ++ ".keyHex") 256 (← field envPath "keyHex" env)
    let value ← hex (envPath ++ ".valueHex") 4096 (← field envPath "valueHex" env)
    environ := environ ++ [(key, value)]
  let command : ApplicationSpkLaunchDescriptor.Command := ⟨argv, environ⟩
  unless command.valid do throw s!"{path}: invalid signed command shape"
  pure command

/-- The package bytes must already be source-authored canonical identity bytes. This
module never accepts a naked raw SHA as a package commitment. -/
def decodeSource (json : Json) : Result Descriptor := do
  let obj ← exactObject "launchDescriptor"
    ["packageCanonicalHex", "createCommands", "continueCommand"] json
  let packageBytes ← hex "launchDescriptor.packageCanonicalHex" (1024*1024)
    (← field "launchDescriptor" "packageCanonicalHex" obj)
  let some package := ApplicationSpkPackageIdentity.decodeCanonical packageBytes
    | throw "launchDescriptor: noncanonical package identity profile"
  unless package.valid do throw "launchDescriptor: invalid package identity"
  let actions ← array "launchDescriptor.createCommands" 64
    (← field "launchDescriptor" "createCommands" obj)
  let mut createCommands := []
  for i in [:actions.size] do
    createCommands := createCommands ++
      [← command s!"launchDescriptor.createCommands[{i}]" actions[i]!]
  let continueCommand ← command "launchDescriptor.continueCommand"
    (← field "launchDescriptor" "continueCommand" obj)
  let descriptor : Descriptor := ⟨package, createCommands, continueCommand⟩
  unless descriptor.valid do throw "launchDescriptor: invalid v2 descriptor"
  pure descriptor

def author (json : Json) : Result (List UInt8 × Digest) := do
  let descriptor ← decodeSource json
  pure (descriptor.canonicalBytes, descriptor.root)

private def commandJson (command : ApplicationSpkLaunchDescriptor.Command) : Json := .mkObj
  [("canonical", hexJson command.canonicalBytes),
   ("digest", decimal command.digest.value),
   ("argvHex", .arr <| command.argv.toArray.map hexJson),
   ("environHex", .arr <| command.environ.toArray.map fun (key,value) =>
      .mkObj [("keyHex", hexJson key), ("valueHex", hexJson value)])]

def inspect (bytes : List UInt8) : Result Json := do
  let some descriptor := decodeCanonical bytes
    | throw "noncanonical launch descriptor profile"
  unless descriptor.valid do throw "invalid launch descriptor"
  pure <| .mkObj
    [("type", if descriptor.legacyProfile then
        "application-spk-launch-descriptor-v2" else
        "application-spk-launch-descriptor-v3"),
     ("canonical", hexJson descriptor.canonicalBytes),
     ("root", decimal descriptor.root.value),
     ("packageCanonicalHex", hexJson descriptor.package.canonicalBytes),
     ("packageRoot", decimal descriptor.package.root.value),
     ("createCommands", .arr <| descriptor.createCommands.toArray.map commandJson),
     ("continueCommand", commandJson descriptor.continueCommand)]

end Minidregg.Host.ApplicationSpkLaunchDescriptorAuthoring
