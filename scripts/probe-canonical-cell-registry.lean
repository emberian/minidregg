import Compiler.CanonicalCellRegistry
import Compiler.DurableReceiverIO

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.EffectDeclaration
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalCellRegistry

namespace CanonicalCellRegistryProbe

def deployment : Deployment := ⟨⟨4242⟩, 10, 11, 12⟩

/-- A declared cell holding one field of the given key; an object field is
declared at its own object (K-FIELD-CLOSURE: a cell holds only declared fields). -/
def declaredStore (key : StateKey) : Store.Store EffectDeclaration.effectLayout :=
  StoreCodec.fromEntries (⟨key.address, (17 : Int)⟩ :: match key with
    | .objectField object field =>
        [⟨(Minidregg.Kernel.FieldClosure.declaredKey object.value field.value).address, (1 : Int)⟩]
    | _ => [])

def objectStore := declaredStore (.objectField ⟨20⟩ ⟨1⟩)
def accountStore := declaredStore (.objectField ⟨21⟩ ⟨1⟩)
def programStore := declaredStore (.programCode ⟨22⟩)

def objectCell (store : Store.Store EffectDeclaration.effectLayout) : PackedCell registry :=
  ⟨.declaredObject, materialize DeclaredEffectCell.materializer store⟩

def accountCell (store : Store.Store EffectDeclaration.effectLayout) : PackedCell registry :=
  ⟨.accountMetadata, materialize DeclaredEffectCell.materializer store⟩

def programCell : PackedCell registry :=
  ⟨.declaredProgram, materialize DeclaredEffectCell.materializer programStore⟩

def samples : List (Nat × PackedCell registry) :=
  [ (20, objectCell objectStore)
  , (21, accountCell accountStore)
  , (22, programCell)
  , (23, ⟨.content, materialize HyperdocumentCell.contentMaterializer 0⟩)
  , (24, ⟨.eventHistory, materialize HyperdocumentCell.eventMaterializer 0⟩)
  , (deployment.authorityCellId,
      ⟨.authority, materialize CredentialAuthorityCell.materializer 0⟩)
  , (deployment.resourceBookId,
      ⟨.resourceBook, materialize CanonicalResourcePageMaterializer.materializer
        (CanonicalResourcePageMaterializer.stateOfOption (some CanonicalResourceKernel.Book.empty))⟩) ]

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL canonical registry: {label}")

def checkRows : IO Unit := do
  for (identifier, cell) in samples do
    let bytes := cellCodec.encode cell
    require s!"every source kind satisfies loaded/final cell law (cell {identifier})" (cellCheck deployment identifier cell)
    match cellCodec.decode bytes with
    | none => throw (IO.userError s!"FAIL canonical registry: roundtrip {repr (show Kind from cell.kind)}")
    | some decoded =>
        require "dependent codec exact bytes and kind"
          (decide (decoded.kind = cell.kind) && cellCodec.encode decoded == bytes)
    require "trailing bytes refuse" ((cellCodec.decode (bytes ++ [0])).isNone)
    let lifecycle := ResourceBirthCodec.LifecycleImage.bytes registry (.live cell)
    match (ResourceBirthCodec.LifecycleImage.codec registry).decode lifecycle with
    | none => throw (IO.userError "FAIL canonical registry: lifecycle decode")
    | some decoded => do
        require "outer lifecycle exact canonical bytes"
          (ResourceBirthCodec.LifecycleImage.bytes registry decoded == lifecycle)
  require "reserved tag refuses" ((kindAtTag 4).isNone)
  require "retired catalogue tag refuses" ((kindAtTag 7).isNone)
  require "unknown tag refuses" ((kindAtTag 255).isNone)
  require "object initial accepted" (userInitialCheck deployment 20 (objectCell objectStore))
  require "account metadata initial accepted" (userInitialCheck deployment 21 (accountCell accountStore))
  require "program metadata initial accepted" (userInitialCheck deployment 22 programCell)
  let shadow := declaredStore (.accountBalance ⟨21⟩ ⟨21⟩)
  require "account shadow balance refuses permanent law" (!cellCheck deployment 21 (accountCell shadow))
  let objectShadow := declaredStore (.accountBalance ⟨20⟩ ⟨20⟩)
  require "object shadow balance refuses permanent law" (!cellCheck deployment 20 (objectCell objectShadow))
  let undeclared : Store.Store EffectDeclaration.effectLayout :=
    StoreCodec.fromEntries [⟨(StateKey.objectField ⟨20⟩ ⟨1⟩).address, (17 : Int)⟩]
  require "an undeclared object field refuses (K-FIELD-CLOSURE)"
    (!cellCheck deployment 20 (objectCell undeclared))
  let foreign := declaredStore (.objectField ⟨37⟩ ⟨1⟩)
  require "foreign id refuses" (!cellCheck deployment 21 (accountCell foreign))
  require "object request cannot select account metadata"
    ((selectDeclared deployment 21 .object (accountCell accountStore)).isNone)
  require "account role selects actual account metadata"
    ((selectDeclared deployment 21 .account (accountCell accountStore)).isSome)
  for (identifier, cell) in samples do
    match cell.kind with
    | .resourceBook =>
        require "Book cannot be a user initial payload" (!userInitialCheck deployment identifier cell)
        require "same valid Book at another id refuses" (!cellCheck deployment (identifier + 100) cell)
    | .authority | .eventHistory =>
        require "internal state cannot be a user initial payload" (!userInitialCheck deployment identifier cell)
    | _ => pure ()
  IO.println "PASS canonical cell registry: 7 actual store-cell materializers/pins, dependent codec+outer lifecycle, permanent role/identity law, shadow-money and wrong-role refusal, retired catalogue tag refused, source-only internal births"

def checkPhysical (binary : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let keyPath := directory / "mac.key"
    IO.FS.writeBinFile keyPath (List.replicate 32 (7 : UInt8)).toByteArray
    IO.setAccessRights keyPath ⟨⟨true, true, false⟩, ⟨false, false, false⟩, ⟨false, false, false⟩⟩
    let config : DurableReceiverIO.NativeConfig :=
      { binary, root := directory / "store", key := keyPath }
    let transport := { config.transport (fun _ => ⟨0⟩) ⟨0⟩ with systemCell := none }
    let seed : Minidregg.Kernel.DurableReceiver.Seed :=
      { absentBytes := []
        cells := samples.map fun (identifier, cell) =>
          (⟨identifier⟩, ResourceBirthCodec.LifecycleImage.bytes registry (.live cell))
        available := fun _ => 100 }
    match ← DurableReceiverIO.bootstrap transport ResourceBirthCodec.rootBytes seed with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
    match ← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes with
    | .error message => throw (IO.userError message)
    | .ok loaded =>
        require "every registry sample survives real native reopen" (loaded.cells.length == samples.length)
        for (identifier, bytes) in loaded.cells do
          match (ResourceBirthCodec.LifecycleImage.codec registry).decode bytes with
          | some (.live cell) => do
              require "reopened cell satisfies same source law"
                (cellCheck deployment identifier.value cell)
          | _ => throw (IO.userError "FAIL canonical registry: native cell lost lifecycle kind")
        require "unallocated id retains canonical fresh bytes" (loaded.snapshot.canonicalBytes ⟨9999⟩ == [])
    IO.println "PASS canonical cell registry native join: fixed lifecycle root + seven store-cell source kinds survive SQLite bootstrap/reopen; policy-source kind has its own probe; this is transport coverage, not birth authorization"

end CanonicalCellRegistryProbe

def main (arguments : List String) : IO Unit := do
  CanonicalCellRegistryProbe.checkRows
  match arguments with
  | [] => pure ()
  | [binary] => CanonicalCellRegistryProbe.checkPhysical binary
  | _ => throw (IO.userError "usage: lean --run scripts/probe-canonical-cell-registry.lean [native-store-binary]")
