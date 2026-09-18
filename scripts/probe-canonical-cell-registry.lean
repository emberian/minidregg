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

def declaredPage (cellId : Nat) (key : StateKey) : DeclaredEffectPageMaterializer.Page :=
  ⟨deployment.domain, cellId % DeclaredEffectPageMaterializer.shardCount,
    some ⟨key, 17⟩, none, none, none⟩

def objectPage := declaredPage 20 (.objectField ⟨20⟩ ⟨1⟩)
def accountPage := declaredPage 21 (.objectField ⟨21⟩ ⟨1⟩)
def programPage := declaredPage 22 (.programCode ⟨22⟩)

def objectCell (page : DeclaredEffectPageMaterializer.Page) : PackedCell registry :=
  ⟨.declaredObject, materialize DeclaredEffectPageMaterializer.materializer
    (DeclaredEffectPageMaterializer.stateOfOption (some page))⟩

def accountCell (page : DeclaredEffectPageMaterializer.Page) : PackedCell registry :=
  ⟨.accountMetadata, materialize DeclaredEffectPageMaterializer.materializer
    (DeclaredEffectPageMaterializer.stateOfOption (some page))⟩

def programCell : PackedCell registry :=
  ⟨.declaredProgram, materialize DeclaredEffectPageMaterializer.materializer
    (DeclaredEffectPageMaterializer.stateOfOption (some programPage))⟩

def contentPage : HyperdocumentContentPageMaterializer.Page :=
  ⟨deployment.domain, ⟨⟨23⟩⟩, 0, none, none, none, none⟩

def eventPage : HyperdocumentEventPageMaterializer.Page :=
  ⟨deployment.domain, contentPage.document, 0, none, none, none, none⟩

def samples : List (Nat × PackedCell registry) :=
  [ (20, objectCell objectPage)
  , (21, accountCell accountPage)
  , (22, programCell)
  , (23, ⟨.content, materialize HyperdocumentContentPageMaterializer.materializer
      (HyperdocumentContentPageMaterializer.stateOfOption (some contentPage))⟩)
  , (24, ⟨.eventHistory, materialize HyperdocumentEventPageMaterializer.materializer
      (HyperdocumentEventPageMaterializer.stateOfOption (some eventPage))⟩)
  , (25, ⟨.authorityShard, materialize CredentialAuthorityPageMaterializer.materializer
      (CredentialAuthorityPageMaterializer.stateOfOption
        (some (CredentialAuthorityDomain.emptyPage deployment.domain 0)))⟩)
  , (deployment.authorityCatalogueId,
      ⟨.authorityCatalogue, materialize CredentialAuthorityDomain.catalogueMaterializer
        (CredentialAuthorityDomain.catalogueState (some ⟨deployment.domain, 0, []⟩))⟩)
  , (deployment.resourceBookId,
      ⟨.resourceBook, materialize CanonicalResourcePageMaterializer.materializer
        (CanonicalResourcePageMaterializer.stateOfOption (some CanonicalResourceKernel.Book.empty))⟩) ]

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL canonical registry: {label}")

def checkRows : IO Unit := do
  for (identifier, cell) in samples do
    let bytes := cellCodec.encode cell
    require "every source kind satisfies loaded/final cell law" (cellCheck deployment identifier cell)
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
  require "unknown tag refuses" ((kindAtTag 255).isNone)
  require "object initial accepted" (userInitialCheck deployment 20 (objectCell objectPage))
  require "account metadata initial accepted" (userInitialCheck deployment 21 (accountCell accountPage))
  require "program metadata initial accepted" (userInitialCheck deployment 22 programCell)
  let shadow := declaredPage 21 (.accountBalance ⟨21⟩ ⟨21⟩)
  require "shadow balance is valid low-level page" (decide shadow.Valid)
  require "account shadow balance refuses permanent law" (!cellCheck deployment 21 (accountCell shadow))
  let objectShadow := declaredPage 20 (.accountBalance ⟨20⟩ ⟨20⟩)
  require "object shadow balance refuses permanent law" (!cellCheck deployment 20 (objectCell objectShadow))
  let foreign := declaredPage 21 (.objectField ⟨37⟩ ⟨1⟩)
  require "same-shard foreign id is valid low-level page" (decide foreign.Valid)
  require "same-shard foreign id refuses" (!cellCheck deployment 21 (accountCell foreign))
  require "object request cannot select account metadata"
    ((selectDeclared deployment 21 .object (accountCell accountPage)).isNone)
  require "account role selects actual account metadata"
    ((selectDeclared deployment 21 .account (accountCell accountPage)).isSome)
  for (identifier, cell) in samples do
    match cell.kind with
    | .resourceBook =>
        require "Book cannot be a user initial payload" (!userInitialCheck deployment identifier cell)
        require "same valid Book at another id refuses" (!cellCheck deployment (identifier + 100) cell)
    | .authorityShard | .authorityCatalogue | .eventHistory =>
        require "internal state cannot be a user initial payload" (!userInitialCheck deployment identifier cell)
    | _ => pure ()
  IO.println "PASS canonical cell registry: 8 actual materializers/pins, dependent codec+outer lifecycle, permanent role/identity law, shadow-money and wrong-role refusal, source-only internal births"

def checkPhysical (binary : System.FilePath) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let config : DurableReceiverIO.NativeConfig := ⟨binary, directory / "store"⟩
    let seed : Minidregg.Kernel.DurableReceiver.Seed :=
      { absentBytes := []
        cells := samples.map fun (identifier, cell) =>
          (⟨identifier⟩, ResourceBirthCodec.LifecycleImage.bytes registry (.live cell))
        available := fun _ => 100 }
    match ← DurableReceiverIO.bootstrap config.transport ResourceBirthCodec.rootBytes seed with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
    match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
    | .error message => throw (IO.userError message)
    | .ok loaded =>
        require "eight original registry samples survive real native reopen" (loaded.cells.length == samples.length)
        for (identifier, bytes) in loaded.cells do
          match (ResourceBirthCodec.LifecycleImage.codec registry).decode bytes with
          | some (.live cell) => do
              require "reopened cell satisfies same source law"
                (cellCheck deployment identifier.value cell)
          | _ => throw (IO.userError "FAIL canonical registry: native cell lost lifecycle kind")
        require "unallocated id retains canonical fresh bytes" (loaded.snapshot.canonicalBytes ⟨9999⟩ == [])
    IO.println "PASS canonical cell registry native join: fixed lifecycle root + eight original source kinds survive SQLite bootstrap/reopen; policy-source kind has its own probe; this is transport coverage, not birth authorization"

end CanonicalCellRegistryProbe

def main (arguments : List String) : IO Unit := do
  CanonicalCellRegistryProbe.checkRows
  match arguments with
  | [] => pure ()
  | [binary] => CanonicalCellRegistryProbe.checkPhysical binary
  | _ => throw (IO.userError "usage: lean --run scripts/probe-canonical-cell-registry.lean [native-store-binary]")
