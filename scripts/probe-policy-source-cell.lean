import Compiler.CanonicalCellRegistry
import Compiler.CanonicalRuntimeProfile
import Compiler.DurableReceiverIO

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CanonicalCellRegistry

namespace PolicySourceCellProbe

def deployment : Deployment := ⟨⟨424242⟩, 10, 11, 12⟩

def record (semantics : Digest) : PolicyRecord where
  policyId := ⟨900⟩
  version := 0
  domain := deployment.domain
  semantics := semantics
  previous := none
  predicate := .eq "request/subject" 7

def initial (source : PolicyRecord) : ResourceBirth.InitialPolicy :=
  ⟨source.policyId, PolicyRecordCodec.digest source, PolicyRecordCodec.encode source⟩

def singletonDirectory (identifier : Nat) (cell : PackedCell registry) : Directory Nat registry :=
  Directory.insert registry (Directory.empty registry) identifier cell

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL policy source cell: {label}")
  IO.println s!"PASS policy source cell: {label}"

def checkSource {F : Type} [Field F] (profile : PolicyCompilerProfile F) : IO PolicyRecord := do
  let source := record profile.semantics
  let address := PolicyRecordCodec.digest source
  let identifier := PolicySourceCell.physicalId deployment.domain address
  let cell := policySourceCell source
  let directory := singletonDirectory identifier cell
  let sourceBytes := PolicyRecordCodec.encode source
  match PolicySourceCell.checkInitial deployment.domain profile (initial source) with
  | none => throw (IO.userError "FAIL policy source cell: source-defined initial policy refused")
  | some checked =>
      require "strict initial checker retains exact source bytes"
        (PolicyRecordCodec.encode checked.record == sourceBytes)
  require "initial checker rejects noncanonical appended source bytes"
    ((PolicySourceCell.checkInitial deployment.domain profile
      { initial source with canonicalBytes := sourceBytes ++ [0] }).isNone)
  require "initial checker rejects wrong domain"
    ((PolicySourceCell.checkInitial ⟨deployment.domain.value + 1⟩ profile (initial source)).isNone)
  require "initial checker rejects wrong content address"
    ((PolicySourceCell.checkInitial deployment.domain profile
      { initial source with address := ⟨address.value + 1⟩ }).isNone)
  require "initial checker rejects another policy identifier"
    ((PolicySourceCell.checkInitial deployment.domain profile
      { initial source with policyId := ⟨source.policyId.value + 1⟩ }).isNone)
  require "initial checker rejects another compiler semantics"
    ((PolicySourceCell.checkInitial deployment.domain profile
      (initial { source with semantics := ⟨source.semantics.value + 1⟩ })).isNone)
  require "initial checker rejects nonzero epoch"
    ((PolicySourceCell.checkInitial deployment.domain profile
      (initial { source with version := 1 })).isNone)
  require "initial checker rejects a predecessor"
    ((PolicySourceCell.checkInitial deployment.domain profile
      (initial { source with previous := some address })).isNone)
  require "source-defined internal kind satisfies actual source law"
    (cellCheck deployment identifier cell)
  require "raw user source-cell birth is refused" (!userInitialCheck deployment identifier cell)
  require "permanent source law binds exact deterministic identity"
    (!cellCheck deployment (identifier + 1) cell)
  let stateBytes := PolicySourceCell.stateCodec.encode cell.payload.logical
  require "source materializer accepts canonical exact state bytes"
    ((PolicySourceCell.stateCodec.decode stateBytes).isSome)
  require "source materializer rejects trailing bytes"
    ((PolicySourceCell.stateCodec.decode (stateBytes ++ [0])).isNone)
  require "source materializer rejects another wire version"
    ((PolicySourceCell.stateCodec.decode (PolicySourceCell.wireFrame ++
      PolicySourceCell.payloadStream.encode (2, some source))).isNone)
  require "source bytes cannot be relabeled as the Book schema"
    ((cellCodec.decode ([68, 82, 1, 6] ++ cell.payload.bytes)).isNone)
  require "absent source is distinct from present source"
    (PolicySourceCell.encode (PolicySourceCell.stateOfOption none) != stateBytes)
  require "same-directory lookup returns exact source bytes"
    (fetchPolicySource deployment.domain directory address == some sourceBytes)
  require "missing source refuses"
    ((fetchPolicySource deployment.domain (Directory.empty registry) address).isNone)
  let absentSource : PackedCell registry :=
    ⟨.policySource, materialize PolicySourceCell.materializer
      (PolicySourceCell.stateOfOption none)⟩
  require "present source cell with absent record refuses"
    ((fetchPolicySource deployment.domain (singletonDirectory identifier absentSource) address).isNone)
  let wrongKind : PackedCell registry :=
    ⟨.resourceBook, materialize CanonicalResourcePageMaterializer.materializer
      (CanonicalResourcePageMaterializer.stateOfOption (some CanonicalResourceKernel.Book.empty))⟩
  require "wrong physical kind at exact derived identity refuses"
    ((fetchPolicySource deployment.domain (singletonDirectory identifier wrongKind) address).isNone)
  let otherDomain := { source with domain := ⟨deployment.domain.value + 1⟩ }
  require "wrong record domain at exact derived identity refuses"
    ((fetchPolicySource deployment.domain
      (singletonDirectory identifier (policySourceCell otherDomain)) address).isNone)
  let altered := { source with predicate := .eq "request/subject" 8 }
  require "same-domain altered record at exact derived identity refuses"
    ((fetchPolicySource deployment.domain
      (singletonDirectory identifier (policySourceCell altered)) address).isNone)
  require "exact source content changes the materialized content root"
    (cell.payload.root != (policySourceCell altered).payload.root)
  match CellRegistry.create registry (Directory.empty registry) (policySourceCreate deployment.domain source) with
  | .error reason => throw (IO.userError s!"FAIL fresh policy source create: {repr reason}")
  | .ok created =>
      require "actual lifecycle source create retains exact source bytes"
        (fetchPolicySource deployment.domain created address == some sourceBytes)
      require "occupied source identity refuses repeated create"
        (match CellRegistry.create registry created (policySourceCreate deployment.domain source) with
          | .error .duplicateCreate => true | _ => false)
      let retired := Directory.retire registry created identifier
      require "retired source identity refuses resurrection"
        (match CellRegistry.create registry retired (policySourceCreate deployment.domain source) with
          | .error .retiredIdentifier => true | _ => false)
  require "duplicate derived source identifiers refuse in actual atomic allocator"
    (match ResourceBirth.allocate registry (Directory.empty registry)
      (initialSourceCreates deployment.domain [source, source]) with
      | .error .duplicateCreate => true | _ => false)
  require "unchanged source passes exact final immutable law"
    (decide (FinalPostLaw deployment identifier cell cell))
  require "rewriting source fails exact final immutable law"
    (!decide (FinalPostLaw deployment identifier cell (policySourceCell altered)))
  IO.println s!"source bytes={sourceBytes.length}, source cell bytes={(cellCodec.encode cell).length}, derived identifier bits={identifier.log2 + 1}"
  pure source

def checkPhysical (binary : System.FilePath) (source : PolicyRecord) : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let config : DurableReceiverIO.NativeConfig := ⟨binary, directory / "store"⟩
    let address := PolicyRecordCodec.digest source
    let identifier := PolicySourceCell.physicalId deployment.domain address
    let sourceCell := policySourceCell source
    let bytes := ResourceBirthCodec.LifecycleImage.bytes registry (.live sourceCell)
    let seed : Minidregg.Kernel.DurableReceiver.Seed :=
      { absentBytes := []
        cells := [(⟨identifier⟩, bytes)]
        available := fun _ => 100 }
    match ← DurableReceiverIO.bootstrap config.transport ResourceBirthCodec.rootBytes seed with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
    match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
    | .error message => throw (IO.userError message)
    | .ok loaded =>
        require "SQLite reopened exact source lifecycle bytes"
          (loaded.snapshot.canonicalBytes ⟨identifier⟩ == bytes)
        match ResourceBirthCodec.DirectoryImage.decode registry
          (loaded.cells.map fun (cellId, payload) => (cellId.value, payload)) with
        | none => throw (IO.userError "FAIL policy source cell: reopened directory decode")
        | some physical =>
            match loadPolicySource deployment.domain physical address with
            | none => throw (IO.userError "FAIL policy source cell: reopened source lookup")
            | some sourceLoaded =>
                require "same reopened snapshot resolves canonical policy source bytes"
                  (sourceLoaded.canonicalBytes == PolicyRecordCodec.encode source)
                require "source read guard uses same snapshot's actual outer physical root"
                  (sourceLoaded.readGuard.1 == identifier &&
                    sourceLoaded.readGuard.2 == loaded.snapshot.model.roots ⟨identifier⟩)
                require "reopened source retains actual internal schema identity"
                  (decide (schemaRef sourceLoaded.cell.kind = ⟨⟨91009⟩, 1⟩))

end PolicySourceCellProbe

namespace PolicySourceCellProbe

/-- These concrete field/range/template parameters are executable probe
parameters, not a production deployment choice. The constructor is the shared
source-owned runtime profile used by birth, invocation and policy installation. -/
local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

def runtime : CanonicalRuntimeProfile.Profile (ZMod 65537) :=
  CanonicalRuntimeProfile.Profile.source ⟨⟨99⟩, 1000, 1000⟩ ⟨65537⟩ 65537
    inferInstance 8 (PredOrder.noWrap_zmod (by norm_num))

def run (arguments : List String) : IO Unit := do
  IO.println "Policy source storage probe parameters: ZMod 65537, scalar width 8; no deployment field selection or authorization claim"
  let source ← PolicySourceCellProbe.checkSource PolicySourceCellProbe.runtime.compilerProfile
  match arguments with
  | [] => pure ()
  | [binary] => PolicySourceCellProbe.checkPhysical binary source
  | _ => throw (IO.userError
      "usage: lean --run scripts/probe-policy-source-cell.lean [native-store-binary]")

end PolicySourceCellProbe

def main (arguments : List String) : IO Unit := PolicySourceCellProbe.run arguments
