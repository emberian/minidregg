/- Canonical reusable Objective Bend prototype prototype artifacts. The artifact
binds exact source/import closure, parents, ancestor order, unresolved interfaces
and prototype core declarations. Reflection uses actual parsed core definitions;
execution still requires complete composition and BendCoreAdmission.
-/
import Compiler.ObjectiveBendComposition
import Compiler.BendCoreAdmission
import Compiler.BendWorldSource

namespace Minidregg.Compiler.ObjectiveBendPrototype
open Minidregg.Theory.BendTT
open ObjectiveBendComposition
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

structure RequirementRef where
  scope : Scope
  selector : String
  typeEntry : String
  deriving DecidableEq, Repr

structure ProvisionRef where
  selector : String
  entry : String
  captures : List String
  deriving DecidableEq, Repr

structure Partial where
  source : BendWorldSource.Package
  directParents : List Nat
  /-- Complete ancestors only. Own content identity is appended after hashing,
  avoiding a circular identity encoded inside the bytes it hashes. -/
  ancestorOrder : List Nat
  core : List UInt8
  required : List RequirementRef
  provided : List ProvisionRef
  deriving DecidableEq, Repr

def scopeStream : StreamCodec Scope :=
  StreamCodec.xmap StreamCodec.bool
    (fun scope => match scope with | .finalSelf => false | .priorSuper => true)
    (fun super => if super then .priorSuper else .finalSelf)
    (by intro scope; cases scope <;> rfl)

def requirementStream : StreamCodec RequirementRef :=
  StreamCodec.xmap (StreamCodec.product scopeStream
    (StreamCodec.product PolicyRecordCodec.stringStream PolicyRecordCodec.stringStream))
    (fun r => (r.scope, r.selector, r.typeEntry))
    (fun r => ⟨r.1, r.2.1, r.2.2⟩) (by intro r; cases r; rfl)

def provisionStream : StreamCodec ProvisionRef :=
  StreamCodec.xmap (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream
      (StreamCodec.list PolicyRecordCodec.stringStream)))
    (fun p => (p.selector, p.entry, p.captures))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (by intro p; cases p; rfl)

def partialStream : StreamCodec Partial :=
  StreamCodec.xmap (StreamCodec.product BendWorldSource.packageStream
    (StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.product bytesStream
    (StreamCodec.product (StreamCodec.list requirementStream)
      (StreamCodec.list provisionStream))))))
    (fun p => (p.source, p.directParents, p.ancestorOrder, p.core, p.required, p.provided))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩)
    (by intro p; cases p; rfl)

def frame : List UInt8 := "DREGG/OBJECTIVE-BEND/PROTOTYPE/v1".toUTF8.toList

def encode (prototype : Partial) : List UInt8 := frame ++ partialStream.encode prototype

def decode (bytes : List UInt8) : Option Partial :=
  NockProgramCodec.framedDecode frame partialStream bytes

def identity (prototype : Partial) : Nat :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.PROTOTYPE/v1".toUTF8.toList
    (encode prototype)).digest.value

/-- Partial source is parsed canonically, but deliberately cannot pass a complete
Book check until requirements are supplied and self/super refs are elaborated.
This loader does not certify a surface compiler or grant runtime authority. -/
def reflect (prototype : Partial) : Except String Spec := do
  if !BendWorldSource.wellFormed prototype.source then throw "invalid source/import closure"
  let some text := String.fromUTF8? ⟨prototype.core.toArray⟩ | throw "invalid core UTF-8"
  let book ← Book.parse text
  if BendCoreAdmission.encode book != prototype.core then throw "noncanonical prototype core"
  let requirements ← prototype.required.mapM fun r => do
    let some definition := Book.get book r.typeEntry | throw "missing required interface type"
    pure (⟨r.scope, ⟨r.selector, definition.T⟩⟩ : Requirement)
  let provisions ← prototype.provided.mapM fun p => do
    let some definition := Book.get book p.entry | throw "missing provided method source"
    if definition.o then throw "opaque provided method"
    let captures ← p.captures.mapM fun name => do
      let some captured := Book.get book name | throw "missing captured Data source"
      pure captured.v
    pure (⟨⟨p.selector, definition.T⟩, identity prototype, p.entry,
      definition.v, captures⟩ : Provision)
  pure ⟨identity prototype, prototype.directParents, prototype.ancestorOrder ++ [identity prototype],
    requirements, provisions⟩

theorem canonical {bytes : List UInt8} {prototype : Partial}
    (decoded : decode bytes = some prototype) : encode prototype = bytes :=
  NockProgramCodec.framedDecode_canonical decoded

theorem roundtrip (prototype : Partial) : decode (encode prototype) = some prototype :=
  NockProgramCodec.framedDecode_encode frame partialStream prototype

#assert_axioms canonical
#assert_axioms roundtrip

end Minidregg.Compiler.ObjectiveBendPrototype
