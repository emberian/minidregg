/- Exact live immutable Objective package in the same signed source store.
This establishes source/module/tool/selection identity, not frontend adequacy.
The publishing/importing signer separately regenerates and compares the full
selected core through its pinned trusted elaborator before signing. -/
import Compiler.ObjectiveSourcePackage
import Kernel.ContentResource
namespace Minidregg.Kernel.ObjectiveBendPublishedPackage
open Minidregg.Compiler Minidregg.Theory Minidregg.Theory.Hyperdocument
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

def schema : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.SOURCE-PACKAGE-SCHEMA/v1".toUTF8.toList ObjectiveSourcePackage.frame).digest

structure Loaded (store : ContentResource.ContentStore) (id : AtomId) (maxBytes : Nat) where
  private mk ::
  record : AtomRecord
  recordExact : Hyperdocument.lookup store .atoms id = some record
  live : record.tombstonedAt.isNone = true
  schemaExact : record.kind = .inlineObject schema
  bounded : record.payload.length ≤ maxBytes
  package : ObjectiveSourcePackage.Package
  decoded : ObjectiveSourcePackage.decode record.payload = some package
  identityExact : ObjectiveSourcePackage.identity package = id.digest
  wellFormed : ObjectiveSourcePackage.wellFormed package = true

def lookup (store : ContentResource.ContentStore) (id : AtomId) (maxBytes : Nat) :
    Option (Loaded store id maxBytes) := do
  match recordExact : Hyperdocument.lookup store .atoms id with
  | none => none
  | some record =>
    if bounded : record.payload.length ≤ maxBytes then
      if live : record.tombstonedAt.isNone = true then
        if schemaExact : record.kind = .inlineObject schema then
          match decoded : ObjectiveSourcePackage.decode record.payload with
          | none => none
          | some package =>
            if identityExact : ObjectiveSourcePackage.identity package = id.digest then
              if wellFormed : ObjectiveSourcePackage.wellFormed package = true then
                some ⟨record,recordExact,live,schemaExact,bounded,package,decoded,identityExact,wellFormed⟩
              else none
            else none
        else none
      else none
    else none

theorem canonical {store : ContentResource.ContentStore} {id : AtomId} {maxBytes : Nat}
    (loaded : Loaded store id maxBytes) : ObjectiveSourcePackage.encode loaded.package = loaded.record.payload :=
  ObjectiveSourcePackage.decoded_canonical loaded.decoded
#assert_axioms canonical
end Minidregg.Kernel.ObjectiveBendPublishedPackage
