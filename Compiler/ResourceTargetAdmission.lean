/-
# Same-snapshot selection of user-facing resource roles

Resource management observes the actual packed payload and its canonical
logical root. It does not assume scalar-page representation, and cannot select
internal authority, Book, receipt-history or policy-source roles by coercing
all object-like registry entries into ordinary resources.
-/
import Compiler.CanonicalCellRegistry

namespace Minidregg.Compiler.ResourceTargetAdmission

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry

/-- One shared role selection for ordinary resource observation and management:
which registry kinds are observable as a resource, and as which kind. The
match is exhaustive on purpose: a new registry kind does not build until it is
placed here. A `_ => none` wildcard once made K-STREAM's new kind silently
unobservable (every read refused, the build green). -/
def externalKind : CanonicalCellRegistry.Kind → Option ResourceKind
  | .content | .declaredObject | .stream => some .object
  | .accountMetadata => some .account
  | .declaredProgram => some .program
  -- A Nock program cell is read through ops 131-133 (public), not observed.
  | .eventHistory | .authority | .resourceBook | .policySource | .pay | .nockProgram | .clock => none

structure Observed (deployment : CanonicalCellRegistry.Deployment)
    (directory : Directory Nat Registry) (kind : ResourceKind) (target : Nat) (expectedRoot : Digest) where
  before : PackedCell Registry
  present : directory.slots target = .present before
  law : CanonicalCellRegistry.CellLaw deployment target before
  role : externalKind before.kind = some kind
  rootExact : expectedRoot = before.payload.root

def observe (deployment : CanonicalCellRegistry.Deployment)
    (directory : Directory Nat Registry) (kind : ResourceKind) (target : Nat) (expectedRoot : Digest) :
    Option (Observed deployment directory kind target expectedRoot) :=
  match present : directory.slots target with
  | .absent => none
  | .present before =>
    if law : CanonicalCellRegistry.CellLaw deployment target before then
      if role : externalKind before.kind = some kind then
        if rootExact : expectedRoot = before.payload.root then
          some ⟨before, present, law, role, rootExact⟩
        else none
      else none
    else none

theorem internal_authority_unselectable : externalKind .authority = none := rfl
theorem content_is_object : externalKind .content = some .object := rfl
theorem account_cannot_be_object : externalKind .accountMetadata ≠ some .object := by decide

end Minidregg.Compiler.ResourceTargetAdmission
