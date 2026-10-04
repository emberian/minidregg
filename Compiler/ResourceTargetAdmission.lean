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
unobservable (every read refused, the build green). The pay cell is a program
resource so that its control grants (`NativeHostGenesis.payControlCapability`)
can be exercised by the ordinary delegation and revocation receivers; its
contents are written only by the pay receivers. -/
def externalKind : CanonicalCellRegistry.Kind → Option ResourceKind
  | .content | .declaredObject | .stream | .worldKind | .worldInstance => some .object
  | .accountMetadata => some .account
  | .declaredProgram | .pay => some .program
  -- A Nock program cell is read through ops 131-133 (public), not observed.
  -- A stream entry is read through its head's `tail` view, never observed itself.
  | .eventHistory | .authority | .resourceBook | .policySource | .nockProgram | .clock
  | .streamEntry | .system => none
  -- An activity cell is read through the activity view, never observed as a resource.
  | .objectiveActivity => none
  -- A seat cell is read through the seat view, never observed as a resource.
  | .seat => none

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
