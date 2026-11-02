/-
Author an ordinary resource birth at the verifier-loaded native prefix. The
human JSON selects resource identities and funding; Host.Json constructs the
canonical cells, policies, grants and fee using current height and authority.
The genesis description is checked against the pinned runtime seed, never
treated as the current authority snapshot.
-/
module

public import Host.CurrentResourceBirthAuthoring
public import Host.SourceAgreementJson
public import Kernel.NativeHost
public import Kernel.NativeHostBookInvariant

@[expose] public section

namespace Minidregg.Host.SourceAgreementBirth

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Kernel

set_option autoImplicit false

/-- Delegate to `Host.CurrentResourceBirthAuthoring.intentLoadedAuthorized` so there is
a single resource-birth authoring implementation on the opened image. -/
def intentLoadedAuthorized (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (signedObservationBytes : List UInt8)
    (json : Lean.Json) : IO (Except String (List UInt8)) :=
  CurrentResourceBirthAuthoring.intentLoadedAuthorized config opened signedObservationBytes json

theorem genesis_initialBook_accountSupported (config : NativeHostGenesis.Config) :
    config.initialBook.AccountSupported :=
  CurrentResourceBirthAuthoring.genesis_initialBook_accountSupported config

theorem preparedBirth_preserves_accountSupported
    {F : Type} [Field F] {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : CanonicalCellRegistry.Deployment} {pins : ResourceBirth.FactoryPins}
    {ground : ServedBasis.Ground deployment} {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile deployment pins ground descriptor) :
    (CanonicalResourceKernel.logicalBook prepared.book.payload.logical).AccountSupported ∧
      (CanonicalResourceKernel.logicalBook prepared.resources.post.logical).AccountSupported :=
  CurrentResourceBirthAuthoring.preparedBirth_preserves_accountSupported prepared

#assert_axioms genesis_initialBook_accountSupported
#assert_axioms preparedBirth_preserves_accountSupported

end Minidregg.Host.SourceAgreementBirth
