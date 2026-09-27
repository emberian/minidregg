/-
The resource materializer's logical payload root and the durable physical-cell
root are distinct commitments. A signed resource request uses the former;
an event-only CAS read guard must use the latter. This bridge derives the
physical root from the same verifier-loaded directory and durable snapshot.
-/
import Compiler.CredentialAuthorityDomainReceiver

namespace Minidregg.Kernel.PhysicalResourceReadGuard

open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CellRegistry

set_option autoImplicit false

variable {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}

theorem current (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (target : Nat) (packed : PackedCell CanonicalCellRegistry.registry)
    (present : loaded.directory.slots target = .present packed) :
    ResourceBirthCodec.physicalRoot (.live packed) =
      durable.snapshot.model.roots ⟨target⟩ := by
  have lifecycle : ResourceBirthCodec.LifecycleImage.view
      CanonicalCellRegistry.registry loaded.directory target = .live packed :=
    (ResourceBirthCodec.LifecycleImage.view_live_iff
      CanonicalCellRegistry.registry loaded.directory target packed).mpr present
  calc
    ResourceBirthCodec.physicalRoot (.live packed) =
        ResourceBirthCodec.rootBytes
          (ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
            (ResourceBirthCodec.LifecycleImage.view CanonicalCellRegistry.registry
              loaded.directory target)) := by rw [lifecycle]; rfl
    _ = ResourceBirthCodec.rootBytes (durable.snapshot.canonicalBytes ⟨target⟩) :=
      congrArg ResourceBirthCodec.rootBytes (loaded.bytes_exact target)
    _ = durable.snapshot.model.roots ⟨target⟩ := durable.snapshot.coherent _

end Minidregg.Kernel.PhysicalResourceReadGuard
