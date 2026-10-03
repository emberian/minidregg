/- Profile-selected current home authority for Activity publication. A profile
with a home pin cannot omit the signed projection. Profiles without a home pin
remain explicitly nonportable; no fabricated worker/home authority is returned. -/
import Kernel.PortableHomeCurrentGuard
namespace Minidregg.Kernel.BendActivityHomeGuard
open Minidregg.Compiler
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false
inductive Selected (config : Config) (opened : Opened config) : Option (List UInt8) → Type
  | nonportable (absent : config.portableHomeControl = none) : Selected config opened none
  | portable {bytes : List UInt8} (guard : PortableHomeCurrentGuard.Guard config opened bytes) :
      Selected config opened (some bytes)

def Selected.guards {config : Config} {opened : Opened config} {bytes : Option (List UInt8)} :
    Selected config opened bytes → List ReadGuard
  | .nonportable _ => []
  | .portable guard => [guard.readGuard]

variable {config : Config} {opened : Opened config} {command : Command} {signed : SignedCommand}
  {prepared : PreparedInvocation config.deployment config.profile
    ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable command}
def admit (bytes : Option (List UInt8)) (shape : PhysicalShape prepared)
    (accepted : AcceptedInvocation prepared signed) : Option (Selected config opened bytes) :=
  match bytes with
  | none => if absent : config.portableHomeControl = none then some (.nonportable absent) else none
  | some bytes => do
    let guard ← PortableHomeCurrentGuard.admit bytes shape accepted
    some (.portable guard)

theorem omitted_only_nonportable {config : Config} {opened : Opened config}
    (selected : Selected config opened none) : config.portableHomeControl = none := by
  cases selected with | nonportable absent => exact absent
#assert_axioms omitted_only_nonportable
end Minidregg.Kernel.BendActivityHomeGuard
