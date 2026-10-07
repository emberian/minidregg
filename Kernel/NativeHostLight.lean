/-
# Kernel.NativeHostLight — the light opening a Host serves ported operations from

KN2 stage 2b-1 (a). A `Light config` is the light opening of the Store's head
(`DurableServed.openHead`: checkpoint + the records after it, nothing older)
validated for this deployment (`NativeHostServed.validateServed`). A session
holds one and refreshes it by `Opening.extend` (the open's own verification of
the entries another writer appended). A request on a ported operation reads its
declared keys from the authenticated history (`Light.basis`) and is prepared on
`Ground.ofBasis`; its commit is `DurableServed.receiveServed`.
-/
import Kernel.NativeHostServed
import Compiler.DurableServed

namespace Minidregg.Kernel.NativeHostLight

open Minidregg.Compiler
open Minidregg.Compiler.DurableServed (Opening)
open Minidregg.Compiler.DurableHistory (StoreIdentity)
open Minidregg.Compiler.ServedBasis (Basis Ground)
open Minidregg.Kernel.NativeHost (Config)
open Minidregg.Kernel.NativeHostServed (OpenedServed validateServed validateServed_served)

set_option autoImplicit false

structure Light (config : Config) where
  opening : Opening ResourceBirthCodec.rootBytes
  opened : OpenedServed config opening.store
  same : opened.served = opening.served

private def validated (config : Config) (opening : Opening ResourceBirthCodec.rootBytes) :
    Except String (Light config) :=
  match checked : validateServed config opening.served with
  | .error detail => .error detail
  | .ok opened => .ok ⟨opening, opened, validateServed_served checked⟩

/-- The light opening of the Store's head, validated for this deployment. -/
def start (config : Config) : IO (Except String (Light config)) := do
  match ← DurableServed.openHead config.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok opening => return validated config opening

/-- The entries another writer appended, verified as the open verifies them; the
advanced state validated again. Nothing new: the same light opening. -/
def Light.refresh {config : Config} (light : Light config) : IO (Except String (Light config)) := do
  match ← light.opening.extend config.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok opening =>
      if opening.head.height = light.opening.head.height then return .ok light
      return validated config opening

/-- Adopt the opening a light receive returned (its record read back exactly). -/
def Light.adopt {config : Config} (_light : Light config) (opening : Opening ResourceBirthCodec.rootBytes) :
    Except String (Light config) :=
  validated config opening

/-- The basis of one request: the validated served state, the Store's head and
the request's declared keys read from the authenticated history. -/
def Light.basis {config : Config} (light : Light config) (keys : DurableView.Keys) :
    IO (Except String {basis : Basis config.deployment light.opening.store // basis.keys = keys}) := do
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  match ← reader.footprint keys with
  | .error refusal => return .error refusal.message
  | .ok footprint =>
      have below : light.opened.served.height ≤ light.opening.head.height := by
        rw [light.same, light.opening.heightExact]
      return .ok ⟨light.opened.basis light.opening.head below footprint, rfl⟩

end Minidregg.Kernel.NativeHostLight
