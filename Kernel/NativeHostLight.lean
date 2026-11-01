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
module

public import Kernel.NativeHostServed
public import Compiler.DurableServed

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.NativeHostLight

open Minidregg.Compiler
open Minidregg.Compiler.DurableServed (Opening)
open Minidregg.Compiler.DurableHistory (StoreIdentity)
open Minidregg.Compiler.ServedBasis (Basis Ground)
open Minidregg.Kernel.NativeHost (Config)
open Minidregg.Kernel.NativeHostServed (OpenedServed validateServed validateServed_served validateServedFrom
  validateServedFrom_eq)

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

/-- `validated` for a later opening of a session: validated against the light
opening it held (`validateServedFrom`, which is `validateServed`). -/
private def validatedFrom {config : Config} (prior : Light config)
    (opening : Opening ResourceBirthCodec.rootBytes)
    (held : Option CredentialAuthorityServed.HeldCell := none) : Except String (Light config) :=
  match checked : validateServedFrom config prior.opened opening.served held with
  | .error detail => .error detail
  | .ok opened => .ok ⟨opening, opened,
      validateServed_served ((validateServedFrom_eq config prior.opened opening.served held).symm.trans checked)⟩

/-- The light opening of the Store's head, validated for this deployment. -/
def start (config : Config) : IO (Except String (Light config)) := do
  match ← DurableServed.openHead config.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok opening => return validated config opening

/-- The entries another writer appended, verified as the open verifies them; the
advanced state validated again, against the held one (`validatedFrom`). Nothing new: the same light opening. -/
def Light.refresh {config : Config} (light : Light config) : IO (Except String (Light config)) := do
  match ← light.opening.extend config.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok opening =>
      if opening.head.height = light.opening.head.height then return .ok light
      return validatedFrom light opening

/-- The same light opening under a config that differs only in its Store paths. -/
def Light.restorage {config : Config} (light : Light config) (storage : DurableReceiverIO.NativeConfig) :
    Light { config with storage } :=
  ⟨light.opening, light.opened.restorage storage, light.same⟩

/-- Adopt the opening a light receive returned (its record read back exactly), given the
authority post-cell the write encoded where it wrote that cell: taken as the served authority
when the stored bytes are its bytes, so the Host never decodes the cell it just encoded nor
rebuilds its trie (`loadServedAuthorityHeld`). -/
def Light.adopt {config : Config} (light : Light config) (opening : Opening ResourceBirthCodec.rootBytes)
    (held : Option CredentialAuthorityServed.HeldCell := none) : Except String (Light config) :=
  validatedFrom light opening held

/-- What a light receive hands the session: the opening it returned and the authority
post-cell of its write, if it wrote the authority cell. -/
abbrev Adopt := Opening ResourceBirthCodec.rootBytes → Option CredentialAuthorityServed.HeldCell → IO Unit

/-- The basis of one request: the validated served state, the Store's head and
the request's declared keys read from the authenticated history (through the
reads of `transport`). -/
def Light.basisVia {config : Config} (transport : DurableReceiverIO.Transport) (light : Light config)
    (keys : DurableView.Keys) : IO (Except String (Basis config.deployment light.opening.store)) := do
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  match ← reader.footprint keys with
  | .error refusal => return .error refusal.message
  | .ok footprint =>
      have below : light.opened.served.height ≤ light.opening.head.height := by
        rw [light.same, light.opening.heightExact]
      -- `OpenedServed.basis` declares exactly `keys` (`basis.keys = keys`, by construction).
      return .ok (light.opened.basis light.opening.head below footprint)

/-- The light ground of one request at the opening's head: `basisVia`'s basis, typed as a
ground of the history the opening's own `Reader` reads (`Grounded … head`), so a historical
selection through that Reader (`NativeHistorySelection.select`) pairs with it. -/
def Light.groundedVia {config : Config} (transport : DurableReceiverIO.Transport) (light : Light config)
    (keys : DurableView.Keys) :
    IO (Except String (ServedBasis.Grounded config.deployment light.opening.head)) := do
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  match ← reader.footprint keys with
  | .error refusal => return .error refusal.message
  | .ok footprint =>
      have below : light.opened.served.height ≤ light.opening.head.height := by
        rw [light.same, light.opening.heightExact]
      return .ok (ServedBasis.Grounded.ofBasis (light.opened.basis light.opening.head below footprint))

/-- A request's basis does not depend on the Store paths a config names: under
`restorage` it is read through the same transport from the same opening. -/
theorem Light.basisVia_restorage {config : Config} (transport : DurableReceiverIO.Transport)
    (light : Light config) (storage : DurableReceiverIO.NativeConfig) (keys : DurableView.Keys) :
    (light.restorage storage).basisVia transport keys = light.basisVia transport keys := by
  unfold Light.basisVia
  simp only [Light.restorage]
  exact bind_congr fun answer => by cases answer <;> rfl

/-- `basisVia` over the deployment's Store transport. -/
def Light.basis {config : Config} (light : Light config) (keys : DurableView.Keys) :
    IO (Except String (Basis config.deployment light.opening.store)) :=
  light.basisVia config.transport keys

end Minidregg.Kernel.NativeHostLight
