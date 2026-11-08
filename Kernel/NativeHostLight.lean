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

/-- Adopt the opening one record after this light's own (a light receive's `.appended`), given
the cells that record wrote and the proof that every other cell kept its bytes
(`Served.advance_moved`): validated over the written cells only (`validateServedStep`, which is
`validateServed`). -/
def Light.adoptStep {config : Config} (light : Light config) (opening : Opening ResourceBirthCodec.rootBytes)
    (written : List DurableDataIntent.CellId)
    (moved : DurableServed.Served.Moved light.opening.served opening.served written)
    (held : Option CredentialAuthorityServed.HeldCell := none) : Except String (Light config) :=
  have moved' : DurableServed.Served.Moved light.opened.served opening.served written := by
    rw [light.same]; exact moved
  match checked : NativeHostServed.validateServedStep config light.opened opening.served written moved' held with
  | .error detail => .error detail
  | .ok opened => .ok ⟨opening, opened,
      validateServed_served ((NativeHostServed.validateServedStep_eq config light.opened opening.served
        written moved' held).symm.trans checked)⟩

/-- What a light receive on `before` hands the session: the opening it returned, the cells its
record wrote with the proof that every other cell kept its bytes (`Received.appended`'s
`moved`), and the authority post-cell of its write, if it wrote the authority cell. The
authority post-cell is taken as the served authority when the stored bytes are its bytes, so
the Host never decodes the cell it just encoded nor rebuilds its trie
(`loadServedAuthorityHeld`). -/
abbrev Adopt (before : Opening ResourceBirthCodec.rootBytes) :=
  (next : Opening ResourceBirthCodec.rootBytes) → (written : List DurableDataIntent.CellId) →
    DurableServed.Served.Moved before.served next.served written →
    Option CredentialAuthorityServed.HeldCell → IO Unit

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
