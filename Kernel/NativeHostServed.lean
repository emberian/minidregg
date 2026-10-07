/-
# Kernel.NativeHostServed — a validated served state (KN2 stage 2b-1)

`OpenedServed config store` is the light counterpart of `NativeHost.Opened`: a
`Served` state of the opened Store (no history), its decoded directory, its
authority cell and the factory pins, with the cell-law check it passed.
`validateServed` runs exactly the checks `validateLoaded` runs
(`NativeHost.validateChecks`, shared), over the served state.

`validateServed_ofLoaded`: on the full shape's state it refuses exactly when
`validateLoaded` refuses, with the same message, and otherwise yields the same
pins and the same directory. The full shape (`Opened`) is the transition's
other route; every caller of it is on `scripts/ports/full-loaded-callers.txt`.
-/
import Kernel.NativeHostContext
import Compiler.CredentialAuthorityServed

namespace Minidregg.Kernel.NativeHostServed

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceBirth (FactoryPins)
open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CredentialAuthorityServed
open Minidregg.Compiler.DurableServed (Served)
open Minidregg.Compiler.DurableHistory (StoreIdentity)
open Minidregg.Kernel.NativeHost
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- Every enumerable cell of the served state obeys its law. -/
def cellsLawfulServed (config : Config) {store : StoreIdentity} (served : State store)
    (directory : Directory Nat CanonicalCellRegistry.registry) : Bool :=
  served.cellIds.all (cellLawful config directory)

structure OpenedServed (config : Config) (store : StoreIdentity) where
  private mk ::
  served : State store
  directory : ServedDirectory served
  authority : ServedAuthority config.deployment served
  pins : FactoryPins
  lawful : cellsLawfulServed config served directory.directory = true

def validateServed (config : Config) {store : StoreIdentity} (served : State store) :
    Except String (OpenedServed config store) :=
  (validateCore config served.seed served.logStart (loadServedDirectory served)
    (loadServedAuthority config.deployment served) (·.directory) (·.cell.logical)
    (fun loaded => cellsLawfulServed config served loaded.directory)).map fun parts =>
      ⟨served, parts.1.1, parts.1.2.1, parts.1.2.2, parts.2⟩

/-- Validation wraps exactly the state it was given. -/
theorem validateServed_served {config : Config} {store : StoreIdentity} {served : State store}
    {opened : OpenedServed config store} (validated : validateServed config served = .ok opened) :
    opened.served = served := by
  unfold validateServed at validated
  cases parts : validateCore config served.seed served.logStart (loadServedDirectory served)
      (loadServedAuthority config.deployment served) (·.directory) (·.cell.logical)
      (fun loaded => cellsLawfulServed config served loaded.directory) with
  | error detail => simp [parts, Except.map] at validated
  | ok value =>
      simp only [parts, Except.map, Except.ok.injEq] at validated
      subst validated
      rfl

/-- A validated state's cell law holds at every identifier: outside the
enumeration the bytes are the absent default, so the slot is absent. -/
theorem OpenedServed.cellLawful_all {config : Config} {store : StoreIdentity}
    (prior : OpenedServed config store) (identifier : Digest) :
    cellLawful config prior.directory.directory identifier = true := by
  by_cases member : (⟨identifier.value⟩ : DurableDataIntent.CellId) ∈ prior.served.cellIds
  · exact List.all_eq_true.mp prior.lawful _ member
  · have bytes := prior.directory.bytes_exact identifier.value
    rw [prior.served.canonicalBytes_outside _ member, prior.directory.absentDefault] at bytes
    have slot := ResourceBirthCodec.LifecycleImage.view_slot CanonicalCellRegistry.registry
      prior.directory.directory identifier.value
    cases view : ResourceBirthCodec.LifecycleImage.view CanonicalCellRegistry.registry
        prior.directory.directory identifier.value with
    | fresh =>
        rw [view] at slot
        unfold cellLawful
        rw [← slot]
        rfl
    | retired =>
        rw [view] at bytes
        simp [ResourceBirthCodec.LifecycleImage.bytes] at bytes
    | live cell =>
        rw [view] at bytes
        simp [ResourceBirthCodec.LifecycleImage.bytes] at bytes

/-- **The served validation of the full shape's state is the full validation**:
the same refusal with the same message, or the same factory pins. -/
theorem validateServed_ofLoaded (config : Config) {store : StoreIdentity} (durable : Durable)
    (sameStart : store.logStart = durable.logStart) :
    (validateServed config (Served.ofLoaded durable sameStart)).map (·.pins) =
      (validateLoaded config durable).map (·.pins) := by
  have served := validateCore_map config durable.image.seed durable.logStart
    (CredentialAuthorityDomainReceiver.loadDirectory durable)
    (CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot)
    (·.directory) (·.snapshot.logical) (fun loaded => cellsLawful config durable loaded.directory)
    (loadServedDirectory (Served.ofLoaded durable sameStart))
    (loadServedAuthority config.deployment (Served.ofLoaded durable sameStart))
    (·.directory) (·.cell.logical)
    (fun loaded => cellsLawfulServed config (Served.ofLoaded durable sameStart) loaded.directory)
    (loadServedDirectory_ofLoaded durable sameStart)
    (by
      have rows := loadServedDirectory_ofLoaded durable sameStart
      rw [show (loadServedDirectory (Served.ofLoaded durable sameStart)).map
            (fun loaded => cellsLawfulServed config (Served.ofLoaded durable sameStart) loaded.directory) =
          ((loadServedDirectory (Served.ofLoaded durable sameStart)).map (·.directory)).map
            (fun directory => cellsLawfulServed config (Served.ofLoaded durable sameStart) directory) by
          rw [Option.map_map]; rfl, rows, Option.map_map]
      congr 1
      funext loaded
      simp only [Function.comp, cellsLawfulServed, cellsLawful, Served.ofLoaded_cellIds])
    (by
      have cells := loadServedAuthority_ofLoaded config.deployment durable sameStart
      rw [show (loadServedAuthority config.deployment (Served.ofLoaded durable sameStart)).map
            (·.cell.logical) =
          ((loadServedAuthority config.deployment (Served.ofLoaded durable sameStart)).map
            (·.cell)).map (·.logical) by rw [Option.map_map]; rfl, cells, Option.map_map]
      rfl)
  have sameSeed : (Served.ofLoaded durable sameStart).seed = durable.image.seed := rfl
  have sameLog : (Served.ofLoaded durable sameStart).logStart = durable.logStart := sameStart
  unfold validateServed validateLoaded validateParts validatePartsWith
  rw [sameSeed, sameLog]
  revert served
  generalize validateCore config durable.image.seed durable.logStart
    (loadServedDirectory (Served.ofLoaded durable sameStart))
    (loadServedAuthority config.deployment (Served.ofLoaded durable sameStart))
    (·.directory) (·.cell.logical)
    (fun loaded => cellsLawfulServed config (Served.ofLoaded durable sameStart) loaded.directory) = light
  generalize validateCore config durable.image.seed durable.logStart
    (CredentialAuthorityDomainReceiver.loadDirectory durable)
    (CredentialAuthorityDomainReceiver.loadDeployment config.deployment durable.snapshot)
    (·.directory) (·.snapshot.logical) (fun loaded => cellsLawful config durable loaded.directory) = full
  intro served
  cases light <;> cases full <;> simp_all [Except.map]

#assert_axioms validateServed_served
#assert_axioms OpenedServed.cellLawful_all
#assert_axioms validateServed_ofLoaded

end Minidregg.Kernel.NativeHostServed
