/-
# `Kernel/ResourceEffectRegistry.lean` — the registry of declared-resource effects

`liveEffects` binds a wire code (the target payload's tag octet) to its one declaration.
`Payload.registered code op` (`Kernel/ResourceTransaction.lean`) carries an operation of
`effectAt code`; a code bound here has no other arm anywhere, and a code not bound here has no
operation at all (`Effect.unregistered`, whose operation type is empty).

Adding an effect is one entry here and its declaration file. The legacy payload constructors'
tags must stay out of this list: `payloadStream`'s round-trip is proved from
`registeredOctet tag = false` at each of them, so binding a legacy tag does not build.
-/
module

public import Kernel.CitedRead

@[expose] public section

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Effects
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
set_option autoImplicit false

/-- **The registry**: wire code ↦ declaration. -/
def liveEffects : List (Nat × Effect) := [(9, citedEffect)]

/-- Whether a code is bound. -/
def registeredCode (code : Nat) : Bool := (liveEffects.lookup code).isSome

/-- Whether a payload tag octet is a bound code. -/
def registeredOctet (tag : UInt8) : Bool := registeredCode tag.toNat

/-- The declaration at a code; the effect without operations at an unbound one. -/
def effectAt (code : Nat) : Effect := (liveEffects.lookup code).getD Effect.unregistered

theorem effectAt_unbound {code : Nat} (unbound : registeredCode code = false) :
    effectAt code = Effect.unregistered := by
  unfold registeredCode at unbound
  unfold effectAt
  cases found : liveEffects.lookup code with
  | none => rfl
  | some e => rw [found] at unbound; cases unbound

/-- An unbound code has no operation. -/
theorem unbound_elim {tag : UInt8} (unbound : registeredOctet tag = false)
    (op : (effectAt tag.toNat).O) : False := by
  rw [effectAt_unbound unbound] at op
  exact Empty.elim op

/-- The code a JSON `type` names, when a declaration bears that name. -/
def effectNamed (name : String) : Option UInt8 :=
  (liveEffects.find? fun entry => entry.2.name == name).map fun entry => UInt8.ofNat entry.1

/-- The names the registry binds (for a refusal that lists what it expected). -/
def effectNames : List String := liveEffects.map fun entry => entry.2.name

/-- A declaration's name as a constructor namespace (`fieldRead` is `FieldRead`). -/
def effectTitle (code : Nat) : String := (effectAt code).name.capitalize

/-- **A dispatch refusal as its requester reads it.** A code nothing binds is
`Effect.Registry.unregistered <code>`; every other refusal is `Effect.<Name>.<refusal>`, the declaration's
own refusal followed by its detail in the declaration's words (`Effect.refusalText`; a cited
read's `citedStale` lists the fields that moved). -/
def dispatchRefusalText : Revival.DispatchRefusal → String
  | .unregistered code => s!"Effect.Registry.unregistered {code}"
  | .malformed code => s!"Effect.{effectTitle code}.malformed"
  | .wrongRole code => s!"Effect.{effectTitle code}.wrongRole"
  | .refused code name detail =>
      let words := (effectAt code).refusalText name detail
      s!"Effect.{effectTitle code}.{name}" ++ (if words.isEmpty then "" else " " ++ words)
  | .outOfFrame code => s!"Effect.{effectTitle code}.outOfFrame"
  | .guardFailed code => s!"Effect.{effectTitle code}.guardFailed"
  | .unsupportedVersion code => s!"Effect.{effectTitle code}.unsupportedVersion"
  | .staleTarget code => s!"Effect.{effectTitle code}.staleTarget"
  | .host code name => s!"Effect.{effectTitle code}.host {name}"

/-- The one `Repr` of a dispatch refusal: the registry's reading. The Host commits a refusal's
detail as the `repr` of its `Reject` (`Host/RefusalText.lean`), so this is what a requester sees
(executed in `Assurance/RegistryRefusalPoles.lean`). -/
instance : Repr Revival.DispatchRefusal where
  reprPrec refusal prec := Repr.addAppParen (.text (dispatchRefusalText refusal)) prec

/-- **The engine registry**: every declaration's handler at its code. -/
def liveRegistry : Revival.Registry DispatchCtx (PackedCell Registry) :=
  liveEffects.map fun entry => (entry.1, entry.2.handler entry.1)

/-- The cited read's payload tag. -/
abbrev citedCode : UInt8 := 9

theorem effectAt_cited : effectAt citedCode.toNat = citedEffect := rfl

/-- The legacy payload tags are unbound (what `payloadStream`'s round-trip reads). -/
theorem legacy_unbound :
    registeredOctet 0 = false ∧ registeredOctet 1 = false ∧ registeredOctet 2 = false ∧
    registeredOctet 3 = false ∧ registeredOctet 4 = false ∧ registeredOctet 5 = false ∧
    registeredOctet 6 = false ∧ registeredOctet 7 = false ∧ registeredOctet 8 = false := by
  decide

example : (effectAt citedCode.toNat).O = List FieldRead := rfl
example : (effectAt (9 : UInt8).toNat).L = EffectDeclaration.effectLayout := rfl

end Minidregg.Kernel.DeclaredResourceController
