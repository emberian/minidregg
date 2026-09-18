/-
The concrete executable native profile. This is not a succinct-proof backend
claim. Integer policies use the sole compiler and its actual-input cast/range
checks; no truncation or token-unit conversion occurs at the host boundary.
-/
import Compiler.CanonicalRuntimeProfile
import Compiler.BabyBear

namespace Minidregg.Compiler.NativeHostProfile

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

abbrev Field := BabyBear

def orderWidth : Nat := 29

theorem orderIntervalFits : 2 ^ (orderWidth + 1) ≤ babyBearP := by
  norm_num [orderWidth, babyBearP]

theorem noWrap : PredOrder.NoWrap Field orderWidth :=
  PredOrder.noWrap_zmod orderIntervalFits

def fieldDescriptor : List UInt8 :=
  "DREGG.FIELD.ZMOD.PRIME/v1".toUTF8.toList ++ StreamCodec.nat.encode babyBearP

def fieldIdentity : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE.FIELD.IDENTITY/v1".toUTF8.toList fieldDescriptor).digest

def profile (template : CanonicalRuntimeProfile.FactoryTemplate)
    (receiverParameters : List UInt8) : CanonicalRuntimeProfile.Profile Field :=
  .source template fieldIdentity babyBearP inferInstance orderWidth noWrap receiverParameters

theorem profile_order (template : CanonicalRuntimeProfile.FactoryTemplate)
    (parameters : List UInt8) :
    (profile template parameters).compilerProfile.compiler = .scalar 29 := rfl

theorem profile_characteristic (template : CanonicalRuntimeProfile.FactoryTemplate)
    (parameters : List UInt8) :
    (profile template parameters).characteristic = 2013265921 := rfl

/-- The scalar contract is a difference bound on present operands. It is not
an economic maximum or a promise that arbitrary full-width arithmetic works. -/
theorem actual_order_range (left right : Int) :
    PredOrder.InputsInRange orderWidth true left right ↔
      -(2 : Int) ^ 29 ≤ right - left ∧ right - left < (2 : Int) ^ 29 := by
  simp [PredOrder.InputsInRange, orderWidth]

/-- At the actual upper endpoint the shared gate's order premise refuses. -/
theorem upper_endpoint_refused (left : Int) :
    ¬ PredOrder.InputsInRange orderWidth true left (left + 2 ^ 29) := by
  simp [actual_order_range]

/-- Instantiating the real native field does not discharge arithmetic by
assumption: every accepted compiled witness still proves its actual range and
cast checks. In particular, this exports no global integer-to-field injectivity. -/
theorem accepted_integer_inputs_checked
    {config : CanonicalPolicyAdmission.CanonicalPolicyConfig Field}
    {kind : ResourceKind} {request : Request kind}
    {witness : CanonicalPolicyAdmission.CompiledPolicyWitness Field}
    (accepted : config.verifies request witness = true) :
    ∃ committed,
      config.registry.resolve request.policyId request.policyRevision = some committed ∧
      inputsInRange config.compilerProfile.compiler committed.record.predicate
        witness.oldState witness.newState = true ∧
      castInjOn Field (intsOf committed.record.predicate witness.oldState witness.newState) := by
  rcases (CanonicalPolicyAdmission.verifies_iff_verified config request witness).mp accepted with
    ⟨committed, resolved, _, _, _, _, _, _, _, _, _, _, ranges, casts, _⟩
  exact ⟨committed, resolved, ranges, casts⟩

end Minidregg.Compiler.NativeHostProfile
