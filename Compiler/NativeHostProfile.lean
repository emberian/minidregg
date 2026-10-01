/-
The concrete executable native profile. This is not a succinct-proof backend
claim. Integer policies use the sole compiler and its actual-input cast/range
checks; no truncation or token-unit conversion occurs at the host boundary.

## The field and the order width

Admission checks a compiled law by evaluating its constraint system natively
(no proof system is in the path), so the field is whatever makes that
evaluation agree with `Pred.eval` on the values friends write. The field is
`ZMod (2^127 - 1)` (`Compiler.Mersenne127`), and the order width is 125: the
largest `k` with `2^(k+1) ≤ 2^127 - 1`, so the order gadget's decomposition of
`2^k + (b - a)` never wraps.

The stated range is the band `R = [-2^123, 2^123)`. For every law whose
literals and whose slot values (both views) lie in `R`, the compiled verdict
equals `eval` (`order_agrees_with_eval_on_R`), with no range or cast premise
left over: `R` covers every signed and unsigned 64-bit value (unix seconds,
micro-unit balances, heights, byte counts) with 59 bits to spare. `2^123`
rather than `2^124` because `leSlotsOff a b c` compares `a` with `b + c`.

Until 2026-10-01 the field was BabyBear and the width 29: every law comparing
`clock/now` (about 1.79e9) with a field holding a small number refused.
-/
import Compiler.CanonicalRuntimeProfile
import Compiler.Mersenne127
import Compiler.PredOrderWide

namespace Minidregg.Compiler.NativeHostProfile

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Pred (Pred State Slot)

set_option autoImplicit false

abbrev Field := Mersenne127

/-- The field characteristic, as the profile commits it. -/
def characteristic : Nat := mersenne127P

def orderWidth : Nat := 125

theorem orderIntervalFits : 2 ^ (orderWidth + 1) ≤ mersenne127P := by
  norm_num [orderWidth, mersenne127P]

theorem noWrap : PredOrder.NoWrap Field orderWidth :=
  PredOrder.noWrap_zmod orderIntervalFits

def fieldDescriptor : List UInt8 :=
  "DREGG.FIELD.ZMOD.PRIME/v1".toUTF8.toList ++ StreamCodec.nat.encode mersenne127P

def fieldIdentity : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE.FIELD.IDENTITY/v1".toUTF8.toList fieldDescriptor).digest

def profile (template : CanonicalRuntimeProfile.FactoryTemplate)
    (receiverParameters : List UInt8) : CanonicalRuntimeProfile.Profile Field :=
  .source template fieldIdentity mersenne127P inferInstance orderWidth noWrap receiverParameters

theorem profile_order (template : CanonicalRuntimeProfile.FactoryTemplate)
    (parameters : List UInt8) :
    (profile template parameters).compilerProfile.compiler = .scalar 125 := rfl

theorem profile_characteristic (template : CanonicalRuntimeProfile.FactoryTemplate)
    (parameters : List UInt8) :
    (profile template parameters).characteristic =
      170141183460469231731687303715884105727 := by
  show mersenne127P = _
  exact mersenne127P_eq

/-- The scalar contract is a difference bound on present operands. It is not
an economic maximum or a promise that arbitrary full-width arithmetic works. -/
theorem actual_order_range (left right : Int) :
    PredOrder.InputsInRange orderWidth true left right ↔
      -(2 : Int) ^ 125 ≤ right - left ∧ right - left < (2 : Int) ^ 125 := by
  simp [PredOrder.InputsInRange, orderWidth]

/-- At the actual upper endpoint the shared gate's order premise refuses. -/
theorem upper_endpoint_refused (left : Int) :
    ¬ PredOrder.InputsInRange orderWidth true left (left + 2 ^ 125) := by
  simp [actual_order_range]

/-! ## The stated range `R` -/

/-- The bound of `R`. -/
def rangeBound : Int := 2 ^ 123

/-- `R = [-2^123, 2^123)`: the values every law may compare and be decided as `eval` decides. -/
abbrev InR (x : Int) : Prop := InBand rangeBound x

theorem rangeBound_fits_order : 3 * rangeBound ≤ (2 : Int) ^ orderWidth := by
  norm_num [rangeBound, orderWidth]

theorem rangeBound_pos : 0 < rangeBound := by norm_num [rangeBound]

theorem rangeBound_fits_field : 2 * rangeBound ≤ (mersenne127P : Int) := by
  norm_num [rangeBound, mersenne127P]

/-- Every unsigned 64-bit value is in `R`. -/
theorem uint64_inR (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) : InR x := by
  refine ⟨?_, ?_⟩ <;> norm_num [rangeBound] at * <;> omega

/-- Every signed 64-bit value is in `R`. -/
theorem int64_inR (x : Int) (h0 : -(2 ^ 63) ≤ x) (h1 : x < 2 ^ 63) : InR x := by
  refine ⟨?_, ?_⟩ <;> norm_num [rangeBound] at * <;> omega

/-- On `R`, the range premise holds for every law: no order atom refuses an honest value. -/
theorem inputsInRange_on_R {p : Pred} {old new : State}
    (h : ∀ x ∈ intsOf p old new, InR x) :
    inputsInRange (.scalar orderWidth) p old new = true :=
  inputsInRange_of_intsOf_inBand rangeBound_fits_order rangeBound_pos h

/-- On `R`, no two distinct values share a field image. -/
theorem castInjOn_on_R (I : List Int) (h : ∀ x ∈ I, InR x) : castInjOn Field I :=
  castInjOn_zmod_of_inBand rangeBound_fits_field I h

theorem admissible : (CompilerProfile.scalar orderWidth).Admissible Field := noWrap

/-- **`order_agrees_with_eval_on_R`** — `lower_correct` at the native profile with its
range and cast premises discharged by `R`: for every supported law whose literals and
slot values lie in `R`, the compiled system accepts (for some auxiliary assignment)
exactly when `eval` accepts. Both directions; every order atom (`le`, `monotone`,
`leSlots`, `leSlotsOff` with its offset) under any negation or disjunction, so `<`
(`not (leSlots b a)`) included. -/
theorem order_agrees_with_eval_on_R {p : Pred} {old new : State}
    (hsup : supported (.scalar orderWidth) p = true)
    (h : ∀ x ∈ intsOf p old new, InR x) :
    (∃ A : List ℕ → ℕ → Field,
        systemAccepts (stepAsg old new A) (lower (.scalar orderWidth) p))
      ↔ Minidregg.Pred.eval p old new = true :=
  lower_correct (F := Field) (.scalar orderWidth) admissible (castInjOn_on_R _ h) hsup
    (inputsInRange_on_R h)

/-- The four order atoms are supported at the native profile; `<` is a negated `≤`. -/
theorem order_atoms_supported (s a b : Slot) (v c : Int) :
    supported (.scalar orderWidth) (.le s v) = true ∧
    supported (.scalar orderWidth) (.monotone s) = true ∧
    supported (.scalar orderWidth) (.leSlots a b) = true ∧
    supported (.scalar orderWidth) (.leSlotsOff a b c) = true ∧
    supported (.scalar orderWidth) (.not (.leSlots b a)) = true := by
  simp [supported, CompilerProfile.scalar]

/-- The canonical verifier at the native field reflects `eval` on `R`: the
binding facts of `canonical_verifies_iff_eval`, with `rangesExact` and
`castExact` replaced by "every integer the instance touches is in `R`". -/
theorem native_verifies_iff_eval_on_R
    {config : CanonicalPolicyAdmission.CanonicalPolicyConfig Field} {kind : ResourceKind}
    {request : Request kind} {committed : CanonicalPolicyAdmission.CommittedPolicy}
    {oldState newState : State}
    (compilerExact : config.compilerProfile.compiler = .scalar orderWidth)
    (resolved : config.registry.resolve request.policyId request.policyRevision =
      some committed)
    (policyIdExact : committed.record.policyId = request.policyId)
    (versionExact : committed.record.version = request.policyRevision)
    (domainExact : committed.record.domain = request.domain)
    (semanticsExact : committed.record.semantics = request.semantics)
    (recordDigestExact : config.recordDigest committed.record = committed.address)
    (stepExact : config.stepBinding.matches request oldState newState = true)
    (profileCompatible : config.compilerProfile.compatible config.stepBinding = true)
    (profileSemanticsExact : request.semantics = config.compilerProfile.semantics)
    (supportedExact : supported config.compilerProfile.compiler committed.record.predicate = true)
    (inR : ∀ x ∈ intsOf committed.record.predicate oldState newState, InR x) :
    config.verifies request
        (CanonicalPolicyAdmission.canonicalWitness config.compilerProfile.compiler committed
          oldState newState) = true ↔
      Minidregg.Pred.eval committed.record.predicate oldState newState = true :=
  CanonicalPolicyAdmission.canonical_verifies_iff_eval resolved policyIdExact versionExact
    domainExact semanticsExact recordDigestExact stepExact profileCompatible
    profileSemanticsExact supportedExact (by rw [compilerExact]; exact inputsInRange_on_R inR)
    (castInjOn_on_R _ inR)

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

#assert_axioms order_agrees_with_eval_on_R
#assert_axioms native_verifies_iff_eval_on_R
#assert_axioms profile_characteristic
#assert_axioms upper_endpoint_refused

end Minidregg.Compiler.NativeHostProfile
