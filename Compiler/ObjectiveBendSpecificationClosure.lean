/- `Specification<T>` is closed under `compose` (OB-LTUO LT1).

Every specification has the one public type `specification(SpecMeta, Extension<T>)`:
`SpecMeta` is first-order data (built-in sums `SpecMeta`/`SpecClaims`, see
`ObjectiveBendElaborate.specMetaName`), so neither a claim nor a composition changes
the public type. Two levels are stated here:

* the front end's own type computation: `composeTy_closed` — composing two operands
  that are each `Specification<T>` or `Extension<T>` has type `Specification<T>`,
  for EVERY target `T` (symbolic);
* the Core4 typing relation: `compose_wrapper_typed` — the term the elaborator lowers one
  `compose` step to (`λl. λr. specification(inject composed {inherited: P l, wrapping:
  P r}, mix l r)`, with `P x = metadata x` for a specification operand and
  `inject extension {}` for a bare extension) has a `PartialTyping` derivation at
  every shareable target `T` and every operand kind, built generically in `T`. So the no-refusal theorem
  (`ObjectiveBendFrontEndAdequacy.accepted_never_refused`, statement unchanged) covers
  every program built from it; `twice_accepted` and `claim_spec_accepted` exhibit the
  surface programs the old metadata typing refused.

The reflection contract (which observers exist; behavioural vs reflective equality;
why associativity holds for behaviour and not for SpecMeta) is
docs/objective-bend/REFLECTION.md. -/
import Compiler.ObjectiveBendFrontEndAdequacy
import Theory.ObjectiveBendTyping
import Theory.AssertCompiled
namespace Minidregg.Compiler.ObjectiveBendSpecificationClosure
open Lean
open Minidregg.Theory.ObjectiveBendTypes
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendOpenRecursion
set_option autoImplicit false

/-! ## The front end's type computation -/

section FrontEnd
open Minidregg.Compiler.ObjectiveBendElaborate

/-- An operand of `compose` at target `T`: a specification (any one metadata type) or a
bare extension. -/
def operandTy (metaTy T : PTy) : Bool → PTy
  | true => .specification metaTy (extensionTy T)
  | false => extensionTy T

theorem composeTy_closed (metaTy T : PTy) (left right : Bool) :
    composeTy metaTy (some (operandTy metaTy T left)) (some (operandTy metaTy T right)) =
      some (.specification metaTy (extensionTy T)) := by
  cases left <;> cases right <;> simp [composeTy, ObjectiveBendElaborate.callable, operandTy, extensionTy, arrowTy]

/-- Folding `compose(e₁, …, eₙ)` left to right stays at `Specification<T>`. -/
theorem composeTy_fold_closed (metaTy T : PTy) (first : Bool) (rest : List Bool) :
    rest.foldl (fun acc next => composeTy metaTy acc (some (operandTy metaTy T next)))
      (some (operandTy metaTy T first)) =
      (if rest.isEmpty then some (operandTy metaTy T first) else some (.specification metaTy (extensionTy T))) := by
  induction rest generalizing first with
  | nil => simp
  | cons next more ih =>
    rw [List.foldl_cons, composeTy_closed,
      show some (PTy.specification metaTy (extensionTy T)) = some (operandTy metaTy T true) from rfl, ih true]
    cases more <;> simp [operandTy]

end FrontEnd

/-! ## The Core4 checker accepts the compose lowering at every target -/

/-- Recursive-sum variables as the elaborator assigns them in a program whose first
specification metadata it resolves: `SpecClaims` is reached first (inside `declared`). -/
def claimsVariable : Nat := 1
def metaVariable : Nat := 2

def specClaimsRow : Ty :=
  .field "none" .emptyRow
    (.field "claim" (.field "name" .label (.field "status" .label (.field "rest" (.variable claimsVariable) .emptyRow)))
      .emptyRow)
def composedPayload : Ty :=
  .field "inherited" (.variable metaVariable) (.field "wrapping" (.variable metaVariable) .emptyRow)
def specMetaRow : Ty :=
  .field "declared" (.field "name" .label (.field "interface" .label (.field "claims" (.variable claimsVariable) .emptyRow)))
    (.field "composed" composedPayload (.field "extension" .emptyRow .emptyRow))
def metaAssumptions : Assumptions :=
  ⟨[(claimsVariable, .variant specClaimsRow), (metaVariable, .variant specMetaRow)], [claimsVariable, metaVariable], []⟩

def extTy (T : Ty) : Ty := .arrow .reusable .unrestricted T (.arrow .reusable .unrestricted T T)
def specTy (T : Ty) : Ty := .specification (.variable metaVariable) (extTy T)
def coreOperandTy (T : Ty) : Bool → Ty
  | true => specTy T
  | false => extTy T
/-- An operand's provenance, as the elaborator lowers it. -/
def provenance (isSpecification : Bool) (operand : Minidregg.Theory.ObjectiveBendOpenRecursion.Term) : Minidregg.Theory.ObjectiveBendOpenRecursion.Term :=
  if isSpecification then .metadata operand else .inject "extension" (.record [])

def composeWrapper (T : Ty) (left right : Bool) : AnnotatedTerm :=
  ⟨.lam (.lam (.specification
      (.inject "composed" (.record [("inherited", provenance left (.bound 1)), ("wrapping", provenance right (.bound 0))]))
      (.mix (.bound 1) (.bound 0)))),
    fun position =>
      if position = [] then some ⟨coreOperandTy T left,
        .arrow .reusable .unrestricted (coreOperandTy T right) (specTy T), .unrestricted, .reusable⟩
      else if position = [0] then some ⟨coreOperandTy T right, specTy T, .unrestricted, .reusable⟩
      else if position = [0, 0, 0] then some ⟨composedPayload, .variable metaVariable, .unrestricted, .reusable⟩
      else if position = [0, 0, 0, 0, 0] then some ⟨.emptyRow, .variable metaVariable, .unrestricted, .reusable⟩
      else if position = [0, 0, 0, 0, 1] then some ⟨.emptyRow, .variable metaVariable, .unrestricted, .reusable⟩
      else none,
    metaAssumptions⟩

theorem shareableUnder_of_shareable (vars : List Nat) (type : Ty) (h : type.shareable = true) :
    type.shareableUnder vars = true := by
  induction type <;> simp_all [Ty.shareable, Ty.shareableUnder]

theorem metaAssumptions_valid : metaAssumptions.valid = true := by decide

theorem operand_shareable (T : Ty) (shareable : T.shareable = true) (b : Bool) :
    (coreOperandTy T b).shareableUnder metaAssumptions.shareableVariables = true := by
  have under := shareableUnder_of_shareable metaAssumptions.shareableVariables T shareable
  cases b <;> simp_all [coreOperandTy, specTy, extTy, Ty.shareableUnder, Ty.shareable, metaAssumptions, metaVariable, claimsVariable]

theorem operand_callable (T : Ty) (b : Bool) :
    callable (coreOperandTy T b) = .arrow .reusable .unrestricted T (.arrow .reusable .unrestricted T T) := by
  cases b <;> rfl

theorem meta_conversion : sameType metaAssumptions (.variant specMetaRow) (.variable metaVariable) = true := by decide

/-- An operand's provenance has type `SpecMeta` (the bounded variable). -/
theorem provenance_typed (T : Ty) (context : Context) (index : Nat) (b : Bool)
    (h : context[index]? = some ⟨coreOperandTy T b, .unrestricted⟩) :
    PartialTyping metaAssumptions context (provenance b (.bound index)) (.variable metaVariable)
      (if b then variableUses context index else zeroUses context) := by
  cases b
  · exact .conversion (.inject (fuel := 4) (.record (.nil context)) (by decide) rfl) meta_conversion
  · exact .metadata (.bound h)

/-- The compose lowering is typable by the Core4 typing relation at EVERY shareable target
`T`, for every operand kind: the derivation is built here, generically in `T`. -/
theorem compose_wrapper_typed (T : Ty) (shareable : T.shareable = true) (left right : Bool) :
    ∃ uses, PartialTyping metaAssumptions [] (composeWrapper T left right).term
      (.arrow .reusable .unrestricted (coreOperandTy T left)
        (.arrow .reusable .unrestricted (coreOperandTy T right) (specTy T))) uses := by
  have sl := operand_shareable T shareable left
  have sr := operand_shareable T shareable right
  have under := shareableUnder_of_shareable metaAssumptions.shareableVariables T shareable
  let inner : Context := [⟨coreOperandTy T right, .unrestricted⟩, ⟨coreOperandTy T left, .unrestricted⟩]
  have pl := provenance_typed T inner 1 left rfl
  have pr := provenance_typed T inner 0 right rfl
  have payload : PartialTyping metaAssumptions inner
      (.record [("inherited", provenance left (.bound 1)), ("wrapping", provenance right (.bound 0))])
      composedPayload _ :=
    .record (.cons pl (.cons pr (.nil inner) rfl) rfl)
  have metaTyped : PartialTyping metaAssumptions inner
      (.inject "composed" (.record [("inherited", provenance left (.bound 1)), ("wrapping", provenance right (.bound 0))]))
      (.variable metaVariable) _ :=
    .conversion (.inject (fuel := 4) payload (by decide) rfl) meta_conversion
  have mixTyped : PartialTyping metaAssumptions inner (.mix (.bound 1) (.bound 0)) (extTy T) _ :=
    .mix (.bound (binding := ⟨coreOperandTy T left, .unrestricted⟩) rfl)
      (.bound (binding := ⟨coreOperandTy T right, .unrestricted⟩) rfl)
      (operand_callable T left) (operand_callable T right)
      (by cases left <;> cases right <;>
        simp_all [reusableCaptures, addUses, variableUses, zeroUses, inner, List.range_succ, List.zipWith])
      under under under
  have body : PartialTyping metaAssumptions inner
      (.specification (.inject "composed" (.record [("inherited", provenance left (.bound 1)),
        ("wrapping", provenance right (.bound 0))])) (.mix (.bound 1) (.bound 0))) (specTy T) _ :=
    .specification metaTyped mixTyped rfl rfl
  refine ⟨_, .lambda (annotation := ⟨coreOperandTy T left,
      .arrow .reusable .unrestricted (coreOperandTy T right) (specTy T), .unrestricted, .reusable⟩)
    (.lambda (annotation := ⟨coreOperandTy T right, specTy T, .unrestricted, .reusable⟩) body ?_ ?_ ?_) ?_ ?_ ?_⟩ <;>
  cases left <;> cases right <;>
  simp_all [safeUses, safeQuantity, validContext, reusableAllowed, reusableCaptures, addUses, variableUses,
    zeroUses, inner, List.range_succ, List.zipWith]

/-! ## Surface programs the old metadata typing refused, now accepted -/

open Minidregg.Compiler.ObjectiveBendFrontEnd in
def acceptsSource (source entry : String) : Bool :=
  let m : SourceModule := ⟨"Probe", source, Sha256.hexString source, []⟩
  match ObjectiveBendFrontEnd.lower [m] 0 entry (Json.arr #[]) (Json.arr #[])
      (Json.mkObj [("heap", toJson "100000"), ("stack", toJson "100000"), ("ticks", toJson "100000")]) "definition" with
  | .ok l => (ObjectiveBendFrontEnd.accept l).toBool
  | .error _ => false

/-- The audit's witness (LTUO probe W01): `Specification<Nat>` is closed under compose. -/
def twiceSource : String :=
  "edition ObjectiveBend 1\n" ++
  "def twice(e: Extension<Nat>) -> Specification<Nat>:\n  compose(e, e)\n"

theorem twice_accepted : acceptsSource twiceSource "twice" = true := by native_decide

/-- LTUO probe W02: a spec with a claim inhabits `Specification<T>`. -/
def claimSpecSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\n" ++
  "spec Start for Counter:\n  claim positive: self.n == 41n\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Counter>:\n  Start\n"

theorem claim_spec_accepted : acceptsSource claimSpecSource "asSpecification" = true := by native_decide

/-- Teeth: the refusal is not gone wholesale — a claim that is not Bool is still refused
(claims are checked code in their own knot field), and a spec at another target is
not a `Specification<Counter>`. -/
def badClaimSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\n" ++
  "spec Start for Counter:\n  claim positive: self.n + 1n\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Counter>:\n  Start\n"

theorem non_boolean_claim_refused : acceptsSource badClaimSource "asSpecification" = false := by native_decide

/-- `law` is no longer a spec clause: it names an ENFORCED predicate (GPT-6 row G), and a
property nothing checks is a `claim`. The old spelling refuses at parse, never reinterpreted. -/
def lawKeywordSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\n" ++
  "spec Start for Counter:\n  law positive: self.n == 41n\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Counter>:\n  Start\n"

theorem law_keyword_refused : acceptsSource lawKeywordSource "asSpecification" = false := by native_decide

def wrongTargetSource : String :=
  "edition ObjectiveBend 1\nrecord Counter:\n  n: Nat\nrecord Other:\n  n: Nat\n  m: Nat\n" ++
  "spec Start for Counter:\n  def n() -> Nat:\n    41n\n" ++
  "def asSpecification() -> Specification<Other>:\n  Start\n"

theorem wrong_target_refused : acceptsSource wrongTargetSource "asSpecification" = false := by native_decide

/-! ## The open inherited row of a closed spec (OB-LTUO LT2 D3)

`fix` over declared plain specs with a seed that is not a whole target instantiates each
layer at the row actually beneath it and discharges the target at the end. -/

def reviewSpecs : String :=
  "edition ObjectiveBend 1\nrecord Review:\n  review(value: Nat) -> Nat\n  twice(value: Nat) -> Nat\n" ++
  "spec Base for Review:\n  def review(value: Nat) -> Nat:\n    value + 1n\n" ++
  "spec Twice for Review:\n  requires review(value: Nat) -> Nat\n  def twice(value: Nat) -> Nat:\n    self.review(self.review(value))\n" ++
  "spec Augmented for Review:\n  def review(value: Nat) -> Nat:\n    super.review(value) + 1n\n"

/-- LTUO probe W05: no placeholder seed. -/
theorem empty_seed_accepted :
    acceptsSource (reviewSpecs ++ "def run() -> Nat:\n  fix(compose(Base, Twice, Augmented), {}).twice(3n)\n") "run" = true := by
  native_decide

/-- A target member nobody provides is refused (W06's shape: Twice's requirement unmet). -/
theorem unprovided_requirement_refused :
    acceptsSource (reviewSpecs ++ "def run() -> Nat:\n  fix(compose(Twice, Augmented), {}).twice(3n)\n") "run" = false := by
  native_decide

/-- A `super` read with nothing beneath it is refused. -/
theorem inherited_unprovided_refused :
    acceptsSource (reviewSpecs ++ "def run() -> Nat:\n  fix(compose(Augmented, Base, Twice), {}).twice(3n)\n") "run" = false := by
  native_decide

/-- A requirement at another type than the target's member is refused (W07). -/
theorem requires_signature_refused :
    acceptsSource ("edition ObjectiveBend 1\nrecord R:\n  review(value: Nat) -> Nat\n" ++
      "spec S for R:\n  requires review(value: String) -> Nat\n  def review(value: Nat) -> Nat:\n    value\n" ++
      "def run() -> Nat:\n  fix(S, {}).review(1n)\n") "run" = false := by
  native_decide

/-! ## Open declarations over Self and Super (OB-LTUO LT2 step 3b) -/

def fourthFieldSource : String :=
  "edition ObjectiveBend 1\nrecord X:\n  x: Nat\nrecord XY:\n  x: Nat\n  y: Nat\n" ++
  "record XYZW:\n  x: Nat\n  y: Nat\n  z: Nat\n  w: Nat\n" ++
  "extension AddY[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:\n" ++
  "  extend(super, {y: 2n * self.x})\n" ++
  "extension AddZW(self: XYZW, super: XY) -> XYZW:\n  extend(super, {z: self.y, w: self.z + 1n})\n" ++
  "def run() -> Nat:\n  fix(compose(AddY, AddZW), {x: 5n}).w\n"

/-- An extension written over what it uses is reused at a self it never named (W09b). -/
theorem open_extension_reused_accepted : acceptsSource fourthFieldSource "run" = true := by native_decide

def heavierSpec : String :=
  "spec Heavier[Self has {weight: Nat, heavier(other: Self) -> Self}, Super has {weight: Nat}]:\n" ++
  "  def heavier(other: Self) -> Self:\n    if other.weight <= self.weight then self else other\n"

/-- An F-bounded binary method closes at a recursive record (W10). -/
theorem binary_self_accepted :
    acceptsSource ("edition ObjectiveBend 1\nrecord Node:\n  weight: Nat\n  heavier(other: Node) -> Node\n" ++
      heavierSpec ++ "def node(n: Nat) -> Node:\n  fix(Heavier, {weight: n})\n") "node" = true := by native_decide

/-- ... and is refused where the self's method has another type (the F-bound is discharged). -/
theorem f_bound_mismatch_refused :
    acceptsSource ("edition ObjectiveBend 1\nrecord Pair:\n  weight: Nat\n  heavier(other: Nat) -> Pair\n" ++
      heavierSpec ++ "def pair(n: Nat) -> Pair:\n  fix(Heavier, {weight: n})\n") "pair" = false := by native_decide

/-- A template is checked against its binder alone: reading an undeclared self member refuses. -/
theorem unbound_self_member_refused :
    acceptsSource ("edition ObjectiveBend 1\n" ++
      "extension Bad[Self has {x: Nat}, Super has {x: Nat}](self: Self, super: Super) -> Super with {y: Nat}:\n" ++
      "  extend(super, {y: self.z})\ndef zero() -> Nat:\n  0n\n") "zero" = false := by native_decide

/-- The built-in module declaring `SpecMeta`/`SpecClaims` is Objective Bend source the
front end's own parser reads. -/
theorem builtin_parses : ObjectiveBendElaborate.builtinModule.toBool = true := by native_decide

#assert_axioms composeTy_closed composeTy_fold_closed shareableUnder_of_shareable metaAssumptions_valid
  provenance_typed compose_wrapper_typed
#assert_compiled twice_accepted
#assert_compiled claim_spec_accepted
#assert_compiled non_boolean_claim_refused
#assert_compiled law_keyword_refused
#assert_compiled wrong_target_refused
#assert_compiled builtin_parses
#assert_compiled empty_seed_accepted
#assert_compiled unprovided_requirement_refused
#assert_compiled inherited_unprovided_refused
#assert_compiled requires_signature_refused
#assert_compiled open_extension_reused_accepted
#assert_compiled binary_self_accepted
#assert_compiled f_bound_mismatch_refused
#assert_compiled unbound_self_member_refused
end Minidregg.Compiler.ObjectiveBendSpecificationClosure
