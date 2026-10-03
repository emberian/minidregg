import Theory.ObjectiveBendTypes
import Theory.ObjectiveBendOpenRecursion
namespace Minidregg.Theory.ObjectiveBendTyping
open ObjectiveBendTypes ObjectiveBendOpenRecursion
set_option autoImplicit false

structure Assumptions where
  bounds : Bounds := []
  shareableVariables : List Nat := []

/-- Finite guarded shareability premises are checked from the declared bounds.
A recursive immutable row may refer to itself; a custody/once member rejects
its shareability even when hidden under that recursive row. -/
def Assumptions.valid (assumptions : Assumptions) : Bool :=
  assumptions.shareableVariables.all (fun index =>
    match assumptions.bounds.lookup index with
    | none => false
    | some bound => bound.shareableUnder assumptions.shareableVariables)

/-- Annotated recursive aliases unfold one declared head only. This explicit
fragment supports the generated global-record knot without an arbitrary subtype
oracle or unrestricted recursive definitional conversion. -/
def sameType (assumptions : Assumptions) (actual expected : Ty) : Bool :=
  actual.canonical == expected.canonical ||
    (match actual with
      | .variable index => (assumptions.bounds.lookup index).map Ty.canonical == some expected.canonical
      | _ => false) ||
    (match expected with
      | .variable index => (assumptions.bounds.lookup index).map Ty.canonical == some actual.canonical
      | _ => false)

/-- Source positions address the annotation of each actual lambda. Missing
annotations are refused, not guessed or silently replaced by Data types. -/
abbrev Annotations := List Nat → Option LambdaAnnotation
structure AnnotatedTerm where
  term : Term
  annotations : Annotations
  assumptions : Assumptions := {}
def AnnotatedTerm.erase (source : AnnotatedTerm) : Term := source.term

def callable : Ty → Ty
  | .specification _ extension => callable extension
  | other => other

def reusableAllowed (assumptions : Assumptions) (reuse : Reuse)
    (context : Context) (uses : Uses) : Bool :=
  reuse != .reusable || reusableCaptures assumptions.shareableVariables context uses

def argumentAllowed (assumptions : Assumptions) (quantity : Quantity)
    (context : Context) (type : Ty) (uses : Uses) : Bool :=
  quantity != .unrestricted ||
    (type.shareableUnder assumptions.shareableVariables &&
      reusableCaptures assumptions.shareableVariables context uses)

def overlay : Ty → Ty → Ty
  | .field name member rest, inherited => .field name member (overlay rest inherited)
  | _, inherited => inherited

def primitiveTypes : Primitive → Ty × Ty
  | .add | .multiply => (.natural, .natural)
  | .equal => (.natural, .boolean)
  | .conjunction => (.boolean, .boolean)

def literalType (_value : String) : Ty := .label

mutual
/-- A derivation over the independent runtime syntax. This judges partial
computations only: Fix is not evaluated by Lean's definitional conversion. -/
inductive PartialTyping (assumptions : Assumptions) : Context → Term → Ty → Uses → Prop where
  | bound {context : Context} {index : Nat} {binding : Binding} :
      context[index]? = some binding →
      PartialTyping assumptions context (.bound index) binding.type (variableUses context index)
  | natural (context : Context) (value : Nat) :
      PartialTyping assumptions context (.nat value) .natural (zeroUses context)
  | boolean (context : Context) (value : Bool) :
      PartialTyping assumptions context (.boolean value) .boolean (zeroUses context)
  | label (context : Context) (value : String) :
      PartialTyping assumptions context (.label value) (literalType value) (zeroUses context)
  | lambda {context : Context} {body : Term} {annotation : LambdaAnnotation} {uses : Uses} :
      PartialTyping assumptions (⟨annotation.domain, annotation.parameter⟩ :: context)
        body annotation.codomain uses →
      safeUses (⟨annotation.domain, annotation.parameter⟩ :: context) uses = true →
      validContext assumptions.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: context) = true →
      reusableAllowed assumptions annotation.reuse context uses.tail = true →
      PartialTyping assumptions context (.lam body)
        (.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain) uses.tail
  | conversion {context : Context} {term : Term} {actual expected : Ty} {uses : Uses} :
      PartialTyping assumptions context term actual uses → sameType assumptions actual expected = true →
      PartialTyping assumptions context term expected uses
  | application {context : Context} {function argument : Term} {functionType argumentType domain codomain : Ty}
      {functionUses argumentUses : Uses} {reuse : Reuse} {quantity : Quantity} :
      PartialTyping assumptions context function functionType functionUses →
      PartialTyping assumptions context argument argumentType argumentUses →
      callable functionType = .arrow reuse quantity domain codomain → argumentType = domain →
      argumentAllowed assumptions quantity context argumentType argumentUses = true →
      PartialTyping assumptions context (.app function argument) codomain (addUses functionUses argumentUses)
  | record {context : Context} {fields : List (String × Term)} {row : Ty} {uses : Uses} :
      FieldsTyping assumptions context fields row uses →
      PartialTyping assumptions context (.record fields) row uses
  | get {context : Context} {target : Term} {targetType member : Ty} {uses : Uses} {name : String} {fuel : Nat} :
      PartialTyping assumptions context target targetType uses →
      targetType.lookup assumptions.bounds fuel name = some member →
      PartialTyping assumptions context (.get target name) member uses
  | extend {context : Context} {target : Term} {fields : List (String × Term)}
      {targetType row : Ty} {targetUses fieldUses : Uses} :
      PartialTyping assumptions context target targetType targetUses →
      FieldsTyping assumptions context fields row fieldUses →
      targetType.isRow assumptions.bounds 64 = true →
      PartialTyping assumptions context (.extend target fields) (overlay row targetType) (addUses targetUses fieldUses)
  | specification {context : Context} {metadata extension : Term} {metadataType extensionType : Ty} {mu eu : Uses} :
      PartialTyping assumptions context metadata metadataType mu →
      PartialTyping assumptions context extension extensionType eu →
      PartialTyping assumptions context (.specification metadata extension)
        (.specification metadataType extensionType) (addUses mu eu)
  | prototype {context : Context} {spec target : Term} {specType targetType : Ty} {su tu : Uses} :
      PartialTyping assumptions context spec specType su → PartialTyping assumptions context target targetType tu →
      PartialTyping assumptions context (.prototype spec target) (.prototype specType targetType) (addUses su tu)
  | reflect {context : Context} {target : Term} {specType targetType : Ty} {uses : Uses} :
      PartialTyping assumptions context target (.prototype specType targetType) uses →
      PartialTyping assumptions context (.reflect target) specType uses
  | metadata {context : Context} {target : Term} {metadataType extensionType : Ty} {uses : Uses} :
      PartialTyping assumptions context target (.specification metadataType extensionType) uses →
      PartialTyping assumptions context (.metadata target) metadataType uses
  | project {context : Context} {target : Term} {specType targetType : Ty} {uses : Uses} :
      PartialTyping assumptions context target (.prototype specType targetType) uses →
      PartialTyping assumptions context (.project target) targetType uses
  | mix {context : Context} {lower upper : Term} {lowerType upperType self inherited middle provided : Ty} {lu uu : Uses} :
      PartialTyping assumptions context lower lowerType lu →
      PartialTyping assumptions context upper upperType uu →
      callable lowerType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle) →
      callable upperType = .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted middle provided) →
      reusableCaptures assumptions.shareableVariables context (addUses lu uu) = true →
      self.shareableUnder assumptions.shareableVariables = true →
      inherited.shareableUnder assumptions.shareableVariables = true →
      middle.shareableUnder assumptions.shareableVariables = true →
      PartialTyping assumptions context (.mix lower upper)
        (.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided)) (addUses lu uu)
  | fix {context : Context} {spec inheritedTerm : Term} {specType inherited target : Ty} {su iu : Uses} :
      PartialTyping assumptions context spec specType su →
      callable specType = .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited target) →
      PartialTyping assumptions context inheritedTerm inherited iu →
      target.shareableUnder assumptions.shareableVariables = true →
      argumentAllowed assumptions .unrestricted context inherited iu = true →
      reusableCaptures assumptions.shareableVariables context su = true →
      PartialTyping assumptions context (.fix spec inheritedTerm) target (addUses su iu)
  | binary {context : Context} {primitive : Primitive} {left right : Term} {input output : Ty} {lu ru : Uses} :
      primitiveTypes primitive = (input, output) →
      PartialTyping assumptions context left input lu → PartialTyping assumptions context right input ru →
      PartialTyping assumptions context (.binary primitive left right) output (addUses lu ru)
  | ifZero {context : Context} {value zero successor : Term} {result : Ty} {vu zu su : Uses} :
      PartialTyping assumptions context value .natural vu → PartialTyping assumptions context zero result zu →
      PartialTyping assumptions (⟨.natural,.unrestricted⟩ :: context) successor result su →
      safeUses (⟨.natural,.unrestricted⟩ :: context) su = true →
      PartialTyping assumptions context (.ifZero value zero successor) result (addUses vu (addUses zu su.tail))
inductive FieldsTyping (assumptions : Assumptions) : Context → List (String × Term) → Ty → Uses → Prop where
  | nil (context : Context) : FieldsTyping assumptions context [] .emptyRow (zeroUses context)
  | cons {context : Context} {name : String} {body : Term} {rest : List (String × Term)} {type row : Ty} {bu ru : Uses} :
      PartialTyping assumptions context body type bu → FieldsTyping assumptions context rest row ru →
      FieldsTyping assumptions context ((name,body) :: rest) (.field name type row) (addUses bu ru)
end

structure Inferred (assumptions : Assumptions) (context : Context) (term : Term) where
  type : Ty
  uses : Uses
  derivation : PartialTyping assumptions context term type uses
structure InferredFields (assumptions : Assumptions) (context : Context) (fields : List (String × Term)) where
  type : Ty
  uses : Uses
  derivation : FieldsTyping assumptions context fields type uses

mutual
/-- Fuel bounds only the checker, never the runtime or meaning of Fix. Failure
means outside this annotated fragment/budget; it is not a proof of ill-typing in
any stronger language. The result carries a runtime-syntax derivation. -/
def infer (assumptions : Assumptions) (annotations : Annotations) (context : Context)
    (position : List Nat) : Nat → (term : Term) → Option (Inferred assumptions context term)
  | 0, _ => none
  | fuel + 1, .bound index => do
      let binding ← context[index]?
      if h : context[index]? = some binding then
        some ⟨binding.type, variableUses context index, .bound h⟩ else none
  | _ + 1, .nat value => some ⟨.natural, zeroUses context, .natural context value⟩
  | _ + 1, .boolean value => some ⟨.boolean, zeroUses context, .boolean context value⟩
  | _ + 1, .label value => some ⟨literalType value, zeroUses context, .label context value⟩
  | fuel + 1, .lam body => do
      let annotation ← annotations position
      let result ← infer assumptions annotations (⟨annotation.domain, annotation.parameter⟩ :: context) (position ++ [0]) fuel body
      if ht : sameType assumptions result.type annotation.codomain = true then
        if hs : safeUses (⟨annotation.domain, annotation.parameter⟩ :: context) result.uses = true then
          if hv : validContext assumptions.shareableVariables (⟨annotation.domain, annotation.parameter⟩ :: context) = true then
            if hc : reusableAllowed assumptions annotation.reuse context result.uses.tail = true then
              some ⟨.arrow annotation.reuse annotation.parameter annotation.domain annotation.codomain, result.uses.tail,
                .lambda (.conversion result.derivation ht) hs hv hc⟩
            else none
          else none
        else none
      else none
  | fuel + 1, .app function argument => do
      let fn ← infer assumptions annotations context (position ++ [0]) fuel function
      let arg ← infer assumptions annotations context (position ++ [1]) fuel argument
      match hft : callable fn.type with
      | .arrow reuse quantity domain codomain =>
          if hat : sameType assumptions arg.type domain = true then
            if hc : argumentAllowed assumptions quantity context domain arg.uses = true then
              some ⟨codomain, addUses fn.uses arg.uses, .application fn.derivation (.conversion arg.derivation hat) hft rfl hc⟩
            else none
          else none
      | _ => none
  | fuel + 1, .record fields => do
      let result ← inferFields assumptions annotations context position 0 fuel fields
      some ⟨result.type, result.uses, .record result.derivation⟩
  | fuel + 1, .get target name => do
      let result ← infer assumptions annotations context (position ++ [0]) fuel target
      let member ← result.type.lookup assumptions.bounds (fuel + 1) name
      if hm : result.type.lookup assumptions.bounds (fuel + 1) name = some member then
        some ⟨member, result.uses, .get result.derivation hm⟩ else none
  | fuel + 1, .extend target fields => do
      let prior ← infer assumptions annotations context (position ++ [0]) fuel target
      let members ← inferFields assumptions annotations context (position ++ [1]) 0 fuel fields
      if hr : prior.type.isRow assumptions.bounds 64 = true then
        some ⟨overlay members.type prior.type, addUses prior.uses members.uses,
          .extend prior.derivation members.derivation hr⟩ else none
  | fuel + 1, .specification metadata extension => do
      let descriptor ← infer assumptions annotations context (position ++ [0]) fuel metadata
      let body ← infer assumptions annotations context (position ++ [1]) fuel extension
      some ⟨.specification descriptor.type body.type, addUses descriptor.uses body.uses,
        .specification descriptor.derivation body.derivation⟩
  | fuel + 1, .prototype spec target => do
      let code ← infer assumptions annotations context (position ++ [0]) fuel spec
      let value ← infer assumptions annotations context (position ++ [1]) fuel target
      some ⟨.prototype code.type value.type, addUses code.uses value.uses, .prototype code.derivation value.derivation⟩
  | fuel + 1, .reflect target => do
      let result ← infer assumptions annotations context (position ++ [0]) fuel target
      match ht : result.type with
      | .prototype specType targetType =>
          some ⟨specType, result.uses, .reflect (ht ▸ result.derivation)⟩
      | _ => none
  | fuel + 1, .metadata target => do
      let result ← infer assumptions annotations context (position ++ [0]) fuel target
      match ht : result.type with
      | .specification metadataType extensionType =>
          some ⟨metadataType, result.uses, .metadata (ht ▸ result.derivation)⟩
      | _ => none
  | fuel + 1, .project target => do
      let result ← infer assumptions annotations context (position ++ [0]) fuel target
      match ht : result.type with
      | .prototype specType targetType =>
          some ⟨targetType, result.uses, .project (ht ▸ result.derivation)⟩
      | _ => none
  | fuel + 1, .mix lower upper => do
      let first ← infer assumptions annotations context (position ++ [0]) fuel lower
      let second ← infer assumptions annotations context (position ++ [1]) fuel upper
      match ht : callable first.type, hs : callable second.type with
      | .arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited middle),
        .arrow .reusable .unrestricted self' (.arrow .reusable .unrestricted middle' provided) =>
          if hc : self' = self then
            if hm : middle' = middle then
              if captures : reusableCaptures assumptions.shareableVariables context (addUses first.uses second.uses) = true then
                if shareSelf : self.shareableUnder assumptions.shareableVariables = true then
                  if shareInherited : inherited.shareableUnder assumptions.shareableVariables = true then
                    if shareMiddle : middle.shareableUnder assumptions.shareableVariables = true then
                      some ⟨.arrow .reusable .unrestricted self (.arrow .reusable .unrestricted inherited provided),
                        addUses first.uses second.uses,
                        .mix first.derivation second.derivation ht (by simpa [hc, hm] using hs)
                          captures shareSelf shareInherited shareMiddle⟩
                    else none
                  else none
                else none
              else none
            else none
          else none
      | _, _ => none
  | fuel + 1, .fix spec inheritedTerm => do
      let code ← infer assumptions annotations context (position ++ [0]) fuel spec
      let base ← infer assumptions annotations context (position ++ [1]) fuel inheritedTerm
      match ht : callable code.type with
      | .arrow .reusable .unrestricted target (.arrow .reusable .unrestricted inherited output) =>
          if ho : output = target then
            if hb : sameType assumptions base.type inherited = true then
              if hs : target.shareableUnder assumptions.shareableVariables = true then
                if ha : argumentAllowed assumptions .unrestricted context inherited base.uses = true then
                  if hc : reusableCaptures assumptions.shareableVariables context code.uses = true then
                    some ⟨target, addUses code.uses base.uses,
                      .fix code.derivation (by simpa [ho] using ht) (.conversion base.derivation hb) hs ha hc⟩
                  else none
                else none
              else none
            else none
          else none
      | _ => none
  | fuel + 1, .binary primitive left right => do
      let l ← infer assumptions annotations context (position ++ [0]) fuel left
      let r ← infer assumptions annotations context (position ++ [1]) fuel right
      if hl : l.type = (primitiveTypes primitive).1 then
        if hr : r.type = (primitiveTypes primitive).1 then
          some ⟨(primitiveTypes primitive).2, addUses l.uses r.uses,
            .binary (Prod.eta _) (hl ▸ l.derivation) (hr ▸ r.derivation)⟩
        else none
      else none
  | fuel + 1, .ifZero value zero successor => do
      let condition ← infer assumptions annotations context (position ++ [0]) fuel value
      let z ← infer assumptions annotations context (position ++ [1]) fuel zero
      let s ← infer assumptions annotations (⟨.natural,.unrestricted⟩ :: context) (position ++ [2]) fuel successor
      if ht : condition.type = .natural then
        if hb : s.type = z.type then
          if hu : safeUses (⟨.natural,.unrestricted⟩ :: context) s.uses = true then
            some ⟨z.type, addUses condition.uses (addUses z.uses s.uses.tail),
              .ifZero (ht ▸ condition.derivation) z.derivation (hb ▸ s.derivation) hu⟩
          else none
        else none
      else none

def inferFields (assumptions : Assumptions) (annotations : Annotations) (context : Context)
    (position : List Nat) (index : Nat) : Nat → (fields : List (String × Term)) → Option (InferredFields assumptions context fields)
  | 0, _ => none
  | _ + 1, [] => some ⟨.emptyRow, zeroUses context, .nil context⟩
  | fuel + 1, (name,body) :: rest => do
      let first ← infer assumptions annotations context (position ++ [index]) fuel body
      let later ← inferFields assumptions annotations context position (index + 1) fuel rest
      some ⟨.field name first.type later.type, addUses first.uses later.uses, .cons first.derivation later.derivation⟩
end

structure Checked (source : AnnotatedTerm) (context : Context) where
  type : Ty
  uses : Uses
  derivation : PartialTyping source.assumptions context source.erase type uses
  safe : safeUses context uses = true
  contextValid : validContext source.assumptions.shareableVariables context = true
  assumptionsValid : source.assumptions.valid = true

def check (source : AnnotatedTerm) (context : Context) (fuel : Nat) : Option (Checked source context) := do
  let result ← infer source.assumptions source.annotations context [] fuel source.term
  if hs : safeUses context result.uses = true then
    if hv : validContext source.assumptions.shareableVariables context = true then
      if ha : source.assumptions.valid = true then
        some ⟨result.type, result.uses, result.derivation, hs, hv, ha⟩ else none
    else none
  else none

/-- Successful checking constructs a derivation for exactly the consumed runtime
term, together with capture/usage premises. This is not preservation/adequacy. -/
theorem checked_erasure (source : AnnotatedTerm) (context : Context)
    (result : Checked source context) :
    PartialTyping source.assumptions context source.erase result.type result.uses := result.derivation

/-- Total proof judgments inhabit Lean Prop, including laws of partial runtime
syntax. No Typing constructor can convert arbitrary Fix into a total proof. -/
def TotalProof (law : Prop) := law

theorem partial_beta_law (body argument : Term) :
    TotalProof (Step (.app (.lam body) argument) (instantiate body argument)) := .beta body argument

/-- Inherited/required/provided annotations all feed checking. Requirements are
finite structural row contracts, independently checked against future Self;
provider type is the heterogeneous two-arrow family, not a subtype oracle. -/
structure CheckedExtension (source : AnnotatedTerm) (context : Context)
    (family : ExtensionFamilies) (futureSelf : Ty) where
  checked : Checked source context
  shape : checked.type = family.functionType futureSelf
  required : futureSelf.supports source.assumptions.bounds 64 family.required = true

def checkExtension (source : AnnotatedTerm) (context : Context) (fuel : Nat)
    (family : ExtensionFamilies) (futureSelf : Ty) : Option (CheckedExtension source context family futureSelf) := do
  let result ← check source context fuel
  if ht : result.type = family.functionType futureSelf then
    if hr : futureSelf.supports source.assumptions.bounds 64 family.required = true then
      some ⟨result,ht,hr⟩ else none
  else none

/-- Reusability is justified by a checked capture premise, not by the immutable
shape of a closure/record wrapper. This holds for every lambda derivation. -/
theorem reusable_lambda_capture_rule {assumptions : Assumptions} {context : Context}
    {body : Term} {annotation : LambdaAnnotation} {uses : Uses}
    (_bodyTyped : PartialTyping assumptions (⟨annotation.domain,annotation.parameter⟩ :: context)
      body annotation.codomain uses)
    (_safe : safeUses (⟨annotation.domain,annotation.parameter⟩ :: context) uses = true)
    (_valid : validContext assumptions.shareableVariables (⟨annotation.domain,annotation.parameter⟩ :: context) = true)
    (captures : reusableAllowed assumptions annotation.reuse context uses.tail = true)
    (reusable : annotation.reuse = .reusable) :
    reusableCaptures assumptions.shareableVariables context uses.tail = true := by
  simpa [reusableAllowed, reusable] using captures

/-- Total logic proves a contextual reduction law despite the discarded
argument being any partial computation, including a divergent Fix. -/
theorem ignores_any_partial_argument (argument : Term) :
    TotalProof (Evaluates (.app (.lam (.nat 7)) argument) (.nat 7)) :=
  by
    refine ⟨.next (.beta _ _) ?_, .natural 7⟩
    simpa [instantiate, Term.substitute] using (Steps.refl (.nat 7))

def reusableNaturalCapture : AnnotatedTerm :=
  ⟨.lam (.bound 1), fun _ => some ⟨.natural,.natural,.erased,.reusable⟩, {}⟩
def custodyCapture (reuse : Reuse) : AnnotatedTerm :=
  ⟨.lam (.bound 1), fun _ => some ⟨.natural,.custody 17,.erased,reuse⟩, {}⟩

theorem reusable_lexical_capture_accepted :
    (check reusableNaturalCapture [⟨.natural,.unrestricted⟩] 8).isSome = true := by decide

theorem custody_in_reusable_closure_refused :
    (check (custodyCapture .reusable) [⟨.custody 17,.linear⟩] 8).isNone = true := by decide

theorem custody_in_once_closure_accepted :
    (check (custodyCapture .once) [⟨.custody 17,.linear⟩] 8).isSome = true := by decide

def duplicateAffine : AnnotatedTerm :=
  ⟨.binary .add (.bound 0) (.bound 0), fun _ => none, {}⟩
theorem duplicate_affine_refused :
    (check duplicateAffine [⟨.natural,.affine⟩] 8).isNone = true := by decide

def hiddenCustody : AnnotatedTerm := ⟨.bound 0, fun _ => none, {}⟩
theorem record_wrapper_does_not_hide_custody :
    (check hiddenCustody [⟨.field "authority" (.custody 17) .emptyRow,.unrestricted⟩] 8).isNone = true := by decide

/-- Independently typed Unit-row→Nat and Nat→Label extensions compose under
one final Nat self; neither targets only records nor homogeneous endomorphisms. -/
def heterogeneousSource : AnnotatedTerm :=
  ⟨.mix (.lam (.lam (.nat 7))) (.lam (.lam (.label "done"))),
    fun position =>
      if position = [0] then some ⟨.natural,.arrow .reusable .unrestricted .emptyRow .natural,.unrestricted,.reusable⟩
      else if position = [0,0] then some ⟨.emptyRow,.natural,.unrestricted,.reusable⟩
      else if position = [1] then some ⟨.natural,.arrow .reusable .unrestricted .natural .label,.unrestricted,.reusable⟩
      else if position = [1,0] then some ⟨.natural,.label,.unrestricted,.reusable⟩ else none, {}⟩
theorem heterogeneous_runtime_mix_accepted :
    (check heterogeneousSource [] 16).isSome = true := by decide

/-- Symbolic future Self has a self-dependent binary method bound; future Super
is passed through as an unknown row and receives a new field. No closed record
or fixed C→V(C) is substituted into this independent source derivation. -/
def futureRowSource : AnnotatedTerm :=
  ⟨.lam (.lam (.extend (.bound 0) [("answer",.nat 42)])),
    fun position =>
      if position = [] then some ⟨.variable 0,
        .arrow .reusable .unrestricted (.variable 1) (.field "answer" .natural (.variable 1)),.unrestricted,.reusable⟩
      else if position = [0] then some ⟨.variable 1,.field "answer" .natural (.variable 1),.unrestricted,.reusable⟩
      else none,
    ⟨[(0,.field "combine" (.arrow .reusable .unrestricted (.variable 0) (.variable 0)) .emptyRow),
       (1,.emptyRow)], [0,1]⟩⟩

theorem independently_checked_future_rows :
    (check futureRowSource [] 16).isSome = true := by decide

def futureRowChecked : Checked futureRowSource [] :=
  (check futureRowSource [] 16).get independently_checked_future_rows

/-- This source can be separately instantiated at EVERY future Self/Super type
in the declared shareable fragment. Unknown members stay in Super itself, not
in a fixed closed record chosen during extension compilation. -/
def futureRowInstantiation (self super : Ty) : AnnotatedTerm :=
  ⟨futureRowSource.term, fun position =>
    if position = [] then some ⟨self,
      .arrow .reusable .unrestricted super (.field "answer" .natural super),.unrestricted,.reusable⟩
    else if position = [0] then some ⟨super,.field "answer" .natural super,.unrestricted,.reusable⟩
    else none, {}⟩

theorem future_row_instantiation_accepted (self super : Ty)
    (selfShareable : self.shareable = true) (superShareable : super.shareable = true)
    (superRow : super.isRow [] 64 = true) :
    (check (futureRowInstantiation self super) [] 16).isSome = true := by
  simp [check, infer, inferFields, futureRowInstantiation, futureRowSource,
    sameType, Assumptions.valid, overlay, zeroUses, variableUses, addUses, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures,
    List.range_succ, List.zipWith, selfShareable, superShareable, superRow]

/-- A total law provider proves a law ABOUT the partial runtime term; source
law names alone cannot construct this evidence. Compatible retention is chosen
explicitly rather than asserted as a universal consequence of inheritance. -/
structure LawProvider (source : AnnotatedTerm) (law : Term → Prop) where
  evidence : law source.erase

structure RetainedContracts (source : AnnotatedTerm) (laws : List (Term → Prop)) where
  providers : ∀ law ∈ laws, LawProvider source law

def FutureRowTyped (source : Ty → Ty → AnnotatedTerm) : Prop :=
  ∀ self super, self.shareable = true → super.shareable = true → super.isRow [] 64 = true →
    ∃ checked : Checked (source self super) [],
      checked.type = .arrow .reusable .unrestricted self
        (.arrow .reusable .unrestricted super (.field "answer" .natural super))


def futureRowInstanceChecked (self super : Ty)
    (selfShareable : self.shareable = true) (superShareable : super.shareable = true)
    (superRow : super.isRow [] 64 = true) : Checked (futureRowInstantiation self super) [] :=
  (check (futureRowInstantiation self super) [] 16).get
    (future_row_instantiation_accepted self super selfShareable superShareable superRow)

theorem future_row_typed : FutureRowTyped futureRowInstantiation := by
  intro self super hs ht hr
  refine ⟨futureRowInstanceChecked self super hs ht hr, ?_⟩
  simp [futureRowInstanceChecked, check, infer, inferFields, futureRowInstantiation,
    futureRowSource, sameType, Assumptions.valid, overlay, zeroUses, variableUses, addUses, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures,
    List.range_succ, List.zipWith, hs, ht, hr]

/-- Independently authored code changes a self-sensitive method type at every
future Self instantiation, including negative arrow occurrences. -/
def futureBinaryInstantiation (self super : Ty) : AnnotatedTerm :=
  ⟨.lam (.lam (.extend (.bound 0) [("combine",.lam (.bound 0))])),
    fun position =>
      if position = [] then some ⟨self,
        .arrow .reusable .unrestricted super
          (.field "combine" (.arrow .reusable .unrestricted self self) super),.unrestricted,.reusable⟩
      else if position = [0] then some ⟨super,
        .field "combine" (.arrow .reusable .unrestricted self self) super,.unrestricted,.reusable⟩
      else if position = [0,0,1,0] then some ⟨self,self,.unrestricted,.reusable⟩
      else none, {}⟩

theorem future_binary_instantiation_accepted (self super : Ty)
    (selfShareable : self.shareable = true) (superShareable : super.shareable = true)
    (superRow : super.isRow [] 64 = true) :
    (check (futureBinaryInstantiation self super) [] 20).isSome = true := by
  simp [check, infer, inferFields, futureBinaryInstantiation, sameType, Assumptions.valid, overlay,
    zeroUses, variableUses, addUses, safeUses, safeQuantity,
    validContext, reusableAllowed, reusableCaptures,
    List.range_succ, List.zipWith, selfShareable, superShareable, superRow]

def scalarExtend : AnnotatedTerm :=
  ⟨.extend (.nat 3) [("answer",.nat 42)], fun _ => none, {}⟩
theorem scalar_record_extend_refused : (check scalarExtend [] 8).isNone = true := by decide


/-- Mix's generated reusable closure owns both captured operands. The previous
rule accepted this affine free binding despite ordinary lambda refusing it. -/
def extensionNaturalType : Ty :=
  .arrow .reusable .unrestricted .natural (.arrow .reusable .unrestricted .natural .natural)
def capturedMixSource : AnnotatedTerm :=
  ⟨.mix (.bound 0) (.lam (.lam (.bound 0))), fun position =>
    if position = [1] then some ⟨.natural,.arrow .reusable .unrestricted .natural .natural,.unrestricted,.reusable⟩
    else if position = [1,0] then some ⟨.natural,.natural,.unrestricted,.reusable⟩ else none, {}⟩
theorem affine_mix_capture_refused :
    (check capturedMixSource [⟨extensionNaturalType,.affine⟩] 16).isNone = true := by decide

theorem reusable_mix_capture_accepted :
    (check capturedMixSource [⟨extensionNaturalType,.unrestricted⟩] 16).isSome = true := by decide

def recursiveGlobalKnot : AnnotatedTerm :=
  ⟨.get (.fix (.lam (.lam (.record [("answer",.nat 42)]))) (.record [])) "answer",
    fun position =>
      if position = [0,0] then some ⟨.variable 0,
        .arrow .reusable .unrestricted .emptyRow (.variable 0),.unrestricted,.reusable⟩
      else if position = [0,0,0] then some ⟨.emptyRow,.variable 0,.unrestricted,.reusable⟩
      else none,
    ⟨[(0,.field "answer" .natural .emptyRow)],[0]⟩⟩
theorem recursive_global_knot_accepted : (check recursiveGlobalKnot [] 16).isSome = true := by decide

def dishonestRecursiveCustody : AnnotatedTerm :=
  ⟨.nat 7, fun _ => none, ⟨[(0,.field "authority" (.custody 17) (.variable 0))],[0]⟩⟩
theorem recursive_alias_does_not_hide_custody :
    (check dishonestRecursiveCustody [] 8).isNone = true := by decide

def stringConjunction : AnnotatedTerm :=
  ⟨.binary .conjunction (.label "hello") (.label "world"), fun _ => none, {}⟩
theorem arbitrary_labels_are_not_booleans : (check stringConjunction [] 8).isNone = true := by decide

def reservedStringConjunction : AnnotatedTerm :=
  ⟨.binary .conjunction (.label "true") (.label "false"), fun _ => none, {}⟩
theorem reserved_strings_are_not_booleans :
    (check reservedStringConjunction [] 8).isNone = true := by decide
theorem reserved_string_has_string_type :
    (check ⟨.label "true", fun _ => none, {}⟩ [] 8).map (fun checked => checked.type) = some .label := by decide
theorem explicit_boolean_has_boolean_type :
    (check ⟨.boolean true, fun _ => none, {}⟩ [] 8).map (fun checked => checked.type) = some .boolean := by decide
theorem explicit_boolean_conjunction_accepted :
    (check ⟨.binary .conjunction (.boolean true) (.boolean false), fun _ => none, {}⟩ [] 8).isSome = true := by decide


def independentlyAuthoredFamily : ExtensionFamilies :=
  ⟨.variable 1,
    .field "combine" (.arrow .reusable .unrestricted (.variable 0) (.variable 0)) .emptyRow,
    .field "answer" .natural (.variable 1)⟩

theorem independent_requirements_checked :
    (checkExtension futureRowSource [] 16 independentlyAuthoredFamily (.variable 0)).isSome = true := by decide

def unmetFamily : ExtensionFamilies :=
  { independentlyAuthoredFamily with required := .field "absent" .natural .emptyRow }
theorem absent_future_requirement_refused :
    (checkExtension futureRowSource [] 16 unmetFamily (.variable 0)).isNone = true := by decide


open Lean (Json toJson)

def requireSome {α : Type} (message : String) : Option α → Except String α
  | some value => .ok value
  | none => .error message

def jsonNat (value : Json) : Except String Nat :=
  match value.getNat? with
  | .ok result => .ok result
  | .error _ => do
      let text ← value.getStr?
      let result ← requireSome "canonical natural required" text.toNat?
      if toString result = text then .ok result else .error "canonical natural required"

def decodeQuantity (value : Json) : Except String Quantity := do
  match ← value.getStr? with
  | "erased" => pure .erased | "affine" => pure .affine
  | "linear" => pure .linear | "unrestricted" => pure .unrestricted
  | _ => .error "explicit Objective quantity required"

def decodeReuse (value : Json) : Except String Reuse := do
  match ← value.getStr? with
  | "once" => pure .once | "reusable" => pure .reusable
  | _ => .error "explicit Objective closure reuse required"

def decodeType : Nat → Json → Except String Ty
  | 0, _ => .error "type nesting capacity"
  | fuel + 1, value => do
    match ← value.getObjValAs? String "tag" with
    | "natural" => pure .natural | "label" => pure .label
    | "boolean" => pure .boolean | "emptyRow" => pure .emptyRow
    | "variable" => return .variable (← jsonNat (← value.getObjVal? "index"))
    | "custody" => return .custody (← jsonNat (← value.getObjVal? "identity"))
    | "field" => return (.field (← value.getObjValAs? String "name")
        (← decodeType fuel (← value.getObjVal? "member"))
        (← decodeType fuel (← value.getObjVal? "tail")))
    | "arrow" => return (.arrow (← decodeReuse (← value.getObjVal? "reuse"))
        (← decodeQuantity (← value.getObjVal? "parameter"))
        (← decodeType fuel (← value.getObjVal? "domain"))
        (← decodeType fuel (← value.getObjVal? "codomain")))
    | "specification" => return (.specification
        (← decodeType fuel (← value.getObjVal? "metadata"))
        (← decodeType fuel (← value.getObjVal? "extension")))
    | "prototype" => return (.prototype
        (← decodeType fuel (← value.getObjVal? "spec"))
        (← decodeType fuel (← value.getObjVal? "target")))
    | _ => .error "unknown Objective type constructor"

def decodePrimitive (value : Json) : Except String Primitive := do
  match ← value.getStr? with
  | "add" => pure .add | "multiply" => pure .multiply
  | "equal" => pure .equal | "conjunction" => pure .conjunction
  | _ => .error "unknown Objective primitive"

/-- Decodes exactly the existing world lowerer's runtime core wire; no second
source translator or alternate fixture term is introduced by the type checker. -/
def decodeTerm : Nat → Json → Except String Term
  | 0, _ => .error "term nesting capacity"
  | fuel + 1, value => do
    let sub := fun key => do decodeTerm fuel (← value.getObjVal? key)
    let fields := fun (_ : Unit) => do
      let array ← (← value.getObjVal? "fields").getArr?
      array.toList.mapM fun field => do
        return (← field.getObjValAs? String "name", ← decodeTerm fuel (← field.getObjVal? "value"))
    match ← value.getObjValAs? String "tag" with
    | "bound" => return .bound (← jsonNat (← value.getObjVal? "index"))
    | "nat" => return .nat (← jsonNat (← value.getObjVal? "value"))
    | "boolean" => return .boolean (← value.getObjValAs? Bool "value")
    | "label" => return .label (← value.getObjValAs? String "value")
    | "lam" => return .lam (← sub "body")
    | "app" => return .app (← sub "fn") (← sub "arg")
    | "mix" => return .mix (← sub "lower") (← sub "upper")
    | "fix" => return .fix (← sub "spec") (← sub "seed")
    | "specification" => return .specification (← sub "metadata") (← sub "extension")
    | "prototype" => return .prototype (← sub "spec") (← sub "target")
    | "reflect" => return .reflect (← sub "value")
    | "metadata" => return .metadata (← sub "value")
    | "project" => return .project (← sub "value")
    | "binary" => return .binary (← decodePrimitive (← value.getObjVal? "primitive")) (← sub "left") (← sub "right")
    | "record" => return .record (← fields ())
    | "extend" => return .extend (← sub "inherited") (← fields ())
    | "get" => return .get (← sub "target") (← value.getObjValAs? String "name")
    | "ifZero" => return .ifZero (← sub "value") (← sub "zero") (← sub "successor")
    | _ => .error "unknown Objective runtime constructor"

def decodeLambda (value : Json) : Except String LambdaAnnotation := do
  return ⟨← decodeType 256 (← value.getObjVal? "domain"),
    ← decodeType 256 (← value.getObjVal? "codomain"),
    ← decodeQuantity (← value.getObjVal? "parameter"),
    ← decodeReuse (← value.getObjVal? "reuse")⟩

structure DecodedPacket where
  source : AnnotatedTerm
  context : Context
  fuel : Nat

def decodePacket (value : Json) : Except String DecodedPacket := do
  if (← value.getObjValAs? String "schema") != "dregg.objective-bend.typed-core.v2" then
    throw "Objective typed core edition required"
  let term ← decodeTerm 4096 (← value.getObjVal? "term")
  let annotations ← (← (← value.getObjVal? "annotations").getArr?).toList.mapM fun entry => do
    let path ← (← (← entry.getObjVal? "path").getArr?).toList.mapM jsonNat
    return (path, ← decodeLambda entry)
  if !decide (annotations.map Prod.fst).Nodup then throw "duplicate lambda annotation path"
  let bounds ← (← (← value.getObjVal? "bounds").getArr?).toList.mapM fun entry => do
    return (← jsonNat (← entry.getObjVal? "index"), ← decodeType 256 (← entry.getObjVal? "type"))
  if !decide (bounds.map Prod.fst).Nodup then throw "duplicate future type bound"
  let shareable ← (← (← value.getObjVal? "shareableVariables").getArr?).toList.mapM jsonNat
  if !decide shareable.Nodup then throw "duplicate shareability premise"
  let context ← match value.getObjVal? "context" with
    | .error _ => pure []
    | .ok context => (← context.getArr?).toList.mapM fun entry => do
        return (⟨← decodeType 256 (← entry.getObjVal? "type"),
          ← decodeQuantity (← entry.getObjVal? "quantity")⟩ : Binding)
  let fuel ← match value.getObjVal? "fuel" with
    | .error _ => pure 4096
    | .ok fuel => jsonNat fuel
  if fuel > 16384 then throw "checker fuel capacity"
  return ⟨⟨term, fun path => (annotations.find? (fun entry => entry.1 == path)).map Prod.snd,
      ⟨bounds,shareable⟩⟩,context,fuel⟩

def quantityJson : Quantity → Json
  | .erased => toJson "erased" | .affine => toJson "affine"
  | .linear => toJson "linear" | .unrestricted => toJson "unrestricted"
def reuseJson : Reuse → Json
  | .once => toJson "once" | .reusable => toJson "reusable"

def typeJson : Ty → Json
  | .natural => Json.mkObj [("tag",toJson "natural")]
  | .label => Json.mkObj [("tag",toJson "label")]
  | .boolean => Json.mkObj [("tag",toJson "boolean")]
  | .emptyRow => Json.mkObj [("tag",toJson "emptyRow")]
  | .variable index => Json.mkObj [("tag",toJson "variable"),("index",toJson (toString index))]
  | .custody identity => Json.mkObj [("tag",toJson "custody"),("identity",toJson (toString identity))]
  | .field name member tail => Json.mkObj [("tag",toJson "field"),("name",toJson name),
      ("member",typeJson member),("tail",typeJson tail)]
  | .arrow reuse quantity domain codomain => Json.mkObj [("tag",toJson "arrow"),
      ("reuse",reuseJson reuse),("parameter",quantityJson quantity),
      ("domain",typeJson domain),("codomain",typeJson codomain)]
  | .specification metadata extension => Json.mkObj [("tag",toJson "specification"),
      ("metadata",typeJson metadata),("extension",typeJson extension)]
  | .prototype spec target => Json.mkObj [("tag",toJson "prototype"),
      ("spec",typeJson spec),("target",typeJson target)]

def packetReceipt (value : Json) : Except String Json := do
  let packet ← decodePacket value
  let result ← requireSome "annotated typing/ownership refused or checker budget insufficient"
    (check packet.source packet.context packet.fuel)
  return Json.mkObj [
    ("schema", toJson "dregg.objective-bend.typing-receipt.v1"),
    ("status", toJson "accepted"),
    ("type", typeJson result.type), ("uses", toJson result.uses),
    ("typingScope", toJson "compiled proof-producing annotated partial checker; preservation and demand adequacy separate"),
    ("laws", toJson "undischarged unless independent total law providers are supplied"),
    ("authority", toJson "no current native authority granted")]

/-- Native entry point for the exact core packet produced by the world lowerer.
Its executable result relies on Lean compilation; it is not a kernel certificate
for the parsed bytes or an executor/authority qualification. -/
def checkPacketFile (path : String) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let result := do
    let parsed ← Json.parse input
    packetReceipt parsed
  match result with
  | .ok receipt => IO.println receipt.compress; return 0
  | .error message =>
      IO.eprintln (Json.mkObj [("schema",toJson "dregg.objective-bend.typing-receipt.v1"),
        ("status",toJson "refused"),("stage",toJson "objective-source-type-check"),("message",toJson message)]).compress
      return 2


end Minidregg.Theory.ObjectiveBendTyping
