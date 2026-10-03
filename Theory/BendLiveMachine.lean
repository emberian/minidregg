/- Live Bend execution starts from the pinned source relation, not checker WNF.
This first executable component walks a whole source case tree before exposing
its leaf. Returned witnesses prove source Walk directly. A fixed-heap closure
representation and its circuit/trace lowering remain subsequent refinements. -/
import Theory.BendTTSource
import Theory.AssertAxioms

namespace Minidregg.Theory.BendLiveMachine
open BendTT
open BendTT.Term BendTT.Quan
set_option autoImplicit false

structure CheckedData (term : Term) : Type where
  valid : BendTT.Data term

/-- Runtime Q2 duplication qualification. It traverses only live fields; a
Q0 field may hold arbitrary dead syntax and is never run by this predicate. -/
def checkData : (term : Term) → Option (CheckedData term)
  | Lab _ => some ⟨.lab⟩
  | Rfl => some ⟨.rfl⟩
  | Tup q first second => do
      let tail ← checkData second
      match q with
      | Q0 => some ⟨.tup (by intro impossible; cases impossible) tail.valid⟩
      | Q1 =>
          let head ← checkData first
          some ⟨.tup (fun _ => head.valid) tail.valid⟩
      | Q2 =>
          let head ← checkData first
          some ⟨.tup (fun _ => head.valid) tail.valid⟩
  | _ => none

inductive Refusal where
  | ticks
  | quantity
  | notData
  | stuck
  deriving DecidableEq, Repr

structure CheckedWalk (book : Book) (term : Term) (environment : Env) (args : List Arg) where
  /-- none is a legitimate underapplication, never a partially unfolded leaf. -/
  output : Option Term
  valid : Walk book term environment args output

private theorem bool_false {value : Bool} (notTrue : ¬ value = true) : value = false := by
  cases value <;> simp_all

/-- The bound limits this case walk, separately from the whole invocation's
step/capacity profile. Every successful result carries the exact pinned source
Walk rule. Failure grants neither a runtime value nor a native effect. -/
def walkChecked (book : Book) : (ticks : Nat) → (term : Term) →
    (environment : Env) → (args : List Arg) →
    Except Refusal (CheckedWalk book term environment args)
  | 0, _, _, _ => .error .ticks
  | ticks + 1, term, environment, args =>
      match term, args with
      | App q function (Var index), args =>
        if isNode : Term.node (App q function (Var index)) = true then do
          let next ← walkChecked book ticks function environment
            ((q, Env.sub environment index) :: args)
          pure ⟨next.output, .app isNode next.valid⟩
        else
          .ok ⟨some (Term.spine (Term.sub (Env.sub environment)
            (App q function (Var index))) args), .done (bool_false isNode)⟩
      | term, [] =>
        if takes : Term.takes term = true then
          .ok ⟨none, .need takes⟩
        else if leaf : Term.node term = false then
          .ok ⟨some (Term.sub (Env.sub environment) term), .done leaf⟩
        else .error .stuck
      | Lam p body, (q, value) :: args =>
        if compatible : p.live = q.live then
          if copied : p = Q2 then
            match checkData value with
            | none => .error .notData
            | some qualified => do
                let next ← walkChecked book ticks body (value :: environment) args
                pure ⟨next.output, .lam compatible (fun _ => qualified.valid) next.valid⟩
          else do
            let next ← walkChecked book ticks body (value :: environment) args
            pure ⟨next.output, .lam compatible (fun equality => False.elim (copied equality)) next.valid⟩
        else .error .quantity
      | Prj handler, (q, Tup r first second) :: args =>
        if live : q.live = true then do
          let next ← walkChecked book ticks handler environment
            ((Quan.fld r q, first) :: (q, second) :: args)
          pure ⟨next.output, .prj live next.valid⟩
        else .error .quantity
      | Mat label yes no, (q, Lab actual) :: args =>
        if live : q.live = true then
          if same : actual = label then do
            let next ← walkChecked book ticks yes environment args
            pure ⟨next.output, by subst actual; exact .hit live next.valid⟩
          else do
            let next ← walkChecked book ticks no environment ((q, Lab actual) :: args)
            pure ⟨next.output, .miss live same next.valid⟩
        else .error .quantity
      | term, args =>
        if leaf : Term.node term = false then
          .ok ⟨some (Term.spine (Term.sub (Env.sub environment) term) args), .done leaf⟩
        else .error .stuck

structure CheckedValue (book : Book) (term : Term) : Type where
  valid : Value book term

structure CheckedValues (book : Book) (args : List Arg) : Type where
  valid : Values book args

mutual

/-- Finite recognition of source values. This never evaluates a redex or
pretends that an opaque model is an uninterpreted runtime value. -/
def valueChecked (book : Book) : (ticks : Nat) → (term : Term) →
    Except Refusal (CheckedValue book term)
  | 0, _ => .error .ticks
  | ticks + 1, term =>
      match term with
      | Lam _ _ => .ok ⟨.lam⟩
      | Prj _ => .ok ⟨.prj⟩
      | Mat _ _ _ => .ok ⟨.mat⟩
      | Efq => .ok ⟨.efq⟩
      | Lab _ => .ok ⟨.lab⟩
      | Rfl => .ok ⟨.rfl⟩
      | Typ _ => .ok ⟨.typ⟩
      | All _ _ _ => .ok ⟨.all⟩
      | Sig _ _ _ => .ok ⟨.sig⟩
      | Enu _ => .ok ⟨.enu⟩
      | Eql _ _ _ => .ok ⟨.eql⟩
      | Tup q first second => do
          let tail ← valueChecked book ticks second
          match q with
          | Q0 => pure ⟨.tup (by intro impossible; cases impossible) tail.valid⟩
          | Q1 =>
              let head ← valueChecked book ticks first
              pure ⟨.tup (fun _ => head.valid) tail.valid⟩
          | Q2 =>
              let head ← valueChecked book ticks first
              pure ⟨.tup (fun _ => head.valid) tail.valid⟩
      | other => callValueChecked book ticks other

/-- The argument quantities determine exactly which values must be checked. -/
def valuesChecked (book : Book) : (ticks : Nat) → (args : List Arg) →
    Except Refusal (CheckedValues book args)
  | 0, _ => .error .ticks
  | _ + 1, [] => .ok ⟨.nil⟩
  | ticks + 1, (q, value) :: args => do
      let tail ← valuesChecked book ticks args
      match q with
      | Q0 => pure ⟨.cons (by intro impossible; cases impossible) tail.valid⟩
      | Q1 =>
          let head ← valueChecked book ticks value
          pure ⟨.cons (fun _ => head.valid) tail.valid⟩
      | Q2 =>
          let head ← valueChecked book ticks value
          pure ⟨.cons (fun _ => head.valid) tail.valid⟩

def callValueChecked (book : Book) : (ticks : Nat) → (term : Term) →
    Except Refusal (CheckedValue book term)
  | 0, _ => .error .ticks
  | ticks + 1, term =>
      match split : Term.unspine term [] with
      | (Ref name, args) =>
        match found : Book.get book name with
        | none => .error .stuck
        | some definition => do
          let values ← valuesChecked book ticks args
          let walk ← walkChecked book ticks definition.v [] args
          match stopped : walk.output with
          | some _ => .error .stuck
          | none =>
            have shape : Term.spine (Ref name) args = term := by
              simpa only [split, Term.spine] using @BendTT.spine_unspine term []
            have sourceWalk : Walk book definition.v [] args none := by
              simpa only [stopped] using walk.valid
            pure ⟨by rw [← shape]; exact .call found values.valid sourceWalk⟩
      | _ => .error .stuck

end

inductive Classification (book : Book) (term : Term)
  | value (valid : Value book term)
  | next (result : Term) (valid : BendTT.Eval book term result)

/-- A complete call either unfolds with the source rule or stays its ORIGINAL
call/spine as an underapplied value. The opaque flag does not alter Eval. -/
def callChecked (book : Book) (ticks : Nat) (term : Term) :
    Except Refusal (Classification book term) :=
  match split : Term.unspine term [] with
  | (Ref name, args) =>
    match found : Book.get book name with
    | none => .error .stuck
    | some definition => do
      let values ← valuesChecked book ticks args
      let walk ← walkChecked book ticks definition.v [] args
      have shape : Term.spine (Ref name) args = term := by
        simpa only [split, Term.spine] using @BendTT.spine_unspine term []
      match output : walk.output with
      | none =>
        have source : Walk book definition.v [] args none := by
          simpa only [output] using walk.valid
        pure (.value (by rw [← shape]; exact .call found values.valid source))
      | some result =>
        have source : Walk book definition.v [] args (some result) := by
          simpa only [output] using walk.valid
        pure (.next result (by rw [← shape]; exact .call found values.valid source))
  | _ => .error .stuck

def applyChecked (book : Book) (ticks : Nat) (quantity : Quan)
    (function argument : Term) (_functionValue : Value book function)
    (argumentValue : quantity.live = true → Value book argument) :
    Except Refusal (Classification book (App quantity function argument)) :=
  match function, argument with
  | Lam binder body, argument =>
    if compatible : binder.live = quantity.live then
      if copied : binder = Q2 then
        match checkData argument with
        | none => .error .notData
        | some data => .ok (.next (Term.inst body argument)
            (.beta compatible argumentValue (fun _ => data.valid)))
      else .ok (.next (Term.inst body argument)
        (.beta compatible argumentValue (fun equal => False.elim (copied equal))))
    else .error .quantity
  | Prj handler, Tup firstQuantity first second =>
    if live : quantity.live = true then
      .ok (.next (App quantity (App (Quan.fld firstQuantity quantity) handler first) second)
        (.split live (argumentValue live)))
    else .error .quantity
  | Mat label yes no, Lab actual =>
    if live : quantity.live = true then
      if same : actual = label then
        .ok (.next yes (by subst actual; exact .hit live))
      else .ok (.next (App quantity no (Lab actual)) (.miss live same))
    else .error .quantity
  | function, argument => callChecked book ticks (App quantity function argument)

def unletChecked (book : Book) (quantity : Quan) (value body : Term)
    (qualified : quantity.live = true → Value book value) :
    Except Refusal (Classification book (Let quantity value body)) :=
  if copied : quantity = Q2 then
    match checkData value with
    | none => .error .notData
    | some data => .ok (.next (Term.inst body value)
        (.unlet qualified (fun _ => data.valid)))
  else .ok (.next (Term.inst body value)
    (.unlet qualified (fun equal => False.elim (copied equal))))

/-- An executable CBV source-step classifier. Each next state CONSTRUCTS an
actual Eval proof. The bounded diagnostic is deliberately not a claim that the
source term has no value: ticks may refuse a perfectly terminating program.
This structural reference still needs closure/heap and fixed-circuit lowering. -/
def stepChecked (book : Book) : (ticks : Nat) → (term : Term) →
    Except Refusal (Classification book term)
  | 0, _ => .error .ticks
  | ticks + 1, term =>
    match term with
    | Ann value _ => .ok (.next value .ann)
    | Ref name => callChecked book ticks (Ref name)
    | App quantity function argument => do
      match ← stepChecked book ticks function with
      | .next next proof => pure (.next (App quantity next argument) (.app_f proof))
      | .value functionValue =>
        if live : quantity.live = true then
          match ← stepChecked book ticks argument with
          | .next next proof => pure (.next (App quantity function next)
              (.app_x functionValue live proof))
          | .value argumentValue =>
              applyChecked book ticks quantity function argument functionValue (fun _ => argumentValue)
        else
          applyChecked book ticks quantity function argument functionValue
            (fun impossible => False.elim (live impossible))
    | Let quantity value body =>
      if live : quantity.live = true then do
        match ← stepChecked book ticks value with
        | .next next proof => pure (.next (Let quantity next body) (.lett live proof))
        | .value valueProof => unletChecked book quantity value body (fun _ => valueProof)
      else unletChecked book quantity value body
        (fun impossible => False.elim (live impossible))
    | Tup quantity first second =>
      if live : quantity.live = true then do
        match ← stepChecked book ticks first with
        | .next next proof => pure (.next (Tup quantity next second) (.tup_a live proof))
        | .value firstValue =>
          match ← stepChecked book ticks second with
          | .next next proof => pure (.next (Tup quantity first next)
              (.tup_b (fun _ => firstValue) proof))
          | .value secondValue => pure (.value (.tup (fun _ => firstValue) secondValue))
      else do
        match ← stepChecked book ticks second with
        | .next next proof => pure (.next (Tup quantity first next)
            (.tup_b (fun impossible => False.elim (live impossible)) proof))
        | .value secondValue => pure (.value
            (.tup (fun impossible => False.elim (live impossible)) secondValue))
    | Rwt evidence motive body => do
      match ← stepChecked book ticks evidence with
      | .next next proof => pure (.next (Rwt next motive body) (.rwt proof))
      | .value _ =>
        match evidence with
        | Rfl => pure (.next body .cast)
        | _ => .error .stuck
    | other => do
      let value ← valueChecked book ticks other
      pure (.value value.valid)

inductive Trace (book : Book) : Nat → Term → Term → Prop
  | refl (term : Term) : Trace book 0 term term
  | step {first middle last : Term} {count : Nat} :
      BendTT.Eval book first middle → Trace book count middle last →
      Trace book (count + 1) first last

inductive Execution (book : Book) (initial : Term)
  | complete (result : Term) (count : Nat)
      (trace : Trace book count initial result) (value : Value book result)
  | refused (residual : Term) (count : Nat)
      (trace : Trace book count initial residual) (reason : Refusal)

private def prepend {book : Book} {first middle : Term}
    (step : BendTT.Eval book first middle) : Execution book middle → Execution book first
  | .complete result count trace value => .complete result (count + 1) (.step step trace) value
  | .refused residual count trace reason => .refused residual (count + 1) (.step step trace) reason

/-- A bounded executable source evaluator with exact accepted source trace.
A value needs zero Eval steps. Exhaustion retains a true prefix and produces no
committable output/effect certificate. Classification bounds are separate from
source transition count; neither is the physical cost of a circuit backend. -/
def executeChecked (book : Book) (classificationTicks : Nat) :
    (steps : Nat) → (term : Term) → Execution book term
  | 0, term =>
      match stepChecked book classificationTicks term with
      | .error reason => .refused term 0 (.refl term) reason
      | .ok (.value value) => .complete term 0 (.refl term) value
      | .ok (.next _ _) => .refused term 0 (.refl term) .ticks
  | steps + 1, term =>
      match stepChecked book classificationTicks term with
      | .error reason => .refused term 0 (.refl term) reason
      | .ok (.value value) => .complete term 0 (.refl term) value
      | .ok (.next next proof) => prepend proof (executeChecked book classificationTicks steps next)

inductive Outcome
  | complete (result : Term) (count : Nat)
  | refused (count : Nat) (reason : Refusal)
  deriving DecidableEq, Repr

def Execution.outcome {book : Book} {initial : Term} : Execution book initial → Outcome
  | .complete result count _ _ => .complete result count
  | .refused _ count _ reason => .refused count reason

/-- This boundary is a source witness, not an unchecked success bit. -/
theorem walkChecked_source (book : Book) (ticks : Nat) (term : Term)
    (environment : Env) (args : List Arg)
    (result : CheckedWalk book term environment args)
    (_ran : walkChecked book ticks term environment args = .ok result) :
    Walk book term environment args result.output := result.valid

#assert_axioms checkData
#assert_axioms walkChecked
#assert_axioms valueChecked
#assert_axioms stepChecked
#assert_axioms executeChecked
#assert_axioms walkChecked_source
end Minidregg.Theory.BendLiveMachine
