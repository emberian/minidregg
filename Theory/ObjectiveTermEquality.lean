/- Bounded, proof-producing structural comparison of Objective source syntax.
Success contains equality of the actual terms; mismatch or exhausted public
comparison fuel refuses. No classical equality oracle or old calculus import. -/
import Theory.ObjectiveBendOpenRecursion
import Theory.AssertAxioms
namespace Minidregg.Theory.ObjectiveBendOpenRecursion
set_option autoImplicit false

mutual
  def termEqual : (fuel : Nat) → (left right : Term) → Option (PLift (left = right))
    | 0, _, _ => none
    | fuel+1, left, right => match left,right with
      | .bound a,.bound b => if same : a = b then some ⟨by cases same; rfl⟩ else none
      | .lam a,.lam b => do let same ← termEqual fuel a b; pure ⟨by cases same.down; rfl⟩
      | .app a b,.app c d => do
        let first ← termEqual fuel a c
        let second ← termEqual fuel b d
        pure ⟨by cases first.down; cases second.down; rfl⟩
      | .mix a b,.mix c d => do
        let first ← termEqual fuel a c
        let second ← termEqual fuel b d
        pure ⟨by cases first.down; cases second.down; rfl⟩
      | .fix a b,.fix c d => do
        let first ← termEqual fuel a c
        let second ← termEqual fuel b d
        pure ⟨by cases first.down; cases second.down; rfl⟩
      | .specification a b,.specification c d => do
        let first ← termEqual fuel a c
        let second ← termEqual fuel b d
        pure ⟨by cases first.down; cases second.down; rfl⟩
      | .prototype a b,.prototype c d => do
        let first ← termEqual fuel a c
        let second ← termEqual fuel b d
        pure ⟨by cases first.down; cases second.down; rfl⟩
      | .reflect a,.reflect b => do let same ← termEqual fuel a b; pure ⟨by cases same.down; rfl⟩
      | .metadata a,.metadata b => do let same ← termEqual fuel a b; pure ⟨by cases same.down; rfl⟩
      | .project a,.project b => do let same ← termEqual fuel a b; pure ⟨by cases same.down; rfl⟩
      | .nat a,.nat b => if same : a = b then some ⟨by cases same; rfl⟩ else none
      | .boolean a,.boolean b => if same : a = b then some ⟨by cases same; rfl⟩ else none
      | .label a,.label b => if same : a = b then some ⟨by cases same; rfl⟩ else none
      | .binary p a b,.binary q c d =>
        if primitive : p = q then do
          let first ← termEqual fuel a c
          let second ← termEqual fuel b d
          pure ⟨by cases primitive; cases first.down; cases second.down; rfl⟩
        else none
      | .extend a fields,.extend b other => do
        let first ← termEqual fuel a b
        let second ← fieldsEqual fuel fields other
        pure ⟨by cases first.down; cases second.down; rfl⟩
      | .record fields,.record other => do
        let same ← fieldsEqual fuel fields other
        pure ⟨by cases same.down; rfl⟩
      | .get a name,.get b other =>
        if names : name = other then do
          let same ← termEqual fuel a b
          pure ⟨by cases names; cases same.down; rfl⟩
        else none
      | .ifZero a b c,.ifZero d e f => do
        let first ← termEqual fuel a d
        let second ← termEqual fuel b e
        let third ← termEqual fuel c f
        pure ⟨by cases first.down; cases second.down; cases third.down; rfl⟩
      | _,_ => none

  def fieldsEqual : (fuel : Nat) → (left right : List (String × Term)) → Option (PLift (left = right))
    | _, [], [] => some ⟨rfl⟩
    | 0, _, _ => none
    | fuel+1, (name,value)::tail, (otherName,otherValue)::rest =>
      if names : name = otherName then do
        let head ← termEqual fuel value otherValue
        let next ← fieldsEqual fuel tail rest
        pure ⟨by cases names; cases head.down; cases next.down; rfl⟩
      else none
    | _,_,_ => none
end

#assert_axioms termEqual
#assert_axioms fieldsEqual
end Minidregg.Theory.ObjectiveBendOpenRecursion
