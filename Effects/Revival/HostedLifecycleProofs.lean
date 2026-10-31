/- Declaration proofs. Native IO correspondence is a separate receiving obligation. -/
module
public import Effects.Revival.HostedLifecycleStatements
public import Effects.Revival.EngineProofs
@[expose] public section
namespace Minidregg.Effects.Revival.HostedLifecycle

set_option backward.isDefEq.respectTransparency false in
 theorem framed : substrate.Framed := by
  intro primitive before after stepped loc outside
  cases loc
  simp [substrate] at outside

 theorem sound (rules : List Rule) : (handler rules).Sound := by
  refine ⟨?_, ?_, framed⟩
  · intro state; rfl
  · intro cell state selected
    change some cell = some state at selected
    exact (Option.some.inj selected).symm

/-- No dispatcher frame refusal is reachable: the sole lifecycle state location
is exactly its declared slot. Guard completeness remains the semantics obligation. -/
 theorem inFrame (rules : List Rule) (operation : Operation) (primitives : List Primitive) :
    (spec rules).InFrame operation primitives := by
  intro loc _ _
  simp [spec]
#assert_axioms framed
#assert_axioms sound
#assert_axioms inFrame
end Minidregg.Effects.Revival.HostedLifecycle
