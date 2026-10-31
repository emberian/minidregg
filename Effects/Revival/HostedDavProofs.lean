/- The generated DAV rule table has inhabited positive and adversarial poles. -/
module
public import Effects.Revival.HostedDavStatements
public import Theory.AxiomPin
import all Effects.Revival.HostedDav
import all Init.Data.List.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
@[expose] public section
namespace Minidregg.Effects.Revival.HostedDav
theorem satisfiable : Satisfiable := by unfold Satisfiable; decide +kernel
theorem teeth : Teeth := by unfold Teeth; decide +kernel
theorem premise : Premise := ⟨headerAllowed, fun _ _ _ => rfl⟩
#assert_axioms satisfiable
#assert_axioms teeth
#assert_axioms premise
end Minidregg.Effects.Revival.HostedDav
