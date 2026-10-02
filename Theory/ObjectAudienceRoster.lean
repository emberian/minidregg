/- Canonical retained key-holder roster. Completeness is established by admitted
package enrollment, not by discovering online readers. -/
import Theory.ObjectAudience
namespace Minidregg.Theory.ObjectAudienceRoster
set_option autoImplicit false
structure Entry where
  subject : Nat
  capability : Nat
  deviceSource : Nat
  deviceGeneration : Nat
  keyCommitment : Nat
  deriving DecidableEq, Repr
structure Roster where
  object : Nat
  epoch : Nat
  transition : Nat
  entries : List Entry
  deriving DecidableEq, Repr
/-- Package recipients are the complete ordered roster, including offline holders.
Cryptographic correctness of each wrap remains the distributor's obligation. -/
def Valid (roster : Roster) : Prop :=
  roster.entries ≠ [] ∧ roster.entries.length ≤ 4096 ∧
  (roster.entries.map fun e => (e.subject, e.deviceSource, e.deviceGeneration)).Nodup
instance (r : Roster) : Decidable (Valid r) := by unfold Valid; infer_instance
end Minidregg.Theory.ObjectAudienceRoster
