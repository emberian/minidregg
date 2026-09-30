/- Byte-level consequences of the distinct selective-release message codec.
These facts do not assert a signer or source Mini historical admission. -/
import Kernel.FnSelectiveRelease

namespace Minidregg.Kernel.FnSelectiveRelease

set_option autoImplicit false

theorem signedPreimage_changes_content (left right : Release)
    (changed : left.content ≠ right.content) :
    signedPreimage left ≠ signedPreimage right := by
  intro same
  exact changed (congrArg Release.content (signedPreimage_injective same))

theorem signedPreimage_changes_destination (left right : Release)
    (changed : left.destination ≠ right.destination) :
    signedPreimage left ≠ signedPreimage right := by
  intro same
  exact changed (congrArg Release.destination (signedPreimage_injective same))

theorem signedPreimage_changes_owner (left right : Release)
    (changed : left.owner ≠ right.owner) :
    signedPreimage left ≠ signedPreimage right := by
  intro same
  exact changed (congrArg Release.owner (signedPreimage_injective same))

theorem signedPreimage_changes_selected_atom (left right : Release)
    (changed : left.source.atom ≠ right.source.atom) :
    signedPreimage left ≠ signedPreimage right := by
  intro same
  exact changed (congrArg (fun release => release.source.atom)
    (signedPreimage_injective same))

theorem comparePrior_self (prior : Recorded) :
    comparePrior prior prior.release prior.signedCall = .exactRepeat := by
  simp [comparePrior]

theorem comparePrior_changed_content (prior : Recorded) (incoming : Release)
    (signedCall : List UInt8)
    (sameKey : prior.release.key = incoming.key)
    (changed : prior.release.content ≠ incoming.content) :
    comparePrior prior incoming signedCall = .conflict := by
  apply comparePrior_conflict prior incoming signedCall sameKey
  left
  intro same
  exact changed (congrArg Release.content same)

theorem comparePrior_changed_call (prior : Recorded) (incoming : Release)
    (signedCall : List UInt8)
    (sameKey : prior.release.key = incoming.key)
    (changed : prior.signedCall ≠ signedCall) :
    comparePrior prior incoming signedCall = .conflict :=
  comparePrior_conflict prior incoming signedCall sameKey (Or.inr changed)

theorem comparePrior_other_key (prior : Recorded) (incoming : Release)
    (signedCall : List UInt8)
    (other : prior.release.key ≠ incoming.key) :
    comparePrior prior incoming signedCall = .unrelated := by
  simp [comparePrior, other]

end Minidregg.Kernel.FnSelectiveRelease

/-- info: 'Minidregg.Kernel.FnSelectiveRelease.signedPreimage_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FnSelectiveRelease.signedPreimage_injective
/-- info: 'Minidregg.Kernel.FnSelectiveRelease.comparePrior_exactRepeat' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FnSelectiveRelease.comparePrior_exactRepeat
/-- info: 'Minidregg.Kernel.FnSelectiveRelease.comparePrior_conflict' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FnSelectiveRelease.comparePrior_conflict
/-- info: 'Minidregg.Kernel.FnSelectiveRelease.signedPreimage_changes_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FnSelectiveRelease.signedPreimage_changes_content
/-- info: 'Minidregg.Kernel.FnSelectiveRelease.signedPreimage_changes_selected_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FnSelectiveRelease.signedPreimage_changes_selected_atom
/-- info: 'Minidregg.Kernel.FnSelectiveRelease.comparePrior_changed_content' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.FnSelectiveRelease.comparePrior_changed_content
