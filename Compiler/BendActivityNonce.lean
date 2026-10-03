/- Explicit signed nonce namespace for the Activity application route. The
source-selected receiver edition must reject this namespace at every ordinary
current-admission entry, including joint wrappers. The typed route still checks
ordinary authority and an actual current pending-phase witness. This classifier
alone does not install that receiving policy or activate a new edition.
-/
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.BendActivityNonce
set_option autoImplicit false

def base : Nat := 2 ^ 256

def marked (nonce : Nat) : Bool := decide (base ≤ nonce ∧ nonce < 2 * base)

def make (digest : Nat) : Nat := base + digest % base

theorem make_marked (digest : Nat) : marked (make digest) = true := by
  have positive : 0 < base := by decide
  have bounded := Nat.mod_lt digest positive
  simp only [marked,decide_eq_true_eq,make]
  omega

def ordinaryAllowed (nonce : Nat) : Bool := !marked nonce

theorem ordinary_refuses_marked (digest : Nat) : ordinaryAllowed (make digest) = false := by
  simp [ordinaryAllowed,make_marked]

#assert_axioms make_marked
#assert_axioms ordinary_refuses_marked
end Minidregg.Compiler.BendActivityNonce
