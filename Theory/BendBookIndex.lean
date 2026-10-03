/- A prepared, exact first-definition lookup for native source execution.
The ordered Book remains the semantic/checker/source identity. Hashing is only a
clear runtime lookup representation; private machines keep their fixed scans.
-/
import Theory.BendTTSource
import Theory.AssertAxioms
import Std.Data.HashMap.Lemmas

namespace Minidregg.Theory.BendBookIndex
open BendTT
set_option autoImplicit false

/-- The upstream right fold implements first-definition wins, including Books
with duplicate names. No uniqueness or successful checker premise is needed. -/
theorem lib_exact (book : Book) (name : String) :
    (Lib.of book)[name]? = Book.get book name := by
  induction book with
  | nil => simp [Lib.of, Book.get]
  | cons definition rest ih =>
    by_cases same : definition.k = name
    · simp [Lib.of, Book.get, Std.HashMap.getElem?_insert, same]
    · simpa [Lib.of, Book.get, Std.HashMap.getElem?_insert, same] using ih

/-- Proof-backed lookup can be cached without putting the cache into program
identity. The map is captured by the function; its refinement proof is erased. -/
structure Lookup (book : Book) where
  get : String → Option Def
  exact : ∀ name, get name = Book.get book name

def linear (book : Book) : Lookup book := ⟨Book.get book, fun _ => rfl⟩

def prepare (book : Book) : Lookup book :=
  let cache := Lib.of book
  ⟨fun name => cache[name]?, lib_exact book⟩

/-- Extensional equality retains both successes and absent-name diagnostics.
It permits clients to prove their whole dependent execution result unchanged,
rather than asserting equality only for completed, honest-generator examples. -/
theorem lookup_eq_linear {book : Book} (lookup : Lookup book) :
    lookup = linear book := by
  cases lookup with
  | mk get exact =>
    have same : get = Book.get book := funext exact
    subst get
    rfl

#assert_axioms lib_exact
#assert_axioms prepare
#assert_axioms lookup_eq_linear
end Minidregg.Theory.BendBookIndex
