/-
# Compiler.FiniteDependentMapCodec -- one finite sparse encoding construction

Finite support is structural `DFinsupp` data. Keys are canonically sorted and
each dependent value is read at its actual key. The decoder reconstructs that
same finite map; there is no countability-selected enumeration or focused
codec. A carrier's outer canonical decoder additionally rejects duplicate,
out-of-order and explicit-zero entries by exact re-encoding.
-/
import Compiler.Tower256ConcreteBackend
import Mathlib.Data.Finset.Sort

namespace Minidregg.Compiler.FiniteDependentMapCodec

open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

variable {K : Type} {V : K → Type} [DecidableEq K] [∀ key, Zero (V key)]

def fromEntries : List (Sigma V) → (Π₀ key : K, V key)
  | [] => 0
  | ⟨key, value⟩ :: entries => (fromEntries entries).update key value

theorem fromEntries_map (keys : List K) (fields : Π₀ key : K, V key) (key : K) :
    fromEntries (keys.map (fun key => ⟨key, fields key⟩)) key =
      if key ∈ keys then fields key else 0 := by
  induction keys with
  | nil => simp [fromEntries]
  | cons head rest induction =>
      by_cases equal : key = head
      · subst key
        simp [fromEntries]
      · simp [fromEntries, DFinsupp.update, equal, induction]

def entries [LinearOrder K] [∀ key, DecidableEq (V key)]
    (fields : Π₀ key : K, V key) : List (Sigma V) :=
  (fields.support.sort (· ≤ ·)).map (fun key => ⟨key, fields key⟩)

theorem fromEntries_entries [LinearOrder K] [∀ key, DecidableEq (V key)]
    (fields : Π₀ key : K, V key) : fromEntries (entries fields) = fields := by
  apply DFinsupp.ext
  intro key
  rw [entries, fromEntries_map]
  simp only [Finset.mem_sort, DFinsupp.mem_support_toFun]
  split_ifs with present
  · rfl
  · simpa using (not_not.mp present).symm

/-- The decoded key chooses its own value type before payload decoding. -/
def entryStream (keyStream : StreamCodec K)
    (valueStream : (key : K) → StreamCodec (V key)) : StreamCodec (Sigma V) where
  encode entry := keyStream.encode entry.1 ++ (valueStream entry.1).encode entry.2
  decodePrefix bytes := do
    let (key, afterKey) ← keyStream.decodePrefix bytes
    let (value, suffix) ← (valueStream key).decodePrefix afterKey
    some (⟨key, value⟩, suffix)
  decodePrefix_encode := by
    rintro ⟨key, value⟩ suffix
    simp [List.append_assoc, keyStream.decodePrefix_encode,
      (valueStream key).decodePrefix_encode]

def stream [LinearOrder K] [∀ key, DecidableEq (V key)]
    (keyStream : StreamCodec K)
    (valueStream : (key : K) → StreamCodec (V key)) :
    StreamCodec (Π₀ key : K, V key) :=
  StreamCodec.xmap (StreamCodec.list (entryStream keyStream valueStream))
    entries fromEntries fromEntries_entries

end Minidregg.Compiler.FiniteDependentMapCodec
