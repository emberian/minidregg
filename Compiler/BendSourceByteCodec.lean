import Compiler.BendSourceTypedRepresentation
namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false
open Minidregg.Theory.BendTT

def bytesTerm (bs : List UInt8) : BTerm := natListTerm (bs.map UInt8.toNat)
def decodeBytes (t : BTerm) : Option (List UInt8) :=
  (decodeByteNats t).map (List.map UInt8.ofNat)

theorem bytesTerm_rep (bs : List UInt8) : RepBytes (bytesTerm bs) (bs.map UInt8.toNat) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hn
  exact b.toNat_lt_size

theorem decode_bytesTerm (bs : List UInt8) : decodeBytes (bytesTerm bs) = some bs := by
  simp [decodeBytes, decode_represented_bytes (bytesTerm_rep bs), List.map_map, Function.comp_def]

#assert_axioms bytesTerm_rep
#assert_axioms decode_bytesTerm
end Minidregg.Compiler.BendSourceRepresentation
