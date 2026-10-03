import Compiler.BendSourceByteCodec
namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false
open Minidregg.Theory.BendTT

theorem decodeNat_sound (t : BTerm) (n : Nat) (h : decodeNat t = some n) : t = natTerm n := by
  fun_induction decodeNat t generalizing n <;>
    simp_all [decodeNat, natTerm, Option.map_eq_some_iff] <;> aesop

theorem decodeBool_sound (t : BTerm) (b : Bool) (h : decodeBool t = some b) : t = boolTerm b := by
  fun_cases decodeBool t <;> simp_all [decodeBool, boolTerm]

theorem decodeNatList_sound (t : BTerm) (ns : List Nat) (h : decodeNatList t = some ns) :
    t = natListTerm ns := by
  fun_induction decodeNatList t generalizing ns <;>
    simp_all [decodeNatList, natListTerm, Option.bind_eq_some_iff] <;>
    aesop (add safe forward decodeNat_sound)

theorem decodeWord_sound (t : BTerm) (bs : List Bool) (h : decodeWord t = some bs) :
    t = wordTerm bs := by
  fun_induction decodeWord t generalizing bs <;>
    simp_all [decodeWord, wordTerm, Option.bind_eq_some_iff] <;>
    aesop (add safe forward decodeBool_sound)

theorem decodeNat_iff (t : BTerm) (n : Nat) : decodeNat t = some n ↔ RepNat t n :=
  ⟨decodeNat_sound t n, fun h => h ▸ decode_natTerm n⟩
theorem decodeWord_iff (t : BTerm) (bs : List Bool) :
    decodeWord t = some bs ↔ t = wordTerm bs :=
  ⟨decodeWord_sound t bs, fun h => h ▸ decode_wordTerm bs⟩

theorem decodeByteNats_sound (t : BTerm) (ns : List Nat)
    (h : decodeByteNats t = some ns) : RepBytes t ns := by
  unfold decodeByteNats at h
  cases hn : decodeNatList t with
  | none => simp [hn] at h
  | some xs =>
    simp only [hn, Option.bind_some] at h
    split at h
    · rename_i hb
      cases h
      refine ⟨decodeNatList_sound t xs hn, ?_⟩
      simpa only [List.all_eq_true, decide_eq_true_eq] using hb
    · cases h

private theorem byteNats_roundtrip (ns : List Nat) (bound : ∀ n ∈ ns, n < 256) :
    (ns.map UInt8.ofNat).map UInt8.toNat = ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    have hn := bound n (by simp)
    have ht : ∀ x ∈ ns, x < 256 := fun x hx => bound x (by simp [hx])
    simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt hn, ih ht]

theorem decodeBytes_sound (t : BTerm) (bs : List UInt8) (h : decodeBytes t = some bs) :
    t = bytesTerm bs := by
  obtain ⟨ns, hn, rfl⟩ := Option.map_eq_some_iff.mp h
  have hb := decodeByteNats_sound t ns hn
  simpa [bytesTerm, byteNats_roundtrip ns hb.2] using hb.1

theorem decodeBytes_iff (t : BTerm) (bs : List UInt8) :
    decodeBytes t = some bs ↔ t = bytesTerm bs :=
  ⟨decodeBytes_sound t bs, fun h => h ▸ decode_bytesTerm bs⟩

#assert_axioms decodeByteNats_sound
#assert_axioms decodeBytes_sound
#assert_axioms decodeBytes_iff

#assert_axioms decodeNat_sound
#assert_axioms decodeBool_sound
#assert_axioms decodeNatList_sound
#assert_axioms decodeWord_sound
#assert_axioms decodeNat_iff
#assert_axioms decodeWord_iff
end Minidregg.Compiler.BendSourceRepresentation
