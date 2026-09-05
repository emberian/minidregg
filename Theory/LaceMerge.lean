/-
# Theory.LaceMerge -- the replica keyset merge, with cross-canonical agreement DERIVED

Port of breadstuffs `Dregg2/Distributed/LaceMerge.lean`: the skip-if-present merge, its
join law `ids_merge`, and the CRDT laws (comm / assoc / idem / monotone / lub) read off
`Finset ∪` on the content-address keyset.

What the ancestor could only HYPOTHESIZE is a theorem here.  `CrossCanonical` -- "equal
keysets are not equal laces", content-address collision at the replica boundary, carried
anonymously at every convergence site until it was named (`docs/DISTRIBUTED-DESIGN.md`
§1 row G2, §3.1) -- is DERIVED from the substrate's typed realizer slot
`CausalVersionDag.ContentAddressing.BindingPremise`: `crossCanonical_of_binding`, hence
`canonical_of_binding`, hence `sameView_of_binding` (equal keysets ⇒ same content at
every address, no canonicity premises left) and `merge_converges` (either merge order
resolves every address identically).  The ancestor's conditional bridge
`sameView_of_canonical_eq_ids` is kept as the honest statement WITHOUT binding.

Carrier: a view is `List (AddressedEvent scheme)`.  `AddressedEvent` bundles a preimage
with its address and the address EQUATION (`entryIdExact`), so the id is the address,
`lookup` returns the preimage, the binding step is the substrate's own
`AddressedEvent.preimage_eq_of_entryId_eq`, and equal preimages give equal events
(`addressed_ext`) -- which is why `Canonical` is automatic under binding.

Teeth (ATLAS §6 laws 1-2), built at two concrete schemes over ONE computable lawful codec
(`unaryCodec`; the tree's `codecOfCountable` is noncomputable, so nothing could `decide`):
`lengthScheme` (digest = byte count) is refuted, `lengthScheme_not_binding`, and hosts the
rebuilt `crossCanonical_is_the_gap` (two canonical views, equal `ids`, different `lookup`)
and `merge_drops_at_collision`; `injectiveScheme` (digest = the bytes as one `Nat`)
realizes the premise, `injectiveScheme_binding` -- ideal, not cryptographic, since
`Digest.value` is an unbounded `Nat`; at a deployed bounded digest the premise is the
collision-resistance floor and stays a slot.  `merge_computes` is the satisfiable pole.

Residuals: `[LACE-frontier]` tips/frontier view (reuse `CausalVersionDag.frontier`);
`[LACE-equivocation]` per-author strands and equivocation exclusion; `[LACE-order]` the
DERIVED finalizer (DISTRIBUTED-DESIGN §3.3); `[LACE-catchup]` fold-of-merge catch-up
(trivial once merge is a semilattice, deferred).
-/
import Theory.CausalVersionDag

namespace Minidregg.Theory.LaceMerge

open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CausalVersionDag

set_option autoImplicit false

variable {scheme : ContentAddressing}

/-! ## 1. The carrier -/

/-- Equal preimages, equal addressed events: the address is fixed by `entryIdExact`. -/
theorem addressed_ext {a b : AddressedEvent scheme} (h : a.preimage = b.preimage) : a = b := by
  obtain ⟨p, i, hi, _⟩ := a
  obtain ⟨q, j, hj, _⟩ := b
  cases h
  subst hi
  subst hj
  rfl

instance : DecidableEq (AddressedEvent scheme) := fun a b =>
  decidable_of_iff (a.preimage = b.preimage) ⟨addressed_ext, fun h => h ▸ rfl⟩

/-- Address a well-formed preimage under `scheme`. -/
def addressed (scheme : ContentAddressing) (event : EventPreimage)
    (wf : event.WellFormed) : AddressedEvent scheme :=
  ⟨event, scheme.address event, rfl, wf⟩

/-- A replica's view: the addressed events it holds. -/
abbrev View (scheme : ContentAddressing) := List (AddressedEvent scheme)

/-- The content-address keyset -- the CRDT observable. -/
def ids (B : View scheme) : Finset Digest := (B.map AddressedEvent.entryId).toFinset

@[simp] theorem mem_ids {B : View scheme} {h : Digest} :
    h ∈ ids B ↔ ∃ a ∈ B, a.entryId = h := by
  simp [ids]

theorem ids_append (B C : View scheme) : ids (B ++ C) = ids B ∪ ids C := by
  simp [ids, List.toFinset_append]

/-! ## 2. The merge and its join law -/

/-- The delta events whose address is new to `B` (skip-if-present). -/
def newEvents (B Δ : View scheme) : View scheme :=
  Δ.filter (fun a => decide (a.entryId ∉ ids B))

/-- `B` with the new delta events appended -- the ancestor's `mergeLace`. -/
def merge (B Δ : View scheme) : View scheme := B ++ newEvents B Δ

theorem ids_merge (B Δ : View scheme) : ids (merge B Δ) = ids B ∪ ids Δ := by
  ext h
  simp only [merge, ids_append, Finset.mem_union, mem_ids, newEvents, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro (hB | ⟨a, ⟨haΔ, _⟩, rfl⟩)
    · exact Or.inl hB
    · exact Or.inr ⟨a, haΔ, rfl⟩
  · rintro (hB | ⟨a, haΔ, rfl⟩)
    · exact Or.inl hB
    · by_cases hmem : a.entryId ∈ ids B
      · exact Or.inl (mem_ids.mp hmem)
      · exact Or.inr ⟨a, ⟨haΔ, fun hc => hmem (mem_ids.mpr hc)⟩, rfl⟩

/-- Commutativity: `Finset.union_comm` after `ids_merge`. -/
theorem merge_comm (B C : View scheme) : ids (merge B C) = ids (merge C B) := by
  rw [ids_merge, ids_merge, Finset.union_comm]

/-- Associativity: `Finset.union_assoc` after `ids_merge`. -/
theorem merge_assoc (B C D : View scheme) :
    ids (merge (merge B C) D) = ids (merge B (merge C D)) := by
  simp only [ids_merge, Finset.union_assoc]

/-- Idempotence: `Finset.union_self` after `ids_merge`. -/
theorem merge_idem (B : View scheme) : ids (merge B B) = ids B := by
  rw [ids_merge, Finset.union_self]

/-- Inflationary: `Finset.subset_union_left` after `ids_merge`. -/
theorem merge_monotone (B Δ : View scheme) : ids B ⊆ ids (merge B Δ) := by
  rw [ids_merge]; exact Finset.subset_union_left

/-- Least upper bound: `Finset.union_subset` after `ids_merge`. -/
theorem merge_lub (B Δ U : View scheme) (hB : ids B ⊆ ids U) (hΔ : ids Δ ⊆ ids U) :
    ids (merge B Δ) ⊆ ids U := by
  rw [ids_merge]; exact Finset.union_subset hB hΔ

/-! ## 3. Canonicity, lookup, and the cross-canonical gap -/

def Canonical (B : View scheme) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a.entryId = b.entryId → a = b

/-- Two views resolve any shared address to the same event. -/
def CrossCanonical (B₁ B₂ : View scheme) : Prop :=
  ∀ a ∈ B₁, ∀ b ∈ B₂, a.entryId = b.entryId → a = b

instance (B : View scheme) : Decidable (Canonical B) := by
  unfold Canonical; infer_instance

instance (B₁ B₂ : View scheme) : Decidable (CrossCanonical B₁ B₂) := by
  unfold CrossCanonical; infer_instance

/-- Resolve an address to the content the view holds for it. -/
def lookup (B : View scheme) (h : Digest) : Option EventPreimage :=
  (B.find? (fun a => decide (a.entryId = h))).map AddressedEvent.preimage

def SameView (B₁ B₂ : View scheme) : Prop := ∀ h, lookup B₁ h = lookup B₂ h

theorem crossCanonical_self (B : View scheme) : CrossCanonical B B ↔ Canonical B := Iff.rfl

theorem canonical_append_iff (B₁ B₂ : View scheme) :
    Canonical (B₁ ++ B₂) ↔ Canonical B₁ ∧ Canonical B₂ ∧ CrossCanonical B₁ B₂ := by
  constructor
  · intro h
    exact ⟨fun a ha b hb => h a (List.mem_append_left _ ha) b (List.mem_append_left _ hb),
      fun a ha b hb => h a (List.mem_append_right _ ha) b (List.mem_append_right _ hb),
      fun a ha b hb => h a (List.mem_append_left _ ha) b (List.mem_append_right _ hb)⟩
  · rintro ⟨h₁, h₂, hx⟩ a ha b hb hid
    rcases List.mem_append.mp ha with ha' | ha' <;> rcases List.mem_append.mp hb with hb' | hb'
    · exact h₁ a ha' b hb' hid
    · exact hx a ha' b hb' hid
    · exact (hx b hb' a ha' hid.symm).symm
    · exact h₂ a ha' b hb' hid

theorem lookup_eq_none_iff {B : View scheme} {h : Digest} : lookup B h = none ↔ h ∉ ids B := by
  simp [lookup, List.find?_eq_none]

theorem lookup_of_mem {B : View scheme} (hc : Canonical B) {a : AddressedEvent scheme}
    (ha : a ∈ B) : lookup B a.entryId = some a.preimage := by
  have hsome : (B.find? (fun x => decide (x.entryId = a.entryId))).isSome := by
    rw [List.find?_isSome]; exact ⟨a, ha, by simp⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  have hbid : b.entryId = a.entryId := by simpa using List.find?_some hb
  rw [lookup, hb, hc b (List.mem_of_find?_eq_some hb) a ha hbid]
  rfl

/-- The ancestor's bridge, kept as stated: WITHOUT binding, cross-canonicity is a premise. -/
theorem sameView_of_canonical_eq_ids {B₁ B₂ : View scheme}
    (hc₁ : Canonical B₁) (hc₂ : Canonical B₂) (hids : ids B₁ = ids B₂)
    (hcross : CrossCanonical B₁ B₂) : SameView B₁ B₂ := by
  intro h
  by_cases hmem : h ∈ ids B₁
  · obtain ⟨a, ha, rfl⟩ := mem_ids.mp hmem
    obtain ⟨b, hb, hbid⟩ := mem_ids.mp (hids ▸ hmem)
    rw [lookup_of_mem hc₁ ha, ← hbid, lookup_of_mem hc₂ hb, hcross a ha b hb hbid.symm]
  · rw [lookup_eq_none_iff.mpr hmem, lookup_eq_none_iff.mpr (hids ▸ hmem)]

/-! ## 4. The named premise closes the gap -/

/-- G2 closed: under `BindingPremise`, EVERY pair of views is cross-canonical. -/
theorem crossCanonical_of_binding (binding : scheme.BindingPremise) (B₁ B₂ : View scheme) :
    CrossCanonical B₁ B₂ :=
  fun _ _ _ _ sameId => addressed_ext (AddressedEvent.preimage_eq_of_entryId_eq binding sameId)

theorem canonical_of_binding (binding : scheme.BindingPremise) (B : View scheme) :
    Canonical B :=
  crossCanonical_of_binding binding B B

/-- Equal keysets ⇒ same content at every address.  The ancestor's two `Canonical`
premises are theorems here (`canonical_of_binding`), so they are dropped. -/
theorem sameView_of_binding (binding : scheme.BindingPremise) {B₁ B₂ : View scheme}
    (hids : ids B₁ = ids B₂) : SameView B₁ B₂ :=
  sameView_of_canonical_eq_ids (canonical_of_binding binding B₁)
    (canonical_of_binding binding B₂) hids (crossCanonical_of_binding binding B₁ B₂)

/-- Replication converges on CONTENT, not just keysets, in either merge order. -/
theorem merge_converges (binding : scheme.BindingPremise) (B C : View scheme) :
    SameView (merge B C) (merge C B) :=
  sameView_of_binding binding (merge_comm B C)

/-! ## 5. A computable lawful codec (witness scaffolding) -/

def encNat : Nat → List UInt8
  | 0 => [0]
  | n + 1 => 1 :: encNat n

def decNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest => if b = 0 then some (0, rest) else (decNat rest).map fun p => (p.1 + 1, p.2)

theorem decNat_encNat (n : Nat) (rest : List UInt8) :
    decNat (encNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [encNat, decNat]
  | succ n ih => simp [encNat, decNat, ih]

/-- Length-prefixed sequence of unary naturals. -/
def encNats (l : List Nat) : List UInt8 := encNat l.length ++ l.flatMap encNat

def decNatsN : Nat → List UInt8 → Option (List Nat × List UInt8)
  | 0, bytes => some ([], bytes)
  | k + 1, bytes =>
      (decNat bytes).bind fun p => (decNatsN k p.2).map fun q => (p.1 :: q.1, q.2)

theorem decNatsN_flatMap (l : List Nat) (rest : List UInt8) :
    decNatsN l.length (l.flatMap encNat ++ rest) = some (l, rest) := by
  induction l with
  | nil => simp [decNatsN]
  | cons a l ih => simp [decNatsN, List.flatMap_cons, List.append_assoc, decNat_encNat, ih]

def decNats (bytes : List UInt8) : Option (List Nat × List UInt8) :=
  (decNat bytes).bind fun p => decNatsN p.1 p.2

theorem decNats_encNats (l : List Nat) (rest : List UInt8) :
    decNats (encNats l ++ rest) = some (l, rest) := by
  simp [decNats, encNats, List.append_assoc, decNat_encNat, decNatsN_flatMap]

theorem decNats_encNats_nil (l : List Nat) : decNats (encNats l) = some (l, []) := by
  simpa using decNats_encNats l []

def encodePreimage (e : EventPreimage) : List UInt8 :=
  encNats [e.historyDomain.value, e.streamId.value, e.schema.schemaId.value,
    e.schema.version, e.semanticVersion, e.semanticObjectRoot.value, e.preStateRoot.value,
    e.postStateRoot.value, e.authorId.value, e.principalId.value, e.requestId.value,
    e.effectId.value] ++ encNats (e.parentFrontier.map Digest.value)

def decodePreimage (bytes : List UInt8) : Option EventPreimage :=
  match decNats bytes with
  | some ([hd, st, sid, sv, semv, so, pre, post, au, pr, rq, ef], rest) =>
      match decNats rest with
      | some (pf, _) =>
          some {
            historyDomain := ⟨hd⟩, streamId := ⟨st⟩, schema := ⟨⟨sid⟩, sv⟩,
            semanticVersion := semv, semanticObjectRoot := ⟨so⟩, preStateRoot := ⟨pre⟩,
            postStateRoot := ⟨post⟩, parentFrontier := pf.map Digest.mk, authorId := ⟨au⟩,
            principalId := ⟨pr⟩, requestId := ⟨rq⟩, effectId := ⟨ef⟩ }
      | none => none
  | _ => none

def unaryCodec : LawfulCodec EventPreimage where
  encode := encodePreimage
  decode := decodePreimage
  decode_encode e := by
    rcases e with ⟨⟨hd⟩, ⟨st⟩, ⟨⟨sid⟩, sv⟩, semv, ⟨so⟩, ⟨pre⟩, ⟨post⟩, pf, ⟨au⟩, ⟨pr⟩, ⟨rq⟩, ⟨ef⟩⟩
    simp [decodePreimage, encodePreimage, decNats_encNats, decNats_encNats_nil, List.map_map]
    exact List.map_id'' (fun _ => rfl) pf

/-! ## 6. Two schemes: the premise refuted, and the premise realized -/

/-- Digest = byte count.  Lawful codec, colliding digest. -/
def lengthScheme : ContentAddressing :=
  { codec := unaryCodec, digestBytes := fun bytes => ⟨bytes.length⟩ }

/-- Digest = the bytes themselves as one `Nat`.  Ideal binding at an unbounded digest. -/
def injectiveScheme : ContentAddressing :=
  { codec := unaryCodec, digestBytes := fun bytes => ⟨Encodable.encode (bytes.map UInt8.toNat)⟩ }

/-- Premise inhabitation: the realizer slot has an occupant. -/
theorem injectiveScheme_binding : injectiveScheme.BindingPremise :=
  ⟨fun {l r} h => by
    have hbytes : unaryCodec.encode l = unaryCodec.encode r :=
      List.map_injective_iff.mpr (fun _ _ => UInt8.toNat_inj.mp)
        (Encodable.encode_injective (congrArg Digest.value h))
    exact Option.some.inj ((unaryCodec.decode_encode l).symm.trans
      ((congrArg unaryCodec.decode hbytes).trans (unaryCodec.decode_encode r)))⟩

def zeroPreimage : EventPreimage :=
  { historyDomain := ⟨0⟩, streamId := ⟨0⟩, schema := ⟨⟨0⟩, 0⟩, semanticVersion := 0,
    semanticObjectRoot := ⟨0⟩, preStateRoot := ⟨0⟩, postStateRoot := ⟨0⟩, parentFrontier := [],
    authorId := ⟨0⟩, principalId := ⟨0⟩, requestId := ⟨0⟩, effectId := ⟨0⟩ }

/-- One bit away from `zeroPreimage`, twice; the two collide under `lengthScheme`. -/
def requestOne : EventPreimage := { zeroPreimage with requestId := ⟨1⟩ }
def effectOne : EventPreimage := { zeroPreimage with effectId := ⟨1⟩ }

def zeroEvent : AddressedEvent lengthScheme :=
  addressed lengthScheme zeroPreimage ⟨List.Pairwise.nil, List.nodup_nil⟩
def requestEvent : AddressedEvent lengthScheme :=
  addressed lengthScheme requestOne ⟨List.Pairwise.nil, List.nodup_nil⟩
def effectEvent : AddressedEvent lengthScheme :=
  addressed lengthScheme effectOne ⟨List.Pairwise.nil, List.nodup_nil⟩

theorem lengthScheme_not_binding : ¬ lengthScheme.BindingPremise := fun h =>
  absurd (h.reflectsEquality (left := requestOne) (right := effectOne) (by decide)) (by decide)

/-- Satisfiable: a computed merge, with the skip guard firing on the shared address. -/
theorem merge_computes :
    merge [zeroEvent] [requestEvent, zeroEvent] = [zeroEvent, requestEvent] ∧
    ids (merge [zeroEvent] [requestEvent, zeroEvent]) = {⟨26⟩, ⟨27⟩} := by
  decide

/-- Teeth, rebuilt: two canonical views, equal keysets, different content. -/
theorem crossCanonical_is_the_gap :
    ∃ B₁ B₂ : View lengthScheme, Canonical B₁ ∧ Canonical B₂ ∧ ids B₁ = ids B₂ ∧
      ¬ CrossCanonical B₁ B₂ ∧ ¬ SameView B₁ B₂ :=
  ⟨[requestEvent], [effectEvent], by decide, by decide, by decide, by decide,
    fun hv => absurd (hv ⟨27⟩) (by decide)⟩

/-- The damage: at a colliding address the merge discards a DIFFERENT event. -/
theorem merge_drops_at_collision :
    merge [requestEvent] [effectEvent] = [requestEvent] ∧ requestEvent ≠ effectEvent := by
  decide

/-! ## 7. Axiom pins -/

/-- info: 'Minidregg.Theory.LaceMerge.ids_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ids_merge

/-- info: 'Minidregg.Theory.LaceMerge.sameView_of_canonical_eq_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sameView_of_canonical_eq_ids

/-- info: 'Minidregg.Theory.LaceMerge.crossCanonical_of_binding' does not depend on any axioms -/
#guard_msgs in #print axioms crossCanonical_of_binding

/-- info: 'Minidregg.Theory.LaceMerge.merge_converges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms merge_converges

/-- info: 'Minidregg.Theory.LaceMerge.injectiveScheme_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms injectiveScheme_binding

/-- info: 'Minidregg.Theory.LaceMerge.lengthScheme_not_binding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lengthScheme_not_binding

/-- info: 'Minidregg.Theory.LaceMerge.crossCanonical_is_the_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms crossCanonical_is_the_gap

/-- info: 'Minidregg.Theory.LaceMerge.merge_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms merge_computes

end Minidregg.Theory.LaceMerge
