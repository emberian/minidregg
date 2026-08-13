/-
# `Compiler/NoteSpend.lean` — [PRIVATE-TURN-air]: the shielded note-spend constraint system

The three note-spend gadgets are closed — `[AIR-range]` (`rangeGadget`), `[AIR-poseidon]`
(`hashConstraint`), `[AIR-membership]` (`membershipGadget`). This file COMPOSES them, by list
append, over ONE shared witness — the note — into the constraint system a private turn must
satisfy: the SHIELDED SPEND (design reference: `shielded_exact_apex_v4`). This closes
`[PRIVATE-TURN-air]` at the arithmetization level.

**Substrate, said out loud: this is Lean-authored arithmetization.** Every constraint below is
a `Term (AirSig F Idx)` produced by the three landed gadgets — `rangeGadget`, `hashConstraint`,
`membershipGadget` — REUSED, never re-derived, and read through the one fold
(`eval = fold evalAlg`); the composition is `List.append` on `ConstraintSystem`s and its meaning
is rung 1's initiality keystone lifted pointwise (`systemAccepts_iff_systemSemHolds`). NO
constraint is hand-authored outside the DSL: no Rust AIR (the breadstuffs `*_air.rs` note-spend
is the debt this replaces), no bespoke `air_accepts`, no parallel executor.

## The construction (the shielded spend)

The PRIVATE witness: a note (`w` field elements, one of which — `note vIdx` — is its VALUE),
the value's bit decomposition, the note's COMMITMENT, and a Merkle PATH (siblings + direction
bits) placing the commitment in the commitment tree. The PUBLIC statement: the revealed
NULLIFIER (binds the spend — double-reveal is double-spend), the tree ROOT, and the range
bound `2^k`. The system, all four gadgets over ONE assignment:

* `rangeGadget (noteW vIdx) bitsW` — the note's value is range-bounded;
* `hashConstraint nfSpec nullifierW noteW` — the nullifier is `H_nf(note)`;
* `hashConstraint cmSpec commitW noteW` — the commitment is `H_cm(note)`;
* `membershipGadget trSpec commitW rootW path` — the commitment sits in the tree at the root.

The SHARING is the point: the note-field wires `noteW` feed the value check AND both hashes,
and the commitment wire feeds both its hash and the membership leaf — tampering with any face
of the note breaks another gadget's equation (the keystones exhibit this with attribution).
Two hash specs (`nfSpec`/`cmSpec`) carry domain separation; a tree spec (`trSpec`) the
compression.

## Statement-first (the ATLAS fields)

* `noteSpend_correct` — the keystone iff: the system accepts `asg` IFF the conjunction of the
  three closed gadget meanings holds (bits boolean + recomposition; nullifier = hash; commitment
  = hash; direction bits boolean + root = the path fold). Proved by `systemAccepts_append` +
  the three gadgets' `_correct` iffs — no new induction, no bespoke soundness argument.
* `noteSpend_binds` — SOUNDNESS, generic wires: any accepted assignment IS a valid spend
  (`ValidSpend`) of the note it carries — value the cast of an integer `< 2^k`, nullifier
  correctly derived, commitment a member of the tree at the exposed root.
* `noteSpend_value_lt` — the deployment-label integer bound: over `ZMod p` with `2^k ≤ p`,
  an accepted spend's value wire carries a genuine `k`-bit integer.
* `noteSpend_meaning` — the spend relation, closed BOTH ways at the canonical wire layout
  (`SWire`): an assignment exposing `(nullifier, root)` satisfies the system IFF some note
  makes `ValidSpend nullifier root note` true. The mpr direction is premise-inhabitation
  (every valid spend has its accepting assignment, built by `spendAsg`).
* Keystone witnesses, BUILT over `ZMod 13` (the gadgets' `demoSpec` + a domain-separated
  `demoNfSpec`, `w = 2`, `k = 2`, depth 2): a concrete valid spend ACCEPTS (via the iff; depth 1
  additionally decided RAW against the real fold); teeth with machine-checked ATTRIBUTION — a
  wrong nullifier, an out-of-range value (quantified over ALL bit witnesses), and a wrong root
  are each REJECTED, and in each case the culprit gadget alone rejects while the other three
  accept; the shared-witness teeth — a TAMPERED note under the old nullifier is rejected even
  though commitment, membership, and range all still pass (the nullifier hash reads the same
  note wires); every accepted nullifier equals the hash (derived from the iff, closed over the
  field).

## The sound/hiding split — what this file IS and IS NOT

This file is the SOUND half of the private turn: `noteSpendSystem` is the relation a
satisfying assignment MUST inhabit — accepting means value-bounded, nullifier-derived,
note-committed. It says NOTHING about hiding. The HIDING half — that the verifier learns the
nullifier and root but nothing about the note — is the ZK layer: `selvage_zk_argument`
(`Selvage/ZK`, the OB-4 disclosure layer), cited here BY NAME because `Compiler` does not import
`Selvage`; the ZK argument proves knowledge of a satisfying assignment of THIS system without
revealing it. Neither layer re-derives the other. `[COMMIT-CR]` is the floor beneath both:
that a dishonest prover cannot forge a commitment opening or a membership path is collision
resistance of the instantiated hash — a cryptographic assumption about
`[AIR-poseidon-params]`, named, never a theorem here (the demo parameters are honestly NOT
collision-resistant, and a keystone below exhibits a real collision rather than hiding it).
-/
import Compiler.AirMembership

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u} {w k : ℕ}

/-! ## §1. Composition rule — `systemAccepts` distributes over append.

Gadgets compose by `List.append`; acceptance of the composite is the conjunction of the
parts' acceptances. This is the ONLY glue the note-spend needs — everything else is the three
gadgets' closed iffs. -/

/- `systemAccepts_append` — acceptance distributes over gadget composition — now lives at
its natural home, `Compiler/AirRange` §1 (beside `systemAccepts` itself), since the general
`Pred` compiler needs it below the note-spend rung. Same name, same statement; every use
site resolves unchanged. -/

/-! ## §2. The note-spend system and its keystone iff. -/

/-- **The shielded note-spend system** `[PRIVATE-TURN-air]`: the three closed gadgets over
ONE shared witness. `noteW` are the note's field wires (`noteW vIdx` its value), `bitsW` the
value's bit wires, `nullifierW`/`rootW` the public wires, `commitW` the note-commitment wire,
`path` the sibling/direction wires. Composition is list append — nothing else. -/
def noteSpendSystem [NeZero w] (nfSpec cmSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (noteW : Fin w → Idx) (vIdx : Fin w) (bitsW : Fin k → Idx)
    (nullifierW commitW rootW : Idx) (path : List (Idx × Idx)) : ConstraintSystem F Idx :=
  rangeGadget (noteW vIdx) bitsW ++
    (hashConstraint nfSpec nullifierW noteW ++
      (hashConstraint cmSpec commitW noteW ++
        membershipGadget trSpec commitW rootW path))

/-- **`noteSpend_correct` — the keystone iff.** The composed system accepts `asg` IFF all
three gadget meanings hold together over the ONE assignment: the value wire is a boolean
decomposition (range), the nullifier wire is the `nfSpec`-hash of the note wires, the
commitment wire is the `cmSpec`-hash of the SAME note wires, and the root wire is the Merkle
fold of the SAME commitment wire along boolean-directed path wires. Derived from
`systemAccepts_append` + `rangeGadget_correct` + `hashConstraint_correct` (twice) +
`membership_correct` — no new induction, no bespoke soundness argument. -/
theorem noteSpend_correct [NeZero w] (asg : Idx → F) (nfSpec cmSpec : PermSpec F w)
    (trSpec : PermSpec F 2) (noteW : Fin w → Idx) (vIdx : Fin w) (bitsW : Fin k → Idx)
    (nullifierW commitW rootW : Idx) (path : List (Idx × Idx)) :
    systemAccepts asg
        (noteSpendSystem nfSpec cmSpec trSpec noteW vIdx bitsW nullifierW commitW rootW path) ↔
      (((∀ i, asg (bitsW i) = 0 ∨ asg (bitsW i) = 1) ∧
          asg (noteW vIdx) = ∑ i : Fin k, asg (bitsW i) * (2 : F) ^ (i : ℕ)) ∧
        (asg nullifierW = hashExec nfSpec fun i => asg (noteW i)) ∧
        (asg commitW = hashExec cmSpec fun i => asg (noteW i)) ∧
        ((∀ sd ∈ path, asg sd.2 = 0 ∨ asg sd.2 = 1) ∧
          asg rootW = merkleMuxExec trSpec (asg commitW)
            (path.map fun sd => (asg sd.1, asg sd.2)))) := by
  unfold noteSpendSystem
  rw [systemAccepts_append, systemAccepts_append, systemAccepts_append,
    rangeGadget_correct, hashConstraint_correct, hashConstraint_correct, membership_correct]

/-- The EXECUTOR reading of the keystone, via rung 1's initiality transfer — the semantic
relation of the composed system is the same conjunction; drift between the circuit and
executor readings stays impossible at the composed level. -/
theorem noteSpend_semHolds_correct [NeZero w] (asg : Idx → F) (nfSpec cmSpec : PermSpec F w)
    (trSpec : PermSpec F 2) (noteW : Fin w → Idx) (vIdx : Fin w) (bitsW : Fin k → Idx)
    (nullifierW commitW rootW : Idx) (path : List (Idx × Idx)) :
    systemSemHolds asg
        (noteSpendSystem nfSpec cmSpec trSpec noteW vIdx bitsW nullifierW commitW rootW path) ↔
      (((∀ i, asg (bitsW i) = 0 ∨ asg (bitsW i) = 1) ∧
          asg (noteW vIdx) = ∑ i : Fin k, asg (bitsW i) * (2 : F) ^ (i : ℕ)) ∧
        (asg nullifierW = hashExec nfSpec fun i => asg (noteW i)) ∧
        (asg commitW = hashExec cmSpec fun i => asg (noteW i)) ∧
        ((∀ sd ∈ path, asg sd.2 = 0 ∨ asg sd.2 = 1) ∧
          asg rootW = merkleMuxExec trSpec (asg commitW)
            (path.map fun sd => (asg sd.1, asg sd.2)))) := by
  rw [← systemAccepts_iff_systemSemHolds, noteSpend_correct]

/-! ## §3. The spend RELATION and soundness — an accepted assignment IS a valid spend. -/

/-- **The valid-spend relation** — the statement the ZK layer proves knowledge of. Public:
the `nullifier`, the tree `root`, the bound `2^k`. Witness: the `note`. It holds when the
note's value is (the cast of) a `k`-bit integer, the nullifier is the note's `nfSpec`-hash,
and the note's `cmSpec`-commitment is a depth-`depth` member of the tree at `root`. -/
def ValidSpend [NeZero w] (nfSpec cmSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (vIdx : Fin w) (k depth : ℕ) (nullifier root : F) (note : Fin w → F) : Prop :=
  (∃ n : ℕ, n < 2 ^ k ∧ note vIdx = (n : F)) ∧
    nullifier = hashExec nfSpec note ∧
    memberAtDepth trSpec depth root (hashExec cmSpec note)

/-- Generic-wire membership soundness bridge: boolean direction values + the mux-fold
equation yield `memberAtDepth` — `exists_boolPath` decodes the field bits to `Bool`s and
`merkleMuxExec_encode` collapses the mux fold to the reference fold (both REUSED from
`AirMembership`). -/
theorem memberAtDepth_of_muxFold (spec : PermSpec F 2) (leaf root : F)
    (pvals : List (F × F)) (hbool : ∀ sd ∈ pvals, sd.2 = 0 ∨ sd.2 = 1)
    (hroot : root = merkleMuxExec spec leaf pvals) :
    memberAtDepth spec pvals.length root leaf := by
  obtain ⟨bpath, hb⟩ := exists_boolPath hbool
  refine ⟨bpath, ?_, ?_⟩
  · simpa using (congrArg List.length hb).symm
  · rw [hroot, hb, merkleMuxExec_encode]

/-- **`noteSpend_binds` — SOUNDNESS, the honest scope.** Any assignment the system accepts
IS a valid shielded spend of the note it carries: the value wire holds (the cast of) an
integer `< 2^k`, the exposed nullifier is the note's hash, and the note's commitment is a
member of the tree at the exposed root. This is the SOUND half of the private turn — what a
satisfying witness is FORCED to be. The HIDING half (the verifier learns nothing beyond
`(nullifier, root)`) is the ZK layer, `selvage_zk_argument` (`Selvage/ZK`), which proves knowledge
of a satisfying assignment of THIS system — cited, not re-derived. That forging a
commitment or a path needs a hash collision is `[COMMIT-CR]`, the named cryptographic floor
about `[AIR-poseidon-params]` — an assumption, never a theorem here. -/
theorem noteSpend_binds [NeZero w] (asg : Idx → F) (nfSpec cmSpec : PermSpec F w)
    (trSpec : PermSpec F 2) (noteW : Fin w → Idx) (vIdx : Fin w) (bitsW : Fin k → Idx)
    (nullifierW commitW rootW : Idx) (path : List (Idx × Idx))
    (hacc : systemAccepts asg
      (noteSpendSystem nfSpec cmSpec trSpec noteW vIdx bitsW nullifierW commitW rootW path)) :
    ValidSpend nfSpec cmSpec trSpec vIdx k path.length
      (asg nullifierW) (asg rootW) (fun i => asg (noteW i)) := by
  rw [noteSpend_correct] at hacc
  obtain ⟨⟨hbool, hsum⟩, hnf, hcm, hmbool, hmroot⟩ := hacc
  refine ⟨?_, hnf, ?_⟩
  · exact rangeGadget_bounds asg (noteW vIdx) bitsW
      ((rangeGadget_correct asg (noteW vIdx) bitsW).mpr ⟨hbool, hsum⟩)
  · have hb : ∀ sd ∈ (path.map fun sd => (asg sd.1, asg sd.2)), sd.2 = 0 ∨ sd.2 = 1 := by
      rintro q hq
      obtain ⟨sd, hsd, rfl⟩ := List.mem_map.mp hq
      exact hmbool sd hsd
    have h := memberAtDepth_of_muxFold trSpec (asg commitW) (asg rootW) _ hb hmroot
    rw [List.length_map] at h
    rw [← hcm]
    exact h

/-- The deployment-label integer bound: over `ZMod p` with `2^k ≤ p`, an accepted spend's
value wire carries a genuine `k`-bit integer — `rangeGadget_val_lt` through the composition.
The `2^k ≤ p` hypothesis is the parameter constraint on the label, exactly as on the range
rung. -/
theorem noteSpend_value_lt [NeZero w] {p : ℕ} [Fact p.Prime] (hp : 2 ^ k ≤ p)
    {Idx : Type} (asg : Idx → ZMod p) (nfSpec cmSpec : PermSpec (ZMod p) w)
    (trSpec : PermSpec (ZMod p) 2) (noteW : Fin w → Idx) (vIdx : Fin w)
    (bitsW : Fin k → Idx) (nullifierW commitW rootW : Idx) (path : List (Idx × Idx))
    (hacc : systemAccepts asg
      (noteSpendSystem nfSpec cmSpec trSpec noteW vIdx bitsW nullifierW commitW rootW path)) :
    (asg (noteW vIdx)).val < 2 ^ k := by
  rw [noteSpend_correct] at hacc
  exact rangeGadget_val_lt hp asg (noteW vIdx) bitsW
    ((rangeGadget_correct asg (noteW vIdx) bitsW).mpr hacc.1)

/-! ## §4. The canonical wire layout and the spend relation, closed both ways. -/

/-- Canonical wire layout for a `w`-field note, `k`-bit value, depth-`depth` spend: the note
fields, the value's bits, the two public wires (nullifier, root), the commitment, and the
path's sibling/direction wires. -/
inductive SWire (w k depth : ℕ) : Type u where
  | noteW (i : Fin w)
  | bitW (i : Fin k)
  | nullifierW
  | commitW
  | rootW
  | sibW (j : Fin depth)
  | dirW (j : Fin depth)

/-- The canonical `(sibling, direction)` wire list. -/
def spendPath (w k depth : ℕ) : List (SWire.{u} w k depth × SWire.{u} w k depth) :=
  List.ofFn fun j => (SWire.sibW j, SWire.dirW j)

theorem spendPath_length (w k depth : ℕ) : (spendPath.{u} w k depth).length = depth := by
  simp [spendPath]

/-- The canonical accepting assignment for a valid spend: the note on its wires, the bit
decomposition on the bit wires, the two hashes on nullifier/commitment, the root, and the
`Bool` path encoded onto the sibling/direction wires. -/
def spendAsg (note : Fin w → F) (b : Fin k → F) (nf cm root : F)
    (bpath : List (F × Bool)) : SWire.{u} w k bpath.length → F
  | .noteW i => note i
  | .bitW i => b i
  | .nullifierW => nf
  | .commitW => cm
  | .rootW => root
  | .sibW j => (bpath.get j).1
  | .dirW j => encodeBit (bpath.get j).2

/-- Reading the canonical assignment along the canonical wires recovers the encoded path. -/
theorem spendAsg_map (note : Fin w → F) (b : Fin k → F) (nf cm root : F)
    (bpath : List (F × Bool)) :
    ((spendPath w k bpath.length).map fun sd =>
        (spendAsg note b nf cm root bpath sd.1, spendAsg note b nf cm root bpath sd.2))
      = bpath.map encodeStep := by
  show List.map _ (List.ofFn _) = _
  rw [List.map_ofFn]
  show List.ofFn (encodeStep ∘ bpath.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- The canonical assignment's direction wires are boolean. -/
theorem spendAsg_dir_bool (note : Fin w → F) (b : Fin k → F) (nf cm root : F)
    (bpath : List (F × Bool)) :
    ∀ sd ∈ spendPath w k bpath.length,
      spendAsg note b nf cm root bpath sd.2 = 0 ∨
        spendAsg note b nf cm root bpath sd.2 = 1 := by
  intro sd hsd
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hsd
  show encodeBit (bpath.get j).2 = 0 ∨ encodeBit (bpath.get j).2 = 1
  cases (bpath.get j).2
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Completeness / premise-inhabitation**: every valid spend HAS its accepting
assignment — the canonical one. Feed it a boolean decomposition of the value and a genuine
`Bool` path and the whole composed system accepts. -/
theorem noteSpend_complete [NeZero w] (nfSpec cmSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (vIdx : Fin w) (note : Fin w → F) (b : Fin k → F) (root : F) (bpath : List (F × Bool))
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hsum : note vIdx = ∑ i : Fin k, b i * (2 : F) ^ (i : ℕ))
    (hroot : merkleExec trSpec (hashExec cmSpec note) bpath = root) :
    systemAccepts (spendAsg note b (hashExec nfSpec note) (hashExec cmSpec note) root bpath)
      (noteSpendSystem nfSpec cmSpec trSpec SWire.noteW vIdx SWire.bitW SWire.nullifierW
        SWire.commitW SWire.rootW (spendPath w k bpath.length)) := by
  rw [noteSpend_correct]
  refine ⟨⟨hb, hsum⟩, rfl, rfl, spendAsg_dir_bool note b _ _ root bpath, ?_⟩
  show root = _
  rw [spendAsg_map, merkleMuxExec_encode]
  exact hroot.symm

/-- **`noteSpend_meaning` — the spend relation, closed both ways.** An assignment exposing
`(nullifier, root)` on the public wires satisfies the composed system IFF some note makes
`ValidSpend` true — the constraint system IS the shielded-spend relation, no more and no
less. This is the statement the ZK layer (`selvage_zk_argument`) proves knowledge of; the
existential over `note` is exactly what stays hidden there. -/
theorem noteSpend_meaning [NeZero w] (nfSpec cmSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (vIdx : Fin w) (k depth : ℕ) (nf root : F) :
    (∃ asg : SWire.{u} w k depth → F,
        asg SWire.nullifierW = nf ∧ asg SWire.rootW = root ∧
        systemAccepts asg
          (noteSpendSystem nfSpec cmSpec trSpec SWire.noteW vIdx SWire.bitW SWire.nullifierW
            SWire.commitW SWire.rootW (spendPath w k depth))) ↔
      ∃ note : Fin w → F, ValidSpend nfSpec cmSpec trSpec vIdx k depth nf root note := by
  constructor
  · rintro ⟨asg, hnf, hroot, hacc⟩
    have h := noteSpend_binds asg nfSpec cmSpec trSpec SWire.noteW vIdx SWire.bitW
      SWire.nullifierW SWire.commitW SWire.rootW (spendPath w k depth) hacc
    rw [spendPath_length] at h
    rw [← hnf, ← hroot]
    exact ⟨_, h⟩
  · rintro ⟨note, ⟨n, hn, hv⟩, hnf, bpath, hlen, hroot⟩
    subst hlen
    subst hnf
    obtain ⟨b, hb, hsum⟩ := exists_boolDecomp (F := F) n hn
    exact ⟨spendAsg note b (hashExec nfSpec note) (hashExec cmSpec note) root bpath, rfl, rfl,
      noteSpend_complete nfSpec cmSpec trSpec vIdx note b root bpath hb (hv.trans hsum) hroot⟩

/-! ## §5. Keystone witnesses — BUILT over `ZMod 13`, the gadgets' `demoSpec` (commitment +
tree compression) plus a domain-separated `demoNfSpec` (nullifier), `w = 2`, `k = 2`,
depth 2. Gadget-level checks route through the PROVEN iff (`noteSpend_correct`) and decide
the executor side — the same discipline as `AirMembership` (kernel-reducing the nested path
term is the cost the iff retires); depth 1 is ALSO decided RAW against the real fold, the
end-to-end exercise.

The demo spend: note `(3, 8)` — value `3` (bits `(1,1)`, in `[0, 4)`), blinding `8`.
Nullifier `H_nf(3,8) = 4`; commitment `H_cm(3,8) = 7`; the commitment sits at position
`(d₀,d₁) = (1,0)` with siblings `(4,7)`: `H2(4,7) = 8`, `H2(8,7) = 11` — root `11`. (Same
`H2 = hashExec demoSpec` table as `AirMembership`'s demo tree.) -/

/-- Domain-separated demo spec for the NULLIFIER hash: same shape as `demoSpec` (α = 5,
full·partial·full, `demoM`), different round constants — the demo stand-in for the
domain-separation `[AIR-poseidon-params]` prescribes. -/
def demoNfSpec : PermSpec (ZMod 13) 2 where
  α := 5
  rounds :=
    [ ⟨![6, 2], true,  demoM⟩,
      ⟨![5, 3], false, demoM⟩,
      ⟨![7, 1], true,  demoM⟩ ]

/-- Demo assignment on the canonical wires (`w = 2`, `k = 2`, depth 2). -/
def spendKeyAsg (note b : Fin 2 → ZMod 13) (nf cm root : ZMod 13)
    (sib dir : Fin 2 → ZMod 13) : SWire 2 2 2 → ZMod 13 := fun wq =>
  match wq with
  | .noteW i => note i
  | .bitW i => b i
  | .nullifierW => nf
  | .commitW => cm
  | .rootW => root
  | .sibW j => sib j
  | .dirW j => dir j

/-- *The demo values are computed, not asserted*: nullifier, commitment, and root of the
demo note under the real executors. -/
example : hashExec demoNfSpec ![3, 8] = 4 ∧ hashExec demoSpec ![3, 8] = 7 ∧
    merkleExec demoSpec 7 [(4, true), (7, false)] = 11 := by decide

/-- *Satisfiable, computed*: the valid spend — note `(3,8)`, bits `(1,1)`, nullifier `4`,
commitment `7`, siblings `(4,7)`, directions `(1,0)`, root `11` — ACCEPTS the full
four-gadget system. -/
example : systemAccepts (spendKeyAsg ![3, 8] ![1, 1] 4 7 11 ![4, 7] ![1, 0])
    (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
      SWire.commitW SWire.rootW (spendPath 2 2 2)) := by
  rw [noteSpend_correct]
  decide

/-- *Depth 1, decided RAW against the real fold*: the whole composed system — range + both
hash constraints + membership — kernel-evaluated through `eval = fold evalAlg` on the ACTUAL
nested DSL terms, no route through the iff. Root `H2(4,7) = 8` (leaf = commitment `7`,
sibling `4`, direction `1`). -/
example : systemAccepts
    (fun wq : SWire 2 2 1 => match wq with
      | .noteW i => (![3, 8] : Fin 2 → ZMod 13) i
      | .bitW i => (![1, 1] : Fin 2 → ZMod 13) i
      | .nullifierW => 4
      | .commitW => 7
      | .rootW => 8
      | .sibW _ => 4
      | .dirW _ => 1)
    (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
      SWire.commitW SWire.rootW (spendPath 2 2 1)) := by
  decide

/-! ### Teeth, with machine-checked attribution — each rejection names its gadget by showing
the OTHER three accept the same assignment. -/

/-- *Teeth (wrong nullifier)*: nullifier `5 ≠ 4 = H_nf(3,8)` — the full system REJECTS. -/
example : ¬ systemAccepts (spendKeyAsg ![3, 8] ![1, 1] 5 7 11 ![4, 7] ![1, 0])
    (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
      SWire.commitW SWire.rootW (spendPath 2 2 2)) := by
  rw [noteSpend_correct]
  decide

/-- *…attribution*: everything EXCEPT the nullifier constraint accepts that assignment —
so the rejection above is the nullifier hash's doing. -/
example : systemAccepts (spendKeyAsg ![3, 8] ![1, 1] 5 7 11 ![4, 7] ![1, 0])
    (rangeGadget (SWire.noteW 0) SWire.bitW ++
      (hashConstraint demoSpec SWire.commitW SWire.noteW ++
        membershipGadget demoSpec SWire.commitW SWire.rootW (spendPath 2 2 2))) := by
  rw [systemAccepts_append, systemAccepts_append, rangeGadget_correct,
    hashConstraint_correct, membership_correct]
  decide

/-- *Teeth (value out of range), quantified*: note `(5, 8)` — value `5 ∉ [0, 4)` — with its
HONEST nullifier `H_nf(5,8) = 3`, commitment `H_cm(5,8) = 12`, and root
(`merkleExec` of `12` up the demo path `= 8`): NO bit assignment whatsoever makes the spend
accept. Every other gadget is satisfied honestly; the range genuinely bounds. -/
example : ¬ ∃ b : Fin 2 → ZMod 13,
    systemAccepts (spendKeyAsg ![5, 8] b 3 12 8 ![4, 7] ![1, 0])
      (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
        SWire.commitW SWire.rootW (spendPath 2 2 2)) := by
  rintro ⟨b, hb⟩
  rw [noteSpend_correct] at hb
  obtain ⟨⟨hbool, hsum⟩, -⟩ := hb
  have h0 := hbool 0
  have h1 := hbool 1
  rw [Fin.sum_univ_two] at hsum
  simp only [spendKeyAsg] at h0 h1 hsum
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] at hsum <;>
    revert hsum <;> decide

/-- *…attribution*: with bits `(0,0)` (any bits — the other gadgets never read bit wires),
everything EXCEPT the range gadget accepts the out-of-range spend — the rejection above is
the range's doing. -/
example : systemAccepts (spendKeyAsg ![5, 8] ![0, 0] 3 12 8 ![4, 7] ![1, 0])
    (hashConstraint demoNfSpec SWire.nullifierW SWire.noteW ++
      (hashConstraint demoSpec SWire.commitW SWire.noteW ++
        membershipGadget demoSpec SWire.commitW SWire.rootW (spendPath 2 2 2))) := by
  rw [systemAccepts_append, systemAccepts_append, hashConstraint_correct,
    hashConstraint_correct, membership_correct]
  decide

/-- *Teeth (non-member root)*: root `5 ≠ 11` — the full system REJECTS. -/
example : ¬ systemAccepts (spendKeyAsg ![3, 8] ![1, 1] 4 7 5 ![4, 7] ![1, 0])
    (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
      SWire.commitW SWire.rootW (spendPath 2 2 2)) := by
  rw [noteSpend_correct]
  decide

/-- *…attribution*: everything EXCEPT the membership gadget accepts that assignment — the
rejection above is the membership's doing. -/
example : systemAccepts (spendKeyAsg ![3, 8] ![1, 1] 4 7 5 ![4, 7] ![1, 0])
    (rangeGadget (SWire.noteW 0) SWire.bitW ++
      (hashConstraint demoNfSpec SWire.nullifierW SWire.noteW ++
        hashConstraint demoSpec SWire.commitW SWire.noteW)) := by
  rw [systemAccepts_append, systemAccepts_append, rangeGadget_correct,
    hashConstraint_correct, hashConstraint_correct]
  decide

/-! ### The shared witness at work — tampering the note trips ANOTHER gadget.

The toy compression COLLIDES (necessarily: it maps `F² → F`): notes `(3,8)` and `(2,8)`
share commitment `7`, so BOTH sit in the demo tree at root `11` and both are honestly
spendable — but under DIFFERENT nullifiers (`4` vs `9`). The nullifier hash reads the SAME
note wires as the commitment hash, so spending the tampered note under the old nullifier is
REJECTED even though range, commitment, and membership all still pass. That two distinct
notes share a commitment at all is exactly why `[COMMIT-CR]` is a FLOOR — binding is an
assumption about deployed parameters, exhibited here rather than hidden. -/

/-- *The collision, machine-checked*: distinct notes, same commitment. -/
example : hashExec demoSpec ![2, 8] = hashExec demoSpec ![3, 8] ∧
    (![2, 8] : Fin 2 → ZMod 13) ≠ ![3, 8] := by decide

/-- *The tampered note is honestly spendable* — under ITS OWN nullifier `H_nf(2,8) = 9`
(value `2`, bits `(0,1)`; same commitment `7`, same root `11`). -/
example : systemAccepts (spendKeyAsg ![2, 8] ![0, 1] 9 7 11 ![4, 7] ![1, 0])
    (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
      SWire.commitW SWire.rootW (spendPath 2 2 2)) := by
  rw [noteSpend_correct]
  decide

/-- *Teeth (shared witness)*: the tampered note under the OLD nullifier `4` is REJECTED —
the note wires feed the nullifier hash too. -/
example : ¬ systemAccepts (spendKeyAsg ![2, 8] ![0, 1] 4 7 11 ![4, 7] ![1, 0])
    (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
      SWire.commitW SWire.rootW (spendPath 2 2 2)) := by
  rw [noteSpend_correct]
  decide

/-- *…attribution*: range + commitment + membership all still accept the tampered note —
the rejection above is the nullifier hash's doing, i.e. the SHARING is load-bearing. -/
example : systemAccepts (spendKeyAsg ![2, 8] ![0, 1] 4 7 11 ![4, 7] ![1, 0])
    (rangeGadget (SWire.noteW 0) SWire.bitW ++
      (hashConstraint demoSpec SWire.commitW SWire.noteW ++
        membershipGadget demoSpec SWire.commitW SWire.rootW (spendPath 2 2 2))) := by
  rw [systemAccepts_append, systemAccepts_append, rangeGadget_correct,
    hashConstraint_correct, membership_correct]
  decide

/-- *The teeth are the iff's, not an enumeration*: EVERY accepted nullifier for the demo
note equals `4` — derived from `noteSpend_correct`, closed over all 13 field values. -/
example (nf : ZMod 13)
    (h : systemAccepts (spendKeyAsg ![3, 8] ![1, 1] nf 7 11 ![4, 7] ![1, 0])
      (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
        SWire.commitW SWire.rootW (spendPath 2 2 2))) : nf = 4 := by
  rw [noteSpend_correct] at h
  have hv : hashExec demoNfSpec ![3, 8] = 4 := by decide
  exact h.2.1.trans hv

set_option maxRecDepth 2048 in
/-- *The spend relation, instantiated*: `ValidSpend` for the demo note yields an accepting
assignment exposing exactly `(nullifier, root) = (4, 11)` — `noteSpend_meaning`'s mpr, the
generic witness builder landing on the demo. -/
example : ∃ asg : SWire 2 2 2 → ZMod 13,
    asg SWire.nullifierW = 4 ∧ asg SWire.rootW = 11 ∧
    systemAccepts asg
      (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
        SWire.commitW SWire.rootW (spendPath 2 2 2)) :=
  (noteSpend_meaning demoNfSpec demoSpec demoSpec 0 2 2 4 11).mpr
    ⟨![3, 8], ⟨3, by norm_num, by decide⟩, by decide, [(4, true), (7, false)], rfl, by decide⟩

/-- *The integer bound, instantiated*: any accepted spend over the demo layout carries a
genuine 2-bit integer on its value wire (`2^2 ≤ 13`). -/
example (asg : SWire 2 2 2 → ZMod 13)
    (h : systemAccepts asg
      (noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
        SWire.commitW SWire.rootW (spendPath 2 2 2))) :
    (asg (SWire.noteW 0)).val < 2 ^ 2 :=
  noteSpend_value_lt (by norm_num) asg demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW
    SWire.nullifierW SWire.commitW SWire.rootW (spendPath 2 2 2) h

/-! ### Honest scope — the sound/hiding split, and the floors (named, none stubbed)

**This file is the SOUND half of `[PRIVATE-TURN-air]`, and closes it at the arithmetization
level**: the composed constraint system a private turn must satisfy exists, is Lean-authored
end-to-end, and provably MEANS the shielded-spend relation (`noteSpend_correct` /
`noteSpend_meaning`, both directions, every width/bit-count/depth). What remains around it:

* HIDING is `selvage_zk_argument` (`Selvage/ZK`, the OB-4 disclosure layer): the verifier learns
  `(nullifier, root)` and NOT the note — that layer proves knowledge of a satisfying
  assignment of THIS system without revealing it. Cited by name (`Compiler` does not import
  `Selvage`); neither layer re-derives the other. Nothing in this file claims hiding.
* `[COMMIT-CR]` — that a dishonest prover cannot open a commitment two ways or exhibit a
  path for a non-member is collision resistance of the instantiated hash: a cryptographic
  ASSUMPTION about `[AIR-poseidon-params]`, exhibited honestly above (the demo parameters
  really do collide), never a theorem here.
* `[AIR-poseidon-params]` — deployed widths/constants/matrices/round counts and the sponge
  discipline, inherited from the hash rung; `demoNfSpec` is the domain-separation stand-in.
* Nullifier UNIQUENESS across turns (the double-spend ledger check: each nullifier revealed
  at most once) is a STATE-MACHINE property of the chain layer, not an arithmetization
  constraint — this system binds each spend to exactly one nullifier
  (`noteSpend_correct`'s hash conjunct); the ledger's reveal-set does the rest.
* `[AIR-flatten]` (bounded-degree gate form, closed upstream, applied downstream) and
  `[AIR-sumcheck]` (retiring the emitted constraints through `Selvage/SumcheckReduction`)
  unchanged upstream. -/

end Minidregg.Compiler
