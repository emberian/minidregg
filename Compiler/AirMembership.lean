/-
# `Compiler/AirMembership.lean` — [AIR-membership]: the Merkle-membership gadget, DERIVED through the DSL

A note-spend must prove its note is IN the committed set without revealing which one: a
Merkle PATH — hash the leaf with a sibling at each level, a direction BIT choosing the
order, and assert the fold reaches the claimed root. With `[AIR-poseidon]` (the hash) and
`[AIR-range]` (the amounts) closed, this is the last note-spend gadget: it brings
`[PRIVATE-TURN-air]` — the soundly-constrained private turn — into composition reach.

**Substrate, said out loud: this is Lean-authored arithmetization.** Every wire of every
level is a `Term (AirSig F Idx)` built from the DSL surface (`vr`/`cst`/`add'`/`mul'`) and
read through the one fold (`eval = fold evalAlg`); the gadget is a `ConstraintSystem`; its
meaning comes from rung 1's initiality keystone (`accepts_iff_semHolds` /
`systemAccepts_iff_systemSemHolds`) — reused, never re-derived. The compression is
`AirHash`'s `permGadget`/`permExec`/`hashExec` REUSED (the level assertion is `hashTerm`'s
shape with the path folded in); the direction bits are rung 1's `boolGadget`. NO constraint
is hand-authored outside the DSL: no Rust, no bespoke `air_accepts`, no parallel executor.

## The construction

A depth-`k` path is a list of `(sibling wire, direction wire)` pairs. Fold up from the leaf:

* `muxTerm d a b` — the selector `a·(1−d) + b·d`: `a` at `d = 0`, `b` at `d = 1`;
* `levelTerm` — one level: `H2(mux(d; node, sib), mux(d; sib, node))`, i.e. `d = 0` keeps
  the node LEFT (`H2(node, sib)`), `d = 1` puts it RIGHT (`H2(sib, node)`); the compression
  `H2` is `permGadget` on the width-2 state, first output wire (`compressExec = hashExec`);
* `pathTerm` — the levels composed by `List.foldl`, the whole path ONE nested DSL term
  (`AirHash` set the precedent: all rounds in one term; degree is `[AIR-flatten]`'s rung,
  applied downstream);
* `membershipGadget` — the system: `boolGadget` per direction wire + the root assertion
  `pathTerm − root ≐ 0`.

The EXECUTORS: `merkleExec` (the REFERENCE fold — genuine `Bool` bits, if-then-else order)
and `merkleMuxExec` (the mux-ARITHMETIC fold on field direction values — what the circuit
literally computes; on boolean-encoded bits the two coincide: `merkleMuxExec_encode`).

## Statement-first (the ATLAS fields)

* `membership_correct` — the keystone iff, EVERY depth, EVERY wire list, EVERY assignment:
  the system accepts `asg` IFF every direction wire is boolean AND the root wire carries
  exactly the fold of the leaf/sibling/direction wire values. Composed from
  `permGadget_eval_apply` (per level, `AirHash`'s keystone), `boolGadget_correct` (per
  bit), and the system-level initiality transfer — no new induction beyond one list fold.
* `membership_meaning` — the SET-MEMBERSHIP framing, closed both ways at the canonical
  wire layout: an assignment carrying `(leaf, root)` satisfies the depth-`k` gadget IFF
  `memberAtDepth spec k root leaf` — there EXIST `k` siblings and direction bits folding
  `leaf` up to `root`, i.e. `leaf` sits at SOME position of a depth-`k` tree with that
  root. Soundness (`membership_sound`) and completeness (`membership_complete`) fall out.
* Teeth, general form: a root wire that is NOT the path's fold is REJECTED
  (`membership_teeth`); a non-boolean direction wire is REJECTED (`membership_teeth_bit`).
* Keystone witnesses, BUILT over `ZMod 13` with `AirHash`'s `demoSpec`, depth 2: the
  member accepts (leaf `9`, path `[(4, true), (7, false)]`, root `8` — both bit values
  exercised); a wrong root rejected; a non-boolean direction rejected WITH the attribution
  machine-checked (the root assertion alone accepts it — booleanity did the rejecting);
  the direction bit genuinely selects order (swapping it moves the root `8 → 3`, and the
  old root is rejected under the swapped bit); every accepted root equals the fold
  (derived from the iff, closed over the field). Depth 1 is additionally decided RAW
  against the real fold end-to-end.

## Honest scope — what this file does NOT claim

* Depth is CLOSED, general: all theorems quantify over arbitrary path lists — there is no
  `[AIR-membership-depth]` residual. (Depth-2 `decide` witnesses go THROUGH the proven iff
  because kernel-reducing the doubly-nested path term is expensive — that reduction is
  exactly what `membership_correct` discharges once and for all; depth 1 is also decided
  raw as the end-to-end fold exercise.)
* `[COMMIT-CR]` FLOOR: the gadget enforces the FOLD EQUATION. That a dishonest prover
  cannot exhibit a path for a leaf OUTSIDE the committed set is collision resistance of
  the instantiated compression — a cryptographic assumption about `[AIR-poseidon-params]`,
  named, never a theorem here.
* `[AIR-poseidon-params]` upstream: the deployed compression parameters (and the
  two-child state's rate/capacity discipline) are the hash rung's residual, inherited.
* Degree: the nested path term is high-degree; bounded-degree gate form is
  `[AIR-flatten]`'s closed rung, applied downstream, not re-proved here.
* `[PRIVATE-TURN-air]`: hash + range + membership now all close at gadget level; the
  COMPOSED note-spend statement (nullifier + amount range + membership over one shared
  witness) is the remaining rung, by list append on this file's systems.
-/
import Compiler.AirHash

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u}

/-! ## §1. The mux — `a·(1−d) + b·d`, the direction selector, term and executor. -/

/-- The mux EXECUTOR: `a·(1−d) + b·d` — `a` at `d = 0`, `b` at `d = 1`; pure field
arithmetic on an arbitrary field value `d` (the boolean READING needs `boolGadget`). -/
def muxExec (d a b : F) : F := a * (1 - d) + b * d

@[simp] theorem muxExec_zero (a b : F) : muxExec 0 a b = a := by unfold muxExec; ring

@[simp] theorem muxExec_one (a b : F) : muxExec 1 a b = b := by unfold muxExec; ring

/-- The mux TERM: `a·(1 + (−1)·d) + b·d`, built from the DSL surface. -/
def muxTerm (d a b : Term (AirSig F Idx)) : Term (AirSig F Idx) :=
  add' (mul' a (add' (cst 1) (mul' (cst (-1)) d))) (mul' b d)

/-- The circuit reads the mux as the mux. -/
@[simp] theorem eval_muxTerm (asg : Idx → F) (d a b : Term (AirSig F Idx)) :
    eval asg (muxTerm d a b) = muxExec (eval asg d) (eval asg a) (eval asg b) := by
  unfold muxTerm muxExec
  simp only [eval_add', eval_mul', eval_cst]
  ring

/-! ## §2. The compression and the two executors — reference (`Bool` bits) and
mux-arithmetic (field bits), with the encoding bridge between them. -/

/-- The two-child compression `H2(a, b)`: `AirHash`'s `hashExec` on the width-2 state —
REUSED, not re-derived. -/
def compressExec (spec : PermSpec F 2) (a b : F) : F := hashExec spec ![a, b]

/-- One level of the fold, mux-arithmetic form: compress
`(mux(d; n, s), mux(d; s, n))` — what the circuit literally computes at a level, for ANY
field value `d`. -/
def muxStepExec (spec : PermSpec F 2) (n : F) (sd : F × F) : F :=
  compressExec spec (muxExec sd.2 n sd.1) (muxExec sd.2 sd.1 n)

/-- The mux-arithmetic fold: `merkleExec`'s shape with FIELD direction values — the
executor the circuit computes verbatim (booleanity is imposed separately by the gadget). -/
def merkleMuxExec (spec : PermSpec F 2) (leaf : F) (path : List (F × F)) : F :=
  path.foldl (muxStepExec spec) leaf

/-- **`merkleExec` — the REFERENCE Merkle fold.** `node₀ = leaf`;
`node_{j+1} = if dⱼ then H2(sⱼ, nodeⱼ) else H2(nodeⱼ, sⱼ)`; the result is the root the
path claims. Genuine `Bool` direction bits — the semantics a Merkle tree means. -/
def merkleExec (spec : PermSpec F 2) (leaf : F) (path : List (F × Bool)) : F :=
  path.foldl
    (fun n sd => bif sd.2 then compressExec spec sd.1 n else compressExec spec n sd.1) leaf

@[simp] theorem merkleMuxExec_nil (spec : PermSpec F 2) (leaf : F) :
    merkleMuxExec spec leaf [] = leaf := rfl

@[simp] theorem merkleMuxExec_cons (spec : PermSpec F 2) (leaf : F) (sd : F × F)
    (path : List (F × F)) :
    merkleMuxExec spec leaf (sd :: path)
      = merkleMuxExec spec (muxStepExec spec leaf sd) path := rfl

@[simp] theorem merkleExec_nil (spec : PermSpec F 2) (leaf : F) :
    merkleExec spec leaf [] = leaf := rfl

@[simp] theorem merkleExec_cons (spec : PermSpec F 2) (leaf : F) (sd : F × Bool)
    (path : List (F × Bool)) :
    merkleExec spec leaf (sd :: path)
      = merkleExec spec
          (bif sd.2 then compressExec spec sd.1 leaf else compressExec spec leaf sd.1)
          path := rfl

/-- The boolean encoding into the field: `false ↦ 0`, `true ↦ 1`. -/
def encodeBit (b : Bool) : F := bif b then 1 else 0

/-- Encode one path step: keep the sibling, encode the bit. -/
def encodeStep (sd : F × Bool) : F × F := (sd.1, encodeBit sd.2)

theorem muxStepExec_zero (spec : PermSpec F 2) (n s : F) :
    muxStepExec spec n (s, 0) = compressExec spec n s := by
  unfold muxStepExec
  rw [muxExec_zero, muxExec_zero]

theorem muxStepExec_one (spec : PermSpec F 2) (n s : F) :
    muxStepExec spec n (s, 1) = compressExec spec s n := by
  unfold muxStepExec
  rw [muxExec_one, muxExec_one]

/-- **The encoding bridge**: on boolean-ENCODED direction values the mux-arithmetic fold
IS the reference fold — the mux degenerates to genuine selection. -/
theorem merkleMuxExec_encode (spec : PermSpec F 2) :
    ∀ (bpath : List (F × Bool)) (leaf : F),
      merkleMuxExec spec leaf (bpath.map encodeStep) = merkleExec spec leaf bpath
  | [], _ => rfl
  | (s, b) :: bpath, leaf => by
    cases b <;>
      simp only [List.map_cons, merkleMuxExec_cons, merkleExec_cons, encodeStep, encodeBit,
        cond_false, cond_true, muxStepExec_zero, muxStepExec_one] <;>
      exact merkleMuxExec_encode spec bpath _

/-! ## §3. The path CIRCUIT — every level a DSL term, the compression `permGadget` reused. -/

/-- One LEVEL of the path circuit: compress the current node term with the sibling wire,
the direction wire choosing the order via the mux — `d = 0`: `H2(node, sib)`; `d = 1`:
`H2(sib, node)`. The compression is `AirHash`'s `permGadget` (first output wire). -/
def levelTerm (spec : PermSpec F 2) (node : Term (AirSig F Idx)) (sd : Idx × Idx) :
    Term (AirSig F Idx) :=
  permGadget spec ![muxTerm (vr sd.2) node (vr sd.1), muxTerm (vr sd.2) (vr sd.1) node] 0

/-- The whole PATH circuit: the levels composed by `List.foldl` from the leaf term — one
nested DSL term, `AirHash`'s all-rounds-in-one-term precedent lifted to the tree. -/
def pathTerm (spec : PermSpec F 2) (leaf : Term (AirSig F Idx))
    (path : List (Idx × Idx)) : Term (AirSig F Idx) :=
  path.foldl (levelTerm spec) leaf

/-- One level, circuit ⟺ executor: evaluating the level gadget is the mux-arithmetic step
on the evaluated node and the wire values — `permGadget_eval_apply` doing the compression's
load-bearing transfer. -/
theorem eval_levelTerm (asg : Idx → F) (spec : PermSpec F 2)
    (node : Term (AirSig F Idx)) (sd : Idx × Idx) :
    eval asg (levelTerm spec node sd)
      = muxStepExec spec (eval asg node) (asg sd.1, asg sd.2) := by
  unfold levelTerm
  rw [permGadget_eval_apply]
  have hst : (fun j => eval asg
        (![muxTerm (vr sd.2) node (vr sd.1), muxTerm (vr sd.2) (vr sd.1) node] j))
      = ![muxExec (asg sd.2) (eval asg node) (asg sd.1),
          muxExec (asg sd.2) (asg sd.1) (eval asg node)] := by
    funext j
    fin_cases j <;> simp
  rw [hst]
  rfl

/-- The whole path, circuit ⟺ executor: evaluating the path circuit is the mux-arithmetic
fold of the evaluated leaf along the wire values — EVERY depth, one list induction. -/
theorem eval_pathTerm (asg : Idx → F) (spec : PermSpec F 2) :
    ∀ (path : List (Idx × Idx)) (t : Term (AirSig F Idx)),
      eval asg (pathTerm spec t path)
        = merkleMuxExec spec (eval asg t) (path.map fun sd => (asg sd.1, asg sd.2))
  | [], _ => rfl
  | sd :: path, t => by
    show eval asg (pathTerm spec (levelTerm spec t sd) path) = _
    rw [eval_pathTerm asg spec path (levelTerm spec t sd), eval_levelTerm]
    rfl

/-! ## §4. The MEMBERSHIP GADGET and its keystone iff. -/

/-- The root assertion: `pathTerm(leaf, path) − root ≐ 0` — `hashTerm`'s shape with the
whole path folded into the hash side. -/
def rootTerm (spec : PermSpec F 2) (leafW rootW : Idx) (path : List (Idx × Idx)) :
    Term (AirSig F Idx) :=
  add' (pathTerm spec (vr leafW) path) (mul' (cst (-1)) (vr rootW))

/-- **The membership gadget** `[AIR-membership]`: one booleanity assertion per direction
wire (rung 1's `boolGadget`, reused) + the root assertion — all DSL terms, composed as a
system. Composes with `hashConstraint` (nullifier) and `rangeGadget` (amounts) by list
append toward `[PRIVATE-TURN-air]`. -/
def membershipGadget (spec : PermSpec F 2) (leafW rootW : Idx)
    (path : List (Idx × Idx)) : ConstraintSystem F Idx :=
  (path.map fun sd => boolGadget sd.2) ++ [rootTerm spec leafW rootW path]

/-- The root assertion MEANS the fold equation: it accepts iff the root wire carries
exactly the mux-arithmetic fold of the leaf wire along the path wires. -/
theorem rootTerm_correct (asg : Idx → F) (spec : PermSpec F 2) (leafW rootW : Idx)
    (path : List (Idx × Idx)) :
    accepts asg (rootTerm spec leafW rootW path) ↔
      asg rootW = merkleMuxExec spec (asg leafW) (path.map fun sd => (asg sd.1, asg sd.2)) := by
  unfold accepts rootTerm
  simp only [eval_add', eval_mul', eval_cst]
  rw [eval_pathTerm asg spec]
  simp only [eval_vr]
  rw [neg_one_mul, add_neg_eq_zero]
  exact eq_comm

/-- **`membership_correct` — the keystone iff, every depth.** The system accepts `asg` IFF
every direction wire is boolean AND the root wire is EXACTLY the fold of the leaf wire
with the sibling wires in the direction-wire order. Derived: `boolGadget_correct` per bit,
`rootTerm_correct` (through `permGadget_eval_apply`, per level) for the fold — no bespoke
soundness argument. On boolean bits the fold IS the reference `merkleExec`
(`merkleMuxExec_encode`), so the two conjuncts read: the bits are bits, and hashing the
leaf up that position reaches the root. -/
theorem membership_correct (asg : Idx → F) (spec : PermSpec F 2) (leafW rootW : Idx)
    (path : List (Idx × Idx)) :
    systemAccepts asg (membershipGadget spec leafW rootW path) ↔
      ((∀ sd ∈ path, asg sd.2 = 0 ∨ asg sd.2 = 1) ∧
        asg rootW = merkleMuxExec spec (asg leafW)
          (path.map fun sd => (asg sd.1, asg sd.2))) := by
  unfold systemAccepts membershipGadget
  constructor
  · intro h
    refine ⟨fun sd hsd => ?_, ?_⟩
    · exact (boolGadget_correct asg sd.2).mp
        (h _ (List.mem_append_left _ (List.mem_map.mpr ⟨sd, hsd, rfl⟩)))
    · exact (rootTerm_correct asg spec leafW rootW path).mp
        (h _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · rintro ⟨hbool, hroot⟩ t ht
    rcases List.mem_append.mp ht with ht' | ht'
    · obtain ⟨sd, hsd, rfl⟩ := List.mem_map.mp ht'
      exact (boolGadget_correct asg sd.2).mpr (hbool sd hsd)
    · rw [List.mem_singleton.mp ht']
      exact (rootTerm_correct asg spec leafW rootW path).mpr hroot

/-- The EXECUTOR reading of the keystone, via rung 1's initiality transfer — the semantic
relation of the membership system is the same statement. -/
theorem membership_semHolds_correct (asg : Idx → F) (spec : PermSpec F 2)
    (leafW rootW : Idx) (path : List (Idx × Idx)) :
    systemSemHolds asg (membershipGadget spec leafW rootW path) ↔
      ((∀ sd ∈ path, asg sd.2 = 0 ∨ asg sd.2 = 1) ∧
        asg rootW = merkleMuxExec spec (asg leafW)
          (path.map fun sd => (asg sd.1, asg sd.2))) := by
  rw [← systemAccepts_iff_systemSemHolds, membership_correct]

/-- **Teeth (root), general form**: an assignment whose root wire is NOT the path's fold
is REJECTED — the membership binds the root, for every spec, depth, and assignment. -/
theorem membership_teeth (asg : Idx → F) (spec : PermSpec F 2) (leafW rootW : Idx)
    (path : List (Idx × Idx))
    (h : asg rootW ≠ merkleMuxExec spec (asg leafW)
      (path.map fun sd => (asg sd.1, asg sd.2))) :
    ¬ systemAccepts asg (membershipGadget spec leafW rootW path) :=
  fun hacc => h ((membership_correct asg spec leafW rootW path).mp hacc).2

/-- **Teeth (bits), general form**: a non-boolean direction wire is REJECTED — the mux is
only a selector because booleanity is separately imposed, and it genuinely is. -/
theorem membership_teeth_bit (asg : Idx → F) (spec : PermSpec F 2) (leafW rootW : Idx)
    (path : List (Idx × Idx)) (sd : Idx × Idx) (hsd : sd ∈ path)
    (h0 : asg sd.2 ≠ 0) (h1 : asg sd.2 ≠ 1) :
    ¬ systemAccepts asg (membershipGadget spec leafW rootW path) := fun hacc => by
  rcases ((membership_correct asg spec leafW rootW path).mp hacc).1 sd hsd with h | h
  exacts [h0 h, h1 h]

/-! ## §5. The SET-MEMBERSHIP framing — "∃ path ⟹ member", closed both ways.

The canonical wire layout (`MWire`): one leaf wire, one root wire, `k` sibling and `k`
direction wires. `memberAtDepth spec k root leaf` — some depth-`k` path folds `leaf` to
`root`, i.e. `leaf` occupies SOME position of a depth-`k` Merkle tree with that root —
is EXACTLY satisfiability of the gadget with `(leaf, root)` on their wires. -/

/-- Canonical wire layout for a depth-`k` membership instance. -/
inductive MWire (k : ℕ) : Type u where
  | leafW : MWire k
  | rootW : MWire k
  | sibW (j : Fin k) : MWire k
  | dirW (j : Fin k) : MWire k

/-- The canonical `(sibling, direction)` wire list. -/
def canonPath (k : ℕ) : List (MWire.{u} k × MWire.{u} k) :=
  List.ofFn fun j => (MWire.sibW j, MWire.dirW j)

/-- **Set membership at depth `k`**: some `k`-level sibling+bit path folds `leaf` up to
`root` — "`leaf` is in the set committed by `root`". (That a dishonest path for a
NON-member requires a compression collision is `[COMMIT-CR]`, the named floor.) -/
def memberAtDepth (spec : PermSpec F 2) (k : ℕ) (root leaf : F) : Prop :=
  ∃ bpath : List (F × Bool), bpath.length = k ∧ merkleExec spec leaf bpath = root

/-- Field values that are each `0` or `1` are SOME encoded `Bool` list — the decode
half of the boolean bridge. -/
theorem exists_boolPath : ∀ {path : List (F × F)},
    (∀ sd ∈ path, sd.2 = 0 ∨ sd.2 = 1) →
      ∃ bpath : List (F × Bool), path = bpath.map encodeStep
  | [], _ => ⟨[], rfl⟩
  | (s, d) :: path, h => by
    obtain ⟨bpath, hb⟩ := exists_boolPath fun sd hsd => h sd (List.mem_cons_of_mem _ hsd)
    rcases h (s, d) List.mem_cons_self with h0 | h1
    · refine ⟨(s, false) :: bpath, ?_⟩
      rw [List.map_cons, ← hb]
      have hd : d = 0 := h0
      rw [hd]
      rfl
    · refine ⟨(s, true) :: bpath, ?_⟩
      rw [List.map_cons, ← hb]
      have hd : d = 1 := h1
      rw [hd]
      rfl

/-- The canonical accepting assignment for a `Bool` path: leaf/root on their wires, the
`j`-th sibling and ENCODED direction bit on theirs. -/
def canonAsg (leaf root : F) (bpath : List (F × Bool)) : MWire.{u} bpath.length → F
  | .leafW => leaf
  | .rootW => root
  | .sibW j => (bpath.get j).1
  | .dirW j => encodeBit (bpath.get j).2

/-- Reading the canonical assignment along the canonical wires recovers the encoded path. -/
theorem canonAsg_map (leaf root : F) (bpath : List (F × Bool)) :
    ((canonPath bpath.length).map fun sd =>
        (canonAsg leaf root bpath sd.1, canonAsg leaf root bpath sd.2))
      = bpath.map encodeStep := by
  show List.map _ (List.ofFn _) = _
  rw [List.map_ofFn]
  show List.ofFn (encodeStep ∘ bpath.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- The canonical assignment's direction wires are boolean. -/
theorem canonAsg_bool (leaf root : F) (bpath : List (F × Bool)) :
    ∀ sd ∈ canonPath bpath.length,
      canonAsg leaf root bpath sd.2 = 0 ∨ canonAsg leaf root bpath sd.2 = 1 := by
  intro sd hsd
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hsd
  show encodeBit (bpath.get j).2 = 0 ∨ encodeBit (bpath.get j).2 = 1
  cases (bpath.get j).2
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Completeness / premise-inhabitation**: every genuine path HAS its accepting
assignment — the canonical one. The iff of `membership_correct` has teeth both ways. -/
theorem membership_complete (spec : PermSpec F 2) (leaf root : F)
    (bpath : List (F × Bool)) (hroot : merkleExec spec leaf bpath = root) :
    systemAccepts (canonAsg leaf root bpath)
      (membershipGadget spec MWire.leafW MWire.rootW (canonPath bpath.length)) := by
  rw [membership_correct]
  refine ⟨canonAsg_bool leaf root bpath, ?_⟩
  show root = merkleMuxExec spec leaf _
  rw [canonAsg_map, merkleMuxExec_encode, hroot]

/-- **Soundness toward the set framing**: ANY accepted assignment exhibits membership of
its leaf-wire value under its root-wire value. -/
theorem membership_sound (spec : PermSpec F 2) (k : ℕ) (asg : MWire.{u} k → F)
    (hacc : systemAccepts asg (membershipGadget spec MWire.leafW MWire.rootW (canonPath k))) :
    memberAtDepth spec k (asg MWire.rootW) (asg MWire.leafW) := by
  obtain ⟨hbool, heq⟩ :=
    (membership_correct asg spec MWire.leafW MWire.rootW (canonPath k)).mp hacc
  obtain ⟨bpath, hb⟩ := exists_boolPath
    (path := (canonPath k).map fun sd => (asg sd.1, asg sd.2))
    (by rintro sd hsd
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hsd
        exact hbool w hw)
  refine ⟨bpath, ?_, ?_⟩
  · have hlen := congrArg List.length hb
    simpa [canonPath] using hlen.symm
  · rw [heq, hb, merkleMuxExec_encode]

/-- **`membership_meaning` — the set-membership framing, closed both ways.** An assignment
carrying `(leaf, root)` on the canonical wires satisfies the depth-`k` membership gadget
IFF `leaf` is a depth-`k` member under `root`: the gadget IS "∃ siblings + direction bits
folding `leaf` to `root`" — the leaf sits at some position of the committed tree. -/
theorem membership_meaning (spec : PermSpec F 2) (k : ℕ) (leaf root : F) :
    (∃ asg : MWire.{u} k → F, asg MWire.leafW = leaf ∧ asg MWire.rootW = root ∧
        systemAccepts asg (membershipGadget spec MWire.leafW MWire.rootW (canonPath k))) ↔
      memberAtDepth spec k root leaf := by
  constructor
  · rintro ⟨asg, hleaf, hroot, hacc⟩
    rw [← hleaf, ← hroot]
    exact membership_sound spec k asg hacc
  · rintro ⟨bpath, hlen, hroot⟩
    subst hlen
    exact ⟨canonAsg leaf root bpath, rfl, rfl,
      membership_complete spec leaf root bpath hroot⟩

/-! ## §6. Keystone witnesses — BUILT over `ZMod 13` with `AirHash`'s `demoSpec`, depth 2,
all computing via the `Decidable` instances (`decide`), the gadget-level ones routed
through the PROVEN iff (`membership_correct`) and the attribution through
`rootTerm_correct` — the executor arithmetic decides fast; kernel-reducing the raw nested
path term at depth 2 is exactly the cost the iff retires. Depth 1 IS decided raw against
the real fold (§ below), so the term-side computes end-to-end too.

The demo tree: `H2 = hashExec demoSpec` with `H2(4,9) = 4`, `H2(9,4) = 1`, `H2(4,7) = 8`,
`H2(1,7) = 3`. Leaf `9` at position `(d₀, d₁) = (true, false)` with siblings `(4, 7)`:
`node₁ = H2(4, 9) = 4` (bit `true`: sibling left), root `= H2(4, 7) = 8` (bit `false`:
node left). Both bit values are exercised in one witness. -/

/-- Demo assignment on the canonical depth-2 wires. -/
def memberAsg (leaf root : ZMod 13) (sib dir : Fin 2 → ZMod 13) : MWire 2 → ZMod 13
  | .leafW => leaf
  | .rootW => root
  | .sibW j => sib j
  | .dirW j => dir j

/-- *The executor computes*: leaf `9` under path `[(4, true), (7, false)]` folds to `8`. -/
example : merkleExec demoSpec 9 [(4, true), (7, false)] = 8 := by decide

/-- *Satisfiable, computed*: the member (leaf `9`, siblings `(4, 7)`, bits `(1, 0)`, root
`8`) ACCEPTS — through the keystone iff, the executor side decided. -/
example : systemAccepts (memberAsg 9 8 ![4, 7] ![1, 0])
    (membershipGadget demoSpec MWire.leafW MWire.rootW (canonPath 2)) := by
  rw [membership_correct]
  decide

/-- *Teeth (wrong root), computed*: root `5 ≠ 8` under the same path is REJECTED — the
membership genuinely binds the claimed root to the path's fold. -/
example : ¬ systemAccepts (memberAsg 9 5 ![4, 7] ![1, 0])
    (membershipGadget demoSpec MWire.leafW MWire.rootW (canonPath 2)) := by
  rw [membership_correct]
  decide

/-- *Teeth (non-boolean direction), computed*: direction `d₀ = 2` is REJECTED — even with
the root wire set to `7`, the exact value the mux-arithmetic fold takes at `δ = 2`. -/
example : ¬ systemAccepts (memberAsg 9 7 ![4, 7] ![2, 0])
    (membershipGadget demoSpec MWire.leafW MWire.rootW (canonPath 2)) := by
  rw [membership_correct]
  decide

/-- *…and the attribution is machine-checked, not asserted*: the root assertion ALONE
accepts that assignment (the fold at `δ = 2` really is `7`) — so the rejection above is
booleanity's doing. The mux is only a SELECTOR because `boolGadget` bites. -/
example : accepts (memberAsg 9 7 ![4, 7] ![2, 0])
    (rootTerm demoSpec MWire.leafW MWire.rootW (canonPath 2)) := by
  rw [rootTerm_correct]
  decide

/-- *The direction bit genuinely selects the order* (executor): swapping `d₀` from `true`
to `false` moves the root `8 → 3` — `H2(9,4) = 1`, `H2(1,7) = 3`, and `3 ≠ 8`. -/
example : merkleExec demoSpec 9 [(4, false), (7, false)] = 3 ∧ (3 : ZMod 13) ≠ 8 := by
  decide

/-- *…and the gadget enforces the selection*: the swapped bit under the ORIGINAL root `8`
is REJECTED — the position is load-bearing, not decorative. -/
example : ¬ systemAccepts (memberAsg 9 8 ![4, 7] ![0, 0])
    (membershipGadget demoSpec MWire.leafW MWire.rootW (canonPath 2)) := by
  rw [membership_correct]
  decide

/-- *The teeth are the iff's, not an enumeration*: EVERY accepted root for this leaf and
path equals `8` — derived from `membership_correct`, closed over all 13 field values. -/
example (r : ZMod 13)
    (h : systemAccepts (memberAsg 9 r ![4, 7] ![1, 0])
      (membershipGadget demoSpec MWire.leafW MWire.rootW (canonPath 2))) : r = 8 := by
  have hb := ((membership_correct _ demoSpec _ _ _).mp h).2
  have hv : merkleMuxExec demoSpec 9 [(4, 1), (7, 0)] = 8 := by decide
  exact hb.trans hv

/-- *Membership, the set framing, instantiated*: leaf `9` IS a depth-2 member under root
`8`, and by `membership_meaning` some assignment carries exactly that. -/
example : ∃ asg : MWire 2 → ZMod 13, asg MWire.leafW = 9 ∧ asg MWire.rootW = 8 ∧
    systemAccepts asg (membershipGadget demoSpec MWire.leafW MWire.rootW (canonPath 2)) :=
  (membership_meaning demoSpec 2 9 8).mpr ⟨[(4, true), (7, false)], rfl, by decide⟩

/-- *Depth 1, decided RAW against the real fold*: the accepting assignment (leaf `9`,
sibling `4`, bit `1`, root `H2(4,9) = 4`) is checked by kernel-evaluating the ACTUAL
nested DSL term through `eval = fold evalAlg` — no route through the iff, the end-to-end
fold exercise. -/
example : systemAccepts
    (fun w => match w with
      | .leafW => (9 : ZMod 13) | .rootW => 4 | .sibW _ => 4 | .dirW _ => 1)
    (membershipGadget demoSpec MWire.leafW MWire.rootW (canonPath 1)) := by
  decide

/-! ### Honest residuals — the rungs above this one (named, none stubbed)

Depth is CLOSED: every theorem above quantifies over arbitrary path lists — no
`[AIR-membership-depth]` residual exists.

`[COMMIT-CR]` — the gadget enforces the FOLD EQUATION; that no dishonest prover can
exhibit a path for a non-member is collision resistance of the instantiated compression,
a cryptographic assumption about `[AIR-poseidon-params]` (both inherited from `AirHash`,
named, never smuggled into a theorem).

`[AIR-flatten]` — the nested path term is high-degree; the bounded-degree gate form is
the flatten rung's closed theorem, applied downstream.

`[PRIVATE-TURN-air]` — the remaining composition: `hashConstraint` (nullifier) +
`rangeGadget` (amounts) + `membershipGadget` (set membership) over one shared witness,
composed by list append — the soundly-constrained note-spend. `[AIR-sumcheck]` unchanged
upstream. -/

end Minidregg.Compiler
