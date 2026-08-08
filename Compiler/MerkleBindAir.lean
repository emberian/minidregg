/-
# `Compiler/MerkleBindAir.lean` — [RECURSE-merkle-bind]: the opened values Merkle-bound —
the emitted AIR is the WHOLE self-contained light-client verifier

**Substrate, said out loud: this is Lean-AUTHORED AIR.** Every constraint below is
AirMembership's `membershipGadget` — `boolGadget` bits + the `pathTerm` root assertion,
each a `Term (AirSig F Idx)` from the DSL surface read through the one fold — composed
with the landed `boundVerifier` by `++`; the meaning comes from `membership_correct` and
`boundVerifier_correct` (both rung 1's initiality downstream). NO check is hand-authored
outside the DSL: no Rust, no bespoke `air_accepts`, no parallel executor. The gadgets are
REUSED, never re-derived.

## What is arithmetized

`FiatShamirAir` closed the challenges (`boundVerifier`: FS-bound challenges ∧ sumcheck
accepts ∧ FRI-query accepts) and named the remaining mass `[RECURSE-merkle-bind]`: the
FRI-query wires `lo k`/`hi k` are OPENED values whose consistency is constrained but whose
PROVENANCE is not — a prover could feed the fold ANY values, not the committed codeword's.
This file closes that door:

* `OpeningsBound` — statement-first: per round, the direction wires are boolean and the
  committed root is EXACTLY the Merkle path fold of the opened value — the opened wire is
  a genuine member of the committed tree (`OpeningsBound.member` extracts `memberAtDepth`).
* `openingBindingGadget` — one `membershipGadget` per round (AirMembership's, verbatim):
  the opened wire is the LEAF, the round's commitment root wire the ROOT, the sibling +
  direction wires the path. In the deployed pair-per-leaf layout the round's OTHER opened
  value `hi k` IS the first sibling wire of `lo k`'s path (the leaf pair `(f(x), f(−x))`
  shares one authentication path) — wire-sharing, exercised in §5's demo — so BOTH opened
  values live under the root.
* `openingBinding_correct` — the keystone iff (accepts ⟺ `OpeningsBound`), plus the set
  framing closed both ways: soundness (`openingBinding_member` — every accepting
  assignment's opened values ARE `memberAtDepth` members), completeness
  (`openingBinding_complete` — genuine paths on the wires accept), and the ∃-form
  (`openingBinding_meaning` — an assignment exists IFF every opened value is a member).
* `fullVerifier` — `boundVerifier ++ openingBindingGadget` with the opened wires SHARED
  (`openedW k = lo k`): the WHOLE light-client verifier as ONE `ConstraintSystem`.
  `fullVerifier_correct`: accepts IFF (challenges FS-bound) ∧ (sumcheck accepts) ∧
  (FRI-query accepts) ∧ (openings Merkle-bound). `fullVerifier_binds`: at the shared
  wiring, EVERY accepting assignment has derived challenges AND member openings — nothing
  on the proof-carrying wires is free.

## The recursion point — THE CROWN

`fullVerifier` is a `ConstraintSystem`, so the verified emit path applies verbatim:
`emit_accepts_iff_fin` is consumed on the composed demo in §6. **"The full light-client
verifier accepted" — challenges derived by Fiat–Shamir, openings members of the committed
roots, sumcheck and FRI checks passed — is ONE emitted, Loom-provable statement.** A Loom
proof of that statement is a proof that a self-contained non-interactive proof verified:
a proof verifies a proof, with no free wire standing in for trust on the proof-carrying
path. What "verified" means here is priced exactly: the constraints force the conjunction
of `fullVerifier_correct`'s four clauses; the cryptographic floors and the remaining
composition mass are named below, none smuggled.

## The Loom correspondence (prose, boundary-honest)

`Compiler` may not import `Loom` (`Theory`-boundary law). `OpeningsBound` is the
in-circuit form of Loom's Merkle opening verification — the object the light client's
query checks read oracle values through; `memberAtDepth` is its set reading. The
machine-checked identification (Assurance-side, like the landed bridge residuals) is part
of `[RECURSE-full-resid]` below.

## Honest scope — `[RECURSE-full-resid]`, and the floors

`[RECURSE-full-resid]` — what remains between `fullVerifier` and the DEPLOYED light-client
statement, each piece named:
1. **Root absorption**: the commitment roots' own absorption into the FS transcript
   (root `k` absorbed BEFORE `β_k` is squeezed). The transcript wires are a PARAMETER, so
   this is the landed wire-sharing mechanism (`rootW k` placed in a transcript block); the
   theorems here do not yet REQUIRE that wiring — §5's demo transcript predates the roots.
2. **Sumcheck oracle binding**: the sumcheck's final oracle wire (`scFinalW`'s claimed
   `g(r)`) bound to a committed-polynomial opening — the SAME `openingBindingGadget`
   vocabulary at the oracle commitment, not instantiated here.
3. **Domain points**: `twoX k` bound to the FS-derived query index's domain point (the
   index-to-point power chain and per-round squaring) — new vocabulary, not landed.
4. **Query multiplicity**: ONE query path is arithmetized; deployment runs many queries —
   more instances of the same gadgets by `++`, instantiation not theory.
5. **The Loom bridges**: `[RECURSE-fs-bridge]`/`[RECURSE-sumcheck-bridge]`/
   `[RECURSE-fri-bridge]` plus the Merkle identification above, Assurance-side.

FLOORS (assumptions, never theorems here): `[COMMIT-CR]` — the binding forces
`root = fold`; that a forger cannot FIND another fold preimage is collision resistance of
the instantiated compression. §5 makes this floor CONCRETE: over `ZMod 13` the accepted
forgery set is exactly the collision fiber of the toy hash — findable in a 13-element
field, priced at deployed parameters by the label. `[FS-oracle]`, `[RECURSE-fs-sponge]`,
`[AIR-poseidon-params]` inherited from `FiatShamirAir`/`AirHash`.

## Statement-first (ATLAS fields)

* `OpeningsBound` — the binding as a `Prop`, stated BEFORE the gadget. Satisfiable: honest
  runs (genuine Merkle members, FS-derived challenges, both verifiers passing) accept —
  §5, decided over `ZMod 7` and the composed `ZMod 13` demo. Teeth: a FORGED opening —
  fold-consistent, chosen so the ENTIRE FS-bound verifier accepts it — is REJECTED by the
  opening binding, with machine-checked attribution; over `ZMod 7` the opened wire is
  FULLY DETERMINED (quantified iff over the field). Premise-inhabitation:
  `openingBinding_complete`/`openingBinding_meaning` build the accepting assignment for
  every genuine path family.
-/
import Compiler.FiatShamirAir

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u} {w s n rounds : ℕ}

/-! ## §1. The semantic spec, statement-first — every opened value under its root. -/

/-- **The opening binding, statement-first.** Per round: the direction values are boolean
and the committed root is EXACTLY the Merkle path fold of the opened value — the opened
value sits at a position of the tree the root commits to. This is the in-circuit form of
Loom's Merkle opening verification; the machine-checked identification is part of
`[RECURSE-full-resid]`. -/
def OpeningsBound (spec : PermSpec F 2) (rootv openedv : Fin rounds → F)
    (pathv : Fin rounds → List (F × F)) : Prop :=
  ∀ k, (∀ sd ∈ pathv k, sd.2 = 0 ∨ sd.2 = 1)
    ∧ rootv k = merkleMuxExec spec (openedv k) (pathv k)

/-- The set reading: a bound opening IS a `memberAtDepth` member — the boolean direction
values decode to a genuine `Bool` path (`exists_boolPath`) and the mux fold collapses to
the reference fold (`merkleMuxExec_encode`). -/
theorem OpeningsBound.member {spec : PermSpec F 2} {rootv openedv : Fin rounds → F}
    {pathv : Fin rounds → List (F × F)} (h : OpeningsBound spec rootv openedv pathv)
    (k : Fin rounds) : memberAtDepth spec (pathv k).length (rootv k) (openedv k) := by
  obtain ⟨hbool, heq⟩ := h k
  obtain ⟨bpath, hb⟩ := exists_boolPath hbool
  refine ⟨bpath, ?_, ?_⟩
  · simpa using (congrArg List.length hb).symm
  · rw [← merkleMuxExec_encode, ← hb, heq]

/-! ## §2. The gadget — one `membershipGadget` per round, AirMembership reused verbatim. -/

/-- A `finRange`-indexed family of subsystems accepts iff every member system accepts —
the `flatMap` sibling of `systemAccepts_map_finRange`, spent once. -/
theorem systemAccepts_flatMap_finRange {m : ℕ} (asg : Idx → F)
    (f : Fin m → ConstraintSystem F Idx) :
    systemAccepts asg ((List.finRange m).flatMap f) ↔ ∀ k, systemAccepts asg (f k) := by
  unfold systemAccepts
  constructor
  · intro h k t ht
    exact h t (List.mem_flatMap.mpr ⟨k, List.mem_finRange k, ht⟩)
  · rintro h t ht
    obtain ⟨k, -, htk⟩ := List.mem_flatMap.mp ht
    exact h k t htk

/-- **The opening-binding gadget** `[RECURSE-merkle-bind]`: per round one
`membershipGadget` (AirMembership's, verbatim — booleanity per direction wire + the
`pathTerm` root assertion) with the OPENED wire as leaf and the round's commitment root
wire as root. The opened values cannot be free-floating: each must fold up its path to the
committed root. A `ConstraintSystem`, so the emit path applies verbatim (§6). -/
def openingBindingGadget (spec : PermSpec F 2) (rootW openedW : Fin rounds → Idx)
    (paths : Fin rounds → List (Idx × Idx)) : ConstraintSystem F Idx :=
  (List.finRange rounds).flatMap fun k =>
    membershipGadget spec (openedW k) (rootW k) (paths k)

/-! ## §3. The keystone iff, teeth, completeness, and the ∃-form meaning. -/

/-- **`openingBinding_correct` — the keystone iff.** The system accepts `asg` IFF every
round's opened value is Merkle-bound: direction wires boolean, root wire EXACTLY the path
fold of the opened wire (`OpeningsBound`, statement-first). Per round this is
`membership_correct`, reused — no new constraint reasoning. -/
theorem openingBinding_correct (asg : Idx → F) (spec : PermSpec F 2)
    (rootW openedW : Fin rounds → Idx) (paths : Fin rounds → List (Idx × Idx)) :
    systemAccepts asg (openingBindingGadget spec rootW openedW paths) ↔
      OpeningsBound spec (fun k => asg (rootW k)) (fun k => asg (openedW k))
        (fun k => (paths k).map fun sd => (asg sd.1, asg sd.2)) := by
  unfold openingBindingGadget OpeningsBound
  rw [systemAccepts_flatMap_finRange]
  refine forall_congr' fun k => Iff.trans
    (membership_correct asg spec (openedW k) (rootW k) (paths k))
    (and_congr ⟨fun h sd hsd => ?_, fun h sd hsd => h _ (List.mem_map.mpr ⟨sd, hsd, rfl⟩)⟩
      Iff.rfl)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hsd
  exact h x hx

/-- The EXECUTOR reading of the keystone — `accepts_iff_semHolds` (initiality) doing the
transfer, no new trust. -/
theorem openingBinding_semHolds_correct (asg : Idx → F) (spec : PermSpec F 2)
    (rootW openedW : Fin rounds → Idx) (paths : Fin rounds → List (Idx × Idx)) :
    systemSemHolds asg (openingBindingGadget spec rootW openedW paths) ↔
      OpeningsBound spec (fun k => asg (rootW k)) (fun k => asg (openedW k))
        (fun k => (paths k).map fun sd => (asg sd.1, asg sd.2)) := by
  rw [← systemAccepts_iff_systemSemHolds, openingBinding_correct]

/-- **Teeth, general form**: an assignment with ANY round's root wire off its path fold is
REJECTED — the forged-opening attack fails, for every spec, depth, and assignment. -/
theorem openingBinding_teeth (asg : Idx → F) (spec : PermSpec F 2)
    (rootW openedW : Fin rounds → Idx) (paths : Fin rounds → List (Idx × Idx))
    (k : Fin rounds)
    (h : asg (rootW k) ≠ merkleMuxExec spec (asg (openedW k))
      ((paths k).map fun sd => (asg sd.1, asg sd.2))) :
    ¬ systemAccepts asg (openingBindingGadget spec rootW openedW paths) :=
  fun hacc => h (((openingBinding_correct asg spec rootW openedW paths).mp hacc k).2)

/-- **Soundness toward the set framing**: EVERY accepting assignment's opened values are
genuine `memberAtDepth` members of their committed roots — no forged opening survives
short of a fold-preimage (`[COMMIT-CR]` prices finding one). -/
theorem openingBinding_member (asg : Idx → F) (spec : PermSpec F 2)
    (rootW openedW : Fin rounds → Idx) (paths : Fin rounds → List (Idx × Idx))
    (hacc : systemAccepts asg (openingBindingGadget spec rootW openedW paths))
    (k : Fin rounds) :
    memberAtDepth spec (paths k).length (asg (rootW k)) (asg (openedW k)) := by
  have hm := ((openingBinding_correct asg spec rootW openedW paths).mp hacc).member k
  simpa using hm

/-- **Completeness / premise-inhabitation**: genuine `Bool` paths carried on the wires
(encoded directions, genuine folds on the root wires) ACCEPT — at every layout. -/
theorem openingBinding_complete (asg : Idx → F) (spec : PermSpec F 2)
    (rootW openedW : Fin rounds → Idx) (paths : Fin rounds → List (Idx × Idx))
    (bpath : Fin rounds → List (F × Bool))
    (hpath : ∀ k, ((paths k).map fun sd => (asg sd.1, asg sd.2)) = (bpath k).map encodeStep)
    (hroot : ∀ k, asg (rootW k) = merkleExec spec (asg (openedW k)) (bpath k)) :
    systemAccepts asg (openingBindingGadget spec rootW openedW paths) := by
  rw [openingBinding_correct]
  intro k
  refine ⟨fun sd hsd => ?_, ?_⟩
  · have hsd' : sd ∈ (bpath k).map encodeStep := by
      have h0 : sd ∈ (paths k).map fun sd => (asg sd.1, asg sd.2) := hsd
      rwa [hpath k] at h0
    obtain ⟨⟨sv, b⟩, -, rfl⟩ := List.mem_map.mp hsd'
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  · show asg (rootW k) = merkleMuxExec spec (asg (openedW k))
      ((paths k).map fun sd => (asg sd.1, asg sd.2))
    rw [hpath k, merkleMuxExec_encode]
    exact hroot k

/-! ### The ∃-form meaning, at the canonical multi-round layout. -/

/-- Canonical wire layout for a `rounds`-family of depth-`depth k` opening bindings —
`MWire`'s shape, one family per round. -/
inductive OWire (rounds : ℕ) (depth : Fin rounds → ℕ) : Type u where
  /-- Round `k`'s opened-value (leaf) wire. -/
  | openedW (k : Fin rounds) : OWire rounds depth
  /-- Round `k`'s commitment-root wire. -/
  | rootW (k : Fin rounds) : OWire rounds depth
  /-- Round `k`'s level-`j` sibling wire. -/
  | sibW (k : Fin rounds) (j : Fin (depth k)) : OWire rounds depth
  /-- Round `k`'s level-`j` direction wire. -/
  | dirW (k : Fin rounds) (j : Fin (depth k)) : OWire rounds depth

/-- The canonical per-round `(sibling, direction)` wire list. -/
def oCanonPaths {rounds : ℕ} (depth : Fin rounds → ℕ) (k : Fin rounds) :
    List (OWire.{u} rounds depth × OWire.{u} rounds depth) :=
  List.ofFn fun j => (OWire.sibW k j, OWire.dirW k j)

/-- The canonical accepting assignment for a family of `Bool` paths: opened/root values on
their wires, the `j`-th sibling and ENCODED direction bit of round `k`'s path on theirs. -/
def oCanonAsg {rounds : ℕ} {depth : Fin rounds → ℕ} (openedv rootv : Fin rounds → F)
    (bpath : Fin rounds → List (F × Bool)) (hlen : ∀ k, (bpath k).length = depth k) :
    OWire.{u} rounds depth → F
  | .openedW k => openedv k
  | .rootW k => rootv k
  | .sibW k j => ((bpath k)[j.val]'(by rw [hlen k]; exact j.isLt)).1
  | .dirW k j => encodeBit ((bpath k)[j.val]'(by rw [hlen k]; exact j.isLt)).2

/-- Reading the canonical assignment along the canonical wires recovers the encoded
paths. -/
theorem oCanonAsg_map {rounds : ℕ} {depth : Fin rounds → ℕ}
    (openedv rootv : Fin rounds → F) (bpath : Fin rounds → List (F × Bool))
    (hlen : ∀ k, (bpath k).length = depth k) (k : Fin rounds) :
    ((oCanonPaths depth k).map fun sd =>
        (oCanonAsg openedv rootv bpath hlen sd.1, oCanonAsg openedv rootv bpath hlen sd.2))
      = (bpath k).map encodeStep := by
  apply List.ext_getElem
  · simp [oCanonPaths, hlen k]
  · intro i h1 h2
    simp [oCanonPaths, oCanonAsg, encodeStep]

/-- **`openingBinding_meaning` — the set framing, closed both ways.** An assignment
carrying the claimed roots and opened values on the canonical wires satisfies the
opening-binding gadget IFF EVERY opened value is a genuine depth-`depth k` member of its
round's root. The opened values cannot be forged: they must be members of the committed
codeword tree (finding a member witness for a non-member is `[COMMIT-CR]`'s priced
collision). -/
theorem openingBinding_meaning (spec : PermSpec F 2) {rounds : ℕ}
    (depth : Fin rounds → ℕ) (rootv openedv : Fin rounds → F) :
    (∃ asg : OWire.{u} rounds depth → F,
        (∀ k, asg (.openedW k) = openedv k) ∧ (∀ k, asg (.rootW k) = rootv k) ∧
          systemAccepts asg (openingBindingGadget spec (fun k => .rootW k)
            (fun k => .openedW k) (oCanonPaths depth))) ↔
      ∀ k, memberAtDepth spec (depth k) (rootv k) (openedv k) := by
  constructor
  · rintro ⟨asg, ho, hr, hacc⟩ k
    have hm := ((openingBinding_correct asg spec _ _ _).mp hacc).member k
    simpa [oCanonPaths, ho k, hr k] using hm
  · intro hmem
    choose bpath hlen hfold using hmem
    refine ⟨oCanonAsg openedv rootv bpath hlen, fun _ => rfl, fun _ => rfl,
      openingBinding_complete _ spec _ _ _ bpath
        (oCanonAsg_map openedv rootv bpath hlen) fun k => (hfold k).symm⟩

/-! ## §4. The FULL verifier — `boundVerifier ++ openingBindingGadget`, one system. -/

/-- **The full light-client verifier**: the FS-bound verifier (challenge binding ++
sumcheck ++ FRI query) ++ the opening binding, as ONE system. The binding is load-bearing
exactly when the opened wires are SHARED (`openedW k = lo k`, and — pair-per-leaf — `hi k`
as the first sibling wire of round `k`'s path); `spec` is the FS sponge permutation,
`mspec` the width-2 Merkle compression. -/
def fullVerifier [NeZero w] (spec : PermSpec F w) (mspec : PermSpec F 2)
    (transcript : Fin s → Fin w → Idx) (challenge : Fin s → Idx)
    (claimW scFinalW : Idx) (g0 g1 chal : Fin n → Idx)
    (half : F) (friFinalW : Idx) (lo hi next beta tw twoX : Fin rounds → Idx)
    (rootW openedW : Fin rounds → Idx) (paths : Fin rounds → List (Idx × Idx)) :
    ConstraintSystem F Idx :=
  boundVerifier spec transcript challenge claimW scFinalW g0 g1 chal
      half friFinalW lo hi next beta tw twoX
    ++ openingBindingGadget mspec rootW openedW paths

/-- **`fullVerifier_correct` — the composed keystone.** The full verifier accepts IFF the
challenges are the FS chain hashes of the transcript AND the sumcheck verifier accepts AND
the FRI query verifier accepts AND every opened value is Merkle-bound to its committed
root — `systemAccepts_append` + the landed keystones, zero new constraint work. -/
theorem fullVerifier_correct [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (mspec : PermSpec F 2) (transcript : Fin s → Fin w → Idx) (challenge : Fin s → Idx)
    (claimW scFinalW : Idx) (g0 g1 chal : Fin n → Idx)
    (half : F) (friFinalW : Idx) (lo hi next beta tw twoX : Fin rounds → Idx)
    (rootW openedW : Fin rounds → Idx) (paths : Fin rounds → List (Idx × Idx)) :
    systemAccepts asg (fullVerifier spec mspec transcript challenge claimW scFinalW
        g0 g1 chal half friFinalW lo hi next beta tw twoX rootW openedW paths) ↔
      (FsBound spec (transcriptVals asg transcript) (fun k => asg (challenge k))
        ∧ SumcheckVerifierAccepts (asg claimW) (asg scFinalW)
            (fun i => asg (g0 i)) (fun i => asg (g1 i)) (fun i => asg (chal i))
        ∧ FriQueryAccepts half (asg friFinalW)
            (fun k => asg (lo k)) (fun k => asg (hi k)) (fun k => asg (next k))
            (fun k => asg (beta k)) (fun k => asg (tw k)) (fun k => asg (twoX k))
        ∧ OpeningsBound mspec (fun k => asg (rootW k)) (fun k => asg (openedW k))
            (fun k => (paths k).map fun sd => (asg sd.1, asg sd.2))) := by
  unfold fullVerifier
  rw [systemAccepts_append, boundVerifier_correct, openingBinding_correct, and_assoc,
    and_assoc]

/-- **Nothing on the proof-carrying wires is free.** At the shared wiring (challenge wires
ARE squeeze wires, opened wires ARE the FRI `lo` wires), EVERY accepting assignment has
its sumcheck challenges and FRI fold challenges equal to the FS chain hashes of the
transcript AND its opened values genuine Merkle members of the committed roots — the
challenges are derived, the openings are committed, as a theorem about every accepting
assignment. -/
theorem fullVerifier_binds [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (mspec : PermSpec F 2) (transcript : Fin s → Fin w → Idx) (challenge : Fin s → Idx)
    (claimW scFinalW : Idx) (g0 g1 chal : Fin n → Idx)
    (half : F) (friFinalW : Idx) (lo hi next beta tw twoX : Fin rounds → Idx)
    (rootW openedW : Fin rounds → Idx) (paths : Fin rounds → List (Idx × Idx))
    (e : Fin n → Fin s) (he : ∀ i, chal i = challenge (e i))
    (eb : Fin rounds → Fin s) (heb : ∀ k, beta k = challenge (eb k))
    (ho : ∀ k, openedW k = lo k)
    (hacc : systemAccepts asg (fullVerifier spec mspec transcript challenge claimW
      scFinalW g0 g1 chal half friFinalW lo hi next beta tw twoX rootW openedW paths)) :
    (∀ i, asg (chal i) = fsChainVal spec (transcriptVals asg transcript) (e i).val)
      ∧ (∀ k, asg (beta k) = fsChainVal spec (transcriptVals asg transcript) (eb k).val)
      ∧ ∀ k, memberAtDepth mspec (paths k).length (asg (rootW k)) (asg (lo k)) := by
  obtain ⟨hfs, -, -, hob⟩ := (fullVerifier_correct asg spec mspec transcript challenge
    claimW scFinalW g0 g1 chal half friFinalW lo hi next beta tw twoX rootW openedW
    paths).mp hacc
  refine ⟨fun i => by rw [he i]; exact hfs (e i),
    fun k => by rw [heb k]; exact hfs (eb k), fun k => ?_⟩
  have hm := hob.member k
  rw [ho k] at hm
  simpa using hm

/-! ## §5. Keystone witnesses — BUILT over `ZMod 7` and `ZMod 13`, all `decide`d against
the REAL fold via `AirRange`'s `Decidable` instances. -/

namespace MerkleBindExample

/-! ### The binding alone, `ZMod 7` — the opened wire is FULLY DETERMINED.

`FiatShamirExample.spec7` as the compression (`H2₇(a, b) = hashExec spec7 ![a, b]`).
Layout on `Fin 4`: opened (leaf) 0, sibling 1, direction 2, root 3; one round, depth 1.
Honest: opened `4`, sibling `5`, direction `0` (leaf left), root `H2₇(4, 5) = 6`. Over
`ZMod 7` the fiber of root `6` along `v ↦ H2₇(v, 5)` is UNIQUELY `v = 4` — the opened
value is fully forced, no toy-field collision in this fiber. -/

/-- The 1-round, depth-1 opening binding over `ZMod 7`. -/
def obGadget7 : ConstraintSystem (ZMod 7) (Fin 4) :=
  openingBindingGadget (rounds := 1) FiatShamirExample.spec7 ![3] ![0] ![[(1, 2)]]

/-- *The executor computes*: opened `4` under sibling `5`, direction `false` folds to
`6`. -/
example : merkleExec FiatShamirExample.spec7 4 [(5, false)] = 6 := by decide

/-- *Satisfiable, computed*: the genuine member (opened `4`, sibling `5`, bit `0`, root
`6`) is ACCEPTED — decided raw against the real fold. -/
example : systemAccepts ![4, 5, 0, 6] obGadget7 := by decide

/-- *Teeth (forged root), computed*: root `5 ≠ 6` under the same path is REJECTED. -/
example : ¬ systemAccepts ![4, 5, 0, 5] obGadget7 := by decide

/-- *The root wire is FORCED, quantified*: with the path fixed, acceptance holds iff the
root wire carries exactly the fold — over every field element. -/
example : ∀ r : ZMod 7, systemAccepts ![4, 5, 0, r] obGadget7 ↔ r = 6 := by decide

/-- *The OPENED wire is FORCED, quantified — the forgery door is closed over the whole
field*: with the committed root `6` fixed, acceptance holds iff the opened wire is the
genuine member `4`. No forged opening exists at this root, quantified over all 7 values. -/
example : ∀ v : ZMod 7, systemAccepts ![v, 5, 0, 6] obGadget7 ↔ v = 4 := by decide

/-- *Teeth (non-boolean direction), computed*: direction `2` is REJECTED even with the
root wire set to `2` — exactly the value the mux-arithmetic fold takes at `δ = 2`
(`H2₇(6, 3) = 2`)… -/
example : ¬ systemAccepts ![4, 5, 2, 2] obGadget7 := by decide

/-- *…and the attribution is machine-checked*: the root assertion ALONE accepts that
assignment — booleanity did the rejecting, exactly as in AirMembership. -/
example : accepts (![4, 5, 2, 2] : Fin 4 → ZMod 7)
    (rootTerm FiatShamirExample.spec7 0 3 [(1, 2)]) := by decide

/-! ### THE FULL VERIFIER, `ZMod 13` — the forged-opening attack rejected.

`FiatShamirAir`'s composed demo EXTENDED: the same FS chain (5 squeezes over `demoSpec`,
challenge wires shared), the same sumcheck (MLE-of-AND) and FRI (1 round, the fold of
`p(X) = 3X + 2` at `x = 2`, `half = 7`) — now with the FRI opening Merkle-bound. Layout
on `Fin 19`: wires 0–16 as in `FiatShamirExample` (sumcheck 0–7, FRI 8–14, FS state
15–16), root₀ at 17, direction₀ at 18. The path of `lo` (wire 9) is `[(10, 18)]` — the
sibling wire IS the `hi` wire (wire 10): the deployed pair-per-leaf layout, `(f(x), f(−x))`
one committed leaf pair sharing one authentication path, by wire-sharing. `openedW = lo`
(wire 9): sharing, not copying. Honest: `lo = 8`, `hi = 9`, direction `0`, root
`H2(8, 9) = 0`.

The attack this file exists to kill: the fold check reads `2·lo + 12·hi ≐ next` (at the
pinned `β = 6`, `tw = 10`, `half = 7`), so for EVERY forged `lo = v` the partner
`hi = 2v − 7` keeps the whole FS-bound verifier accepting — 13 fold-consistent forgeries,
every one accepted by everything `FiatShamirAir` landed. The opening binding cuts the
accepted set to the collision fiber of the committed root: `{8}` ∪ the toy hash's
collisions `{1, 2}` — `[COMMIT-CR]` made CONCRETE: the constraints force `root = fold`;
that a forger cannot FIND another fold preimage is collision resistance, findable in a
13-element toy field, priced at deployed parameters by the label. -/

set_option maxRecDepth 16384

/-- The five squeeze wires (as in `FiatShamirExample.wChalFS`, lifted to `Fin 19`). -/
def wChalMB : Fin 5 → Fin 19 := ![15, 6, 16, 7, 12]

/-- The five absorb blocks (as in `FiatShamirExample.transcript13`). -/
def transcriptMB : Fin 5 → Fin 2 → Fin 19 :=
  ![![0, 2], ![15, 4], ![6, 3], ![16, 5], ![7, 1]]

def scG0MB : Fin 2 → Fin 19 := ![2, 3]
def scG1MB : Fin 2 → Fin 19 := ![4, 5]
def scChalMB : Fin 2 → Fin 19 := ![6, 7]

/-- **The full light-client verifier** over `ZMod 13` at the shared layout: FS binding ++
sumcheck ++ FRI query ++ opening binding, `openedW = lo` (wire 9) and `hi` (wire 10) the
path sibling — one `ConstraintSystem`. -/
def fullDemo : ConstraintSystem (ZMod 13) (Fin 19) :=
  fullVerifier demoSpec demoSpec transcriptMB wChalMB 0 1 scG0MB scG1MB scChalMB
    7 8 ![9] ![10] ![11] ![12] ![13] ![14] ![17] ![9] ![[(10, 18)]]

/-- The FS-bound verifier part alone (everything `FiatShamirAir` landed, at this layout) —
the system the forged openings PASS. -/
def boundPart : ConstraintSystem (ZMod 13) (Fin 19) :=
  boundVerifier demoSpec transcriptMB wChalMB 0 1 scG0MB scG1MB scChalMB
    7 8 ![9] ![10] ![11] ![12] ![13] ![14]

/-- The opening binding part alone — the system that kills them. -/
def bindPart : ConstraintSystem (ZMod 13) (Fin 19) :=
  openingBindingGadget demoSpec ![17] ![9] ![[(10, 18)]]

/-- The HONEST assignment: `FiatShamirExample.honest` extended by the genuine root
`H2(8, 9) = 0` and direction `0`. -/
def honestMB : Fin 19 → ZMod 13 :=
  ![1, 5, 0, 0, 1, 10, 10, 7, 7, 8, 9, 7, 6, 10, 4, 6, 10, 0, 0]

/-- The fold-consistent forgery family: opened `lo = v` with partner `hi = 2v − 7`
(EXACTLY the pairs the FRI fold check accepts at the FS-pinned `β`), everything else
honest — `v = 8` is the honest run. -/
def familyMB (v : ZMod 13) : Fin 19 → ZMod 13 :=
  ![1, 5, 0, 0, 1, 10, 10, 7, 7, v, 2 * v - 7, 7, 6, 10, 4, 6, 10, 0, 0]

/-- *The executor computes*: the honest opening folds to the committed root —
`H2(8, 9) = 0`. -/
example : merkleExec demoSpec 8 [(9, false)] = 0 := by decide

/-- *Satisfiable, computed*: the honest run — FS-derived challenges, genuine sumcheck and
FRI transcripts, the opening a genuine member of the committed root — is ACCEPTED by the
WHOLE verifier in one system. -/
example : systemAccepts honestMB fullDemo := by decide

/-- *The attack the binding exists to kill, computed*: the forged opening pair
`(lo, hi) = (9, 11)` — fold-consistent, so the ENTIRE FS-bound verifier (challenge
binding + sumcheck + FRI, everything previously landed) ACCEPTS it. Openings without
provenance are forgeable at will. -/
example : systemAccepts (familyMB 9) boundPart := by decide

/-- *…and the opening binding alone kills it*: `H2(9, 11) = 9 ≠ 0` — the committed root
does not match the forged fold. The Merkle binding is load-bearing, not decorative. -/
example : ¬ systemAccepts (familyMB 9) bindPart := by decide

/-- *So the FULL verifier rejects the forged opening.* -/
example : ¬ systemAccepts (familyMB 9) fullDemo := by decide

/-- *The whole forgery family passes the unbound verifier, quantified*: ALL 13
fold-consistent forgeries are accepted by everything short of the opening binding. -/
example : ∀ v : ZMod 13, systemAccepts (familyMB v) boundPart := by decide

/-- *The binding cuts the family to the collision fiber, quantified — `[COMMIT-CR]` made
concrete*: the full verifier accepts the forgery family EXACTLY on the fiber of the
committed root — the honest `8`, plus `1` and `2`, the toy 13-element hash's findable
collisions (`H2(1, 8) = H2(2, 10) = H2(8, 9) = 0`). The constraints force `root = fold`
(that iff is the theorem); that no OTHER fold preimage can be FOUND is collision
resistance of the instantiated compression — the `[COMMIT-CR]` floor, visible here
because a 13-element field has findable collisions, priced at deployed parameters by the
label, never smuggled into a theorem. -/
example : ∀ v : ZMod 13,
    systemAccepts (familyMB v) fullDemo ↔ (v = 1 ∨ v = 2 ∨ v = 8) := by decide

/-- *The root wire is FORCED, quantified*: with the honest openings fixed, acceptance
holds iff the root wire carries exactly `H2(8, 9) = 0` — the commitment the prover binds
to is pinned, over every field element. -/
example : ∀ r : ZMod 13,
    systemAccepts ![1, 5, 0, 0, 1, 10, 10, 7, 7, 8, 9, 7, 6, 10, 4, 6, 10, r, 0]
      fullDemo ↔ r = 0 := by decide

/-- *The general binding, consumed on the demo*: EVERY accepting assignment of `fullDemo`
has its FRI opened value a genuine depth-1 Merkle member of its committed root —
`fullVerifier_binds` at the shared wiring, no enumeration. -/
example (asg : Fin 19 → ZMod 13) (h : systemAccepts asg fullDemo) :
    memberAtDepth demoSpec 1 (asg 17) (asg 9) := by
  have hb := (fullVerifier_binds asg demoSpec demoSpec transcriptMB wChalMB 0 1 scG0MB
    scG1MB scChalMB 7 8 ![9] ![10] ![11] ![12] ![13] ![14] ![17] ![9] ![[(10, 18)]]
    ![1, 3] (by decide) ![4] (by decide) (fun _ => rfl) h).2.2 0
  simpa using hb

/-! ## §6. THE CROWN, BUILT — the full verifier EMITS.

Because `fullVerifier` is a `ConstraintSystem`, the verified emit path applies with zero
new work: the emitted `ConstraintDescriptor`'s satisfiability IS the full verifier's
acceptance. **"The full light-client verifier accepted this transcript" — challenges
FS-derived, openings Merkle-members, sumcheck and FRI passed — is ONE emitted,
Loom-provable statement.** A Loom proof of the emitted statement is a self-contained
recursive proof: a proof that a proof verified, with no free wire on the proof-carrying
path (`fullVerifier_binds`). Remaining mass: `[RECURSE-full-resid]` (header), the floors
named, none load-bearing in any theorem here. -/

/-- **The full verifier emitted**: descriptor satisfiability at the demo layout ⟺ the
whole light-client verifier accepts — `emit_accepts_iff_fin` consumed on the composed
system, no new proof. -/
example (asg : Fin 19 → ZMod 13) :
    (∃ wv : ℕ → ZMod 13, (∀ i : Fin 19, wv i.val = asg i) ∧
        descriptorHolds (emit Fin.val 19 19 fullDemo) wv)
      ↔ systemAccepts asg fullDemo :=
  emit_accepts_iff_fin 19 19 asg fullDemo

end MerkleBindExample

/-! ### Honest residuals — the rungs above this one (named, none stubbed)

`[RECURSE-full-resid]` — itemized in the header: (1) root absorption into the FS
transcript (wire-sharing, landed mechanism, not yet required by hypothesis); (2) the
sumcheck oracle wire's own opening binding (same vocabulary, not instantiated); (3)
`twoX`/query-index domain-point arithmetization (new vocabulary); (4) query multiplicity
(instantiation by `++`); (5) the Assurance-side Loom identifications
(`[RECURSE-fs-bridge]`/`[RECURSE-sumcheck-bridge]`/`[RECURSE-fri-bridge]` + the Merkle
one). FLOORS: `[COMMIT-CR]` (§5 exhibits its concreteness — the accepted forgery set IS
the toy hash's collision fiber), `[FS-oracle]`, `[RECURSE-fs-sponge]`,
`[AIR-poseidon-params]` — assumptions on the instantiated primitives, never theorems
here. -/

end Minidregg.Compiler
